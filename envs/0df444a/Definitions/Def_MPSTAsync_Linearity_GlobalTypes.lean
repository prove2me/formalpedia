-- Prove2me | Definitions.Def_MPSTAsync_Linearity_GlobalTypes
-- name    : MPSTAsync_Linearity_GlobalTypes
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T23:02:59.506004+00:00
-- url     : https://prove2.me/theorems/06589882-80ca-4596-85f7-a0f2056fb55d
-- title:
--   Fig. 4 and Notation A.1 — global and end-point types, substitution, finite unfoldings
-- statement:
--   A **global type** describes the actions of a multiparty session: a value communication, a labelled choice, parallel composition, recursion, a recursion variable, or termination. Value types contain either a list of sorts or a located end-point type; a shared-name sort can itself carry a global type. The end-point syntax records sends, receives, selections, branches, recursion, variables, and termination.
--
--   For a global type $G$, let $G^{(n)}$ denote the result of unfolding each recursion $n$ times, with the remaining bound variable replaced by termination. In particular, for a single recursion $G=\mu t.H$,
--
--   $$
--   G^{(0)}=H[\mathrm{end}/t],\qquad G^{(n+1)}=H[G^{(n)}/t].
--   $$
--
--   These definitions supply the finite syntax on which action ordering and channel linearity are checked. Unfolding leaves carried global types untouched.
--
--   **Formalization Note** Roles, labels, recursion variables, and channel indices are natural numbers. The constructor `mu` represents the paper's $\mu$ binder, and `SType` represents its sort grammar; Lean reserves `rec` and `Sort` as names. The sort grammar has Boolean, natural-number, shared-name, and coded additional base sorts. Substitution stops at a binder of the same variable and is capture avoiding for the closed replacement types used by well-formed global types.
-- source:
--   Honda, Yoshida, Carbone, Multiparty Asynchronous Session Types, J. ACM 63(1) (2016), Art. 9, pp. 12–13, 20, 52, Fig. 4 and Notation A.1; https://doi.org/10.1145/2827695

import Mathlib

namespace MPSTAsync.Linearity

abbrev Role := ℕ
abbrev Label := ℕ
abbrev TVar := ℕ

mutual
  inductive GType where
    | comm (p q : Role) (k : ℕ) (U : VType) (G : GType)
    | branch (p q : Role) (k : ℕ) (bs : List (Label × GType))
    | par (G₁ G₂ : GType)
    | mu (t : TVar) (G : GType)
    | var (t : TVar)
    | stop
  inductive VType where
    | sorts (Ss : List SType)
    | located (T : EType) (p : Role)
  inductive SType where
    | bool
    | nat
    | base (code : ℕ)
    | shared (G : GType)
  inductive EType where
    | send (k : ℕ) (U : VType) (T : EType)
    | recv (k : ℕ) (U : VType) (T : EType)
    | sel (k : ℕ) (bs : List (Label × EType))
    | bra (k : ℕ) (bs : List (Label × EType))
    | mu (t : TVar) (T : EType)
    | var (t : TVar)
    | stop
end

/- A closed replacement is used at a recursive binder. Substitution stops at a
   binder for the same variable; carried types are separate, closed scopes. -/
mutual
  def subst (t : TVar) (X : GType) : GType → GType
    | .comm p q k U G => .comm p q k U (subst t X G)
    | .branch p q k bs => .branch p q k (substBranches t X bs)
    | .par G H => .par (subst t X G) (subst t X H)
    | .mu u G => if t = u then .mu u G else .mu u (subst t X G)
    | .var u => if t = u then X else .var u
    | .stop => .stop
  def substBranches (t : TVar) (X : GType) : List (Label × GType) → List (Label × GType)
    | [] => []
    | (l, G) :: bs => (l, subst t X G) :: substBranches t X bs
end

/- Notation A.1: n=0 already replaces each recursion by its body with end
   substituted for the bound variable. No unfolding enters carried types. -/
mutual
  def unfold (n : ℕ) : GType → GType
    | .comm p q k U G => .comm p q k U (unfold n G)
    | .branch p q k bs => .branch p q k (unfoldBranches n bs)
    | .par G H => .par (unfold n G) (unfold n H)
    | .mu t G => (fun X => subst t X (unfold n G))^[n+1] .stop
    | .var t => .var t
    | .stop => .stop
  def unfoldBranches (n : ℕ) : List (Label × GType) → List (Label × GType)
    | [] => []
    | (l, G) :: bs => (l, unfold n G) :: unfoldBranches n bs
end

end MPSTAsync.Linearity


