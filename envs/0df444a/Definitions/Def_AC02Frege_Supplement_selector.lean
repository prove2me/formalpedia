-- Prove2me | Definitions.Def_AC02Frege_Supplement_selector
-- name    : AC02Frege_Supplement_selector
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T19:56:36.959451+00:00
-- url     : https://prove2.me/theorems/b421c441-a2a0-4763-abdb-94e57abde6ff
-- title:
--   Selector substitution $F'\circ\mathrm{Sel}_q$ and the selector restriction $\rho$
-- statement:
--   Let $q\ge2$. The **selector function** $\mathrm{Sel}_q$ reads $2q$ bits $X=(X_{1,1},\dots,X_{1,q};X_{0,1},\dots,X_{0,q})$ arranged in two rows; on one-hot inputs it returns the row $b\in\{0,1\}$ of the bit equal to $1$, so there $\mathrm{Sel}_q(X)=\bigvee_a X_{1,a}$ and $\neg\mathrm{Sel}_q(X)=\bigvee_a X_{0,a}$.
--
--   For a CNF $F'$ on variables $y_1,\dots,y_{n'}$, the CNF $F'\circ\mathrm{Sel}_q$ has a block $X_i$ of $2q$ variables $X_{i,b,a}$ for each $i$, and consists of
--
--   1. for each clause $C$ of $F'$, the clause $C^{\mathrm{Sel}}$ obtained by replacing each literal $y_i$ by $\bigvee_a X_{i,1,a}$ and each literal $\neg y_i$ by $\bigvee_a X_{i,0,a}$;
--   2. for each block $i$, the one-hot clauses: $\bigvee_{b,a}X_{i,b,a}$, and $\neg X_{i,b,a}\vee\neg X_{i,b',a'}$ for every two distinct bits of the block.
--
--   A **selector restriction** $\rho$ chooses, for each block $i$ and row $b$, a column $A_{i,b}\in[q]$, and substitutes
--   $$
--   X_{i,1,A_{i,1}}\mapsto y_i,\qquad X_{i,0,A_{i,0}}\mapsto 1+y_i,\qquad X_{i,b,a}\mapsto 0\ \ (a\ne A_{i,b}).
--   $$
--   A random selector restriction chooses the $2n'$ columns independently and uniformly. For a $\mathrm{Res}(\mathrm{PC})$ refutation $\Pi$ of $F'\circ\mathrm{Sel}_q$, $\Pi|_\rho$ replaces every polynomial $u$ by the multilinearization $\mathrm{ML}(u|_\rho)$.
--
--   This is the gadget and the random restriction of Theorem 6.3, which converts total-size lower bounds for unrestricted-degree $\mathrm{Res}(\mathrm{PC})$ into line lower bounds for $\mathrm{Res}(\mathrm{PC}_{2d})$.
--
--   **Formalization Note** The variables of $F'$ are a finite type `V`; the variable $X_{i,b,a}$ is `(i, b, a) : V × Bool × Fin q`, with row $1$ as `true`. Both literals of $y_i$ become disjunctions of positive literals. A restriction is a function `A : V → Bool → Fin q`, applied by `MvPolynomial.aeval` and followed by the base `ML`.
-- source:
--   Alekseev, Gryaznov, Pitassi, Robere, Shekhovtsov, Tzameret, Progress on AC0[2]-Frege Lower Bounds (manuscript dated November 3, 2026, STOC 2027 submission, sha256 88d149fa2bcae702e55a6b72efecda2b4137fd18dca3e23a056c3db5da0ece61), Definition 6.1, p.33; Definition 6.2, pp.33–34; Theorem 6.3, proof (Step 1), p.34

import Mathlib
import Definitions.Def_LiftSAParity_CNF
import Definitions.Def_AC02Frege_ML
import Definitions.Def_AC02Frege_Supplement_ResPC

namespace AC02Frege.Supplement

open MvPolynomial LiftSAParity

/-- The clause `C^Sel` of the selector substitution (Alekseev–Gryaznov–Pitassi–Robere–Shekhovtsov–
Tzameret, *Progress on AC0[2]-Frege Lower Bounds*, manuscript (sha256 88d149fa…), Definition 6.1,
p.33): each literal `y_i` of `C` is replaced by `⋁_a X_{i,1,a}` and each literal `¬y_i` by
`⋁_a X_{i,0,a}`.

**Formalization Note** The variable `X_{i,b,a}` (block `i`, row `b ∈ {0,1}`, column `a ∈ [q]`) is
`(i, b, a) : V × Bool × Fin q`, with row `1` = `true`. Both literals of `y_i` become disjunctions of
**positive** literals `((i, b, a), true)`; the row is the polarity of the literal. -/
def selClause {V : Type*} [DecidableEq V] (q : ℕ) (C : Clause V) : Clause (V × Bool × Fin q) :=
  C.biUnion (fun l => (Finset.univ : Finset (Fin q)).image (fun a => ((l.1, l.2, a), true)))

/-- The one-hot clauses `C′_i` of block `i` (Definition 6.1, p.33): the at-least-one clause
`⋁_{b,a} X_{i,b,a}`, and the clause `¬X_{i,b,a} ∨ ¬X_{i,b′,a′}` for every two distinct bits of the
block. -/
def oneHotClauses {V : Type*} [DecidableEq V] (q : ℕ) (i : V) :
    Finset (Clause (V × Bool × Fin q)) :=
  insert ((Finset.univ : Finset (Bool × Fin q)).image (fun x => ((i, x.1, x.2), true)))
    (((Finset.univ : Finset ((Bool × Fin q) × (Bool × Fin q))).filter (fun p => p.1 ≠ p.2)).image
      (fun p => ({((i, p.1.1, p.1.2), false), ((i, p.2.1, p.2.2), false)} :
        Clause (V × Bool × Fin q))))

/-- The **selector substitution** `F′ ∘ Sel_q` (Definition 6.1, p.33): the CNF over the `2n′q`
variables `X_{i,b,a}` consisting of the clauses `C^Sel`, `C ∈ F′`, and the one-hot clauses of every
block `i`. -/
def selSubst {V : Type*} [Fintype V] [DecidableEq V] (F' : CNF V) (q : ℕ) :
    CNF (V × Bool × Fin q) :=
  F'.image (selClause q) ∪ (Finset.univ : Finset V).biUnion (oneHotClauses q)

/-- The **selector restriction** `ρ` determined by a choice of columns `A_{i,b} = A i b`
(Definition 6.2, pp.33–34), as a substitution of polynomials in the original variables:
`X_{i,1,A_{i,1}} ↦ y_i`, `X_{i,0,A_{i,0}} ↦ 1 + y_i`, and `X_{i,b,a} ↦ 0` for `a ≠ A_{i,b}`. -/
noncomputable def selRho {V : Type*} {q : ℕ} (A : V → Bool → Fin q) (x : V × Bool × Fin q) :
    MvPolynomial V (ZMod 2) :=
  if x.2.2 = A x.1 x.2.1 then (if x.2.1 then X x.1 else 1 + X x.1) else 0

/-- The restricted polynomial `ML(u|_ρ)` (Theorem 6.3, proof, Step 1, p.34): substitute `ρ` and
multilinearize. -/
noncomputable def restrictPoly {V : Type*} {q : ℕ} (A : V → Bool → Fin q)
    (u : MvPolynomial (V × Bool × Fin q) (ZMod 2)) : MvPolynomial V (ZMod 2) :=
  ML (aeval (selRho A) u)

/-- The restricted line: `L|_ρ` replaces every polynomial `u` of `L` by `ML(u|_ρ)`. The restricted
refutation `Π|_ρ` is `Π.map (restrictLine A)`. -/
noncomputable def restrictLine {V : Type*} [DecidableEq V] {q : ℕ} (A : V → Bool → Fin q)
    (L : RLine (V × Bool × Fin q)) : RLine V :=
  L.image (restrictPoly A)

end AC02Frege.Supplement


