-- Prove2me | Definitions.Def_SemAC02_lift
-- name    : SemAC02_lift
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T11:27:57.781211+00:00
-- url     : https://prove2.me/theorems/f969fe7b-7c1f-4660-a07f-5ca0960c7219
-- title:
--   The lifted formula $\mathrm{Lift}_g(F_n)$
-- statement:
--   Let $g$ be a gadget on $m$ variables, $g_0=g$, $g_1(X)=g(\overline X)$, and write $g_b=\bigwedge_{j\in J}H_{b,j}$ with each $H_{b,j}$ OR-rooted (a literal or a constant counts as a unary OR). Let $F_n$ be a CNF in $z_1,\dots,z_n$, with $z_i^1=z_i$ and $z_i^0=\neg z_i$. For each $i$ introduce a block $X_i=(x_{i,1},\dots,x_{i,m})$ of fresh variables and replace the literal $z_i^b$ by $g_b(X_i)$. For a clause $C=\bigvee_{(i,b)\in I}z_i^b$ of $F_n$ and $\alpha\in J^I$, distributivity gives the circuits
--   $$
--   A_{C,\alpha}(X)=\bigvee_{(i,b)\in I}H_{b,\alpha(i,b)}(X_i),
--   $$
--   whose OR root merges with the OR roots of the $H$'s, so $A_{C,\alpha}$ has depth at most $d$. The **lifted formula** is
--   $$
--   \mathrm{Lift}_g(F_n)=\{A_{C,\alpha}: C\in F_n,\ \alpha\in J^I\}.
--   $$
--
--   **Formalization Note** The lifted variables are `Fin n × Fin m`. The literal `(i, true)` is $z_i=z_i^1$ and is replaced by $g_1(X_i)$; `(i, false)` by $g_0(X_i)$. $H_{1,j}$ is $H_{0,j}$ with all literal polarities flipped. $\alpha$ is given on all literals (only its values on $C$ matter), and the merged OR lists the children in the fixed order of `C.toList`.
-- source:
--   Alekseev, Gryaznov, Itsykson, Pitassi, Robere, Tzameret, Hard Instances for Strong Semantic Proof Systems: CNFs for Depth-Four PC and Deep Instances for AC0[2]-Frege, manuscript (STOC 2027 submission, sha256 c228d68b89b45b5c6c547aa994f7d1799441bb22b2a85e36c6cd400bea8cdb6a), Definition 8.2, (43)–(44), p.63 (PDF p.65)

import Mathlib
import Definitions.Def_SemAC02_Circ
import Definitions.Def_LiftSAParity_CNF

namespace SemAC02

/-- The conjuncts `H_{b,j}` of `g_b` (§8.1, p.63): for `g = ⋀_{j∈J} H_{0,j}` AND-rooted,
`g_0 = g` and `g_1(X) = g(X̄)`, so `H_{1,j}` is `H_{0,j}` with every literal's polarity flipped.
Here `J = Fin (andChildren g).length`. -/
def gadgetH {m : ℕ} (g : Circ (Fin m)) (b : Bool) (j : Fin g.andChildren.length) : Circ (Fin m) :=
  if b then (g.andChildren.get j).flip else g.andChildren.get j

/-- The lifted axiom `A_{C,α}` (Definition 8.2, p.63):
`A_{C,α}(X) = ⋁_{(i,b) ∈ I} H_{b,α(i,b)}(X_i)`, with its OR root merged with the OR roots of the
`H`'s (a non-OR `H` counts as a unary OR, p.63). Block `i` consists of the variables
`(i, j)`, `j ∈ Fin m`.

**Formalization Note** The base literal `(i, true)` is `z_i = z_i^1` and is replaced by
`g_1(X_i)`; `(i, false)` is `¬z_i = z_i^0` and is replaced by `g_0(X_i)` (p.62). The choice
function `α` is given on all literals; only its values on `C` matter. The clause is traversed in
the fixed order `C.toList` (the order of children is immaterial). -/
noncomputable def liftAxiom {n m : ℕ} (g : Circ (Fin m)) (C : LiftSAParity.Clause (Fin n))
    (α : Fin n × Bool → Fin g.andChildren.length) : Circ (Fin n × Fin m) :=
  Circ.or (C.toList.flatMap (fun l =>
    ((gadgetH g l.2 (α l)).orChildren).map (Circ.rename (fun j => (l.1, j)))))

open Classical in
/-- The **lifted formula** `Lift_g(F_n)` (Alekseev–Gryaznov–Itsykson–Pitassi–Robere–Tzameret,
*Hard Instances for Strong Semantic Proof Systems*, manuscript (STOC 2027 submission), Definition
8.2, (44), p.63): `{A_{C,α} : C ∈ F_n, α ∈ J^I}`, a family of circuits in the `n·m` variables
`x_{i,j}`.

**Formalization Note** Variables of the lift are `Fin n × Fin m`. The definition is meant for
gadgets `g` satisfying `IsGadget d g` (AND-rooted, normal form); for those, `J` is the list of
children of the AND root of `g`. -/
noncomputable def lift {n m : ℕ} (g : Circ (Fin m)) (F : LiftSAParity.CNF (Fin n)) :
    Finset (Circ (Fin n × Fin m)) :=
  F.biUnion (fun C => Finset.univ.image (fun α => liftAxiom g C α))

end SemAC02


