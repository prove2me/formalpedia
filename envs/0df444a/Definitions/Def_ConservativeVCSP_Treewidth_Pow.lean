-- Prove2me | Definitions.Def_ConservativeVCSP_Treewidth_Pow
-- name    : ConservativeVCSP_Treewidth_Pow
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T21:46:05.508351+00:00
-- url     : https://prove2.me/theorems/e31de241-7db2-468d-b270-4fa7193ac229
-- title:
--   Expressive power pow(Γ) and the running time base c_Γ
-- statement:
--   The **expressive power** $\mathrm{pow}(\Gamma)$ is the set of cost functions $g$ of some arity $r$ for which there are $m\ge0$ auxiliary variables, a finite weighted constraint system over $\Gamma$ on the variables $x_1,\dots,x_r,y_1,\dots,y_m$ (positive rational weights, scopes may repeat variables) with cost $F(\bar x,\bar y)$, and a rational shift $c$, such that
--   $$g(\bar x)=\min_{\bar y\in D^m}F(\bar x,\bar y)+c\qquad\text{for all }\bar x\in D^r,$$
--   with $\infty+c=\infty$ and the result nonnegative.
--
--   The **running time base** $c_\Gamma$ is the largest $|D'|$ over $D'\subseteq D$ for which some binary $f\in\mathrm{pow}(\Gamma)$ has $f(x,y)=0$ for distinct $x,y\in D'$ and $f(x,x)=1$ for $x\in D'$; nothing is required outside $D'^2$. Since constants are expressible, every singleton qualifies and $c_\Gamma\ge1$.
--
--   **Formalization Note** Nonnegativity of an expressed function is built into its codomain `WithTop ℚ≥0`; the shift is applied in `WithTop ℚ` through `toQ`. `cGamma` is the supremum of `Finset.card` over the qualifying finite subsets.
-- source:
--   Greilhuber, Marx, Osipov, Piecyk, Rzążewski, Živný, Tight Algorithms for Conservative Finite-Valued CSPs Parameterized by Treewidth, STOC 2027 submission (manuscript sha256 e3f9968e…), p. 3 and p. 17 (pow(Γ)); p. 26, Definition 5.6

import Definitions.Def_ConservativeVCSP_Treewidth_Instance

set_option autoImplicit false

namespace ConservativeVCSP.Treewidth

/-- The inclusion `ℚ≥0 ∪ {∞} → ℚ ∪ {∞}` (`∞ ↦ ∞`), used to apply rational shifts `c ∈ ℚ`. -/
def toQ (x : WithTop ℚ≥0) : WithTop ℚ :=
  WithTop.map (fun q : ℚ≥0 => (q : ℚ)) x

/-- `g ∈ pow(Γ)`, the expressive power of `Γ` (§1, p. 3; §3, p. 17): `g` (of arity `r`) is obtained
from a finite weighted sum of constraints from `Γ` (positive rational weights, scopes over the `r`
input variables and `m ≥ 0` auxiliary variables, repeated variables allowed) by minimizing over the
auxiliary variables and adding a rational shift `c`, the result being nonnegative:
`g(x̄) = min_{ȳ ∈ D^m} Σ_C w_C f_C(…) + c` for every `x̄ ∈ D^r` (with `∞ + c = ∞`). Nonnegativity
of the result is built into the codomain `ℚ≥0 ∪ {∞}` of `g`. -/
def InPow {D : Type} [Fintype D] (Γ : Set (CostFn D)) (g : CostFn D) : Prop :=
  ∃ (m : ℕ) (cs : List (Constraint D (Fin g.arity ⊕ Fin m))) (c : ℚ),
    (∀ C ∈ cs, C.fn ∈ Γ) ∧
    ∀ x : Fin g.arity → D,
      toQ (g.f x) = toQ (Finset.univ.inf fun y : Fin m → D => sysCost cs (Sum.elim x y)) + (c : WithTop ℚ)

/-- `S` qualifies in Definition 5.6 (p. 26): some binary `f ∈ pow(Γ)` has `f(x, y) = 0` for distinct
`x, y ∈ S` and `f(x, x) = 1` for `x ∈ S` (no condition outside `S × S`). -/
def IsDiseqSet {D : Type} [Fintype D] (Γ : Set (CostFn D)) (S : Finset D) : Prop :=
  ∃ f : D → D → WithTop ℚ≥0, InPow Γ (binary f) ∧
    (∀ x ∈ S, ∀ y ∈ S, x ≠ y → f x y = 0) ∧ ∀ x ∈ S, f x x = 1

open scoped Classical in
/-- The running time base `c_Γ` (Definition 5.6, p. 26; §1, p. 3): the maximum cardinality of a
subset `D' ⊆ D` with the property `IsDiseqSet`. -/
noncomputable def cGamma {D : Type} [Fintype D] (Γ : Set (CostFn D)) : ℕ :=
  ((Finset.univ : Finset (Finset D)).filter (IsDiseqSet Γ)).sup Finset.card

end ConservativeVCSP.Treewidth


