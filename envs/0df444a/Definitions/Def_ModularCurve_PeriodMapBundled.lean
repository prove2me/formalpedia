-- Prove2me | Definitions.Def_ModularCurve_PeriodMapBundled
-- name    : ModularCurve_PeriodMapBundled
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.712661+00:00
-- url     : https://prove2.me/theorems/d43bec83-2176-5d54-84a9-3d42beff39e5
-- title:
--   Period homomorphism of a weight-two cusp form
-- statement:
--   Fix $N$ and a cusp form $f$ of weight $2$ for $\Gamma_0(N)$. The predicate [`ModularCurve.HasEquivariantPrimitive N f F`](../def/ModularCurve_PeriodMapBundled.html#L12), for $F : \mathbb{H} \to \mathbb{C}$, is the conjunction of four clauses: (i) for every $\tau \in \mathbb{H}$, the function $F \circ$ `ofComplex` (the extension of $F$ to $\mathbb{C}$ through Mathlib's partial inverse of the coercion $\mathbb{H} \to \mathbb{C}$) has derivative $f(\tau)$ at the point $\tau$; (ii) $F \to 0$ along the filter `atImInfty`, i.e. as $\operatorname{Im} \tau \to \infty$; (iii) `Period.IsEquivariantPrimitive (Gamma0 N) F`, which says that for each $\gamma \in \Gamma_0(N)$ there is a constant $c \in \mathbb{C}$ with $F(\gamma \cdot z) - F(z) = c$ for all $z \in \mathbb{H}$; (iv) for every $\delta \in \mathrm{SL}_2(\mathbb{Z})$ the function $w \mapsto F(\delta \cdot w)$ has a limit along `atImInfty`, that is, $F$ has a limit at every cusp. So $F$ is a primitive of $f$ vanishing at $i\infty$, with constant $\Gamma_0(N)$-coboundaries and limits at all cusps.
--
--   From clause (iii) the imported module builds the period of $\gamma$, namely the constant $F(\gamma \cdot i) - F(i)$, and assembles these into an additive homomorphism `periodHom` from `Additive (Gamma0 N)` to $\mathbb{C}$, using $F(\gamma\delta\cdot z) - F(z) = (F(\gamma\cdot z)-F(z)) + (F(\delta\cdot z)-F(z))$. The definition [`ModularCurve.periodMap N f : Additive (Gamma0 N) →+ ℂ`](../def/ModularCurve_PeriodMapBundled.html#L20) is then, by cases on whether some $F$ with `HasEquivariantPrimitive N f F` exists, the homomorphism `periodHom` attached to a classically chosen such $F$, and the zero homomorphism otherwise; the existence of an admissible primitive is not asserted here. The helper theorem `periodMap_def` records the unfolding in the non-degenerate case: given any $F$ with `HasEquivariantPrimitive N f F`, there are $F_0$ and a proof $h_0$ of `HasEquivariantPrimitive N f F₀` with `periodMap N f` equal to the period homomorphism determined by the third clause of $h_0$. The conclusion concerns the chosen $F_0$, not the given $F$; no claim that the period homomorphism is independent of the primitive is made at this point.
--
--   The imported module also defines, for an abelian group $A$, the predicate `IsParabolicHom` on homomorphisms $\varphi :$ `Additive Γ` $\to_+ A$ — vanishing on every $\gamma \in \Gamma$ whose matrix trace satisfies $\operatorname{tr}(\gamma)^2 = 4$ — and the submodule `parabolicHoms` of homomorphisms satisfying it.
--
--   **Relation to Mathlib.** Mathlib supplies the ingredients used here (`CuspForm`, `Gamma0`, the Möbius action on `ℍ`, the filter `atImInfty`, and `ofComplex`); the notions of equivariant primitive, period homomorphism and parabolic homomorphism, and the period map of a weight-two cusp form, are the project's own.
--
--   **Where it is used.** The period homomorphism of a weight-two cusp form for $\Gamma_0(N)$ is the analytic input to the Eichler–Shimura description of the homology of the modular curve $X_0(N)$ and to the construction of period lattices and modular parametrisations used on the modularity side of the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_ModularCurve_PeriodMapBundled.lean

import Definitions.Def_ModularCurve_PeriodMap
import Mathlib.Analysis.Complex.UpperHalfPlane.FunctionsBoundedAtInfty
import Mathlib.NumberTheory.ModularForms.Basic
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace ModularCurve

open UpperHalfPlane CongruenceSubgroup Filter Topology Period

open scoped MatrixGroups

def HasEquivariantPrimitive (N : ℕ) (f : CuspForm (Gamma0 N) 2) (F : ℍ → ℂ) : Prop :=
  (∀ τ : ℍ, HasDerivAt (F ∘ ofComplex) (f τ) ↑τ) ∧
    Tendsto F atImInfty (𝓝 0) ∧
    IsEquivariantPrimitive (Gamma0 N) F ∧
    ∀ δ : SL(2, ℤ), ∃ L : ℂ, Tendsto (fun w : ℍ => F (δ • w)) atImInfty (𝓝 L)

open Classical in

noncomputable def periodMap (N : ℕ) (f : CuspForm (Gamma0 N) 2) : Additive (Gamma0 N) →+ ℂ :=
  if h : ∃ F : ℍ → ℂ, HasEquivariantPrimitive N f F then h.choose_spec.2.2.1.periodHom else 0

theorem periodMap_def (N : ℕ) (f : CuspForm (Gamma0 N) 2) {F : ℍ → ℂ}
    (hF : HasEquivariantPrimitive N f F) :
    ∃ (F₀ : ℍ → ℂ) (h₀ : HasEquivariantPrimitive N f F₀), periodMap N f = h₀.2.2.1.periodHom := by
  classical
  have h : ∃ F : ℍ → ℂ, HasEquivariantPrimitive N f F := ⟨F, hF⟩
  exact ⟨h.choose, h.choose_spec, dif_pos h⟩

end ModularCurve


