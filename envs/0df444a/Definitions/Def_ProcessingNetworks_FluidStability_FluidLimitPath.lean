-- Prove2me | Definitions.Def_ProcessingNetworks_FluidStability_FluidLimitPath
-- name    : ProcessingNetworks_FluidStability_FluidLimitPath
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T17:34:17.313318+00:00
-- url     : https://prove2.me/theorems/5979d5b4-1d3a-4362-8cf1-87063ef092d1
-- title:
--   Definition 6.6 — fluid limit path
-- statement:
--   **Definition 6.6 (fluid limit path).** A four-tuple
--   $(\hat D, \hat F, \hat T, \hat Z) \in C^I \times C^J \times C^J \times C^I$ (continuous
--   functions on $[0,\infty)$) is a **fluid limit path** of the SPN if there is a sample point
--   $\omega$ and a sequence of initial states $\{x_n\} \subset \mathcal X$ with $|x_n| \to \infty$
--   such that the fluid-scaled processes
--   $$
--   \big(\hat D^{x_n}, \hat F^{x_n}, \hat T^{x_n}, \hat Z^{x_n}\big)(t,\omega)
--     := \frac{1}{|x_n|}\big(D^{x_n}, F^{x_n}, T^{x_n}, Z^{x_n}\big)(|x_n| t, \omega)
--   $$
--   converge to $(\hat D, \hat F, \hat T, \hat Z)$ uniformly on compact sets (u.o.c.) as
--   $n \to \infty$.
--
--   Fluid limit paths are the actual scaling limits of the stochastic SPN — as opposed to fluid
--   *model solutions* (`IsFluidModelSolution`), which are any four-tuple satisfying the fluid
--   equations, whether or not they arise this way. Theorem 6.5 is the bridge: every fluid limit
--   path is a fluid model solution.
--
--   **Formalization note.** `UOCConverges` (u.o.c. convergence) is convergence uniform on every
--   interval $[0,T]$, not uniform convergence on all of $[0,\infty)$ — the latter would be a
--   strictly stronger, unachievable requirement. Continuity of the limiting four-tuple is
--   asserted directly as part of the Prop (mirroring the book's ambient space
--   $C^I \times C^J \times C^J \times C^I$) rather than left to be derived. The integer-valued
--   processes $D^x, F^x, Z^x$ of the family are cast to $\mathbb{R}$ in the scaling (6.37).
-- source:
--   Dai & Harrison, Processing Networks: Fluid Models and Stability, pre-publication draft 2020-4-2, p. 116, Definition 6.6

import Mathlib
import Definitions.Def_ProcessingNetworks_Stability_MarkovRepresentation
import Definitions.Def_ProcessingNetworks_FluidStability_FluidEquationData
import Definitions.Def_ProcessingNetworks_Stability_SPNModel
import Definitions.Def_ProcessingNetworks_FluidStability_SPNProcessFamily

namespace ProcessingNetworks.FluidStability

open MeasureTheory ProbabilityTheory Filter ProcessingNetworks.Stability

/-- Definition 6.6 (fluid limit path), Dai & Harrison p. 116 (PDF p. 132): a four-tuple
`(D̂, F̂, T̂, Ẑ) ∈ C^I × C^J × C^J × C^I` (continuity of all four components is part of the
ambient function space, matching Theorem 6.5's conclusion) is a *fluid limit path* of the SPN if
there is a sample point `ω` and a sequence `{xₙ} ⊂ 𝒳` with `|xₙ| → ∞` such that the fluid-scaled
processes of (6.37),
`(D̂^{xₙ}, F̂^{xₙ}, T̂^{xₙ}, Ẑ^{xₙ})(t, ω) := (1/|xₙ|) · (D^{xₙ}, F^{xₙ}, T^{xₙ}, Z^{xₙ})(|xₙ| t, ω)`,
converge to `(D̂, F̂, T̂, Ẑ)` u.o.c. as `n → ∞` (6.39). -/
def FluidLimitPath {Xstate : Type*} [Countable Xstate] {Ω : Type*} [MeasureSpace Ω] {I J K : ℕ}
    {N : ℝ → Ω → Fin J → ℕ} {Z : ℝ → Ω → Fin I → ℕ}
    {Mrep : MarkovRepresentation Xstate I J N Z} {sd : SPNData I J K}
    {dat : FluidEquationData I J K} {E : Fin I → ℝ → Ω → ℕ} {v : Fin J → ℕ → Ω → ℝ}
    {φ : Fin J → ℕ → Ω → Fin I → ℕ} (fam : SPNProcessFamily Mrep sd dat E v φ)
    (Dh : ℝ → Fin I → ℝ) (Fh Th : ℝ → Fin J → ℝ) (Zh : ℝ → Fin I → ℝ) : Prop :=
  Continuous Dh ∧ Continuous Fh ∧ Continuous Th ∧ Continuous Zh ∧
  ∃ (ω : Ω) (x : ℕ → Xstate), Tendsto (fun n => spnSize Mrep (x n)) atTop atTop ∧
    UOCConverges
      (fun n t i => (spnSize Mrep (x n))⁻¹ * (fam.D (x n) (spnSize Mrep (x n) * t) ω i : ℝ)) Dh ∧
    UOCConverges
      (fun n t j => (spnSize Mrep (x n))⁻¹ * (fam.F (x n) (spnSize Mrep (x n) * t) ω j : ℝ)) Fh ∧
    UOCConverges
      (fun n t j => (spnSize Mrep (x n))⁻¹ * fam.T (x n) (spnSize Mrep (x n) * t) ω j) Th ∧
    UOCConverges
      (fun n t i => (spnSize Mrep (x n))⁻¹ * (fam.Zx (x n) (spnSize Mrep (x n) * t) ω i : ℝ)) Zh

end ProcessingNetworks.FluidStability


