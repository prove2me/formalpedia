-- Prove2me | Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_EisensteinSeriesG2_G2RootData_PlRegion
-- name    : Development_WeilBound_CoreStatements_AutomorphicKernels_EisensteinSeriesG2_G2RootData_PlRegion
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:42:48.597803+00:00
-- url     : https://prove2.me/theorems/1b2e8569-8762-48cb-89a6-86077de0ddd1
-- title:
--   Pl Region
-- statement:
--   Definitions and structural lemmas for Pl Region, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/EisensteinSeriesG2/G2RootData/PlRegion.lean

import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_EisensteinSeriesG2_G2RootData_OnCoroot
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace SiegelEisensteinSeries.BRoad
open Filter Topology
namespace Datum
variable {G : Type*} [Group G] [TopologicalSpace G] {r : ℕ} (D : Datum G r)
structure Plucker (L : Fin r → Type*) (ℓ : ∀ i, D.Cos → L i) (nrm : ∀ i, L i → G → ℝ) (s0 : Fin r → ℝ) : Prop where
  inj : Function.Injective (fun q : D.Cos => fun i => ℓ i q)
  pos : ∀ i l g, 0 < nrm i l g
  factor : ∀ (q : D.Cos) (g : G) (i : Fin r), D.Hv ((Quotient.out q).1 * g) i = -Real.log (nrm i (ℓ i q) g)
  zeta : ∀ i, ∀ s > s0 i, ∃ (c : ℝ) (N : ℕ), ∀ g, Summable (fun l => nrm i l g ^ (-s)) ∧
    ∑' l, nrm i l g ^ (-s) ≤ c * D.ht g ^ N
  loc : ∀ i (g0 : G), ∃ U ∈ 𝓝 g0, ∃ c > 0, ∀ g ∈ U, ∀ l, c * nrm i l g0 ≤ nrm i l g ∧ nrm i l g ≤ c⁻¹ * nrm i l g0
def plRegion (s0 : Fin r → ℝ) : Set (Fin r → ℝ) := {x | ∀ i, s0 i < x i + D.rho i}
def TubeGood (U : Set (Fin r → ℝ)) (F : (Fin r → ℂ) → G → ℂ) : Prop :=
  (∀ g, DifferentiableOn ℂ (fun lam => F lam g) {lam | (fun j => (lam j).re) ∈ U}) ∧
    ContinuousOn (fun p : (Fin r → ℂ) × G => F p.1 p.2) ({lam | (fun j => (lam j).re) ∈ U} ×ˢ Set.univ) ∧
    ∀ C ⊆ U, IsCompact C → ∃ (c : ℝ) (N : ℕ), ∀ lam : Fin r → ℂ, (fun j => (lam j).re) ∈ C → ∀ g,
      ‖F lam g‖ ≤ c * (1 + ‖fun j => (lam j).im‖) ^ N * D.ht g ^ N
end Datum
end SiegelEisensteinSeries.BRoad


