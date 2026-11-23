-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_FirstMinimumPos
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_FirstMinimumPos
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T06:12:34.328056+00:00
-- url     : https://prove2.me/theorems/5444c78e-be2c-4ac4-b4f7-32a80717a536
-- title:
--   First Minimum Pos
-- statement:
--   Definitions and structural lemmas for First Minimum Pos, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/FirstMinimumPos.lean

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_GROWCountStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.AR
open MeasureTheory Filter Topology ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open scoped ENNReal
noncomputable section
def Bdd {n : ℕ} {Y : Type*} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
    [MeasurableSpace Y] [BorelSpace Y] {ι La : Type*} [AddCommGroup La]
    (A : WeightedAtlas n Y ι La) (G : La) (F : ι → Y → ℂ) : Prop :=
  ∃ C : ℝ, ∀ y, A.nsq G F y ≤ C
structure Cusp {n : ℕ} {Y : Type*} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
    [MeasurableSpace Y] [BorelSpace Y] {ι La : Type*} [AddCommGroup La]
    (A : WeightedAtlas n Y ι La) where
  conn : ConnectedSpace Y
  la1 : Y → ℝ
  first_minimum_pos : ∀ y, 0 < la1 y
  vol_fin : A.mu Set.univ < ⊤
  van : La → ℝ → (ι → Y → ℂ) → Prop
  van_zero : ∀ G c, van G c (fun _ _ => 0)
  van_add : ∀ G c F F', A.IsSec G F → A.IsSec G F' → van G c F → van G c F' →
    van G c (fun i y => F i y + F' i y)
  van_smul : ∀ G c (a : ℂ) F, A.IsSec G F → van G c F → van G c (fun i y => a * F i y)
  van_anti : ∀ G c c' F, c' ≤ c → van G c F → van G c' F

  van_mul : ∀ G G' c F F', A.IsSec G F → A.IsSec G' F' → Bdd A G F → Bdd A G' F' →
    van G c F → van (G + G') c (fun i y => F i y * F' i y)

  kd : ℝ
  two_lt_kd : 2 < kd
  dec : ∀ G F (c : ℝ), A.IsSec G F → Bdd A G F → van G c F →
    ∃ C : ℝ, ∀ y, A.nsq G F y ≤ C * Real.exp (-(kd * c) / la1 y ^ 2)
  gap : ∀ G F, A.IsSec G F → Bdd A G F → van G 0 F → ∃ c : ℝ, 0 < c ∧ van G c F
  cfw : (Y → ℝ) → ℝ → Prop
  cfw_zero : cfw (fun _ => 0) 0
  cfw_smul : ∀ ps a (t : ℝ), 1 ≤ t → cfw ps a → cfw (fun y => t * ps y) (t * a)

  cf : ∀ (G L : La) (N : ℕ) (w : Fin N → ι → Y → ℂ) (F : ι → Y → ℂ) (ps : Y → ℝ) (a η : ℝ),
    (∀ k, A.IsSec L (w k)) → (∀ k, Bdd A L (w k)) → (∀ k, van L 0 (w k)) →
    (∀ y, ∃ k, w k (A.pick y) y ≠ 0) → 0 < η → 0 ≤ a → A.IsSec G F → cfw ps a →
    ∫⁻ y, ENNReal.ofReal (A.nsq G F y * Real.exp (-ps y) * A.sqn L w y ^ (-η)) ∂A.mu < ⊤ →
    Bdd A G F ∧ van G 0 F ∧ van G a F
end
end ReciprocityTheory.ChartRestriction.G.AR


