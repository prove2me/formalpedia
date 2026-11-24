-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsVertRIndexSteps
-- name    : GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsVertRIndexSteps
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:25:31.384277+00:00
-- url     : https://prove2.me/theorems/9d3c38de-a07a-46a4-ac0c-9c1cf2489830
-- title:
--   Statements Vert RIndex Steps
-- statement:
--   Definitions and structural lemmas for Statements Vert RIndex Steps, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/StatementsVertRIndexSteps.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsPointVertRSteps
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsLogCardLength
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_mem_curveRing_46da28e9018f

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 MvPolynomial NumberField
noncomputable section
section Objects
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {Ω : Type*} [Field Ω]
def sectionMod (y : (Σ k, ι k) → Ω) : Submodule (curveRing y) Ω where
  carrier := chartLat y (fun _ => 1) 1
  zero_mem' := (chartLat y (fun _ => 1) 1).zero_mem
  add_mem' := fun ha hb => (chartLat y (fun _ => 1) 1).add_mem ha hb
  smul_mem' := fun b m hm c hc => by
    have hb : (b : Ω) ∈ chartRingZ y c := mem_curveRing.mp b.2 c hc
    have hm' := hm c hc
    rw [Subring.smul_def, smul_eq_mul, mul_assoc]
    exact mul_mem hb hm'
abbrev sectionQuot (y : (Σ k, ι k) → Ω) (x : Ω) : Type _ :=
  ↥(sectionMod y) ⧸ (Submodule.span (curveRing y) {x}).comap (sectionMod y).subtype
def curvePtIdeal (y : (Σ k, ι k) → Ω) (W : Ideal (MRing ι)) : Ideal (curveRing y) :=
  Ideal.span {b | ∃ (d : K → ℕ) (g h : MRing ι), IsMultiHomog g d ∧ IsMultiHomog h d ∧ g ∈ W ∧ h ∉ W ∧
    (b : Ω) * aeval y h = aeval y g}
end Objects
def SectionQuotFinite.Statement : Prop :=
  ∀ (T : Type) [Fintype T] (K' : Type) [Field K'] [NumberField K'] (y : (Σ _ : Unit, T) → K')
    (s : MRing (fun _ : Unit => T)),
    IsArithVar (mCoordIdeal y) 1 → IsMultiHomog s (fun _ => 1) → s ∉ mCoordIdeal y →
      Finite (sectionQuot y (aeval y s))
def VertPointLength.Statement : Prop :=
  ∀ (T : Type) [Fintype T] (K' : Type) [Field K'] [NumberField K'] (y : (Σ _ : Unit, T) → K')
    (s : MRing (fun _ : Unit => T)),
    IsArithVar (mCoordIdeal y) 1 → IsMultiHomog s (fun _ => 1) → s ∉ mCoordIdeal y →
      Set.BijOn (curvePtIdeal y) (divSupp (mCoordIdeal y) s)
          {m | m.IsMaximal ∧ locLen m (sectionQuot y (aeval y s)) ≠ 0} ∧
        ∀ W ∈ divSupp (mCoordIdeal y) s,
          multAt (mCoordIdeal y ⊔ Ideal.span {s}) W =
            locLen (curvePtIdeal y W) (sectionQuot y (aeval y s))
def VertPointResidue.Statement : Prop :=
  ∀ (T : Type) [Fintype T] (K' : Type) [Field K'] [NumberField K'] (y : (Σ _ : Unit, T) → K')
    (s : MRing (fun _ : Unit => T)),
    IsArithVar (mCoordIdeal y) 1 → IsMultiHomog s (fun _ => 1) → s ∉ mCoordIdeal y →
      ∀ W ∈ divSupp (mCoordIdeal y) s,
        (geoNum 0 W Fin.elim0 : ℝ) * Real.log (charOf W) =
          Real.log (Nat.card (curveRing y ⧸ curvePtIdeal y W))
end
end GroundTheory.Heights₂.Heights


