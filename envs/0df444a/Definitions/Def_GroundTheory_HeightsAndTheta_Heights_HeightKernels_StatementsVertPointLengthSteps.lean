-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsVertPointLengthSteps
-- name    : GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsVertPointLengthSteps
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T05:56:17.597027+00:00
-- url     : https://prove2.me/theorems/5f0815fa-e874-4149-8b2f-4aeb95a2a2b5
-- title:
--   Statements Vert Point Length Steps
-- statement:
--   Definitions and structural lemmas for Statements Vert Point Length Steps, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/StatementsVertPointLengthSteps.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsVertRIndexSteps
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_chartRingZ_yPt_1d5185d5084e
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
open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial NumberField
noncomputable section
def VertPointChart.Statement : Prop :=
  ∀ (T : Type) [Fintype T] (K' : Type) [Field K'] [NumberField K'] (y : (Σ _ : Unit, T) → K')
    (s : MRing (fun _ : Unit => T)),
    IsArithVar (mCoordIdeal y) 1 → IsMultiHomog s (fun _ => 1) → s ∉ mCoordIdeal y →
      ∀ W ∈ divSupp (mCoordIdeal y) s, ∀ t : T, (X ⟨(), t⟩ : MRing (fun _ : Unit => T)) ∉ W →
        (curvePtIdeal y W).IsMaximal ∧
        (∀ u : T, ∃ a b : curveRing y, b ∉ curvePtIdeal y W ∧ (b : K') * (y ⟨(), u⟩ / y ⟨(), t⟩) = a) ∧
        ∀ (d : ℕ) (g : MRing (fun _ : Unit => T)), IsMultiHomog g (fun _ => d) →
          (g ∈ W ↔ ∃ a b : curveRing y, a ∈ curvePtIdeal y W ∧ b ∉ curvePtIdeal y W ∧
            (b : K') * aeval y g = a * y ⟨(), t⟩ ^ d)
def VertPointInj.Statement : Prop :=
  ∀ (T : Type) [Fintype T] (K' : Type) [Field K'] [NumberField K'] (y : (Σ _ : Unit, T) → K')
    (s : MRing (fun _ : Unit => T)),
    IsArithVar (mCoordIdeal y) 1 → IsMultiHomog s (fun _ => 1) → s ∉ mCoordIdeal y →
      Set.InjOn (curvePtIdeal y) (divSupp (mCoordIdeal y) s)
def VertPointSurj.Statement : Prop :=
  ∀ (T : Type) [Fintype T] (K' : Type) [Field K'] [NumberField K'] (y : (Σ _ : Unit, T) → K')
    (s : MRing (fun _ : Unit => T)),
    IsArithVar (mCoordIdeal y) 1 → IsMultiHomog s (fun _ => 1) → s ∉ mCoordIdeal y →
      ∀ m : Ideal (curveRing y), m.IsMaximal → locLen m (sectionQuot y (aeval y s)) ≠ 0 →
        ∃ W ∈ divSupp (mCoordIdeal y) s, curvePtIdeal y W = m
def VertPointMultChart.Statement : Prop :=
  ∀ (T : Type) [Fintype T] (K' : Type) [Field K'] [NumberField K'] (y : (Σ _ : Unit, T) → K')
    (s : MRing (fun _ : Unit => T)),
    IsArithVar (mCoordIdeal y) 1 → IsMultiHomog s (fun _ => 1) → s ∉ mCoordIdeal y →
      ∀ W ∈ divSupp (mCoordIdeal y) s, ∀ t : T, (X ⟨(), t⟩ : MRing (fun _ : Unit => T)) ∉ W →
        ∀ a b : curveRing y, b ∉ curvePtIdeal y W → (b : K') * aeval y s = a * y ⟨(), t⟩ →
          multAt (mCoordIdeal y ⊔ Ideal.span {s}) W =
            locLen (curvePtIdeal y W) (curveRing y ⧸ Ideal.span {a})
def SectionQuotLocal.Statement : Prop :=
  ∀ (T : Type) [Fintype T] (K' : Type) [Field K'] [NumberField K'] (y : (Σ _ : Unit, T) → K')
    (s : MRing (fun _ : Unit => T)),
    IsArithVar (mCoordIdeal y) 1 → IsMultiHomog s (fun _ => 1) → s ∉ mCoordIdeal y →
      ∀ (m : Ideal (curveRing y)) (t : T), m.IsPrime →
        (∀ u : T, ∃ a b : curveRing y, b ∉ m ∧ (b : K') * (y ⟨(), u⟩ / y ⟨(), t⟩) = a) →
        ∀ a b : curveRing y, b ∉ m → (b : K') * aeval y s = a * y ⟨(), t⟩ →
          locLen m (sectionQuot y (aeval y s)) = locLen m (curveRing y ⧸ Ideal.span {a})
abbrev twoXPt : MRing (PBlk 1) := C 2 * X ⟨(), 0⟩
abbrev twoIdealPt : Ideal (MRing (PBlk 1)) := Ideal.span {C 2}
theorem exists_int_of_mem_curveRing_yPt (b : curveRing IndefiniteRowSideFullHecke.HeightsSet.yPt) : ∃ n : ℤ, (b : ℚ) = n := by
  have h := mem_curveRing.mp b.2 (fun _ => 0) (fun _ => by simp [IndefiniteRowSideFullHecke.HeightsSet.yPt])
  rw [chartRingZ_yPt, Algebra.mem_bot] at h
  obtain ⟨n, hn⟩ := h
  exact ⟨n, by rw [← hn]; simp⟩
def evenIdealPt : Ideal (curveRing IndefiniteRowSideFullHecke.HeightsSet.yPt) where
  carrier := {b | ∃ n : ℤ, (b : ℚ) = 2 * n}
  add_mem' := by
    rintro a b ⟨m, hm⟩ ⟨n, hn⟩
    refine ⟨m + n, ?_⟩
    show (a : ℚ) + b = _
    rw [hm, hn]
    push_cast
    ring
  zero_mem' := ⟨0, by simp⟩
  smul_mem' := by
    rintro c b ⟨n, hn⟩
    obtain ⟨k, hk⟩ := exists_int_of_mem_curveRing_yPt c
    refine ⟨k * n, ?_⟩
    show (c : ℚ) * b = _
    rw [hk, hn]
    push_cast
    ring
end
end GroundTheory.Heights₂.Heights


