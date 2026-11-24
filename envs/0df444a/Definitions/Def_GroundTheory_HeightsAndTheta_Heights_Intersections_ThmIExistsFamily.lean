-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ThmIExistsFamily
-- name    : GroundTheory_HeightsAndTheta_Heights_Intersections_ThmIExistsFamily
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:46:48.800711+00:00
-- url     : https://prove2.me/theorems/acf36436-ee9d-4f59-8056-f16c73b3bd90
-- title:
--   Thm IExists Family
-- statement:
--   Definitions and structural lemmas for Thm IExists Family, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/ThmIExistsFamily.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsArith
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_IsMultiHomogXpow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2
noncomputable section
namespace ThmIExists
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
def segreLine (m : ℕ) : HermLine ι :=
  HermLine.ofMetrics (fun k => fsMetric (ι k)) (fun _ => (m : ℤ))
open Classical in

def secOf (P : Ideal (MRing ι)) (b : K → ℕ) : MRing ι :=
  if h : ∃ s : MRing ι, IsMultiHomog s b ∧ s ∉ P then h.choose else 0
def shift (A : HermLine ι) : ℕ := ∑ k, (A.a k).natAbs
def upDeg (A : HermLine ι) : K → ℕ := fun k => (A.a k + shift A).toNat
def lift {n : ℕ} (J : Ideal (MRing ι) → (Fin n → HermLine ι) → ℝ) :
    Ideal (MRing ι) → (m : ℕ) → (Fin m → HermLine ι) → ℝ :=
  fun W m L => if h : m = n then J W (L ∘ Fin.cast h.symm) else 0
def step {n : ℕ} (J : Ideal (MRing ι) → (Fin n → HermLine ι) → ℝ) (P : Ideal (MRing ι))
    (L : Fin n → HermLine ι) (A : HermLine ι) : ℝ :=
  recR (lift J) P L (A.tensor (segreLine (shift A))) (secOf P (upDeg A)) -
    recR (lift J) P L (segreLine (shift A)) (secOf P fun _ => shift A)
def fam : (n : ℕ) → Ideal (MRing ι) → (Fin n → HermLine ι) → ℝ
  | 0 => fun _ _ => 0
  | n + 1 => fun P L => step (fam n) P (Fin.init L) (L (Fin.last n))
def famI : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ := fun P n L => fam n P L
def LastAddAt (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ) (n : ℕ) : Prop :=
  ∀ (P : Ideal (MRing ι)) (L : Fin n → HermLine ι) (A B : HermLine ι),
    IsArithVar P (n + 1) → (∀ j, IsSmoothHerm (L j)) → IsSmoothHerm A → IsSmoothHerm B →
    I P (n + 1) (Fin.snoc L (A.tensor B)) = I P (n + 1) (Fin.snoc L A) + I P (n + 1) (Fin.snoc L B)
def WDAt (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ) (n : ℕ) : Prop :=
  ∀ (P : Ideal (MRing ι)) (L : Fin n → HermLine ι) (B : HermLine ι) (s t : MRing ι),
    IsArithVar P (n + 1) → (∀ j, IsSmoothHerm (L j)) → IsSmoothHerm B →
    IsSectionOn P B s → IsSectionOn P B t → recR I P L B s = recR I P L B t
section Steps
variable (hMul : RMulStatement) {n : ℕ} (hwd : WDAt (famI (ι := ι)) n)
include hMul hwd
end Steps
end ThmIExists
end
end GroundTheory.Heights₂.Heights.Inter


