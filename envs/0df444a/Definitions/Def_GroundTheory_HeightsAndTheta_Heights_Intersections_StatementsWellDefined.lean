-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsWellDefined
-- name    : GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsWellDefined
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:05:25.681297+00:00
-- url     : https://prove2.me/theorems/3d0ba8a6-d938-4130-86e9-709e8a8b3db7
-- title:
--   Statements Well Defined
-- statement:
--   Definitions and structural lemmas for Statements Well Defined, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/Intersections/StatementsWellDefined.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsArith
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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
def AddAt {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
    (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ) (n : ℕ) : Prop :=
  ∀ (W : Ideal (MRing ι)) (L : Fin n → HermLine ι) (A C : HermLine ι),
    IsArithVar W (n + 1) → (∀ j, IsSmoothHerm (L j)) → IsSmoothHerm A → IsSmoothHerm C →
    I W (n + 1) (Fin.snoc L (A.tensor C)) = I W (n + 1) (Fin.snoc L A) + I W (n + 1) (Fin.snoc L C)
def RPositionAdd.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ) (P : Ideal (MRing ι)) (n : ℕ)
    (L : Fin n → HermLine ι) (A C B : HermLine ι) (s : MRing ι),
    AddAt I n → IsArithVar P (n + 2) → (∀ j, IsSmoothHerm (L j)) → IsSmoothHerm A →
    IsSmoothHerm C → IsSmoothHerm B → IsSectionOn P B s →
    recR I P (Fin.snoc L (A.tensor C)) B s = recR I P (Fin.snoc L A) B s + recR I P (Fin.snoc L C) B s
def WellDefined.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ) (P : Ideal (MRing ι)) (n : ℕ)
    (L : Fin (n + 1) → HermLine ι) (B : HermLine ι) (s t : MRing ι),
    HasRAt I n → AddAt I n → IsArithVar P (n + 2) → (∀ j, IsSmoothHerm (L j)) → IsSmoothHerm B →
    IsSectionOn P B s → IsSectionOn P B t → recR I P L B s = recR I P L B t
end
end GroundTheory.Heights₂.Heights.Inter


