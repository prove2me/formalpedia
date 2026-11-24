-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LUFactorOrbitBounds
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_LUFactorOrbitBounds
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-24T19:46:36.598408+00:00
-- url     : https://prove2.me/theorems/af75acd0-974d-403e-b135-364a024cf5a0
-- title:
--   LUFactor Orbit Bounds
-- statement:
--   Definitions and structural lemmas for LUFactor Orbit Bounds, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LUFactorOrbitBounds.lean

import Definitions.Def_Formalism_HermitianCurvature_StatementJF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ConjugationContinuousOnInvertible
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UnipotentHeisenbergDecomposition
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Block3MulBlocks
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CoordinateSizesOfHypotheses
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SeminormCompletion
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SandwichRhoAction
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SmoothnessOnGoodSet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormDiagonalEntryDilationGeneratorLeOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_JfJqSmoothOfNnMaj
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_first_eq_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_last_eq_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_base_vector_restriction_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_first_eq_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_last
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_dual_base_vector_restriction_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_F
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_L
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x6_lift_res
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.base_vector_first_eq_one
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.base_vector_last_eq_zero
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.base_vector_restriction_zero
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.dual_base_vector_first_eq_zero
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.dual_base_vector_last
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.dual_base_vector_restriction_zero
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.lift_F
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.lift_L
attribute [local simp] Formalism.FourierDecayAlt.P.B2x6.lift_res


set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory Filter Topology
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF
namespace Formalism.FourierDecayAlt.P.WeakDominationMajorants.Orb
variable {k r : ℕ}
def sg (k r : ℕ) (i : Fin (2 * r + k + 1)) : Fin (2 * r + k + 1) :=
  if i.val < r ∨ r + k < i.val then ⟨2 * r + k - i.val, by omega⟩ else i
def ep (k r : ℕ) (i : Fin (2 * r + k + 1)) : ℂ := if i.val = r + k then -1 else 1
lemma sg_sg (i : Fin (2 * r + k + 1)) : sg k r (sg k r i) = i := by
  unfold sg
  by_cases h1 : i.val < r ∨ r + k < i.val
  · rw [if_pos h1, if_pos (by simp; omega)]; ext; simp; omega
  · rw [if_neg h1, if_neg h1]
end Formalism.FourierDecayAlt.P.WeakDominationMajorants.Orb
open Matrix MeasureTheory Filter Topology
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF
namespace Formalism.FourierDecayAlt.P.WeakDominationMajorants.Orb
variable {k r : ℕ}
def Zm (y : Mat k r) : Matrix (Fin r) (Fin r) ℂ := Matrix.of fun a b => y (esI k r a) (eI k r b)
def Lm (n : Mat k r) : Matrix (Fin r) (Fin r) ℂ := Matrix.of fun a c => n⁻¹ (esI k r a) (esI k r c)
def Um (n : Mat k r) : Matrix (Fin r) (Fin r) ℂ := Matrix.of fun b c => n (eI k r b) (eI k r c)
def cE (y : Mat k r) : Matrix (Fin (2 * r + k + 1)) (Fin r) ℂ := Matrix.of fun i b => y i (eI k r b)
end Formalism.FourierDecayAlt.P.WeakDominationMajorants.Orb
open Matrix
namespace Formalism.FourierDecayAlt.P.WeakDominationMajorants.LU
variable {r : ℕ}
def rs (b a : Fin r) : Fin (b.val + 1) → Fin r := fun i => if h : i.val < b.val then ⟨i.val, by omega⟩ else a
def cs (b : Fin r) : Fin (b.val + 1) → Fin r := fun i => ⟨i.val, by omega⟩
def mn (Y : Matrix (Fin r) (Fin r) ℂ) (a b : Fin r) : ℂ := (Y.submatrix (rs b a) (cs b)).det
def ld (Y : Matrix (Fin r) (Fin r) ℂ) (b : Fin r) : ℂ := mn Y b b
def ell (Y : Matrix (Fin r) (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ :=
  Matrix.of fun a b => if b ≤ a then mn Y a b / ld Y b else 0
def IsLU (L : Matrix (Fin r) (Fin r) ℂ) : Prop := (∀ i j : Fin r, i < j → L i j = 0) ∧ ∀ i, L i i = 1
def IsUU (U : Matrix (Fin r) (Fin r) ℂ) : Prop := (∀ i j : Fin r, j < i → U i j = 0) ∧ ∀ i, U i i = 1
end Formalism.FourierDecayAlt.P.WeakDominationMajorants.LU
open Matrix
namespace Formalism.FourierDecayAlt.P.WeakDominationMajorants.LU
variable {r : ℕ}
end Formalism.FourierDecayAlt.P.WeakDominationMajorants.LU
open Matrix MeasureTheory Filter Topology
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF
namespace Formalism.FourierDecayAlt.P.WeakDominationMajorants.Orb
open Formalism.FourierDecayAlt.P.WeakDominationMajorants.LU
variable {k r : ℕ}
def lowerFactorEntryConstant (r : ℕ) (Γ δ : ℝ) : ℝ := 1 + (r.factorial : ℝ) * Γ ^ r / δ
def cL (r : ℕ) (Γ δ : ℝ) : ℝ := (r : ℝ) * (((r.factorial : ℝ) / δ) * ((r.factorial : ℝ) * lowerFactorEntryConstant r Γ δ ^ r))
end Formalism.FourierDecayAlt.P.WeakDominationMajorants.Orb
open Matrix MeasureTheory Filter Topology
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF
namespace Formalism.FourierDecayAlt.P.WeakDominationMajorants.Orb
open Formalism.FourierDecayAlt.P.WeakDominationMajorants.LU
variable {k r : ℕ}
def cZi (r : ℕ) (δ : ℝ) : ℝ := (r.factorial : ℝ) / δ
def c5 (r : ℕ) (Γ δ : ℝ) : ℝ := (r : ℝ) * (((r : ℝ) * (Γ * cL r Γ δ)) * cZi r δ)
def c8 (r : ℕ) (δ : ℝ) : ℝ := (r : ℝ) * cZi r δ
def cPg (r : ℕ) (Γ δ : ℝ) : ℝ := (r : ℝ) * (Γ * (cZi r δ * Γ ^ r))
def c9 (r : ℕ) (Γ δ : ℝ) : ℝ := (r : ℝ) * (c8 r δ * cL r Γ δ)
def c10 (r : ℕ) (Γ δ : ℝ) : ℝ := (r : ℝ) * (cPg r Γ δ * c5 r Γ δ) + c8 r δ
def c11 (r : ℕ) (Γ δ : ℝ) : ℝ := 1 + c5 r Γ δ + c10 r Γ δ
def c13 (k r : ℕ) (Γ δ : ℝ) : ℝ :=
  c9 r Γ δ + ((2 * r + k + 1 : ℕ) : ℝ) * (c11 r Γ δ * cPg r Γ δ) + c11 r Γ δ
section
variable {Γ δ : ℝ} (hΓ : 1 ≤ Γ) (hδ : 0 < δ)
include hΓ hδ
end
section main
variable {Γ δ : ℝ} {g n n' : Mat k r}
end main
end Formalism.FourierDecayAlt.P.WeakDominationMajorants.Orb
open Matrix MeasureTheory Filter Topology
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF
namespace Formalism.FourierDecayAlt.P.WeakDominationMajorants.Orb
open Formalism.FourierDecayAlt.P.WeakDominationMajorants.LU
variable {k r : ℕ}
def Pm (y : Mat k r) : Matrix (Fin (2 * r + k + 1)) (Fin r) ℂ := cE y * (Zm y)⁻¹
section main
variable {Γ δ : ℝ} {g n n' : Mat k r}
end main
end Formalism.FourierDecayAlt.P.WeakDominationMajorants.Orb
open Matrix MeasureTheory Filter Topology
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF
namespace Formalism.FourierDecayAlt.P.WeakDominationMajorants.Orb
open Formalism.FourierDecayAlt.P.WeakDominationMajorants.LU
variable {k r : ℕ}
def sgE (k r : ℕ) : Equiv.Perm (Fin (2 * r + k + 1)) := Function.Involutive.toPerm (sg k r) sg_sg
end Formalism.FourierDecayAlt.P.WeakDominationMajorants.Orb
open Matrix MeasureTheory Filter Topology
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF
namespace Formalism.FourierDecayAlt.P.WeakDominationMajorants.Orb
open Formalism.FourierDecayAlt.P.WeakDominationMajorants.LU
variable {k r : ℕ}
end Formalism.FourierDecayAlt.P.WeakDominationMajorants.Orb
open Matrix MeasureTheory Filter Topology
open scoped ENNReal NNReal
namespace Formalism.FourierDecayAlt.P.WeakDominationMajorants.NInt
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 Formalism.FourierDecayAlt.P.B2x6
section pointwise
variable {k r' : ℕ}
instance haar_hpar (k r' : ℕ) : (volume : Measure (HPar k r')).IsAddHaarMeasure := by
  have : (volume : Measure (Fin (2 * r' + k + 1) → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  exact Measure.prod.instIsAddHaarMeasure _ _
end pointwise
section main
end main
end Formalism.FourierDecayAlt.P.WeakDominationMajorants.NInt
open Matrix MeasureTheory Filter Topology
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF
namespace Formalism.FourierDecayAlt.P.WeakDominationMajorants.Asm
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Formalism.FourierDecayAlt.P.WeakDominationMajorants
variable {k r : ℕ}
end Formalism.FourierDecayAlt.P.WeakDominationMajorants.Asm
open Matrix MeasureTheory Filter Topology
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF
namespace Formalism.FourierDecayAlt.P.WeakDominationMajorants.Asm
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open Formalism.FourierDecayAlt.P.WeakDominationMajorants
end Formalism.FourierDecayAlt.P.WeakDominationMajorants.Asm


