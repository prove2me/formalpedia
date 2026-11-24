-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SliceLastLevel
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_SliceLastLevel
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-24T19:48:01.503805+00:00
-- url     : https://prove2.me/theorems/11d6058b-bda0-49c9-973c-3ac43b04abb1
-- title:
--   Slice Last Level
-- statement:
--   Definitions and structural lemmas for Slice Last Level, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SliceLastLevel.lean

import Definitions.Def_Formalism_HermitianCurvature_StatementJF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Block3MulBlocks
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhiBoundPartsOfRadicalParametrisation
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DilationUnipotentWeylMeasure
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LongWeylElement
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SettingExistence
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OppositeWeylSubgroupClosed
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HermitianFormFactor
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwoByOneBlock
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CompactGroupHaarExists
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SmoothnessOnGoodSet
import Definitions.Def_Formalism_FormalDegreeBessel_FinalBF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormDiagonalEntryDilationGeneratorLeOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralAeConvergenceContinuity
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x3_Em_mul_mid
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x3_Em_mul_out
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x3_mul_EmT_mid
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x3_mul_EmT_out
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
section PartDefs
open Matrix MeasureTheory
namespace Formalism.FourierDecayAlt.P.SliceLastLevel
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
def phi (k r : ℕ) (c : Fin r → ℂ) (n n' : B.Mat k r) (μ : B.Mat k 0) : B.Mat k r :=
  n⁻¹ * bigCell k r c (castW μ) * n'
def emb0 (k r : ℕ) (Y : B.Mat k 0) : B.Mat k r := fun i j =>
  if h : (r ≤ i.val ∧ i.val ≤ r + k) ∧ (r ≤ j.val ∧ j.val ≤ r + k) then
    Y ⟨i.val - r, by omega⟩ ⟨j.val - r, by omega⟩ else 0
end Formalism.FourierDecayAlt.P.SliceLastLevel
end PartDefs
section PartSz
open Matrix
namespace Formalism.FourierDecayAlt.P.SliceLastLevel
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF Formalism.FourierDecayAlt.P.Ux5
section szIndex
variable (k r : ℕ)
def szX (a : Fin r) : Fin (2 * r + k + 1) := ⟨a.val, by omega⟩
def szW (w : Fin (k + 1)) : Fin (2 * r + k + 1) := ⟨r + w.val, by omega⟩
def szS (a : Fin r) : Fin (2 * r + k + 1) := ⟨2 * r + k - a.val, by omega⟩
lemma szX_val (a : Fin r) : (szX k r a).val = a.val := rfl
lemma szW_val (w : Fin (k + 1)) : (szW k r w).val = r + w.val := rfl
lemma szS_val (a : Fin r) : (szS k r a).val = 2 * r + k - a.val := rfl
def szF : (Fin r ⊕ Fin (k + 1)) ⊕ Fin r → Fin (2 * r + k + 1) :=
  Sum.elim (Sum.elim (szX k r) (szW k r)) (szS k r)
lemma szF_bij : Function.Bijective (szF k r) := by
  constructor
  · rintro ((a | a) | a) ((b | b) | b) h <;>
      simp only [szF, Sum.elim_inl, Sum.elim_inr, Fin.ext_iff, szX_val, szW_val, szS_val] at h <;>
      first
        | (have := a.isLt; have := b.isLt; congr 2; exact Fin.ext (by omega))
        | (have := a.isLt; have := b.isLt; congr 1; exact Fin.ext (by omega))
        | (exfalso; have := a.isLt; have := b.isLt; omega)
  · intro i
    have hi := i.isLt
    by_cases h1 : i.val < r
    · exact ⟨Sum.inl (Sum.inl ⟨i.val, h1⟩), Fin.ext rfl⟩
    · by_cases h2 : i.val ≤ r + k
      · exact ⟨Sum.inl (Sum.inr ⟨i.val - r, by omega⟩), Fin.ext (by simp [szF, szW_val]; omega)⟩
      · exact ⟨Sum.inr ⟨2 * r + k - i.val, by omega⟩, Fin.ext (by simp [szF, szS_val]; omega)⟩
def szE : (Fin r ⊕ Fin (k + 1)) ⊕ Fin r ≃ Fin (2 * r + k + 1) := Equiv.ofBijective _ (szF_bij k r)
variable {k r}
end szIndex
section szBlocks
variable {k r : ℕ}
end szBlocks
section szRel
variable {k r : ℕ}
end szRel
section szBound
def unitriangularFactorConstant {p : ℕ} (d : Fin p → ℂ) : ℝ :=
  ∑ i : Fin p, ((i.val + 1).factorial : ℝ) / ‖∏ t : Fin (i.val + 1), d (Fin.castLE i.isLt t)‖
end szBound
section szMain
end szMain
end Formalism.FourierDecayAlt.P.SliceLastLevel
end PartSz
section PartTr
open Matrix MeasureTheory Filter Topology
set_option linter.style.haveILetI false
namespace Formalism.FourierDecayAlt.P.SliceLastLevel
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
lemma tr_castW_add (a b : B.Mat k 0) : castW (a + b) = castW a + castW b := by
  ext i j
  simp [castW]
lemma levelEmbed_eq_conj_cast (Y : B.Mat k 0) : emb0 k r Y = P.B2x3.Em k r * castW Y * (P.B2x3.Em k r)ᵀ := by
  ext i j
  by_cases hj : P.TwoByOneBlock.mid k r j
  · rw [P.B2x3.mul_EmT_mid _ j i hj]
    by_cases hi : P.TwoByOneBlock.mid k r i
    · rw [P.B2x3.Em_mul_mid _ i _ hi]
      unfold emb0
      rw [dif_pos ⟨hi, hj⟩]
      simp only [castW, Matrix.reindex_apply, Matrix.submatrix_apply]
      congr 1
    · rw [P.B2x3.Em_mul_out _ i _ hi]
      unfold emb0
      rw [dif_neg (fun h => hi h.1)]
  · rw [P.B2x3.mul_EmT_out _ j i hj]
    unfold emb0
    rw [dif_neg (fun h => hj h.2)]
lemma tr_castW_smul (c : ℂ) (a : B.Mat k 0) : castW (c • a) = c • castW a := by
  ext i j
  simp [castW]
lemma levelEmbed_add (a b : B.Mat k 0) : emb0 k r (a + b) = emb0 k r a + emb0 k r b := by
  rw [levelEmbed_eq_conj_cast, levelEmbed_eq_conj_cast, levelEmbed_eq_conj_cast, tr_castW_add, Matrix.mul_add, Matrix.add_mul]
lemma levelEmbed_smul (c : ℂ) (a : B.Mat k 0) : emb0 k r (c • a) = c • emb0 k r a := by
  rw [levelEmbed_eq_conj_cast, levelEmbed_eq_conj_cast, tr_castW_smul, Matrix.mul_smul, Matrix.smul_mul]
def tr_emb0L (k r : ℕ) : B.Mat k 0 →L[ℂ] B.Mat k r :=
  LinearMap.toContinuousLinearMap
    { toFun := emb0 k r
      map_add' := levelEmbed_add
      map_smul' := levelEmbed_smul }
section transport
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
end transport
end Formalism.FourierDecayAlt.P.SliceLastLevel
end PartTr
section PartCd
open Matrix Filter Topology
open scoped ContDiff
namespace Formalism.FourierDecayAlt.P.SliceLastLevel
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
section cdmap
variable {k r d : ℕ} {O : Set (Fin d → ℝ)} {cx : (Fin d → ℝ) → Fin r → ℂ} {μx : (Fin d → ℝ) → B.Mat k 0}
def bmap (k r : ℕ) (cx : (Fin d → ℝ) → Fin r → ℂ) (μx : (Fin d → ℝ) → B.Mat k 0) (x : Fin d → ℝ) : B.Mat k r :=
  bigCell k r (cx x) (castW (μx x))
end cdmap
section cdmap2
variable {k r d : ℕ} {O : Set (Fin d → ℝ)} {cx : (Fin d → ℝ) → Fin r → ℂ} {μx : (Fin d → ℝ) → B.Mat k 0}
def ebd (b : Fin d) : Fin d → ℝ := fun j => if b = j then 1 else 0
def aB (k r : ℕ) (cx : (Fin d → ℝ) → Fin r → ℂ) (μx : (Fin d → ℝ) → B.Mat k 0) (i : Formalism.FourierDecayAlt.P.Ux10.J k r)
    (x : Fin d → ℝ) : (Fin d → ℝ) →L[ℝ] ℝ :=
  ∑ b, Formalism.FourierDecayAlt.P.Ux10.kc i ((bmap k r cx μx x)⁻¹ * fderiv ℝ (bmap k r cx μx) x (ebd b)) •
    ContinuousLinearMap.proj b
end cdmap2
section cdmap3
variable {k r d : ℕ} {O : Set (Fin d → ℝ)} {cx : (Fin d → ℝ) → Fin r → ℂ} {μx : (Fin d → ℝ) → B.Mat k 0}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
end cdmap3
end Formalism.FourierDecayAlt.P.SliceLastLevel
end PartCd
section PartM
open Matrix MeasureTheory Filter Topology
namespace Formalism.FourierDecayAlt.P.SliceLastLevel
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
def Ap (r : ℕ) (A : ℝ) (m : ℕ) : ℝ := (A - 6 * (r : ℝ) * (m : ℝ)) / (9 * ((r : ℝ) + 1))
section bound
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
end bound
section meas
variable {k r : ℕ}
def Sn (k r : ℕ) : Set (Mt k r × Mt k r) :=
  {ξ | (Matrix.of ξ.1 : B.Mat k r) ∈ Nset k r ∧ (Matrix.of ξ.2 : B.Mat k r) ∈ Nset k r}
def psiN {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (ξ : Mt k r × Mt k r) : ℂ :=
  psi k r D.z cStd (Matrix.of ξ.1) * star (psi k r D.z' cStd (Matrix.of ξ.2))
end meas
section clause2
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]
def hS (F : B.Mat k r → (Wq →L[ℂ] Wp)) (c : Fin r → ℂ) (ξ : Mt k r × Mt k r) (μ : B.Mat k 0) : Wq →L[ℂ] Wp :=
  Set.indicator (Sn k r) (fun ξ => F (phi k r c (Matrix.of ξ.1) (Matrix.of ξ.2) μ)) ξ
end clause2
section clause12
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]
def beta0 (M a : ℝ) (ξ : Mt k r × Mt k r) : ℝ :=
  M * (B.gN (Matrix.of ξ.1 : B.Mat k r) ^ (-a) * B.gN (Matrix.of ξ.2 : B.Mat k r) ^ (-a))
end clause12
end Formalism.FourierDecayAlt.P.SliceLastLevel
end PartM
section PartE
open Matrix MeasureTheory Filter Topology
open scoped ContDiff
set_option linter.style.haveILetI false
namespace Formalism.FourierDecayAlt.P.SliceLastLevel
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
section words
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]
def adR (n' : B.Mat k r) (i : Formalism.FourierDecayAlt.P.Ux10.J k r) : B.Mat k r := n'⁻¹ * Formalism.FourierDecayAlt.P.Ux10.Lt i * n'
def Gw (F : B.Mat k r → (Wq →L[ℂ] Wp)) (ξ : Mt k r × Mt k r) (w : List (Formalism.FourierDecayAlt.P.Ux10.J k r)) :
    B.Mat k r → (Wq →L[ℂ] Wp) :=
  B.Rw (w.map (adR (Matrix.of ξ.2))) F
end words
section clause3
variable {k r d : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]
def Fw (D : B.RealPlaceData k r Wp Wq) (F : B.Mat k r → (Wq →L[ℂ] Wp)) (cx : (Fin d → ℝ) → Fin r → ℂ)
    (μx : (Fin d → ℝ) → B.Mat k 0) (w : List (Formalism.FourierDecayAlt.P.Ux10.J k r)) (x : Fin d → ℝ)
    (ξ : Mt k r × Mt k r) : Wq →L[ℂ] Wp :=
  psiN D ξ • Set.indicator (Sn k r)
    (fun ξ => Gw F ξ w (phi k r (cx x) (Matrix.of ξ.1) (Matrix.of ξ.2) (μx x))) ξ
end clause3
section clause3b
variable {k r d : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]
end clause3b
end Formalism.FourierDecayAlt.P.SliceLastLevel
end PartE


