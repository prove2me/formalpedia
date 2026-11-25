-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RestrictionIrrelevantDoubleLevelOperator
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_RestrictionIrrelevantDoubleLevelOperator
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T01:11:10.888439+00:00
-- url     : https://prove2.me/theorems/cd3ab22f-e680-47de-a27b-12ff940ce91a
-- title:
--   Restriction Irrelevant Double Level Operator
-- statement:
--   Definitions and structural lemmas for Restriction Irrelevant Double Level Operator, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/RestrictionIrrelevantDoubleLevelOperator.lean

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TransferRtt
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_FormalDegreeBessel_FinalWR
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_YangianSpanCharacter_YangianRelationFirst
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstEmbeddingOne
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralAeConvergenceContinuity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TwoByOneBlock
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GammaFamilyCommuteGenerators
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_InterlaceSignTwo
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_MulIntegralStatement
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x3_hpk_e
import Theorems.Thm_Formalism_FourierDecayAlt_P_B2x3_hpk_es
import Theorems.Thm_Formalism_FourierDecayAlt_P_B5_curve_hasDerivAt
import Theorems.Thm_Formalism_FourierDecayAlt_P_B5_exp_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx3_mono
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx4_mono
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_PC_IsPolyS_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_PC_IsPolyS_id
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_PC_IsPoly_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_PC_IsPoly_neg
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_PC_IsPoly_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Mx6_PC_IsPoly_sum
import Theorems.Thm_Formalism_FourierDecayAlt_P_RankOneEmbeddings_In_key
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_key
import Theorems.Thm_Formalism_FourierDecayAlt_P_TwoByOneBlock_trans
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_hpk_sq
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_uh_mul
import Theorems.Thm_Formalism_QuantumDeterminants_WeylGroupFacts_uh_one
import Theorems.Thm_Formalism_QuantumDeterminants_hermitian_pos_facts_hold
import Theorems.Thm_Formalism_QuantumDeterminants_isOpen_OmX
import Theorems.Thm_Formalism_QuantumDeterminants_linOps
import Theorems.Thm_Formalism_REAL_hasDerivAt_mul_exp_smul_zero
import Theorems.Thm_Formalism_REAL_mulRightCLM_apply
import Theorems.Thm_Formalism_REAL_withTop_enat_infty_add_one_le_infty

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset MeasureTheory
open scoped ContDiff InnerProductSpace
noncomputable section
namespace Formalism.FourierDecayAlt.P.Qx8
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
def Dp (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) : Set (Mx k r) := {g | 0 < GGl k r z z' g}
section PairAlg
variable {V : Type} [AddCommGroup V] [Module ℂ V]
def pairM (t : ℂ → Fin 2 → Fin 2 → Module.End ℂ V) (Y : ℂ) : Matrix (Fin 2) (Fin 2) (Pr V) :=
  Matrix.of fun a b => mkP (t Y a b) (t (star Y) b a)
end PairAlg
section Rad
theorem smoothLev_congr {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {k r : ℕ} {i : Fin (r + 1)}
    {D : Set (Mx k r)} (hD : IsOpen D) {f f₂ : Mx k r → E} (h : SmoothLev k r i D f)
    (he : ∀ x ∈ Glev k r i ∩ D, f₂ x = f x) : SmoothLev k r i D f₂ := by
  intro g₀ hg₀
  obtain ⟨U, F, hU, hgU, hF, hfF⟩ := h g₀ hg₀
  exact ⟨U ∩ D, F, hU.inter hD, ⟨hgU, hg₀.2⟩, hF.mono Set.inter_subset_left,
    fun g hg hgl => by rw [he g ⟨hgl, hg.2⟩, hfF g hg.1 hgl]⟩
variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp]
  [NormedAddCommGroup Wq] [NormedSpace ℂ Wq] {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}
end Rad
end Formalism.FourierDecayAlt.P.Qx8
namespace Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.Qx8
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
end Formalism.FourierDecayAlt.P
namespace Formalism.FourierDecayAlt.P.Qx8
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
section Eigen
open Formalism.FourierDecayAlt.B
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
end Eigen
end Formalism.FourierDecayAlt.P.Qx8
namespace Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.Qx8
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
end Formalism.FourierDecayAlt.P
namespace Formalism.FourierDecayAlt.P.Qx8
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
section NF
open Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt.Fr Formalism.FourierDecayAlt.R
variable {P : M.Par} {𝒜 : Type} [Ring 𝒜] [StarRing 𝒜] [Algebra ℂ 𝒜] [StarModule ℂ 𝒜]
def nfStart (d : NFData P 𝒜) (QQ : ℂ → Matrix (Fin 2) (Fin 2) 𝒜) (l : ℕ) : Fr.Start 𝒜 where
  QQ Y := sgn P l • QQ Y
  q := qC P
  x Y := d.κ fun π => x0 P l π Y
  xi Y := d.κ fun π => (x0 P l π Y)⁻¹
  ee Y := d.L.ζ * d.L.ζbi * ∑ j ∈ Icc 1 (P.k - 1), (d.κ fun π => (Y + (rho P π j : ℂ))⁻¹) * d.SS j
  inv := {Y | ∀ π, xC P π Y ≠ 0}
end NF
end Formalism.FourierDecayAlt.P.Qx8
namespace Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.Qx8
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
end Formalism.FourierDecayAlt.P
namespace Formalism.FourierDecayAlt.P.Qx8
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
section Lie
variable {k r : ℕ}
theorem glev_one (i : Fin (r + 1)) : (1 : Mx k r) ∈ Glev k r i :=
  ⟨WeylGroupFacts.uh_one, fun _ _ => ⟨by simp, by simp⟩⟩
theorem glev_mul {i : Fin (r + 1)} {g h : Mx k r} (hg : g ∈ Glev k r i) (hh : h ∈ Glev k r i) :
    g * h ∈ Glev k r i := by
  refine ⟨WeylGroupFacts.uh_mul hg.1 hh.1, fun a ha => ⟨?_, ?_⟩⟩
  · rw [← Matrix.mulVec_mulVec, (hh.2 a ha).1, (hg.2 a ha).1]
  · rw [← Matrix.mulVec_mulVec, (hh.2 a ha).2, (hg.2 a ha).2]
theorem uw_glev {z : Fin (2 * r + k + 1) → ℂ} (i : Fin (r + 1)) : UWset k r z ⊆ Glev k r i :=
  fun _ hg => ⟨hg.1, fun a _ => hg.2.1 a⟩
theorem uw_one (z : Fin (2 * r + k + 1) → ℂ) : (1 : Mx k r) ∈ UWset k r z :=
  ⟨WeylGroupFacts.uh_one, fun _ => ⟨by simp, by simp⟩, by simp⟩
theorem nlev_one (i : Fin (r + 1)) : (1 : Mx k r) ∈ Nlev k r i :=
  ⟨⟨WeylGroupFacts.uh_one, fun _ _ _ => Matrix.one_apply, fun _ _ _ _ _ => Matrix.one_apply⟩, glev_one i⟩
def mulVecL (v : Fin (2 * r + k + 1) → ℂ) : Mx k r →L[ℝ] (Fin (2 * r + k + 1) → ℂ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun A => A *ᵥ v
      map_add' := fun A B => Matrix.add_mulVec A B v
      map_smul' := fun c A => Matrix.smul_mulVec c A v }
theorem exp_fix {X : Mx k r} {v : Fin (2 * r + k + 1) → ℂ} (h : X *ᵥ v = 0) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • X) *ᵥ v = v := by
  have hd : ∀ s : ℝ, HasDerivAt (fun s : ℝ => mulVecL v ((1 : Mx k r) * NormedSpace.exp ((s : ℂ) • X))) 0 s := by
    intro s
    have h1 := B5.curve_hasDerivAt (1 : Mx k r) X s
    have h2 := (mulVecL v).hasFDerivAt.comp_hasDerivAt s h1
    refine h2.congr_deriv ?_
    show ((1 : Mx k r) * NormedSpace.exp ((s : ℂ) • X) * X) *ᵥ v = 0
    rw [← Matrix.mulVec_mulVec, h, Matrix.mulVec_zero]
  have hc := is_const_of_deriv_eq_zero (fun s => (hd s).differentiableAt) (fun s => (hd s).deriv) t 0
  simpa [mulVecL, NormedSpace.exp_zero] using hc
theorem exp_lev {i : Fin (r + 1)} {X : Mx k r} (hX : inLieLev k r i X) (t : ℝ) :
    NormedSpace.exp ((t : ℂ) • X) ∈ Glev k r i :=
  ⟨B5.exp_mem hX.1 t, fun a ha => ⟨exp_fix (hX.2 a ha).1 t, exp_fix (hX.2 a ha).2 t⟩⟩
theorem hpk_e (a : Fin r) : Hpk k r *ᵥ bvec (eI k r a) = bvec (esI k r a) := by
  funext p
  simp only [bvec, Matrix.mulVec_single_one, Matrix.col_apply, Pi.single_apply]
  unfold Hpk eI esI
  simp only [Fin.ext_iff]
  have := p.isLt
  have := a.isLt
  split_ifs <;> first | rfl | (exfalso; omega)
theorem hpk_es (a : Fin r) : Hpk k r *ᵥ bvec (esI k r a) = bvec (eI k r a) := by
  funext p
  simp only [bvec, Matrix.mulVec_single_one, Matrix.col_apply, Pi.single_apply]
  unfold Hpk eI esI
  simp only [Fin.ext_iff]
  have := p.isLt
  have := a.isLt
  split_ifs <;> first | rfl | (exfalso; omega)
theorem hpk_herm : (Hpk k r)ᴴ = Hpk k r := (hermitian_pos_facts_hold k r).1
theorem hpk_inv : (Hpk k r)⁻¹ = Hpk k r := Matrix.inv_eq_right_inv WeylGroupFacts.hpk_sq
theorem hpart_skew {n : ℕ} (H Z : Matrix (Fin n) (Fin n) ℂ) (hsq : H * H = 1) (hh : Hᴴ = H) :
    (hpart1 H Z)ᴴ * H + H * hpart1 H Z = 0 ∧ (hpart2 H Z)ᴴ * H + H * hpart2 H Z = 0 := by
  have hinv : H⁻¹ = H := Matrix.inv_eq_right_inv hsq
  have e1 : H * Z * H * H = H * Z := by rw [Matrix.mul_assoc, hsq, Matrix.mul_one]
  have e2 : H * (H * Zᴴ * H) = Zᴴ * H := by
    rw [Matrix.mul_assoc H Zᴴ H, ← Matrix.mul_assoc H H, hsq, Matrix.one_mul]
  have e3 : (H * Zᴴ * H)ᴴ = H * Z * H := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hh,
      Matrix.mul_assoc]
  constructor
  · unfold hpart1
    rw [hinv, Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, e3, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.sub_mul, Matrix.mul_sub, e1, e2]
    have : star (1 / 2 : ℂ) = 1 / 2 := by simp
    rw [this, ← smul_add]
    simp
  · unfold hpart2
    rw [hinv, Matrix.conjTranspose_smul, Matrix.conjTranspose_add, e3, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.add_mul, Matrix.mul_add, e1, e2]
    have : star (1 / (2 * Complex.I) : ℂ) = -(1 / (2 * Complex.I)) := by
      simp [Complex.conj_I]
    rw [this, neg_smul, add_comm (Zᴴ * H) (H * Z), neg_add_cancel]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
def LocOn (S : Set (Mx k r)) (T : (Mx k r → E) → Mx k r → E) : Prop :=
  ∀ f f₂ : Mx k r → E, (∀ x ∈ S, f x = f₂ x) → ∀ x ∈ S, T f x = T f₂ x
end Lie
section Frames
variable {k r : ℕ}
end Frames
section FFmod
variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp]
  [NormedAddCommGroup Wq] [NormedSpace ℂ Wq] {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}
  {i : Fin (r + 1)} {D : Set (Mx k r)}
theorem dom_mem (hD : IsDom k r z z' i D) {g : Mx k r} (hg : g ∈ Glev k r i ∩ D) {h n h' n' : Mx k r}
    (hh : h ∈ UWset k r z) (hn : n ∈ Nlev k r i) (hh' : h' ∈ UWset k r z') (hn' : n' ∈ Nlev k r i) :
    (h * n) * g * (h' * n') ∈ Glev k r i ∩ D :=
  ⟨glev_mul (glev_mul (glev_mul (uw_glev i hh) hn.2) hg.1) (glev_mul (uw_glev i hh') hn'.2),
    hD.2 g hg _ ⟨h, hh, n, hn, rfl⟩ _ ⟨h', hh', n', hn', rfl⟩⟩
theorem smooth_add {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {f f₂ : Mx k r → E}
    (hf : SmoothLev k r i D f) (hf₂ : SmoothLev k r i D f₂) : SmoothLev k r i D (f + f₂) := by
  intro g₀ hg₀
  obtain ⟨U, F, hU, hxU, hF, hΦ⟩ := hf g₀ hg₀
  obtain ⟨U', F', hU', hxU', hF', hΨ⟩ := hf₂ g₀ hg₀
  exact ⟨U ∩ U', F + F', hU.inter hU', ⟨hxU, hxU'⟩,
    (hF.mono Set.inter_subset_left).add (hF'.mono Set.inter_subset_right),
    fun x hx hg => by simp [hΦ x hx.1 hg, hΨ x hx.2 hg]⟩
theorem smooth_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {f : Mx k r → E}
    (hf : SmoothLev k r i D f) (a : ℂ) : SmoothLev k r i D (a • f) := by
  intro g₀ hg₀
  obtain ⟨U, F, hU, hxU, hF, hΦ⟩ := hf g₀ hg₀
  exact ⟨U, a • F, hU, hxU, hF.const_smul a, fun x hx hg => by simp [hΦ x hx hg]⟩
theorem smooth_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] :
    SmoothLev k r i D (0 : Mx k r → E) :=
  fun _ _ => ⟨Set.univ, 0, isOpen_univ, trivial, contDiffOn_const, fun _ _ _ => rfl⟩
theorem FFl_congr (hD : IsDom k r z z' i D) {J J' : Mx k r → (Wq →L[ℂ] Wp)} (hJ : J ∈ FFl k r z z' π π' i D)
    (he : ∀ x ∈ Glev k r i ∩ D, J' x = J x) : J' ∈ FFl k r z z' π π' i D := by
  obtain ⟨h1, h2, h3, h4⟩ := hJ
  refine ⟨smoothLev_congr hD.1 h1 he, ?_, ?_, ?_⟩
  · intro g hg n hn
    have hm := dom_mem hD hg (uw_one z) hn (uw_one z') (nlev_one i)
    simp only [one_mul, mul_one] at hm
    rw [he _ hm, he _ hg, h2 g hg n hn]
  · intro g hg n hn
    have hm := dom_mem hD hg (uw_one z) (nlev_one i) (uw_one z') hn
    simp only [one_mul, mul_one] at hm
    rw [he _ hm, he _ hg, h3 g hg n hn]
  · intro g hg h hh h' hh'
    have hm := dom_mem hD hg hh (nlev_one i) hh' (nlev_one i)
    simp only [mul_one] at hm
    rw [he _ hm, he _ hg, h4 g hg h hh h' hh']
theorem FFl_add {J J' : Mx k r → (Wq →L[ℂ] Wp)} (hJ : J ∈ FFl k r z z' π π' i D)
    (hJ' : J' ∈ FFl k r z z' π π' i D) : J + J' ∈ FFl k r z z' π π' i D := by
  obtain ⟨h1, h2, h3, h4⟩ := hJ
  obtain ⟨h1', h2', h3', h4'⟩ := hJ'
  refine ⟨smooth_add h1 h1', ?_, ?_, ?_⟩
  · intro g hg n hn
    simp only [Pi.add_apply]
    rw [h2 g hg n hn, h2' g hg n hn, smul_add]
  · intro g hg n hn
    simp only [Pi.add_apply]
    rw [h3 g hg n hn, h3' g hg n hn, smul_add]
  · intro g hg h hh h' hh'
    simp only [Pi.add_apply]
    rw [h4 g hg h hh h' hh', h4' g hg h hh h' hh']
    ext v
    simp
theorem FFl_smul {J : Mx k r → (Wq →L[ℂ] Wp)} (hJ : J ∈ FFl k r z z' π π' i D) (a : ℂ) :
    a • J ∈ FFl k r z z' π π' i D := by
  obtain ⟨h1, h2, h3, h4⟩ := hJ
  refine ⟨smooth_smul h1 a, ?_, ?_, ?_⟩
  · intro g hg n hn
    simp only [Pi.smul_apply]
    rw [h2 g hg n hn, smul_comm]
  · intro g hg n hn
    simp only [Pi.smul_apply]
    rw [h3 g hg n hn, smul_comm]
  · intro g hg h hh h' hh'
    simp only [Pi.smul_apply]
    rw [h4 g hg h hh h' hh']
    ext v
    simp
theorem FFl_zero : (0 : Mx k r → (Wq →L[ℂ] Wp)) ∈ FFl k r z z' π π' i D :=
  ⟨smooth_zero, fun _ _ _ _ => by simp, fun _ _ _ _ => by simp, fun _ _ _ _ _ _ => by simp⟩
variable (k r z z' π π' i D) in

def FFV : Submodule ℂ (Mx k r → (Wq →L[ℂ] Wp)) where
  carrier := {J | J ∈ FFl k r z z' π π' i D ∧ ∀ g, g ∉ Glev k r i ∩ D → J g = 0}
  zero_mem' := ⟨FFl_zero, fun _ _ => rfl⟩
  add_mem' := fun hJ hJ' => ⟨FFl_add hJ.1 hJ'.1, fun g hg => by simp [hJ.2 g hg, hJ'.2 g hg]⟩
  smul_mem' := fun a _ hJ => ⟨FFl_smul hJ.1 a, fun g hg => by simp [hJ.2 g hg]⟩
theorem FFV_ext {Φ Ψ : FFV k r z z' π π' i D}
    (h : ∀ x ∈ Glev k r i ∩ D, (Φ : Mx k r → (Wq →L[ℂ] Wp)) x = (Ψ : Mx k r → (Wq →L[ℂ] Wp)) x) : Φ = Ψ := by
  apply Subtype.ext
  funext g
  by_cases hg : g ∈ Glev k r i ∩ D
  · exact h g hg
  · rw [Φ.2.2 g hg, Ψ.2.2 g hg]
open Classical in

def cutV (hD : IsDom k r z z' i D) (J : Mx k r → (Wq →L[ℂ] Wp)) (hJ : J ∈ FFl k r z z' π π' i D) :
    FFV k r z z' π π' i D :=
  ⟨(Glev k r i ∩ D).indicator J, FFl_congr hD hJ (fun _ hx => Set.indicator_of_mem hx _),
    fun _ hg => Set.indicator_of_notMem hg _⟩
theorem cutV_apply (hD : IsDom k r z z' i D) (J : Mx k r → (Wq →L[ℂ] Wp)) (hJ : J ∈ FFl k r z z' π π' i D)
    {x : Mx k r} (hx : x ∈ Glev k r i ∩ D) : (cutV hD J hJ : Mx k r → (Wq →L[ℂ] Wp)) x = J x :=
  Set.indicator_of_mem hx _
theorem tl_zero (hT : TLinLoc) {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (hD : IsOpen D) (Y : ℂ)
    (a b : Fin 2) {g : Mx k r} (hg : g ∈ Glev k r i ∩ D) : tL k r z z' i Y a b (0 : Mx k r → E) g = 0 := by
  have h := (hT E k r z z' i D Y a b 0 0 1 hD smooth_zero smooth_zero g hg).1
  have e : (fun x => (0 : Mx k r → E) x + (1 : ℂ) • (0 : Mx k r → E) x) = 0 := by funext x; simp
  rw [e, one_smul] at h
  exact left_eq_add.mp h
theorem tl_add (hT : TLinLoc) {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (hD : IsOpen D) (Y : ℂ)
    (a b : Fin 2) {f f₂ : Mx k r → E} (hf : SmoothLev k r i D f) (hf₂ : SmoothLev k r i D f₂) {g : Mx k r}
    (hg : g ∈ Glev k r i ∩ D) :
    tL k r z z' i Y a b (f + f₂) g = tL k r z z' i Y a b f g + tL k r z z' i Y a b f₂ g := by
  have h := (hT E k r z z' i D Y a b f f₂ 1 hD hf hf₂ g hg).1
  have e : (fun x => f x + (1 : ℂ) • f₂ x) = f + f₂ := by funext x; simp
  rw [e, one_smul] at h
  exact h
theorem tl_smul (hT : TLinLoc) {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (hD : IsOpen D) (Y : ℂ)
    (a b : Fin 2) (s : ℂ) {f : Mx k r → E} (hf : SmoothLev k r i D f) {g : Mx k r}
    (hg : g ∈ Glev k r i ∩ D) : tL k r z z' i Y a b (s • f) g = s • tL k r z z' i Y a b f g := by
  have h := (hT E k r z z' i D Y a b 0 f s hD smooth_zero hf g hg).1
  have e : (fun x => (0 : Mx k r → E) x + s • f x) = s • f := by funext x; simp
  rw [e, tl_zero hT hD Y a b hg, zero_add] at h
  exact h
def TV (hT : TLinLoc) (hP : TPreservesFF) (hz : inWb k r z) (hz' : inWb k r z') (hD : IsDom k r z z' i D) (Y : ℂ)
    (a b : Fin 2) : Module.End ℂ (FFV k r z z' π π' i D) where
  toFun Φ := cutV hD (tL k r z z' i Y a b (Φ : Mx k r → (Wq →L[ℂ] Wp)))
    (hP Wp Wq k r z z' π π' i D Y a b hz hz' hD _ Φ.2.1)
  map_add' Φ Ψ := by
    apply FFV_ext
    intro x hx
    rw [cutV_apply hD _ _ hx, Submodule.coe_add, Submodule.coe_add, Pi.add_apply, cutV_apply hD _ _ hx,
      cutV_apply hD _ _ hx]
    exact tl_add hT hD.1 Y a b Φ.2.1.1 Ψ.2.1.1 hx
  map_smul' s Φ := by
    apply FFV_ext
    intro x hx
    rw [cutV_apply hD _ _ hx, Submodule.coe_smul, RingHom.id_apply, Submodule.coe_smul, Pi.smul_apply,
      cutV_apply hD _ _ hx]
    exact tl_smul hT hD.1 Y a b s Φ.2.1.1 hx
end FFmod
end Formalism.FourierDecayAlt.P.Qx8
namespace Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.Qx8
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
end Formalism.FourierDecayAlt.P
namespace Formalism.FourierDecayAlt.P.Qx8
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
section CDsec
open Topology
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
abbrev XX (k r : ℕ) := (Fin r → ℂ) × Mx k r
variable {i : Fin (r + 1)} {U₀ : Set (XX k r)}
def dv (v : Fin r → ℂ) (Φ : Fn k r E) : Fn k r E := fun c g => fderiv ℝ (fun c' => Φ c' g) c v
theorem slice_hasFDeriv {Φ : Fn k r E} {F : XX k r → E} {U : Set (XX k r)} (hU : IsOpen U)
    (hF : ContDiffOn ℝ ∞ F U) (hΦ : ∀ x ∈ U, x.2 ∈ Glev k r i → Φ x.1 x.2 = F x) {x : XX k r} (hx : x ∈ U)
    (hG : x.2 ∈ Glev k r i) :
    HasFDerivAt (fun c' => Φ c' x.2) ((fderiv ℝ F x).comp (ContinuousLinearMap.inl ℝ (Fin r → ℂ) (Mx k r))) x.1 := by
  have hFd : DifferentiableAt ℝ F x := (hF.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hx)
  have hγ : HasFDerivAt (fun c' : Fin r → ℂ => ((c', x.2) : XX k r))
      (ContinuousLinearMap.inl ℝ (Fin r → ℂ) (Mx k r)) x.1 := hasFDerivAt_prodMk_left x.1 x.2
  have hcomp : HasFDerivAt (fun c' => F (c', x.2))
      ((fderiv ℝ F x).comp (ContinuousLinearMap.inl ℝ (Fin r → ℂ) (Mx k r))) x.1 :=
    HasFDerivAt.comp x.1 (f := fun c' : Fin r → ℂ => ((c', x.2) : XX k r)) hFd.hasFDerivAt hγ
  refine hcomp.congr_of_eventuallyEq ?_
  have hmem : ∀ᶠ c' in 𝓝 x.1, ((c', x.2) : XX k r) ∈ U :=
    hγ.continuousAt.preimage_mem_nhds (hU.mem_nhds hx)
  filter_upwards [hmem] with c' hc'
  exact hΦ _ hc' hG
theorem dv_eq {Φ : Fn k r E} {F : XX k r → E} {U : Set (XX k r)} (hU : IsOpen U)
    (hF : ContDiffOn ℝ ∞ F U) (hΦ : ∀ x ∈ U, x.2 ∈ Glev k r i → Φ x.1 x.2 = F x) {x : XX k r} (hx : x ∈ U)
    (hG : x.2 ∈ Glev k r i) (v : Fin r → ℂ) : dv v Φ x.1 x.2 = fderiv ℝ F x (v, 0) := by
  unfold dv
  rw [(slice_hasFDeriv hU hF hΦ hx hG).fderiv]
  rfl
theorem sf_diff {Φ : Fn k r E} (h : SmoothFam k r i U₀ Φ) {x : XX k r} (hx : x ∈ U₀) (hG : x.2 ∈ Glev k r i) :
    DifferentiableAt ℝ (fun c' => Φ c' x.2) x.1 := by
  obtain ⟨U, F, hU, hxU, hF, hΦ⟩ := h x hx hG
  exact (slice_hasFDeriv hU hF hΦ hxU hG).differentiableAt
def Ldir (X : Mx k r) : XX k r →L[ℝ] XX k r := (ContinuousLinearMap.inr ℝ (Fin r → ℂ) (Mx k r)).comp
    ((mulRightRealCLM X).comp (ContinuousLinearMap.snd ℝ (Fin r → ℂ) (Mx k r)))
theorem rd_eq {Φ : Fn k r E} {F : XX k r → E} {U : Set (XX k r)} (hU : IsOpen U)
    (hF : ContDiffOn ℝ ∞ F U) (hΦ : ∀ x ∈ U, x.2 ∈ Glev k r i → Φ x.1 x.2 = F x) {X : Mx k r}
    (hX : inLieLev k r i X) {x : XX k r} (hx : x ∈ U) (hxG : x.2 ∈ Glev k r i) :
    RdV X (Φ x.1) x.2 = fderiv ℝ F x (Ldir X x) := by
  have hγ : HasDerivAt (fun t : ℝ => ((x.1, x.2 * NormedSpace.exp ((t : ℂ) • X)) : XX k r)) (Ldir X x) 0 :=
    (hasDerivAt_const (0 : ℝ) x.1).prodMk (hasDerivAt_mul_exp_smul_zero x.2 X)
  have hγ0 : ((x.1, x.2 * NormedSpace.exp (((0 : ℝ) : ℂ) • X)) : XX k r) = x := by
    simp [NormedSpace.exp_zero]
  have hFd : DifferentiableAt ℝ F x :=
    (hF.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hx)
  have hcomp : HasDerivAt (fun t : ℝ => F (x.1, x.2 * NormedSpace.exp ((t : ℂ) • X)))
      (fderiv ℝ F x (Ldir X x)) 0 :=
    hFd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hγ hγ0.symm
  have hev : (fun t : ℝ => Φ x.1 (x.2 * NormedSpace.exp ((t : ℂ) • X))) =ᶠ[𝓝 0]
      (fun t : ℝ => F (x.1, x.2 * NormedSpace.exp ((t : ℂ) • X))) := by
    have hmem : ∀ᶠ t : ℝ in 𝓝 0, ((x.1, x.2 * NormedSpace.exp ((t : ℂ) • X)) : XX k r) ∈ U :=
      hγ.continuousAt.preimage_mem_nhds (by rw [hγ0]; exact hU.mem_nhds hx)
    filter_upwards [hmem] with t ht
    exact hΦ _ ht (glev_mul hxG (exp_lev hX t))
  show deriv (fun t : ℝ => Φ x.1 (x.2 * NormedSpace.exp ((t : ℂ) • X))) 0 = _
  rw [hev.deriv_eq]
  exact hcomp.deriv
structure CD (i : Fin (r + 1)) (U₀ : Set (XX k r)) (T : (Mx k r → E) → Mx k r → E) : Prop where
  sm : ∀ Φ : Fn k r E, SmoothFam k r i U₀ Φ → SmoothFam k r i U₀ (fun c => T (Φ c))
  loc : ∀ Φ Ψ : Fn k r E, (∀ x ∈ U₀, x.2 ∈ Glev k r i → Φ x.1 x.2 = Ψ x.1 x.2) →
    ∀ x ∈ U₀, x.2 ∈ Glev k r i → T (Φ x.1) x.2 = T (Ψ x.1) x.2
  comm : ∀ (v : Fin r → ℂ) (Φ : Fn k r E), SmoothFam k r i U₀ Φ → ∀ x ∈ U₀, x.2 ∈ Glev k r i →
    dv v (fun c => T (Φ c)) x.1 x.2 = T (dv v Φ x.1) x.2
theorem CD.rdV (hU₀ : IsOpen U₀) {X : Mx k r} (hX : inLieLev k r i X) : CD (E := E) i U₀ (RdV X) := by
  refine ⟨?_, ?_, ?_⟩
  · intro Φ h x₀ hx₀ hg₀
    obtain ⟨U, F, hU, hxU, hF, hΦ⟩ := h x₀ hx₀ hg₀
    exact ⟨U, fun x => fderiv ℝ F x (Ldir X x), hU, hxU,
      (hF.fderiv_of_isOpen (m := ∞) hU withTop_enat_infty_add_one_le_infty).clm_apply (Ldir X).contDiff.contDiffOn,
      fun x hx hxG => rd_eq hU hF hΦ hX hx hxG⟩
  · intro Φ Ψ h x hx hxG
    have hγ : HasDerivAt (fun t : ℝ => ((x.1, x.2 * NormedSpace.exp ((t : ℂ) • X)) : XX k r)) (Ldir X x) 0 :=
      (hasDerivAt_const (0 : ℝ) x.1).prodMk (hasDerivAt_mul_exp_smul_zero x.2 X)
    have hγ0 : ((x.1, x.2 * NormedSpace.exp (((0 : ℝ) : ℂ) • X)) : XX k r) = x := by
      simp [NormedSpace.exp_zero]
    have hmem : ∀ᶠ t : ℝ in 𝓝 0, ((x.1, x.2 * NormedSpace.exp ((t : ℂ) • X)) : XX k r) ∈ U₀ :=
      hγ.continuousAt.preimage_mem_nhds (by rw [hγ0]; exact hU₀.mem_nhds hx)
    unfold RdV
    apply Filter.EventuallyEq.deriv_eq
    filter_upwards [hmem] with t ht
    exact h _ ht (glev_mul hxG (exp_lev hX t))
  · intro v Φ h x hx hxG
    obtain ⟨U, F, hU, hxU, hF, hΦ⟩ := h x hx hxG
    have hF1 : ContDiffOn ℝ ∞ (fun y => fderiv ℝ F y (Ldir X y)) U :=
      (hF.fderiv_of_isOpen (m := ∞) hU withTop_enat_infty_add_one_le_infty).clm_apply (Ldir X).contDiff.contDiffOn
    have hF2 : ContDiffOn ℝ ∞ (fun y => fderiv ℝ F y ((v, 0) : XX k r)) U :=
      (hF.fderiv_of_isOpen (m := ∞) hU withTop_enat_infty_add_one_le_infty).clm_apply contDiffOn_const
    rw [dv_eq (Φ := fun c => RdV X (Φ c)) hU hF1 (fun y hy hyG => rd_eq hU hF hΦ hX hy hyG) hxU hxG v,
      rd_eq (Φ := dv v Φ) hU hF2 (fun y hy hyG => dv_eq hU hF hΦ hy hyG v) hX hxU hxG]
    have hFa : ContDiffAt ℝ ∞ F x := hF.contDiffAt (hU.mem_nhds hxU)
    have hc : DifferentiableAt ℝ (fderiv ℝ F) x :=
      (hFa.fderiv_right (m := ∞) withTop_enat_infty_add_one_le_infty).differentiableAt (by simp)
    have H1 := (hc.hasFDerivAt.clm_apply (Ldir X).hasFDerivAt).fderiv
    have H2 := (hc.hasFDerivAt.clm_apply (hasFDerivAt_const ((v, 0) : XX k r) x)).fderiv
    have e1 := congrFun (congrArg DFunLike.coe H1) ((v, 0) : XX k r)
    have e2 := congrFun (congrArg DFunLike.coe H2) (Ldir X x)
    refine e1.trans (Eq.trans ?_ e2.symm)
    have hsym : IsSymmSndFDerivAt ℝ F x := hFa.isSymmSndFDerivAt (by simp only [minSmoothness_of_isRCLikeNormedField]; exact WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤))
    have hL0 : Ldir X ((v, 0) : XX k r) = 0 := by
      simp [Ldir, mulRightCLM_apply]
    show fderiv ℝ F x (Ldir X ((v, 0) : XX k r)) + fderiv ℝ (fderiv ℝ F) x ((v, 0) : XX k r) (Ldir X x) =
      fderiv ℝ F x 0 + fderiv ℝ (fderiv ℝ F) x (Ldir X x) ((v, 0) : XX k r)
    rw [hL0, map_zero, zero_add, zero_add]
    exact hsym _ _
theorem CD.id : CD (E := E) i U₀ (fun f => f) := ⟨fun _ h => h, fun _ _ h => h, fun _ _ _ _ _ _ => rfl⟩
theorem sf_zero : SmoothFam k r i U₀ (fun _ _ => (0 : E)) :=
  fun _ _ _ => ⟨Set.univ, fun _ => 0, isOpen_univ, trivial, contDiffOn_const, fun _ _ _ => rfl⟩
theorem sf_add {Φ Ψ : Fn k r E} (h : SmoothFam k r i U₀ Φ) (h' : SmoothFam k r i U₀ Ψ) :
    SmoothFam k r i U₀ (fun c g => Φ c g + Ψ c g) := by
  intro x₀ hx₀ hg₀
  obtain ⟨U, F, hU, hxU, hF, hΦ⟩ := h x₀ hx₀ hg₀
  obtain ⟨U', F', hU', hxU', hF', hΦ'⟩ := h' x₀ hx₀ hg₀
  exact ⟨U ∩ U', fun x => F x + F' x, hU.inter hU', ⟨hxU, hxU'⟩,
    (hF.mono Set.inter_subset_left).add (hF'.mono Set.inter_subset_right),
    fun x hx hxG => by
      show Φ x.1 x.2 + Ψ x.1 x.2 = F x + F' x
      rw [hΦ x hx.1 hxG, hΦ' x hx.2 hxG]⟩
theorem sf_smul {a : Fn k r ℂ} {Φ : Fn k r E} (h : SmoothFam k r i U₀ a) (h' : SmoothFam k r i U₀ Φ) :
    SmoothFam k r i U₀ (fun c g => a c g • Φ c g) := by
  intro x₀ hx₀ hg₀
  obtain ⟨U, F, hU, hxU, hF, hΦ⟩ := h x₀ hx₀ hg₀
  obtain ⟨U', F', hU', hxU', hF', hΦ'⟩ := h' x₀ hx₀ hg₀
  exact ⟨U ∩ U', fun x => F x • F' x, hU.inter hU', ⟨hxU, hxU'⟩,
    (hF.mono Set.inter_subset_left).smul (hF'.mono Set.inter_subset_right),
    fun x hx hxG => by
      show a x.1 x.2 • Φ x.1 x.2 = F x • F' x
      rw [hΦ x hx.1 hxG, hΦ' x hx.2 hxG]⟩
theorem sf_const (s : ℂ) : SmoothFam k r i U₀ (fun _ _ => s) :=
  fun _ _ _ => ⟨Set.univ, fun _ => s, isOpen_univ, trivial, contDiffOn_const, fun _ _ _ => rfl⟩
theorem CD.zero : CD (E := E) i U₀ (fun _ _ => 0) :=
  ⟨fun _ _ => sf_zero, fun _ _ _ _ _ _ => rfl, fun v _ _ _ _ _ => by simp [dv]⟩
theorem CD.comp {T S : (Mx k r → E) → Mx k r → E} (hT : CD i U₀ T) (hS : CD i U₀ S) :
    CD i U₀ (fun f => T (S f)) := by
  refine ⟨fun Φ h => hT.sm _ (hS.sm Φ h), fun Φ Ψ h => hT.loc (fun c => S (Φ c)) (fun c => S (Ψ c)) (hS.loc Φ Ψ h), ?_⟩
  intro v Φ h x hx hxG
  rw [hT.comm v _ (hS.sm Φ h) x hx hxG]
  exact hT.loc (dv v fun c => S (Φ c)) (fun c => S (dv v Φ c)) (fun y hy hyG => hS.comm v Φ h y hy hyG) x hx hxG
theorem CD.add {T S : (Mx k r → E) → Mx k r → E} (hT : CD i U₀ T) (hS : CD i U₀ S) :
    CD i U₀ (fun f g => T f g + S f g) := by
  refine ⟨fun Φ h => sf_add (hT.sm Φ h) (hS.sm Φ h), fun Φ Ψ h x hx hxG => ?_, ?_⟩
  · show T (Φ x.1) x.2 + S (Φ x.1) x.2 = T (Ψ x.1) x.2 + S (Ψ x.1) x.2
    rw [hT.loc Φ Ψ h x hx hxG, hS.loc Φ Ψ h x hx hxG]
  · intro v Φ h x hx hxG
    show _ = T (dv v Φ x.1) x.2 + S (dv v Φ x.1) x.2
    rw [← hT.comm v Φ h x hx hxG, ← hS.comm v Φ h x hx hxG]
    unfold dv
    have := fderiv_fun_add (sf_diff (hT.sm Φ h) hx hxG) (sf_diff (hS.sm Φ h) hx hxG)
    rw [this]
    rfl
theorem CD.coef {T : (Mx k r → E) → Mx k r → E} (hT : CD i U₀ T) (a : Mx k r → ℂ)
    (ha : SmoothFam k r i U₀ (fun _ g => a g)) : CD i U₀ (fun f g => a g • T f g) := by
  refine ⟨fun Φ h => sf_smul ha (hT.sm Φ h), fun Φ Ψ h x hx hxG => ?_, ?_⟩
  · show a x.2 • T (Φ x.1) x.2 = a x.2 • T (Ψ x.1) x.2
    rw [hT.loc Φ Ψ h x hx hxG]
  · intro v Φ h x hx hxG
    show _ = a x.2 • T (dv v Φ x.1) x.2
    rw [← hT.comm v Φ h x hx hxG]
    unfold dv
    have := fderiv_fun_const_smul (sf_diff (hT.sm Φ h) hx hxG) (a x.2)
    rw [this]
    rfl
theorem CD.csmul {T : (Mx k r → E) → Mx k r → E} (hT : CD i U₀ T) (s : ℂ) : CD i U₀ (fun f g => s • T f g) :=
  hT.coef (fun _ => s) (sf_const s)
theorem CD.neg {T : (Mx k r → E) → Mx k r → E} (hT : CD i U₀ T) : CD i U₀ (fun f g => -(T f g)) := by
  have := hT.csmul (-1)
  simpa using this
theorem CD.sum {ι : Type*} (s : Finset ι) {T : ι → (Mx k r → E) → Mx k r → E} (h : ∀ j ∈ s, CD i U₀ (T j)) :
    CD i U₀ (fun f g => ∑ j ∈ s, T j f g) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (CD.zero (E := E) (i := i) (U₀ := U₀))
  | insert a s ha ih =>
    have := (h a (Finset.mem_insert_self a s)).add (ih fun j hj => h j (Finset.mem_insert_of_mem hj))
    simpa [Finset.sum_insert ha] using this
theorem CD.foldr (L : List ((Mx k r → E) → Mx k r → E)) (hL : ∀ T ∈ L, CD i U₀ T) :
    CD i U₀ (fun f => L.foldr (fun T h => T h) f) := by
  induction L with
  | nil => exact CD.id
  | cons T L ih =>
    exact (hL T List.mem_cons_self).comp (ih fun T' hT' => hL T' (List.mem_cons_of_mem _ hT'))
end CDsec
section CDentries
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {i : Fin (r + 1)} {U₀ : Set (XX k r)}
theorem single_bvec {p q c : Fin (2 * r + k + 1)} (h : q ≠ c) :
    (Matrix.single p q (1 : ℂ)) *ᵥ bvec c = 0 := by
  funext x
  simp [bvec, h]
theorem posL_ne_e (i : Fin (r + 1)) (a : Fin (mdim k r i)) (b : Fin r) (hb : b.val < i.val) :
    posL k r i a ≠ eI k r b ∧ posL k r i a ≠ esI k r b := by
  have h1 := a.isLt
  have h2 := i.isLt
  unfold mdim at h1
  simp only [posL, eI, esI, ne_eq, Fin.ext_iff]
  omega
theorem hpart_lie (i : Fin (r + 1)) (a b : Fin (mdim k r i)) :
    inLieLev k r i (hpart1 (Hpk k r) (Matrix.single (posL k r i a) (posL k r i b) 1)) ∧
    inLieLev k r i (hpart2 (Hpk k r) (Matrix.single (posL k r i a) (posL k r i b) 1)) := by
  have hs := hpart_skew (Hpk k r) (Matrix.single (posL k r i a) (posL k r i b) 1) WeylGroupFacts.hpk_sq hpk_herm
  have hZh : (Matrix.single (posL k r i a) (posL k r i b) (1 : ℂ))ᴴ =
      Matrix.single (posL k r i b) (posL k r i a) 1 := by
    rw [Matrix.conjTranspose_single, star_one]
  have hkill : ∀ c : Fin r, c.val < i.val →
      (Matrix.single (posL k r i a) (posL k r i b) (1 : ℂ)) *ᵥ bvec (eI k r c) = 0 ∧
      (Matrix.single (posL k r i a) (posL k r i b) (1 : ℂ)) *ᵥ bvec (esI k r c) = 0 ∧
      (Hpk k r * (Matrix.single (posL k r i a) (posL k r i b) (1 : ℂ))ᴴ * Hpk k r) *ᵥ bvec (eI k r c) = 0 ∧
      (Hpk k r * (Matrix.single (posL k r i a) (posL k r i b) (1 : ℂ))ᴴ * Hpk k r) *ᵥ bvec (esI k r c) = 0 := by
    intro c hc
    refine ⟨single_bvec (posL_ne_e i b c hc).1, single_bvec (posL_ne_e i b c hc).2, ?_, ?_⟩
    · rw [← Matrix.mulVec_mulVec, hpk_e, ← Matrix.mulVec_mulVec, hZh, single_bvec (posL_ne_e i a c hc).2,
        Matrix.mulVec_zero]
    · rw [← Matrix.mulVec_mulVec, hpk_es, ← Matrix.mulVec_mulVec, hZh, single_bvec (posL_ne_e i a c hc).1,
        Matrix.mulVec_zero]
  refine ⟨⟨hs.1, fun c hc => ?_⟩, ⟨hs.2, fun c hc => ?_⟩⟩
  · obtain ⟨k1, k2, k3, k4⟩ := hkill c hc
    unfold hpart1
    rw [hpk_inv]
    simp only [Matrix.smul_mulVec, Matrix.sub_mulVec, k1, k2, k3, k4, sub_zero, smul_zero, and_self]
  · obtain ⟨k1, k2, k3, k4⟩ := hkill c hc
    unfold hpart2
    rw [hpk_inv]
    simp only [Matrix.smul_mulVec, Matrix.add_mulVec, k1, k2, k3, k4, add_zero, smul_zero, and_self]
theorem sf_mul {a b : Fn k r ℂ} (h : SmoothFam k r i U₀ a) (h' : SmoothFam k r i U₀ b) :
    SmoothFam k r i U₀ (fun c g => a c g * b c g) := sf_smul h h'
theorem sf_sub' {a b : Fn k r ℂ} (h : SmoothFam k r i U₀ a) (h' : SmoothFam k r i U₀ b) :
    SmoothFam k r i U₀ (fun c g => a c g - b c g) := by
  have := sf_add h (sf_smul (sf_const (-1)) h')
  simpa [sub_eq_add_neg] using this
theorem sf_lin (L : Mx k r →ₗ[ℝ] ℂ) {a : Mx k r → ℂ} (h : ∀ g ∈ Glev k r i, a g = L g) :
    SmoothFam k r i U₀ (fun _ g => a g) :=
  fun _ _ _ => ⟨Set.univ, fun x => (LinearMap.toContinuousLinearMap L) x.2, isOpen_univ, trivial,
    ((LinearMap.toContinuousLinearMap L).contDiff.comp contDiff_snd).contDiffOn, fun x _ hx => h x.2 hx⟩
theorem uh_inv_eq {g : Mx k r} (hg : g ∈ UH (Hpk k r)) : g⁻¹ = Hpk k r * gᴴ * Hpk k r := by
  apply Matrix.inv_eq_left_inv
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  calc Hpk k r * gᴴ * Hpk k r * g = Hpk k r * (gᴴ * Hpk k r * g) := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hg', WeylGroupFacts.hpk_sq]
theorem sf_yv (z : Fin (2 * r + k + 1) → ℂ) (j : Fin (mdim k r i)) :
    SmoothFam k r i U₀ (fun _ g => yv k r z i g j) := by
  refine sf_lin
    { toFun := fun g => ((Hpk k r * gᴴ * Hpk k r) *ᵥ fvec k r z i) (posL k r i j)
      map_add' := ?_
      map_smul' := ?_ } ?_
  · intro x y
    simp [Matrix.conjTranspose_add, Matrix.mul_add, Matrix.add_mul, Matrix.add_mulVec]
  · intro c x
    simp [Matrix.conjTranspose_smul, Matrix.smul_mulVec]
  · intro g hg
    show (g⁻¹ *ᵥ fvec k r z i) (posL k r i j) = _
    rw [uh_inv_eq hg.1]
    rfl
theorem sf_ybv (z : Fin (2 * r + k + 1) → ℂ) (j : Fin (mdim k r i)) :
    SmoothFam k r i U₀ (fun _ g => ybv k r z i g j) := by
  refine sf_lin
    { toFun := fun g => herm (Hpk k r) (g *ᵥ bvec (posL k r i j)) (fvec k r z i)
      map_add' := ?_
      map_smul' := ?_ } ?_
  · intro x y
    simp [herm, Matrix.add_mulVec, Matrix.mulVec_add, dotProduct_add]
  · intro c x
    simp [herm, Matrix.smul_mulVec, Matrix.mulVec_smul, dotProduct_smul]
  · intro g _
    rfl
theorem cd_EH (hU₀ : IsOpen U₀) (a b : Fin (mdim k r i)) :
    CD (E := E) i U₀ (EH k r (posL k r i a) (posL k r i b)) :=
  (CD.rdV hU₀ (hpart_lie i a b).1).add ((CD.rdV hU₀ (hpart_lie i a b).2).csmul Complex.I)
theorem cd_Top (hU₀ : IsOpen U₀) (u : ℂ) (a b : Fin (mdim k r i)) :
    CD (E := E) i U₀ (Top (EH k r) u (posL k r i a) (posL k r i b)) := by
  by_cases hab : posL k r i a = posL k r i b
  · have := (CD.id (E := E) (i := i) (U₀ := U₀)).csmul u |>.add (cd_EH hU₀ a b)
    unfold QuantumDeterminants.Top
    simpa only [if_pos hab] using this
  · have := (CD.zero (E := E) (i := i) (U₀ := U₀)).add (cd_EH hU₀ a b)
    unfold QuantumDeterminants.Top
    simpa only [if_neg hab] using this
theorem cd_qminor (hU₀ : IsOpen U₀) {t : ℕ} (a b : Fin t → Fin (mdim k r i)) (u : ℂ) :
    CD (E := E) i U₀ (qminorOp (EH k r) (posL k r i ∘ a) (posL k r i ∘ b) u) := by
  have key : ∀ σ : Equiv.Perm (Fin t), CD (E := E) i U₀ (fun f g =>
      (((Equiv.Perm.sign σ : ℤ) : ℂ) • (List.ofFn fun j : Fin t =>
        Top (E := E) (EH k r) (u - ((j : ℕ) : ℂ)) ((posL k r i ∘ a) (σ j)) ((posL k r i ∘ b) j)).foldr
          (fun T h => T h) f g)) := by
    intro σ
    refine CD.csmul (CD.foldr _ ?_) _
    intro T hT
    obtain ⟨j, rfl⟩ := (List.mem_ofFn' _ _).1 hT
    exact cd_Top hU₀ _ _ _
  have := CD.sum Finset.univ (fun σ _ => key σ)
  convert this using 3
  simp [qminorOp, Finset.sum_apply]
theorem cd_chatL (hU₀ : IsOpen U₀) (u : ℂ) (a β : Mx k r → Fin (mdim k r i) → ℂ)
    (ha : ∀ j, SmoothFam k r i U₀ (fun _ g => a g j)) (hβ : ∀ j, SmoothFam k r i U₀ (fun _ g => β g j)) :
    CD (E := E) i U₀ (chatL (EH k r) (posL k r i) u a β) := by
  unfold chatL
  exact CD.sum _ fun i' _ => CD.sum _ fun j' _ =>
    (cd_qminor hU₀ _ _ _).coef _ (sf_mul (sf_mul (sf_const _) (hβ i')) (ha j'))
theorem cd_chat2L (hU₀ : IsOpen U₀) (u : ℂ) (a a' β β' : Mx k r → Fin (mdim k r i) → ℂ)
    (ha : ∀ j, SmoothFam k r i U₀ (fun _ g => a g j)) (ha' : ∀ j, SmoothFam k r i U₀ (fun _ g => a' g j))
    (hβ : ∀ j, SmoothFam k r i U₀ (fun _ g => β g j)) (hβ' : ∀ j, SmoothFam k r i U₀ (fun _ g => β' g j)) :
    CD (E := E) i U₀ (chat2L (EH k r) (posL k r i) u a a' β β') := by
  unfold chat2L
  refine CD.sum _ fun i₁ _ => CD.sum _ fun i₂ _ => CD.sum _ fun j₁ _ => CD.sum _ fun j₂ _ => ?_
  by_cases hc : i₁ < i₂ ∧ j₁ < j₂
  · simp only [if_pos hc]
    exact (cd_qminor hU₀ _ _ _).coef _
      (sf_mul (sf_mul (sf_const _) (sf_sub' (sf_mul (hβ i₁) (hβ' i₂)) (sf_mul (hβ i₂) (hβ' i₁))))
      (sf_sub' (sf_mul (ha j₁) (ha' j₂)) (sf_mul (ha j₂) (ha' j₁))))
  · simp only [if_neg hc]
    exact CD.zero
theorem cd_tL (hU₀ : IsOpen U₀) (z z' : Fin (2 * r + k + 1) → ℂ) (Y : ℂ) (p q : Fin 2) :
    CD (E := E) i U₀ (tL k r z z' i Y p q) := by
  fin_cases p <;> fin_cases q
  · show CD i U₀ (fun f => capL k r i (uC k r i Y) f)
    exact cd_qminor hU₀ id id _
  · show CD i U₀ (fun f g => -(chatL (EH k r) (posL k r i) (uC k r i Y - 1) (fun _ => xv k r z' i)
      (ybv k r z i) f g))
    exact (cd_chatL hU₀ (uC k r i Y - 1) (fun _ => xv k r z' i) (ybv k r z i)
      (fun j => sf_const _) (fun j => sf_ybv z j)).neg
  · show CD i U₀ (fun f g => -(chatL (EH k r) (posL k r i) (uC k r i Y) (yv k r z i)
      (fun _ => xbv k r z' i) f g))
    exact (cd_chatL hU₀ (uC k r i Y) (yv k r z i) (fun _ => xbv k r z' i)
      (fun j => sf_yv z j) (fun j => sf_const _)).neg
  · show CD i U₀ (fun f g => -(chat2L (EH k r) (posL k r i) (uC k r i Y - 1) (yv k r z i)
      (fun _ => xv k r z' i) (ybv k r z i) (fun _ => xbv k r z' i) f g))
    exact (cd_chat2L hU₀ (uC k r i Y - 1) (yv k r z i) (fun _ => xv k r z' i) (ybv k r z i)
      (fun _ => xbv k r z' i) (fun j => sf_yv z j) (fun j => sf_const _) (fun j => sf_ybv z j)
      (fun j => sf_const _)).neg
end CDentries
section Germ
open Topology
variable {m : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
theorem isOpen_OmX (m : ℕ) : IsOpen (OmX m) := by
  have : OmX m = ⋂ l : Fin m, {x : Fin m → ℂ | x l ≠ 0} := by
    ext x
    simp [OmX]
  rw [this]
  exact isOpen_iInter_of_finite fun l => isOpen_ne_fun (continuous_apply l) continuous_const
theorem opL_germ (l : Fin m) (j : Fin 6) {f g : (Fin m → ℂ) → E} {c : Fin m → ℂ} (h : f =ᶠ[𝓝 c] g) :
    opL l j f =ᶠ[𝓝 c] opL l j g := by
  filter_upwards [h.eventually_nhds] with y hy
  have hy' : f =ᶠ[𝓝 y] g := hy
  have h0 : f y = g y := hy'.eq_of_nhds
  have h1 : fderiv ℝ f y = fderiv ℝ g y := hy'.fderiv_eq
  fin_cases j
  · show pOp l f y = pOp l g y
    simp only [pOp, wirt, h1]
  · show cOp l f y = cOp l g y
    simp only [cOp, h0]
  · show ciOp l f y = ciOp l g y
    simp only [ciOp, h0]
  · show pbOp l f y = pbOp l g y
    simp only [pbOp, wirtBar, h1]
  · show cbOp l f y = cbOp l g y
    simp only [cbOp, h0]
  · show cbiOp l f y = cbiOp l g y
    simp only [cbiOp, h0]
def Sm (f : (Fin m → ℂ) → E) (c : Fin m → ℂ) : Prop := ∃ f' ∈ WSm m E, f' =ᶠ[𝓝 c] f
theorem cutoff {f : (Fin m → ℂ) → E} {c : Fin m → ℂ} (hc : c ∈ OmX m) {V : Set (Fin m → ℂ)} (hV : IsOpen V)
    (hcV : c ∈ V) (hf : ContDiffOn ℝ ∞ f V) : Sm f c := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 (hV.inter (isOpen_OmX m)) c ⟨hcV, hc⟩
  let b : ContDiffBump c := ⟨ε / 4, ε / 2, by positivity, by linarith⟩
  have hzero : ∀ y, y ∉ Metric.ball c ε → b y = 0 := by
    intro y hy
    apply b.zero_of_le_dist
    rw [Metric.mem_ball, not_lt] at hy
    show ε / 2 ≤ dist y c
    linarith
  refine ⟨fun y => b y • f y, ⟨?_, ?_⟩, ?_⟩
  · apply ContDiff.contDiffOn
    rw [contDiff_iff_contDiffAt]
    intro y
    by_cases hy : y ∈ Metric.ball c ε
    · exact b.contDiff.contDiffAt.smul (hf.contDiffAt (hV.mem_nhds (hball hy).1))
    · have hy' : y ∈ (Metric.closedBall c (ε / 2))ᶜ := by
        rw [Metric.mem_ball, not_lt] at hy
        simp only [Set.mem_compl_iff, Metric.mem_closedBall, not_le]
        linarith
      have he : (fun y => b y • f y) =ᶠ[𝓝 y] fun _ => 0 := by
        filter_upwards [Metric.isClosed_closedBall.isOpen_compl.mem_nhds hy'] with w hw
        have : b w = 0 := by
          apply b.zero_of_le_dist
          simp only [Set.mem_compl_iff, Metric.mem_closedBall, not_le] at hw
          exact hw.le
        rw [this, zero_smul]
      exact contDiffAt_const.congr_of_eventuallyEq he
  · intro y hy
    have : y ∉ Metric.ball c ε := fun h => hy (hball h).2
    show b y • f y = 0
    rw [hzero y this, zero_smul]
  · filter_upwards [b.eventuallyEq_one] with y hy
    show b y • f y = f y
    rw [hy]
    simp
theorem Sm.add {f g : (Fin m → ℂ) → E} {c : Fin m → ℂ} (hf : Sm f c) (hg : Sm g c) (l : Fin m) (j : Fin 6) :
    opL l j (f + g) c = opL l j f c + opL l j g c := by
  obtain ⟨f', hf', he⟩ := hf
  obtain ⟨g', hg', he'⟩ := hg
  rw [← (opL_germ l j he).eq_of_nhds, ← (opL_germ l j he').eq_of_nhds,
    ← (opL_germ l j (he.add he')).eq_of_nhds]
  exact congrFun (linOps m E l j f' g' 1 hf' hg').1 c
theorem Sm.smul {f : (Fin m → ℂ) → E} {c : Fin m → ℂ} (hf : Sm f c) (a : ℂ) (l : Fin m) (j : Fin 6) :
    opL l j (a • f) c = a • opL l j f c := by
  obtain ⟨f', hf', he⟩ := hf
  rw [← (opL_germ l j he).eq_of_nhds, ← (opL_germ l j (he.const_smul a)).eq_of_nhds]
  exact congrFun (linOps m E l j f' f' a hf' hf').2 c
end Germ
section FamMod
open Topology
variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp]
  [NormedAddCommGroup Wq] [NormedSpace ℂ Wq] {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}
  {i : Fin (r + 1)} {Dc : (Fin r → ℂ) → Set (Mx k r)}
def UU (Dc : (Fin r → ℂ) → Set (Mx k r)) : Set (XX k r) := {x | x.1 ∈ OmX r ∧ x.2 ∈ Dc x.1}
def levelPointsWithGroupElement (i : Fin (r + 1)) (Dc : (Fin r → ℂ) → Set (Mx k r)) : Set (XX k r) := {x | x ∈ UU Dc ∧ x.2 ∈ Glev k r i}
variable (k r z z' i Dc) in

structure FamCtx : Prop where
  hz : inWb k r z
  hz' : inWb k r z'
  isOpen : IsOpen (UU Dc)
  dom : ∀ c ∈ OmX r, IsDom k r z z' i (Dc c)
theorem FamFF_congr (C : FamCtx k r z z' i Dc) {Φ Ψ : Fn k r (Wq →L[ℂ] Wp)} (h : FamFF k r z z' π π' i Dc Φ)
    (he : ∀ x ∈ levelPointsWithGroupElement i Dc, Ψ x.1 x.2 = Φ x.1 x.2) : FamFF k r z z' π π' i Dc Ψ := by
  refine ⟨?_, fun c hc => FFl_congr (C.dom c hc) (h.2 c hc) fun g hg => he (c, g) ⟨⟨hc, hg.2⟩, hg.1⟩⟩
  intro x₀ hx₀ hg₀
  obtain ⟨U, F, hU, hxU, hF, hΦ⟩ := h.1 x₀ hx₀ hg₀
  exact ⟨U ∩ UU Dc, F, hU.inter C.isOpen, ⟨hxU, hx₀⟩, hF.mono Set.inter_subset_left,
    fun x hx hxG => by rw [he x ⟨hx.2, hxG⟩, hΦ x hx.1 hxG]⟩
theorem FamFF_add {Φ Ψ : Fn k r (Wq →L[ℂ] Wp)} (h : FamFF k r z z' π π' i Dc Φ)
    (h' : FamFF k r z z' π π' i Dc Ψ) : FamFF k r z z' π π' i Dc (Φ + Ψ) :=
  ⟨sf_add h.1 h'.1, fun c hc => FFl_add (h.2 c hc) (h'.2 c hc)⟩
theorem FamFF_smul {Φ : Fn k r (Wq →L[ℂ] Wp)} (h : FamFF k r z z' π π' i Dc Φ) (s : ℂ) :
    FamFF k r z z' π π' i Dc (s • Φ) :=
  ⟨sf_smul (sf_const s) h.1, fun c hc => FFl_smul (h.2 c hc) s⟩
theorem FamFF_zero : FamFF k r z z' π π' i Dc (0 : Fn k r (Wq →L[ℂ] Wp)) :=
  ⟨sf_zero, fun _ _ => FFl_zero⟩
variable (k r z z' π π' i Dc) in

def FamV : Submodule ℂ (Fn k r (Wq →L[ℂ] Wp)) where
  carrier := {Φ | FamFF k r z z' π π' i Dc Φ ∧ ∀ x, x ∉ levelPointsWithGroupElement i Dc → Φ x.1 x.2 = 0}
  zero_mem' := ⟨FamFF_zero, fun _ _ => rfl⟩
  add_mem' := fun h h' => ⟨FamFF_add h.1 h'.1, fun x hx => by simp [h.2 x hx, h'.2 x hx]⟩
  smul_mem' := fun s _ h => ⟨FamFF_smul h.1 s, fun x hx => by simp [h.2 x hx]⟩
theorem FamV_ext {Φ Ψ : FamV k r z z' π π' i Dc}
    (h : ∀ x ∈ levelPointsWithGroupElement i Dc, (Φ : Fn k r (Wq →L[ℂ] Wp)) x.1 x.2 = (Ψ : Fn k r (Wq →L[ℂ] Wp)) x.1 x.2) : Φ = Ψ := by
  apply Subtype.ext
  funext c g
  by_cases hx : (c, g) ∈ levelPointsWithGroupElement i Dc
  · exact h (c, g) hx
  · rw [Φ.2.2 (c, g) hx, Ψ.2.2 (c, g) hx]
open Classical in

def cutF (C : FamCtx k r z z' i Dc) (Φ : Fn k r (Wq →L[ℂ] Wp)) (h : FamFF k r z z' π π' i Dc Φ) :
    FamV k r z z' π π' i Dc :=
  ⟨fun c g => if (c, g) ∈ levelPointsWithGroupElement i Dc then Φ c g else 0,
    FamFF_congr C h (fun _ hx => if_pos hx), fun _ hx => if_neg hx⟩
theorem cutF_apply (C : FamCtx k r z z' i Dc) (Φ : Fn k r (Wq →L[ℂ] Wp)) (h : FamFF k r z z' π π' i Dc Φ)
    {x : XX k r} (hx : x ∈ levelPointsWithGroupElement i Dc) : (cutF C Φ h : Fn k r (Wq →L[ℂ] Wp)) x.1 x.2 = Φ x.1 x.2 := if_pos hx
variable (k r z z' π π' i Dc) in

structure GoodOp (A : Fn k r (Wq →L[ℂ] Wp) → Fn k r (Wq →L[ℂ] Wp)) : Prop where
  fam : ∀ Φ, FamFF k r z z' π π' i Dc Φ → FamFF k r z z' π π' i Dc (A Φ)
  loc : ∀ Φ Ψ, FamFF k r z z' π π' i Dc Φ → FamFF k r z z' π π' i Dc Ψ →
    (∀ x ∈ levelPointsWithGroupElement i Dc, Φ x.1 x.2 = Ψ x.1 x.2) → ∀ x ∈ levelPointsWithGroupElement i Dc, A Φ x.1 x.2 = A Ψ x.1 x.2
  add : ∀ Φ Ψ, FamFF k r z z' π π' i Dc Φ → FamFF k r z z' π π' i Dc Ψ →
    ∀ x ∈ levelPointsWithGroupElement i Dc, A (Φ + Ψ) x.1 x.2 = A Φ x.1 x.2 + A Ψ x.1 x.2
  smul : ∀ (s : ℂ) Φ, FamFF k r z z' π π' i Dc Φ → ∀ x ∈ levelPointsWithGroupElement i Dc, A (s • Φ) x.1 x.2 = s • A Φ x.1 x.2
def GoodOp.toEnd (C : FamCtx k r z z' i Dc) {A : Fn k r (Wq →L[ℂ] Wp) → Fn k r (Wq →L[ℂ] Wp)}
    (h : GoodOp k r z z' π π' i Dc A) : Module.End ℂ (FamV k r z z' π π' i Dc) where
  toFun Ψ := cutF C (A Ψ) (h.fam _ Ψ.2.1)
  map_add' Φ Ψ := by
    apply FamV_ext
    intro x hx
    rw [cutF_apply C _ _ hx, Submodule.coe_add, Submodule.coe_add, Pi.add_apply, Pi.add_apply, cutF_apply C _ _ hx,
      cutF_apply C _ _ hx]
    exact h.add _ _ Φ.2.1 Ψ.2.1 x hx
  map_smul' s Φ := by
    apply FamV_ext
    intro x hx
    rw [cutF_apply C _ _ hx, Submodule.coe_smul, RingHom.id_apply, Submodule.coe_smul, Pi.smul_apply, Pi.smul_apply,
      cutF_apply C _ _ hx]
    exact h.smul s _ Φ.2.1 x hx
variable (k r z z' π π' i Dc) in

def Rep (A : Fn k r (Wq →L[ℂ] Wp) → Fn k r (Wq →L[ℂ] Wp)) (a : Module.End ℂ (FamV k r z z' π π' i Dc)) : Prop :=
  ∀ Φ, FamFF k r z z' π π' i Dc Φ → ∀ Ψ : FamV k r z z' π π' i Dc,
    (∀ x ∈ levelPointsWithGroupElement i Dc, Φ x.1 x.2 = (Ψ : Fn k r (Wq →L[ℂ] Wp)) x.1 x.2) →
    FamFF k r z z' π π' i Dc (A Φ) ∧ ∀ x ∈ levelPointsWithGroupElement i Dc, A Φ x.1 x.2 = (a Ψ : Fn k r (Wq →L[ℂ] Wp)) x.1 x.2
theorem Rep.comp {A B : Fn k r (Wq →L[ℂ] Wp) → Fn k r (Wq →L[ℂ] Wp)}
    {a b : Module.End ℂ (FamV k r z z' π π' i Dc)} (hA : Rep k r z z' π π' i Dc A a)
    (hB : Rep k r z z' π π' i Dc B b) : Rep k r z z' π π' i Dc (fun Φ => A (B Φ)) (a * b) := by
  intro Φ hΦ Ψ he
  obtain ⟨h1, h2⟩ := hB Φ hΦ Ψ he
  exact hA _ h1 (b Ψ) h2
theorem Rep.add {A B : Fn k r (Wq →L[ℂ] Wp) → Fn k r (Wq →L[ℂ] Wp)}
    {a b : Module.End ℂ (FamV k r z z' π π' i Dc)} (hA : Rep k r z z' π π' i Dc A a)
    (hB : Rep k r z z' π π' i Dc B b) : Rep k r z z' π π' i Dc (fun Φ => A Φ + B Φ) (a + b) := by
  intro Φ hΦ Ψ he
  obtain ⟨h1, h2⟩ := hB Φ hΦ Ψ he
  obtain ⟨h3, h4⟩ := hA Φ hΦ Ψ he
  refine ⟨FamFF_add h3 h1, fun x hx => ?_⟩
  rw [LinearMap.add_apply, Submodule.coe_add, Pi.add_apply, Pi.add_apply, ← h2 x hx, ← h4 x hx]
  rfl
theorem Rep.congr {A B : Fn k r (Wq →L[ℂ] Wp) → Fn k r (Wq →L[ℂ] Wp)}
    {a : Module.End ℂ (FamV k r z z' π π' i Dc)} (hA : Rep k r z z' π π' i Dc A a) (h : ∀ Φ, B Φ = A Φ) :
    Rep k r z z' π π' i Dc B a := by
  have : B = A := funext h
  rw [this]; exact hA
theorem level_points_set_eventually_nearby (C : FamCtx k r z z' i Dc) {x : XX k r} (hx : x ∈ levelPointsWithGroupElement i Dc) :
    ∀ᶠ c' in 𝓝 x.1, ((c', x.2) : XX k r) ∈ levelPointsWithGroupElement i Dc := by
  have hc : Continuous fun c' : Fin r → ℂ => ((c', x.2) : XX k r) := by fun_prop
  filter_upwards [hc.continuousAt.preimage_mem_nhds (C.isOpen.mem_nhds hx.1)] with c' hc'
  exact ⟨hc', hx.2⟩
theorem sf_Sm {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {Φ : Fn k r E}
    (h : SmoothFam k r i (UU Dc) Φ) {x : XX k r} (hx : x ∈ levelPointsWithGroupElement i Dc) : Sm (fun c' => Φ c' x.2) x.1 := by
  obtain ⟨U, F, hU, hxU, hF, hΦ⟩ := h x hx.1 hx.2
  have hc : Continuous fun c' : Fin r → ℂ => ((c', x.2) : XX k r) := by fun_prop
  refine cutoff hx.1.1 (hU.preimage hc) hxU ?_
  have h1 : ContDiffOn ℝ ∞ (fun c' : Fin r → ℂ => F (c', x.2)) ((fun c' : Fin r → ℂ => ((c', x.2) : XX k r)) ⁻¹' U) :=
    hF.comp (contDiff_id.prodMk contDiff_const).contDiffOn (fun c' hc' => hc')
  exact h1.congr fun c' hc' => hΦ (c', x.2) hc' hx.2
theorem good_op (C : FamCtx k r z z' i Dc) (hFO : FamOps) (l : Fin r) (j : Fin 6) :
    GoodOp k r z z' π π' i Dc (crd (opL l j)) := by
  refine ⟨fun Φ h => hFO Wp Wq k r z z' π π' i Dc Φ C.hz C.hz' C.isOpen h l j, ?_, ?_, ?_⟩
  · intro Φ Ψ _ _ he x hx
    have hg : (fun c' => Φ c' x.2) =ᶠ[𝓝 x.1] (fun c' => Ψ c' x.2) := by
      filter_upwards [level_points_set_eventually_nearby C hx] with c' hc'
      exact he _ hc'
    exact (opL_germ l j hg).eq_of_nhds
  · intro Φ Ψ hΦ hΨ x hx
    exact (sf_Sm hΦ.1 hx).add (sf_Sm hΨ.1 hx) l j
  · intro s Φ hΦ x hx
    exact (sf_Sm hΦ.1 hx).smul s l j
theorem good_alt_bis (C : FamCtx k r z z' i Dc) (hP : TPreservesFF) (hT : TLinLoc) (Y : ℂ) (a b : Fin 2) :
    GoodOp k r z z' π π' i Dc (grp (tL k r z z' i Y a b)) := by
  refine ⟨fun Φ h => ⟨(cd_tL C.isOpen z z' Y a b).sm Φ h.1,
    fun c hc => hP Wp Wq k r z z' π π' i (Dc c) Y a b C.hz C.hz' (C.dom c hc) _ (h.2 c hc)⟩, ?_, ?_, ?_⟩
  · intro Φ Ψ _ _ he x hx
    exact (cd_tL C.isOpen z z' Y a b).loc Φ Ψ (fun y hy hyG => he y ⟨hy, hyG⟩) x hx.1 hx.2
  · intro Φ Ψ hΦ hΨ x hx
    exact tl_add hT (C.dom _ hx.1.1).1 Y a b (hΦ.2 _ hx.1.1).1 (hΨ.2 _ hx.1.1).1 ⟨hx.2, hx.1.2⟩
  · intro s Φ hΦ x hx
    exact tl_smul hT (C.dom _ hx.1.1).1 Y a b s (hΦ.2 _ hx.1.1).1 ⟨hx.2, hx.1.2⟩
end FamMod
section FamRing
open Topology Formalism.YangianSpanCharacter.T
variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp]
  [NormedAddCommGroup Wq] [NormedSpace ℂ Wq] {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}
  {i : Fin (r + 1)} {Dc : (Fin r → ℂ) → Set (Mx k r)}
def opE (C : FamCtx k r z z' i Dc) (hFO : FamOps) (l : Fin r) (j : Fin 6) :
    Module.End ℂ (FamV k r z z' π π' i Dc) := (good_op C hFO l j).toEnd C
def qE (C : FamCtx k r z z' i Dc) (hP : TPreservesFF) (hT : TLinLoc) (Y : ℂ) (a b : Fin 2) :
    Module.End ℂ (FamV k r z z' π π' i Dc) := (good_alt_bis C hP hT Y a b).toEnd C
end FamRing
section Step
open Topology Formalism.YangianSpanCharacter.T
variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp]
  [NormedAddCommGroup Wq] [NormedSpace ℂ Wq] {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}
def DcOf (l : Fin r) (D : Set (Mx k r)) : (Fin r → ℂ) → Set (Mx k r) := fun c => {g | w1 k r l (c l) * g ∈ D}
variable {i : Fin (r + 1)} {Dc : (Fin r → ℂ) → Set (Mx k r)}
def TrE (C : FamCtx k r z z' i Dc) (hFO : FamOps) (l : Fin r) (Y : ℂ) :
    Matrix (Fin 2) (Fin 2) (Module.End ℂ (FamV k r z z' π π' i Dc)) :=
  YangianSpanCharacter.T.Tm Y (opE C hFO l 0) (opE C hFO l 1) (opE C hFO l 2)
def TsE (C : FamCtx k r z z' i Dc) (hFO : FamOps) (l : Fin r) (Y : ℂ) :
    Matrix (Fin 2) (Fin 2) (Module.End ℂ (FamV k r z z' π π' i Dc)) :=
  YangianSpanCharacter.T.Tm Y (-opE C hFO l 3) (-opE C hFO l 5) (-opE C hFO l 4)
def QmE (C : FamCtx k r z z' i Dc) (hP : TPreservesFF) (hT : TLinLoc) (Y : ℂ) :
    Matrix (Fin 2) (Fin 2) (Module.End ℂ (FamV k r z z' π π' i Dc)) := Matrix.of (qE C hP hT Y)
def ME (C : FamCtx k r z z' i Dc) (hFO : FamOps) (hP : TPreservesFF) (hT : TLinLoc) (l : Fin r) (Y : ℂ) :
    Matrix (Fin 2) (Fin 2) (Module.End ℂ (FamV k r z z' π π' i Dc)) :=
  TsE C hFO l Y * (QmE C hP hT Y * TrE C hFO l Y)
end Step
section Final
open Topology Formalism.YangianSpanCharacter.T
variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp]
  [NormedAddCommGroup Wq] [NormedSpace ℂ Wq] {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}
def DetOn (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (π' : Mx k r → (Wq →L[ℂ] Wq))
    (i : Fin (r + 1)) (q : ℂ → ℂ) : Prop :=
  ∀ D, IsDom k r z z' i D → ∀ J ∈ FFl k r z z' π π' i D, ∀ g ∈ Glev k r i ∩ D, ∀ (Y : ℂ) (c d : Fin 2),
      (tL k r z z' i (Y + 1) 0 c (tL k r z z' i Y 1 d J) g -
          tL k r z z' i (Y + 1) 1 c (tL k r z z' i Y 0 d J) g = (q Y * epsJ c d) • J g) ∧
      (tL k r z z' i Y c 0 (tL k r z z' i (Y + 1) d 1 J) g -
          tL k r z z' i Y c 1 (tL k r z z' i (Y + 1) d 0 J) g = (q Y * epsJ c d) • J g)
end Final
end Formalism.FourierDecayAlt.P.Qx8
namespace Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.Qx8
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
end Formalism.FourierDecayAlt.P
namespace Formalism.FourierDecayAlt.P.Qx8
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
section OneParam
open Topology intervalIntegral
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W] [CompleteSpace W]
end OneParam
section RepDer
open Topology
def IsLin {W : Type*} [AddCommGroup W] [Module ℂ W] (T : W → W) : Prop :=
  ∀ (a b : W) (c : ℂ), T (a + c • b) = T a + c • T b
namespace IsLin
variable {W : Type*} [AddCommGroup W] [Module ℂ W]
theorem id : IsLin (fun x : W => x) := fun _ _ _ => rfl
theorem comp {T S : W → W} (hT : IsLin T) (hS : IsLin S) : IsLin (fun x => T (S x)) := fun a b c => by
  show T (S (a + c • b)) = _
  rw [hS, hT]
theorem foldr (L : List (W → W)) (hL : ∀ T ∈ L, IsLin T) : IsLin (fun x => L.foldr (fun T h => T h) x) := by
  induction L with
  | nil => exact IsLin.id
  | cons T L ih => exact (hL T List.mem_cons_self).comp (ih fun T' hT' => hL T' (List.mem_cons_of_mem _ hT'))
end IsLin
variable {k r : ℕ} {Wp : Type*} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [FiniteDimensional ℂ Wp]
def InU (U : Set (Mx k r)) (X : Mx k r) : Prop := ∀ t : ℝ, NormedSpace.exp ((t : ℂ) • X) ∈ U
end RepDer
section UnitB
variable {k r : ℕ}
end UnitB
section Geom2
variable {k r : ℕ}
end Geom2
section Params
open Formalism.FourierDecayAlt.M
def P1 (P : M.Par) : M.Par := ⟨P.k, P.r, P.T, P.T', P.u', P.u'⟩
def P2 (P : M.Par) : M.Par := ⟨P.k, P.r, P.T, P.T', P.u, P.u⟩
variable {P : M.Par}
end Params
section Spectral
open Formalism.FourierDecayAlt.M
def piL {W ι : Type*} [AddCommGroup W] [Module ℂ W] (L : ι → W → W) (c : ι → ℂ) (l : List ι) (x : W) : W :=
  l.foldr (fun τ acc => L τ acc - c τ • acc) x
end Spectral
section Core
open Formalism.FourierDecayAlt.M
variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp]
  [NormedAddCommGroup Wq] [NormedSpace ℂ Wq] {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}
end Core
section Core2
open Formalism.FourierDecayAlt.M
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]
end Core2
end Formalism.FourierDecayAlt.P.Qx8
namespace Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.Qx8
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
end Formalism.FourierDecayAlt.P


