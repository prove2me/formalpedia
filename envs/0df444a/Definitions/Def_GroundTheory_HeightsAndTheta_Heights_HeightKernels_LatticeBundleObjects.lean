-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_LatticeBundleObjects
-- name    : GroundTheory_HeightsAndTheta_Heights_HeightKernels_LatticeBundleObjects
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T10:20:54.062371+00:00
-- url     : https://prove2.me/theorems/11ddc2a7-17fb-5066-8fdf-ad0c4dc9c062
-- title:
--   Lattice Bundle Objects
-- statement:
--   Definitions and structural lemmas for Lattice Bundle Objects, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/HeightKernels/LatticeBundleObjects.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KernelsLattice
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StandardInnerSingleNe
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ImportsRest
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithDegreeIdeal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_AssemblyLines
import Definitions.Def_GroundTheory_PowerSubgroups_CountableNeighbourhoods_CommonDenominator
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_S6_LatticeAsBundle_hypotheses_inhabited_2b13e1235568
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_S6_hypotheses_inhabited_687dc14d1232
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_KLinesIdealLatticeFG_fg_3ea39c9fb6fe
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LinesCoordDet_full_c35610a5b491
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LinesCoordImage_full_39a2e8bb2bcf
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LinesDiagGram_full_8ff11ddb230b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LinesExtendBasis_full_63f55d25134d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LinesFischer_full_deb5581a4d66
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LinesGenIndexDet_full_b60a8a3c7864
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LinesGenIndexMono_full_6f6f30f807ce
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LinesGenIndexPi_full_33ed3f72d0c2
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LinesGenIndexTrans_full_3ca845fd298c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LinesGramChange_full_dcb0a61411bd
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LinesGramDetChange_full_12fe0540b59d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LinesGramFischerBound_full_1469f2c017cd
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LinesGramPosDef_full_e43342dbfc82
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LinesIdealIndexPos_full_4f9c5f06aec4
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LinesIdealLatticeFG_full_1aee04d7db78
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LinesIdealStdIndex_full_42daaad5b08f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LinesIsLattice_full_bf47e659fe20
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LinesLatticeBasis_full_7e8167254293
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LinesLineDegree_full_c44e0f792b53
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LinesProductFormula_full_ff39a65d05f0
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LinesProjIndexLower_full_1df55b623de3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LinesProjLattice_full_509886f65659
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LinesQuotDegreeBound_full_f1f9aab9b801
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LinesQuotGramLog_full_1c29f5d3742d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LinesQuotIndexLog_full_349909a2722b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LinesQuotIndexSplit_full_f051c7119c9e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LinesQuotIndex_full_e73217d08651
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LinesStdIndexDet_full_f76414530167
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LinesStdPi_full_9d1e83483f6d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_OrthogonalLines_full_ff0437c876fb
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_fibreMap_tmul_6f6be11e0e36
import Theorems.Thm_P2M_GroundTheory_Variant__N1_exists_common_denominator_214cd264a479

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels
open NumberField NumberField.ComplexEmbedding TensorProduct Matrix GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.ComplexAt
open scoped nonZeroDivisors ComplexOrder
noncomputable section
variable {K : Type} [Field K] [NumberField K]
theorem exists_common_denominator {N : ℕ} {M : Submodule (𝓞 K) (Fin N → K)} (hM : M.FG) :
    ∃ c : 𝓞 K, c ≠ 0 ∧ ∀ v ∈ M, ∀ i, ∃ w : 𝓞 K,
      algebraMap (𝓞 K) K w = algebraMap (𝓞 K) K c * v i :=
  _root_.GroundTheory.Variant₂.N1.exists_common_denominator hM
def intIncl (K : Type) [Field K] (N : ℕ) : (Fin N → 𝓞 K) →ₗ[𝓞 K] (Fin N → K) :=
  LinearMap.compLeft (Algebra.linearMap (𝓞 K) K) (Fin N)
omit [NumberField K] in
theorem intIncl_apply {N : ℕ} (v : Fin N → 𝓞 K) (i : Fin N) : intIncl K N v i = (v i : K) := rfl
omit [NumberField K] in
theorem intIncl_injective (N : ℕ) : Function.Injective (intIncl K N) := fun _ _ h =>
  funext fun i => RingOfIntegers.coe_injective (congrFun h i)
def denom {N : ℕ} (M : Submodule (𝓞 K) (Fin N → K)) [Module.Finite (𝓞 K) M] : 𝓞 K :=
  (exists_common_denominator (Module.Finite.iff_fg.mp ‹_›)).choose
theorem denom_ne_zero {N : ℕ} (M : Submodule (𝓞 K) (Fin N → K)) [Module.Finite (𝓞 K) M] :
    denom M ≠ 0 :=
  (exists_common_denominator (Module.Finite.iff_fg.mp ‹_›)).choose_spec.1
theorem denom_mul_mem {N : ℕ} (M : Submodule (𝓞 K) (Fin N → K)) [Module.Finite (𝓞 K) M]
    (v : M) : denom M • (v : Fin N → K) ∈ LinearMap.range (intIncl K N) := by
  obtain ⟨-, h⟩ := (exists_common_denominator (Module.Finite.iff_fg.mp ‹_›)).choose_spec
  choose w hw using h v v.2
  exact ⟨w, funext fun i => by rw [intIncl_apply, Pi.smul_apply, Algebra.smul_def]; exact hw i⟩
def scaleMap {N : ℕ} (M : Submodule (𝓞 K) (Fin N → K)) [Module.Finite (𝓞 K) M] :
    M →ₗ[𝓞 K] (Fin N → 𝓞 K) :=
  (LinearEquiv.ofInjective (intIncl K N) (intIncl_injective N)).symm.toLinearMap ∘ₗ
    (denom M • M.subtype).codRestrict (LinearMap.range (intIncl K N)) (denom_mul_mem M)
theorem intIncl_scaleMap {N : ℕ} (M : Submodule (𝓞 K) (Fin N → K)) [Module.Finite (𝓞 K) M]
    (v : M) : intIncl K N (scaleMap M v) = denom M • (v : Fin N → K) := by
  simp only [scaleMap, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe]
  rw [LinearEquiv.ofInjective_symm_apply]
  rfl
theorem scaleMap_apply {N : ℕ} (M : Submodule (𝓞 K) (Fin N → K)) [Module.Finite (𝓞 K) M]
    (v : M) (i : Fin N) : (scaleMap M v i : K) = (denom M : K) * (v : Fin N → K) i := by
  have := congrFun (intIncl_scaleMap M v) i
  rw [intIncl_apply] at this
  rw [this, Pi.smul_apply, Algebra.smul_def]
instance projective_of_finite {N : ℕ} (M : Submodule (𝓞 K) (Fin N → K)) [Module.Finite (𝓞 K) M] :
    Module.Projective (𝓞 K) M :=
  projective_of_isTorsionFree M
def latticeCoord (σ : K →+* ℂ) {N : ℕ} (M : Submodule (𝓞 K) (Fin N → K)) [Module.Finite (𝓞 K) M] :
    Fibre σ M →ₗ[ℂ] (Fin N → ℂ) :=
  (σ (denom M : K))⁻¹ • ((WithLp.linearEquiv 2 ℂ (Fin N → ℂ)).toLinearMap ∘ₗ
    (standardCoord K σ (Fin N)).toLinearMap ∘ₗ fibreMap σ (scaleMap M))
theorem latticeCoord_tmul (σ : K →+* ℂ) {N : ℕ} (M : Submodule (𝓞 K) (Fin N → K))
    [Module.Finite (𝓞 K) M] (z : ComplexAt σ) (v : M) (i : Fin N) :
    latticeCoord σ M (z ⊗ₜ v) i = σ ((v : Fin N → K) i) * (ofComplex σ).symm z := by
  have hc : σ (denom M : K) ≠ 0 := by
    rw [map_ne_zero]
    exact_mod_cast denom_ne_zero M
  simp only [latticeCoord, LinearMap.smul_apply, LinearMap.coe_comp, Function.comp_apply,
    fibreMap_tmul, LinearEquiv.coe_coe, Pi.smul_apply, smul_eq_mul]
  change (σ (denom M : K))⁻¹ * standardCoord K σ (Fin N) (z ⊗ₜ scaleMap M v) i = _
  rw [standardCoord_tmul, scaleMap_apply, map_mul]
  field_simp
theorem latticeCoord_injective (σ : K →+* ℂ) {N : ℕ} (M : Submodule (𝓞 K) (Fin N → K))
    [Module.Finite (𝓞 K) M] : Function.Injective (latticeCoord σ M) := by
  have hc : σ (denom M : K) ≠ 0 := by
    rw [map_ne_zero]
    exact_mod_cast denom_ne_zero M
  have hs : Function.Injective (scaleMap M) := by
    intro v w h
    have := congrArg (intIncl K N) h
    rw [intIncl_scaleMap, intIncl_scaleMap] at this
    exact Subtype.ext (smul_right_injective (Fin N → K) (denom_ne_zero M) this)
  intro x y h
  simp only [latticeCoord, LinearMap.smul_apply] at h
  have h' := smul_right_injective _ (inv_ne_zero hc) h
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
    EmbeddingLike.apply_eq_iff_eq] at h'
  exact fibreMap_injective σ hs h'
theorem latticeCoord_conjMap (σ : K →+* ℂ) {N : ℕ} (M : Submodule (𝓞 K) (Fin N → K))
    [Module.Finite (𝓞 K) M] (x : Fibre σ M) :
    latticeCoord (conjugate σ) M (conjMap σ M x) = star (latticeCoord σ M x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul z v =>
    funext i
    rw [conjMap_tmul, latticeCoord_tmul, Pi.star_apply, latticeCoord_tmul, conjugate_coe_eq]
    change _ * starRingEnd ℂ ((ofComplex σ).symm z) = _
    simp
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, star_add]
@[instance_reducible]
def matrixCore {V : Type*} [AddCommGroup V] [Module ℂ V] {ι : Type*} [Fintype ι]
    (Ψ : V →ₗ[ℂ] (ι → ℂ)) (hΨ : Function.Injective Ψ) (H : Matrix ι ι ℂ) (hH : H.PosDef) :
    InnerProductSpace.Core ℂ V where
  inner x y := star (Ψ x) ⬝ᵥ (H *ᵥ Ψ y)
  conj_inner_symm x y := by
    have hh := hH.1
    simp only [dotProduct, mulVec, Pi.star_apply, map_sum, map_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    have hij : starRingEnd ℂ (H j i) = H i j := by
      simpa using congrFun (congrFun hh i) j
    simp only [RCLike.star_def, Complex.conj_conj, hij]
    ring
  re_inner_nonneg x := by
    have := hH.posSemidef.dotProduct_mulVec_nonneg (Ψ x)
    exact (Complex.nonneg_iff.mp this).1
  add_left x y z := by simp only [map_add, star_add, add_dotProduct]
  smul_left x y r := by simp only [map_smul, star_smul, smul_dotProduct, smul_eq_mul, RCLike.star_def]
  definite x h := by
    by_contra hx
    have hx' : Ψ x ≠ 0 := fun h0 => hx (hΨ (h0.trans (map_zero Ψ).symm))
    exact (hH.dotProduct_mulVec_pos hx').ne' h
theorem matrixCore_inner {V : Type*} [AddCommGroup V] [Module ℂ V] {ι : Type*} [Fintype ι]
    (Ψ : V →ₗ[ℂ] (ι → ℂ)) (hΨ : Function.Injective Ψ) (H : Matrix ι ι ℂ) (hH : H.PosDef)
    (x y : V) : (matrixCore Ψ hΨ H hH).inner x y = star (Ψ x) ⬝ᵥ (H *ᵥ Ψ y) := rfl
def matrixMetric {N : ℕ} (M : Submodule (𝓞 K) (Fin N → K)) [Module.Finite (𝓞 K) M]
    (H : (K →+* ℂ) → Matrix (Fin N) (Fin N) ℂ) (hH : ∀ σ, (H σ).PosDef)
    (hconj : ∀ σ, H (conjugate σ) = (H σ).map (starRingEnd ℂ)) : HermitianMetric K M where
  form σ := matrixCore (latticeCoord σ M) (latticeCoord_injective σ M) (H σ) (hH σ)
  form_conj σ x y := by
    rw [matrixCore_inner, matrixCore_inner, latticeCoord_conjMap, latticeCoord_conjMap, hconj]
    simp only [dotProduct, mulVec, Pi.star_apply, map_sum, map_mul, Matrix.map_apply,
      RCLike.star_def, Complex.conj_conj]
def matrixBundle {N : ℕ} (M : Submodule (𝓞 K) (Fin N → K)) [Module.Finite (𝓞 K) M]
    (H : (K →+* ℂ) → Matrix (Fin N) (Fin N) ℂ) (hH : ∀ σ, (H σ).PosDef)
    (hconj : ∀ σ, H (conjugate σ) = (H σ).map (starRingEnd ℂ)) : HermitianBundle.{0} K :=
  ⟨M, matrixMetric M H hH hconj⟩
instance idealLattice_finite {n : ℕ} (a : Fin n → FractionalIdeal (𝓞 K)⁰ K) :
    Module.Finite (𝓞 K) (idealLattice a) :=
  Module.Finite.iff_fg.mpr (KLinesIdealLatticeFG.fg K a)
omit [NumberField K] in
theorem diagMetric_posDef {n : ℕ} {d : (K →+* ℂ) → Fin n → ℝ} (hd : ∀ σ x, 0 < d σ x)
    (σ : K →+* ℂ) : (diagMetric d σ).PosDef :=
  Matrix.PosDef.diagonal fun x => Complex.zero_lt_real.mpr (hd σ x)
omit [NumberField K] in
theorem diagMetric_conj {n : ℕ} {d : (K →+* ℂ) → Fin n → ℝ}
    (hc : ∀ σ x, d (conjugate σ) x = d σ x) (σ : K →+* ℂ) :
    diagMetric d (conjugate σ) = (diagMetric d σ).map (starRingEnd ℂ) := by
  simp only [diagMetric, Matrix.diagonal_map (map_zero _), Complex.conj_ofReal, hc]
def latticeBundle {n : ℕ} (a : Fin n → FractionalIdeal (𝓞 K)⁰ K) (d : (K →+* ℂ) → Fin n → ℝ)
    (hd : ∀ σ x, 0 < d σ x) (hc : ∀ σ x, d (conjugate σ) x = d σ x) : HermitianBundle.{0} K :=
  matrixBundle (idealLattice a) (diagMetric d) (diagMetric_posDef hd) (diagMetric_conj hc)
def satSub {N : ℕ} {ι : Type*} (M : Submodule (𝓞 K) (Fin N → K)) (u : ι → Fin N → K) :
    Submodule (𝓞 K) M :=
  ((Submodule.span K (Set.range u)).restrictScalars (𝓞 K)).comap M.subtype
def coordLine {n : ℕ} (a : Fin n → FractionalIdeal (𝓞 K)⁰ K) (x : Fin n) :
    Submodule (𝓞 K) (idealLattice a) :=
  satSub (idealLattice a) (fun _ : Fin 1 => (Pi.single x 1 : Fin n → K))
def sumBasis {n m k : ℕ} (b : Fin m → Fin n → K) (c : Fin k → Fin n → K)
    (hli : LinearIndependent K (Sum.elim b c)) (hmk : m + k = n) :
    Module.Basis (Fin m ⊕ Fin k) K (Fin n → K) :=
  Module.Basis.mk hli (by
    rw [hli.span_eq_top_of_card_eq_finrank' (by simp [hmk])])
def subLattice {n m : ℕ} (a : Fin n → FractionalIdeal (𝓞 K)⁰ K) (b : Fin m → Fin n → K) :
    Submodule (𝓞 K) (idealLattice a) :=
  satSub (idealLattice a) b
def subBundle {n m : ℕ} (a : Fin n → FractionalIdeal (𝓞 K)⁰ K) (d : (K →+* ℂ) → Fin n → ℝ)
    (hd : ∀ σ x, 0 < d σ x) (hc : ∀ σ x, d (conjugate σ) x = d σ x) (b : Fin m → Fin n → K) :
    HermitianBundle.{0} K :=
  ⟨subLattice a b, (latticeBundle a d hd hc).metric.comap (subLattice a b).subtype
    (subLattice a b).injective_subtype⟩
def quotLattice {n m k : ℕ} (a : Fin n → FractionalIdeal (𝓞 K)⁰ K) (b : Fin m → Fin n → K)
    (c : Fin k → Fin n → K) (hli : LinearIndependent K (Sum.elim b c)) (hmk : m + k = n) :
    Submodule (𝓞 K) (Fin k → K) :=
  (idealLattice a).map ((coordProj (sumBasis b c hli hmk)).restrictScalars (𝓞 K))
instance quotLattice_finite {n m k : ℕ} (a : Fin n → FractionalIdeal (𝓞 K)⁰ K)
    (b : Fin m → Fin n → K) (c : Fin k → Fin n → K) (hli : LinearIndependent K (Sum.elim b c))
    (hmk : m + k = n) : Module.Finite (𝓞 K) (quotLattice a b c hli hmk) :=
  Module.Finite.iff_fg.mpr ((KLinesIdealLatticeFG.fg K a).map _)
def quotProj {n m k : ℕ} (a : Fin n → FractionalIdeal (𝓞 K)⁰ K) (b : Fin m → Fin n → K)
    (c : Fin k → Fin n → K) (hli : LinearIndependent K (Sum.elim b c)) (hmk : m + k = n) :
    idealLattice a →ₗ[𝓞 K] quotLattice a b c hli hmk :=
  ((coordProj (sumBasis b c hli hmk)).restrictScalars (𝓞 K)).submoduleMap (idealLattice a)
def schurMetric {n m k : ℕ} (d : (K →+* ℂ) → Fin n → ℝ) (b : Fin m → Fin n → K)
    (c : Fin k → Fin n → K) (σ : K →+* ℂ) : Matrix (Fin k) (Fin k) ℂ :=
  let G := gramAt (diagMetric d σ) σ (Sum.elim b c)
  G.toBlocks₂₂ - G.toBlocks₂₁ * G.toBlocks₁₁⁻¹ * G.toBlocks₁₂
theorem posDef_schur {m k : Type*} [Fintype m] [Fintype k] [DecidableEq m] [DecidableEq k]
    {G : Matrix (m ⊕ k) (m ⊕ k) ℂ} (hG : G.PosDef) :
    (G.toBlocks₂₂ - G.toBlocks₂₁ * G.toBlocks₁₁⁻¹ * G.toBlocks₁₂).PosDef := by
  have hA : G.toBlocks₁₁.PosDef := hG.submatrix Sum.inl_injective
  have hBC : G.toBlocks₂₁ = G.toBlocks₁₂ᴴ := by
    ext i j
    simpa [toBlocks₂₁, toBlocks₁₂] using (congrFun (congrFun hG.1 (Sum.inr i)) (Sum.inl j)).symm
  have : Invertible G.toBlocks₁₁ := hA.isUnit.invertible
  have hG' : G = fromBlocks G.toBlocks₁₁ G.toBlocks₁₂ G.toBlocks₁₂ᴴ G.toBlocks₂₂ := by
    rw [← hBC, fromBlocks_toBlocks]
  rw [hBC]
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ fun y hy => ?_
  · exact (IsHermitian.fromBlocks₁₁ (A := G.toBlocks₁₁) G.toBlocks₁₂ G.toBlocks₂₂ hA.1).mp
      (hG' ▸ hG.1)
  · set A := G.toBlocks₁₁
    set B := G.toBlocks₁₂
    set x : m → ℂ := -((A⁻¹ * B) *ᵥ y)
    have hxy : (x ⊕ᵥ y) ≠ 0 := by
      intro h
      apply hy
      funext j
      simpa using congrFun h (Sum.inr j)
    have hpos := hG.dotProduct_mulVec_pos hxy
    rw [dotProduct_mulVec, hG', schur_complement_eq₁₁ B G.toBlocks₂₂ x y hA.1] at hpos
    simpa [x, ← dotProduct_mulVec] using hpos
omit [NumberField K] in
theorem gramAt_diagMetric_conj {n : ℕ} {d : (K →+* ℂ) → Fin n → ℝ}
    (hc : ∀ σ x, d (conjugate σ) x = d σ x) (σ : K →+* ℂ) {ι : Type*} (u : ι → Fin n → K) :
    gramAt (diagMetric d (conjugate σ)) (conjugate σ) u =
      (gramAt (diagMetric d σ) σ u).map (starRingEnd ℂ) := by
  ext i j
  simp [gramAt, embVec, diagMetric, dotProduct, mulVec_diagonal, conjugate_coe_eq, hc, map_sum]
omit [NumberField K] in
theorem schurMetric_posDef {n m k : ℕ} {d : (K →+* ℂ) → Fin n → ℝ} (hd : ∀ σ x, 0 < d σ x)
    {b : Fin m → Fin n → K} {c : Fin k → Fin n → K} (hli : LinearIndependent K (Sum.elim b c))
    (σ : K →+* ℂ) : (schurMetric d b c σ).PosDef :=
  posDef_schur (LinesGramPosDef.full K n _ σ _ _ (diagMetric_posDef hd σ) hli)
omit [NumberField K] in
theorem schurMetric_conj {n m k : ℕ} {d : (K →+* ℂ) → Fin n → ℝ}
    (hc : ∀ σ x, d (conjugate σ) x = d σ x) (b : Fin m → Fin n → K) (c : Fin k → Fin n → K)
    (σ : K →+* ℂ) :
    schurMetric d b c (conjugate σ) = (schurMetric d b c σ).map (starRingEnd ℂ) := by
  have hmap : ∀ {p q : Type} [Fintype p] [Fintype q] (X : Matrix p q ℂ),
      X.map (starRingEnd ℂ) = Xᴴᵀ := fun X => by ext; simp
  have hinv : ∀ {p : Type} [Fintype p] [DecidableEq p] (X : Matrix p p ℂ),
      (X.map (starRingEnd ℂ))⁻¹ = X⁻¹.map (starRingEnd ℂ) := fun X => by
    rw [hmap, hmap, ← transpose_nonsing_inv, ← conjTranspose_nonsing_inv]
  simp only [schurMetric, gramAt_diagMetric_conj hc σ]
  set G := gramAt (diagMetric d σ) σ (Sum.elim b c)
  change G.toBlocks₂₂.map (starRingEnd ℂ) - G.toBlocks₂₁.map (starRingEnd ℂ) *
      (G.toBlocks₁₁.map (starRingEnd ℂ))⁻¹ * G.toBlocks₁₂.map (starRingEnd ℂ) = _
  rw [hinv, ← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_sub _ (map_sub _)]
def quotBundle {n m k : ℕ} (a : Fin n → FractionalIdeal (𝓞 K)⁰ K) (d : (K →+* ℂ) → Fin n → ℝ)
    (hd : ∀ σ x, 0 < d σ x) (hc : ∀ σ x, d (conjugate σ) x = d σ x) (b : Fin m → Fin n → K)
    (c : Fin k → Fin n → K) (hli : LinearIndependent K (Sum.elim b c)) (hmk : m + k = n) :
    HermitianBundle.{0} K :=
  matrixBundle (quotLattice a b c hli hmk) (schurMetric d b c) (schurMetric_posDef hd hli)
    (schurMetric_conj hc b c)
example : HermitianBundle.{0} ℚ :=
  quotBundle (fun _ : Fin 2 => (1 : FractionalIdeal (𝓞 ℚ)⁰ ℚ)) (fun _ _ => 1) (fun _ _ => one_pos)
    (fun _ _ => rfl) (fun _ : Fin 1 => (Pi.single 0 1 : Fin 2 → ℚ))
    (fun _ : Fin 1 => (Pi.single 1 1 : Fin 2 → ℚ)) S6.LatticeAsBundle.hypotheses_inhabited.2.2.2.1 rfl
end
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels


