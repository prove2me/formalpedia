-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefExample
-- name    : Formalism_LocalToGlobal_IndefiniteForms_IndefExample
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-24T11:01:28.12388+00:00
-- url     : https://prove2.me/theorems/00f5a37b-48f2-488c-b206-da371905cf62
-- title:
--   Indef Example
-- statement:
--   Definitions and structural lemmas for Indef Example, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteForms/IndefExample.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefSide
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ConjugateWeightLatticeOfGeneral
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_KappaNormalise
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_RamBasic
import Theorems.Thm_Formalism_DivisionValues_LocalCovolumeBasis_key
import Theorems.Thm_Formalism_DivisionValues_ReductionFirst_vw_one
import Theorems.Thm_Formalism_DivisionValues_ValuationRepresentative_conjPl_conjPl
import Theorems.Thm_Formalism_DivisionValues_ValuationRepresentative_vw_one
import Theorems.Thm_Formalism_DivisionValues_conjugate_weight_gram_general
import Theorems.Thm_Formalism_EigenvalueLevelCeiling_one_le_ramw

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder InnerProductSpace
noncomputable section
namespace Formalism.L2.Indef.Examples₂
open Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
section Std
variable (K : Type) [Field K] [NumberField K] [StarRing K]
def sb (D : ℕ) : Fin D → Fin D → K := fun i => Pi.single i 1
def sl (D : ℕ) : Submodule (𝓞 K) (Fin D → K) := Submodule.span (𝓞 K) (Set.range (sb K D))
def fr (D : ℕ) : InfinitePlace K → Matrix (Fin D) (Fin D) ℂ := fun _ => 1
theorem sl_lattice (D : ℕ) : Submodule.IsLattice K (sl K D) := by
  refine ⟨Submodule.fg_span (Set.finite_range _), ?_⟩
  unfold sl
  rw [Submodule.span_span_of_tower]
  have h : sb K D = ⇑(Pi.basisFun K (Fin D)) := by
    ext i j
    simp [sb, Pi.basisFun_apply]
  rw [h]
  exact (Pi.basisFun K (Fin D)).span_eq
theorem std_ratHerm (K0 : Subfield K) (n : ℕ) :
    IsRatHerm K0 (1 : Matrix (Fin n) (Fin n) K) (fr K n) := by
  refine ⟨fun i j => ?_, fun v => ⟨by simp [fr], ?_⟩⟩
  · rw [Matrix.one_apply]
    split_ifs
    · exact K0.one_mem
    · exact K0.zero_mem
  · simp [fr]
theorem locB (D : ℕ) (w : HeightOneSpectrum (𝓞 K)) : IsLocBasis (sl K D) w (sb K D) := by
  refine ⟨?_, rfl⟩
  have h : sb K D = ⇑(Pi.basisFun K (Fin D)) := by
    ext i j
    simp [sb, Pi.basisFun_apply]
  rw [h]
  exact (Pi.basisFun K (Fin D)).linearIndependent
theorem matLat_one (D : ℕ) (L : Submodule (𝓞 K) (Fin D → K)) :
    matLat (1 : Matrix (Fin D) (Fin D) K) L = L := by
  ext x
  simp [matLat]
theorem idx_std (D : ℕ) (w : HeightOneSpectrum (𝓞 K)) : idx w (sl K D) (sl K D) = 0 := by
  unfold idx Formalism.HermitianLatticesTheory.lidx
  simp
theorem gramR_one (D : ℕ) : gramR (1 : Matrix (Fin D) (Fin D) K) (sb K D) = 1 := by
  unfold gramR
  have h : (Matrix.of fun a b : Fin D =>
      star (sb K D a) ⬝ᵥ (1 : Matrix (Fin D) (Fin D) K).mulVec (sb K D b)) = 1 := by
    ext a b
    simp only [Matrix.of_apply, Matrix.one_mulVec, sb, dotProduct_single, mul_one, Pi.star_apply,
      Matrix.one_apply]
    by_cases hab : a = b
    · subst hab
      simp
    · simp [hab, Pi.single_apply, Ne.symm hab]
  rw [h, Matrix.det_one]
theorem jw_std (D : ℕ) (w : HeightOneSpectrum (𝓞 K)) :
    jw (1 : Matrix (Fin D) (Fin D) K) w (sl K D) = 0 := by
  have h := conjugate_weight_gram_general K D (1 : Matrix (Fin D) (Fin D) K) (fun i j => by
      by_cases hij : i = j
      · subst hij
        simp
      · simp [Matrix.one_apply, hij, Ne.symm hij]) (by simp) (sl K D) (sl_lattice K D) w (sb K D)
    (locB K D w)
  rw [h, gramR_one, ValuationRepresentative.vw_one, neg_zero]
def conjLinearRankOne (r : ℝ) : (Fin 1 → ℂ) →ₗ⋆[ℂ] ℂ where
  toFun y := (r : ℂ) * star (y 0)
  map_add' x y := by simp [mul_add]
  map_smul' c y := by simp; ring
theorem fnorm_rank_one (Y : Matrix (Fin 1) (Fin 1) ℂ) (r : ℝ) (hr : 0 ≤ r) (hY : Y⁻¹ = (r : ℂ) • 1) (y : Fin 1 → ℂ) :
    fnorm Y y = r * ‖y 0‖ := by
  unfold fnorm Formalism.HermitianLatticesTheory.cnorm
  rw [hY]
  have h1 : ((r : ℂ) • (1 : Matrix (Fin 1) (Fin 1) ℂ)).mulVec y = (r : ℂ) • y := by
    ext i
    fin_cases i
    simp [Matrix.mulVec, dotProduct, Matrix.one_apply]
  rw [h1, Fin.sum_univ_one, Pi.smul_apply, smul_eq_mul, norm_mul, Real.sqrt_sq (by positivity),
    Complex.norm_real, Real.norm_of_nonneg hr]
theorem conj_linear_rank_one_norm (Y : Matrix (Fin 1) (Fin 1) ℂ) (r : ℝ) (hr : 0 ≤ r) (hY : Y⁻¹ = (r : ℂ) • 1) (y : Fin 1 → ℂ) :
    ‖conjLinearRankOne r y‖ = fnorm Y y := by
  rw [fnorm_rank_one Y r hr hY y]
  show ‖(r : ℂ) * star (y 0)‖ = r * ‖y 0‖
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hr, norm_star]
theorem pairC_std (v : InfinitePlace K) (r : ℝ) (hr : 0 < r) (x y : Fin 1 → ℂ) :
    pairC v (Pi.basisFun K (Fin 1)).toDual x y = ((r : ℂ))⁻¹ * ⟪conjLinearRankOne r y, x 0⟫_ℂ := by
  have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have h1 : (Pi.basisFun K (Fin 1)).toDual (Pi.single 0 1) (Pi.single 0 1) = 1 := by
    simpa [Pi.basisFun_apply] using (Pi.basisFun K (Fin 1)).toDual_apply 0 0
  simp only [pairC, Fin.sum_univ_one, h1, map_one, mul_one]
  show x 0 * y 0 = (r : ℂ)⁻¹ * ⟪(r : ℂ) * star (y 0), x 0⟫_ℂ
  rw [RCLike.inner_apply, map_mul, Complex.conj_ofReal, RCLike.star_def, Complex.conj_conj]
  linear_combination (-(x 0 * y 0)) * mul_inv_cancel₀ hr'
theorem scale_inv_one (t : InfinitePlace K → ℝ) (ht : ∀ v, 0 < t v) (v : InfinitePlace K) :
    (scaleFrame t (fr K 1) v)⁻¹ = ((Real.sqrt (t v) : ℝ) : ℂ) • 1 := by
  simp only [scaleFrame, fr]
  have hs : (Real.sqrt (t v) : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr (ht v)).ne'
  apply Matrix.inv_eq_left_inv
  rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul, Complex.ofReal_inv,
    mul_inv_cancel₀ hs, one_smul]
variable {K}
theorem maj_scale {d : ℕ} (t : InfinitePlace K → ℝ) (ht : ∀ v, 0 < t v)
    (X : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ) (hX : ∀ v, IsUnit (X v).det) (v : InfinitePlace K)
    (x y : Fin d → K) :
    Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin d)) (scaleFrame t X) v x y =
      (t v : ℂ) * Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin d)) X v x y := by
  have hs : 0 < Real.sqrt (t v) := Real.sqrt_pos.mpr (ht v)
  have hinv : ((((Real.sqrt (t v))⁻¹ : ℝ) : ℂ) • X v)⁻¹ = ((Real.sqrt (t v) : ℝ) : ℂ) • (X v)⁻¹ := by
    apply Matrix.inv_eq_left_inv
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.nonsing_inv_mul _ (hX v),
      ← Complex.ofReal_mul, mul_inv_cancel₀ hs.ne', Complex.ofReal_one, one_smul]
  have ht' : star ((Real.sqrt (t v) : ℝ) : ℂ) * ((Real.sqrt (t v) : ℝ) : ℂ) = (t v : ℂ) := by
    rw [RCLike.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul, Real.mul_self_sqrt (ht v).le]
  simp only [Formalism.HermitianLatticesTheory.majAt, Formalism.HermitianLatticesTheory.fcoord, scaleFrame, hinv, Matrix.smul_mulVec, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul, star_mul']
  rw [← ht']
  ring
theorem maj_smul {d : ℕ} (X : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ) (v : InfinitePlace K) (a : K)
    (x y : Fin d → K) :
    Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin d)) X v (a • x) (a • y) =
      ((‖v.embedding a‖ ^ 2 : ℝ) : ℂ) * Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin d)) X v x y := by
  have hv : ∀ z : Fin d → K, Formalism.HermitianLatticesTheory.vecAt (Pi.basisFun K (Fin d)) v (a • z) =
      v.embedding a • Formalism.HermitianLatticesTheory.vecAt (Pi.basisFun K (Fin d)) v z := by
    intro z
    ext i
    simp [Formalism.HermitianLatticesTheory.vecAt]
  have hn : ((‖v.embedding a‖ ^ 2 : ℝ) : ℂ) = star (v.embedding a) * v.embedding a := by
    simp [RCLike.star_def, Complex.conj_mul']
  simp only [Formalism.HermitianLatticesTheory.majAt, Formalism.HermitianLatticesTheory.fcoord, hv, Matrix.mulVec_smul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul, star_mul']
  rw [hn]
  ring
theorem smul_one_mulVec {d : ℕ} (a : K) (x : Fin d → K) :
    (a • (1 : Matrix (Fin d) (Fin d) K)).mulVec x = a • x := by
  ext i
  simp [Matrix.mulVec, dotProduct, Matrix.one_apply]
theorem bij_smul {d : ℕ} (a : K) (ha : a ≠ 0) :
    Function.Bijective (a • (1 : Matrix (Fin d) (Fin d) K)).mulVec := by
  have h : (a • (1 : Matrix (Fin d) (Fin d) K)).mulVec = fun x => a • x :=
    funext (smul_one_mulVec a)
  rw [h]
  refine ⟨fun x y hxy => smul_right_injective _ ha hxy, fun y => ⟨a⁻¹ • y, ?_⟩⟩
  simp [smul_smul, mul_inv_cancel₀ ha]
theorem bij_one' {d : ℕ} : Function.Bijective (1 : Matrix (Fin d) (Fin d) K).mulVec := by
  have h : (1 : Matrix (Fin d) (Fin d) K).mulVec = id := funext Matrix.one_mulVec
  rw [h]
  exact Function.bijective_id
theorem map_top_of_bij {d : ℕ} (A : Matrix (Fin d) (Fin d) K) (h : Function.Bijective A.mulVec) :
    Submodule.map A.mulVecLin ⊤ = ⊤ := by
  rw [Submodule.map_top]
  exact LinearMap.range_eq_top.mpr h.2
end Std
section Amb
variable {K : Type} [Field K] [NumberField K] [StarRing K]
abbrev amb (Bs : DefBase K) : DefAmb Bs where
  FR := fun _ => Fin 1 → K
  aR := fun _ => inferInstance
  mR := fun _ => inferInstance
  OpR := fun _ => Unit
  opR := fun _ _ => 1
  ZHR := fun _ => ⊤
  FL := fun _ _ => Fin 1 → K
  aL := fun _ _ => inferInstance
  mL := fun _ _ => inferInstance
  OpL := fun _ _ => Unit
  opL := fun _ _ _ => 1
  ZHL := fun _ _ => ⊤
abbrev zs (Bs : DefBase K) : DefSub (amb Bs) := ⟨fun _ => ⊤, fun _ _ => ⊤⟩
theorem zs_stable (Bs : DefBase K) : (zs Bs).Stable := by
  exact ⟨fun _ _ => le_top, fun _ _ _ => le_top⟩
theorem zs_inBlock (Bs : DefBase K) : (zs Bs).InBlock := by
  exact ⟨fun _ => le_top, fun _ _ => le_top⟩
def scaleOf {Bs : DefBase K} (N : IndefNum Bs) : IndefScale Bs where
  F0 := N.F0
  J0 := N.J0
  E1u := 0
  l3m := N.l3
  l3u := 0
  l6m := N.l6
  l6u := 0
  x := 1
  b := N.hh
  la := N.la
  de := N.de
theorem scaleOf_num {Bs : DefBase K} (N : IndefNum Bs) (hE : N.E1 = fun _ => 0) (C CH : ℝ) :
    N = (scaleOf N).num C CH := by
  obtain ⟨F0, J0, E1, l3, l6, hh, la, de⟩ := N
  simp only at hE
  subst hE
  simp [IndefScale.num, scaleOf]
def castN {Bs : DefBase K} {Df0 Df1 : DefSide Bs} {Dc : DefCols Df1} {Sp : SPer Dc} {N N' : IndefNum Bs} (h : N = N')
    (P : IndefCore Df0 Df1 Dc Sp N) : IndefCore Df0 Df1 Dc Sp N' := h ▸ P
def pkgOf {Bs : DefBase K} {Df0 Df1 : DefSide Bs} {Dc : DefCols Df1} {Sp : SPer Dc} {N : IndefNum Bs}
    (hE : N.E1 = fun _ => 0) (P : IndefCore Df0 Df1 Dc Sp N) (C CH : ℝ) :
    IndefPkg (amb Bs) (fun _ => ⟨Df0, Df1, Dc, Sp, scaleOf N⟩) C CH :=
  ⟨zs Bs, zs_stable Bs, zs_inBlock Bs, castN (scaleOf_num N hE C CH) P⟩
end Amb
namespace one
variable (K : Type) [Field K] [NumberField K] [StarRing K] (v0 : InfinitePlace K)
abbrev base : DefBase K where
  K0 := cmMax K
  v0 := v0
  Tup := Unit
  μ0 := ()
  Ix := Unit
  fIx := inferInstance
  J := Unit
  fJ := inferInstance
abbrev df : DefSide (base K v0) where
  nV := fun _ => 1
  HV := fun _ => 1
  Mt := fun _ => sl K 1
  dQ := fun _ => 1
  Pq := fun _ => 1
  XQ := fun _ => fr K 1
  Qp := fun _ _ => ⊤
  dZ := fun _ _ => 1
  HT := fun _ _ => 1
  XT := fun _ _ => fr K 1
  Tl := fun _ _ => sl K 1
  Zp := fun _ _ _ => ⊤
abbrev dat : IndefData (df K v0) where
  μ := fun _ => ()
  Tw := ∅
  D := 1
  XE := fr K 1
  Ep := fun _ => ⊤
  ι := fun _ => 1
  dW := fun _ => 1
  XW := fun _ => fr K 1
  Wp := fun _ _ => ⊤
  M := fun _ => sl K 1
  θ := fun _ _ => 1
  κ := fun _ => 1
  lam := fun _ _ _ _ => 1
  err0 := fun _ _ => 0
abbrev num : IndefNum (base K v0) where
  F0 := fun _ _ => 0
  J0 := fun _ _ _ => 0
  E1 := fun _ => 0
  l3 := fun _ => lcv (fr K 1) (sl K 1) / ((1 : ℕ) : ℝ)
  l6 := fun _ => 0
  hh := Formalism.HN.muMaxDef (Pi.basisFun K (Fin 1)) (fr K 1) (dat K v0).RR + meanLog (dat K v0).κ
  la := 0
  de := 0
theorem h0 : (dat K v0).H0 := by
  exact ⟨fun _ => rfl, fun w => by simp⟩
theorem frames : (dat K v0).Frames := by
  exact ⟨fun v => by simp [fr], fun _ v => by simp [fr], fun _ => sl_lattice K 1⟩
theorem l1a : (dat K v0).BaseTypeSubspacesMapOntoBothSides := by
  exact ⟨fun p => map_top_of_bij _ bij_one', fun j p => map_top_of_bij _ bij_one'⟩
theorem l1c : (dat K v0).RowLatticeBoundForBasis := by
  refine ⟨fun _ => bij_one', fun _ _ => bij_one', fun _ => one_pos, fun _ _ _ _ => one_pos,
    fun t v _ p => ?_, fun j t v _ p => ?_⟩
  · intro x _ y
    simp [dat, df, Matrix.one_mulVec]
  · intro x _ y
    simp [dat, df, Matrix.one_mulVec]
theorem l1d : (dat K v0).DimensionsOfPartsAgree := by
  intro j p
  rfl
theorem l6 : (dat K v0).L6 (num K v0) := by
  intro j p v
  simp
theorem l3 : (dat K v0).L3 (num K v0) := by
  intro j
  exact le_refl _
theorem on : (dat K v0).ON (num K v0) := by
  refine ⟨fun w hw => by simp [dat] at hw, fun w hw => by simp [dat] at hw, fun j => ?_⟩
  simp [dat, num]
def what₂ : IndefRows (df K v0) where
  toIndefData := dat K v0
  pos := one_pos
  proviso := fun _ => std_ratHerm K (cmMax K) 1
  types := fun _ => by simp
  h0 := h0 K v0
  frames := frames K v0
  l1a := l1a K v0
  l1c := l1c K v0
  l1d := l1d K v0
def side : IndefSide (df K v0) (num K v0) where
  toIndefRows := what₂ K v0
  l3 := l3 K v0
  on := on K v0
abbrev dc : DefCols (df K v0) where
  Mem := Unit
  a := fun _ => 1
  Xc := fun _ => fr K 1
  Pt := fun _ _ => (Pi.basisFun K (Fin 1)).toDual
abbrev sp : SPer (dc K v0) where
  HH := ℂ
  nHH := inferInstance
  iHH := inferInstance
  Pu := fun _ => LinearMap.proj 0
  Rw := ⊤
abbrev cd : ColData (dc K v0) (sp K v0) (dat K v0) where
  B := fun _ => (Pi.basisFun K (Fin 1)).toDual
  ζ := fun _ _ => 1
  sE := conjLinearRankOne 1
theorem l1b : (cd K v0).PairingFactorsThroughPeriods := by
  refine ⟨fun u t φ F => by simp [cd, dc, dat, df], fun _ => rfl, fun _ _ => one_ne_zero,
    fun _ w => ValuationRepresentative.vw_one w⟩
theorem l1e : (cd K v0).L1e := by
  refine ⟨fun y => conj_linear_rank_one_norm 1 1 zero_le_one (by simp) y, fun y => Submodule.mem_top, by simp, 1,
    fun y => by rw [Matrix.one_mulVec], fun u => ⟨1, one_ne_zero, 1, fun x => by rw [Matrix.one_mulVec],
    fun x y => ?_⟩⟩
  dsimp only [cd, dc, sp, dat, df, base]
  rw [Matrix.one_mulVec, Matrix.one_mulVec, pairC_std K v0 1 one_pos]
  simp [ColData.bes]
def cols : IndefCols (df K v0) (dc K v0) (sp K v0) (num K v0) where
  toIndefRows := what₂ K v0
  l6 := l6 K v0
  col := cd K v0
  l1b := l1b K v0
  l1e := l1e K v0
theorem untw : (dat K v0).Untwisted (num K v0) := by
  intro w _ j
  refine ⟨?_, rfl⟩
  simp only [IndefData.Aw, IndefData.Iw, dat, df]
  rw [matLat_one, idx_std, idx_std, jw_std]
  simp
theorem funn : (dat K v0).FUN (num K v0) := by
  unfold IndefData.FUN IndefData.muMaxRR
  simp
theorem extra : IndefExtra (side K v0) (cols K v0) where
  untw := untw K v0
  level := ⟨rfl, rfl, rfl⟩
  passage := fun _ _ HH0 h => by
    refine ⟨?_, ?_⟩
    · show (dat K v0).muMaxRR ≤ HH0 + 14 * (0 : ℝ)
      rw [mul_zero, add_zero]; exact h
    · show (dat K v0).muCC ≤ (dat K v0).muCC + 3 * (0 : ℝ) * _ + 28 * (0 : ℝ)
      simp
  fun0 := funn K v0
end one
namespace two
open scoped Classical
variable (K : Type) [Field K] [NumberField K] [StarRing K] (v0 : InfinitePlace K)
  (S : Finset (HeightOneSpectrum (𝓞 K))) (a : K) (kap l : InfinitePlace K → ℝ)
abbrev base : DefBase K where
  K0 := cmMax K
  v0 := v0
  Tup := Bool
  μ0 := false
  Ix := Unit
  fIx := inferInstance
  J := Unit
  fJ := inferInstance
abbrev df : DefSide (base K v0) where
  nV := fun _ => 1
  HV := fun _ => 1
  Mt := fun _ => sl K 1
  dQ := fun _ => 1
  Pq := fun _ => 1
  XQ := fun _ => fr K 1
  Qp := fun _ _ => ⊤
  dZ := fun _ _ => 1
  HT := fun _ _ => 1
  XT := fun _ _ => fr K 1
  Tl := fun _ _ => sl K 1
  Zp := fun _ _ _ => ⊤
def mp (t : Bool) : Matrix (Fin 1) (Fin 1) K := cond t (a • 1) 1
abbrev dat : IndefData (df K v0) where
  μ := fun w => decide (w ∈ S)
  Tw := S
  D := 1
  XE := scaleFrame (fun v => kap v * l v) (fr K 1)
  Ep := fun _ => ⊤
  ι := fun t => mp K a t
  dW := fun _ => 1
  XW := fun _ => scaleFrame l (fr K 1)
  Wp := fun _ _ => ⊤
  M := fun _ => sl K 1
  θ := fun _ t => mp K a t
  κ := kap
  lam := fun _ t _ v => cond t (l v * ‖v.embedding a‖ ^ 2) (l v)
  err0 := fun _ _ => 0
abbrev num : IndefNum (base K v0) where
  F0 := fun w _ => if w ∈ S then
    (((dat K v0 S a kap l).Iw () true w : ℝ) + ((dat K v0 S a kap l).Iw () true (conjPl w) : ℝ)) /
      (2 * (ramw w : ℝ)) else 0
  J0 := fun _ _ _ => 0
  E1 := fun _ => 0
  l3 := fun _ => lcv (scaleFrame l (fr K 1)) (sl K 1) / ((1 : ℕ) : ℝ)
  l6 := fun _ => Finset.univ.inf' Finset.univ_nonempty fun v => Real.log (l v)
  hh := Formalism.HN.muMaxDef (Pi.basisFun K (Fin 1)) (scaleFrame (fun v => kap v * l v) (fr K 1))
    (dat K v0 S a kap l).RR + meanLog kap
  la := 0
  de := 0
variable {K v0 S a kap l}
theorem fr_unit (v : InfinitePlace K) : IsUnit (fr K 1 v).det := by
  simp [fr]
theorem h0 (hS : ∀ w, conjPl w ∈ S ↔ w ∈ S) : (dat K v0 S a kap l).H0 := by
  exact ⟨fun w => by simp [hS w], fun w => by simp⟩
theorem frames (hk : ∀ v, 0 < kap v) (hl : ∀ v, 0 < l v) : (dat K v0 S a kap l).Frames := by
  refine ⟨fun v => ?_, fun _ v => ?_, fun _ => sl_lattice K 1⟩
  · have h := Real.sqrt_pos.mpr (mul_pos (hk v) (hl v))
    simp [scaleFrame, fr, h.ne']
  · have h := Real.sqrt_pos.mpr (hl v)
    simp [scaleFrame, fr, h.ne']
theorem mp_bij (ha : a ≠ 0) (t : Bool) : Function.Bijective (mp K a t).mulVec := by
  cases t
  · exact bij_one'
  · exact bij_smul a ha
theorem l1a (ha : a ≠ 0) : (dat K v0 S a kap l).BaseTypeSubspacesMapOntoBothSides := by
  exact ⟨fun p => map_top_of_bij _ (mp_bij ha false), fun j p => map_top_of_bij _ (mp_bij ha false)⟩
theorem l1c (ha : a ≠ 0) (hk : ∀ v, 0 < kap v) (hl : ∀ v, 0 < l v) : (dat K v0 S a kap l).RowLatticeBoundForBasis := by
  refine ⟨fun t => mp_bij ha t, fun _ t => mp_bij ha t, hk, fun j t p v => ?_,
    fun t v _ p => ?_, fun j t v _ p => ?_⟩
  · have hae : 0 < ‖v.embedding a‖ := norm_pos_iff.mpr ((map_ne_zero _).mpr ha)
    cases t
    · exact hl v
    · exact mul_pos (hl v) (pow_pos hae 2)
  · intro x _ y
    dsimp only [dat, df]
    rw [maj_scale _ (fun v => mul_pos (hk v) (hl v)) _ (fun v => fr_unit v)]
    cases t
    · simp only [mp, cond_false, Matrix.one_mulVec, Fintype.prod_unique]
      all_goals push_cast
      all_goals ring
    · simp only [mp, cond_true, smul_one_mulVec, maj_smul, Fintype.prod_unique]
      all_goals push_cast
      all_goals ring
  · intro x _ y
    dsimp only [dat, df]
    rw [maj_scale _ hl _ (fun v => fr_unit v)]
    cases t
    · simp only [mp, cond_false, Matrix.one_mulVec]
    · simp only [mp, cond_true, smul_one_mulVec, maj_smul]
      all_goals push_cast
      all_goals ring
theorem l1d : (dat K v0 S a kap l).DimensionsOfPartsAgree := by
  intro j p
  rfl
theorem l6 : (dat K v0 S a kap l).L6 (num K v0 S a kap l) := by
  intro j p v
  exact Finset.inf'_le _ (Finset.mem_univ v)
theorem l3 : (dat K v0 S a kap l).L3 (num K v0 S a kap l) := by
  intro j
  exact le_refl _
theorem on : (dat K v0 S a kap l).ON (num K v0 S a kap l) := by
  refine ⟨fun w hw => ?_, fun w _ j => le_refl _, fun j => by simp [dat, num]⟩
  have hw' : w ∈ S := hw
  have hμ : decide (w ∈ S) = true := by simp [hw']
  have hr : (0 : ℝ) < (ramw w : ℝ) := by
    have := one_le_ramw w
    have h1 : (1 : ℝ) ≤ (ramw w : ℝ) := by exact_mod_cast this
    linarith
  have hr0 : (ramw w : ℝ) ≠ 0 := hr.ne'
  have key : ∀ X : ℝ, X ≤ (2 * ((ramw w : ℝ) * (X / (2 * (ramw w : ℝ)))) + (ramw w : ℝ) * 0 +
      (ramw w : ℝ) * (2 / (plc w : ℝ) ^ 2)) * ((1 : ℕ) : ℝ) := by
    intro X
    have h2 : 2 * ((ramw w : ℝ) * (X / (2 * (ramw w : ℝ)))) = X := by
      rw [div_eq_mul_inv]
      have hi : (2 * (ramw w : ℝ)) * (2 * (ramw w : ℝ))⁻¹ = 1 := mul_inv_cancel₀ (by positivity)
      linear_combination X * hi
    have hnn : (0 : ℝ) ≤ (ramw w : ℝ) * (2 / (plc w : ℝ) ^ 2) := by positivity
    have e : (X + (ramw w : ℝ) * 0 + (ramw w : ℝ) * (2 / (plc w : ℝ) ^ 2)) * ((1 : ℕ) : ℝ) =
        X + (ramw w : ℝ) * (2 / (plc w : ℝ) ^ 2) := by push_cast; ring
    rw [h2, e]
    linarith
  simp only [dat, num, hμ, hw', if_true, Fintype.sum_unique]
  exact key _
def what₂ (hS : ∀ w, conjPl w ∈ S ↔ w ∈ S) (ha : a ≠ 0) (hk : ∀ v, 0 < kap v) (hl : ∀ v, 0 < l v) :
    IndefRows (df K v0) where
  toIndefData := dat K v0 S a kap l
  pos := one_pos
  proviso := fun _ => std_ratHerm K (cmMax K) 1
  types := fun _ => by simp
  h0 := h0 hS
  frames := frames hk hl
  l1a := l1a ha
  l1c := l1c ha hk hl
  l1d := l1d
def side (hS : ∀ w, conjPl w ∈ S ↔ w ∈ S) (ha : a ≠ 0) (hk : ∀ v, 0 < kap v) (hl : ∀ v, 0 < l v) :
    IndefSide (df K v0) (num K v0 S a kap l) where
  toIndefRows := what₂ hS ha hk hl
  l3 := l3
  on := on
variable (K v0 S a kap l)
abbrev dc : DefCols (df K v0) where
  Mem := Unit
  a := fun _ => 1
  Xc := fun _ => fr K 1
  Pt := fun _ t => cond t (a • (Pi.basisFun K (Fin 1)).toDual) (Pi.basisFun K (Fin 1)).toDual
abbrev sp : SPer (dc K v0 a) where
  HH := ℂ
  nHH := inferInstance
  iHH := inferInstance
  Pu := fun _ => LinearMap.proj 0
  Rw := ⊤
abbrev cd : ColData (dc K v0 a) (sp K v0 a) (dat K v0 S a kap l) where
  B := fun _ => (Pi.basisFun K (Fin 1)).toDual
  ζ := fun _ _ => 1
  sE := conjLinearRankOne (Real.sqrt (kap v0 * l v0))
variable {K v0 S a kap l}
theorem l1b : (cd K v0 S a kap l).PairingFactorsThroughPeriods := by
  refine ⟨fun u t φ F => ?_, fun _ => rfl, fun _ _ => one_ne_zero, fun _ w => ValuationRepresentative.vw_one w⟩
  dsimp only [cd, dc, dat, df]
  cases t
  · simp [mp]
  · simp [mp, smul_one_mulVec]
theorem l1e (hk : ∀ v, 0 < kap v) (hl : ∀ v, 0 < l v) : (cd K v0 S a kap l).L1e := by
  have hpos : ∀ v, 0 < kap v * l v := fun v => mul_pos (hk v) (hl v)
  have hr : 0 < Real.sqrt (kap v0 * l v0) := Real.sqrt_pos.mpr (hpos v0)
  refine ⟨fun y => conj_linear_rank_one_norm _ _ hr.le (scale_inv_one K (fun v => kap v * l v) hpos v0) y,
    fun y => Submodule.mem_top, by simp, 1, fun y => by rw [Matrix.one_mulVec],
    fun u => ⟨((Real.sqrt (kap v0 * l v0) : ℝ) : ℂ)⁻¹, inv_ne_zero (by exact_mod_cast hr.ne'), 1,
      fun x => by rw [Matrix.one_mulVec], fun x y => ?_⟩⟩
  dsimp only [cd, dc, sp, dat, df, base]
  rw [Matrix.one_mulVec, Matrix.one_mulVec, pairC_std K v0 _ hr]
  simp [ColData.bes]
def cols (hS : ∀ w, conjPl w ∈ S ↔ w ∈ S) (ha : a ≠ 0) (hk : ∀ v, 0 < kap v) (hl : ∀ v, 0 < l v) :
    IndefCols (df K v0) (dc K v0 a) (sp K v0 a) (num K v0 S a kap l) where
  toIndefRows := what₂ hS ha hk hl
  l6 := l6
  col := cd K v0 S a kap l
  l1b := l1b
  l1e := l1e hk hl
theorem untw : (dat K v0 S a kap l).Untwisted (num K v0 S a kap l) := by
  intro w hw j
  have hw' : w ∉ S := hw
  have hμ : decide (w ∈ S) = false := by simp [hw']
  refine ⟨?_, ?_⟩
  · simp only [IndefData.Aw, IndefData.Iw, dat, df, hμ, mp, cond_false]
    rw [matLat_one, idx_std, idx_std, jw_std]
    simp
  · simp [num, hw']
theorem funn : (dat K v0 S a kap l).FUN (num K v0 S a kap l) := by
  unfold IndefData.FUN IndefData.muMaxRR
  simp
theorem extra (hS : ∀ w, conjPl w ∈ S ↔ w ∈ S) (ha : a ≠ 0) (hk : ∀ v, 0 < kap v) (hl : ∀ v, 0 < l v) :
    IndefExtra (side (v0 := v0) hS ha hk hl) (cols hS ha hk hl) where
  untw := untw
  level := ⟨rfl, rfl, rfl⟩
  passage := fun _ _ HH0 h => by
    refine ⟨?_, ?_⟩
    · show (dat K v0 S a kap l).muMaxRR ≤ HH0 + 14 * (0 : ℝ)
      rw [mul_zero, add_zero]; exact h
    · show (dat K v0 S a kap l).muCC ≤ (dat K v0 S a kap l).muCC + 3 * (0 : ℝ) * _ + 28 * (0 : ℝ)
      simp
  fun0 := funn
end two
section Pair
variable {K : Type} [Field K] [NumberField K] [StarRing K]
open scoped Classical in

def pairSet (w : HeightOneSpectrum (𝓞 K)) : Finset (HeightOneSpectrum (𝓞 K)) := {w, conjPl w}
theorem pairSet_conj (w u : HeightOneSpectrum (𝓞 K)) : conjPl u ∈ pairSet w ↔ u ∈ pairSet w := by
  classical
  simp only [pairSet, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro (h | h)
    · right
      rw [← h, ValuationRepresentative.conjPl_conjPl]
    · left
      rw [← ValuationRepresentative.conjPl_conjPl u, h, ValuationRepresentative.conjPl_conjPl]
  · rintro (h | h)
    · right
      rw [h]
    · left
      rw [h, ValuationRepresentative.conjPl_conjPl]
end Pair
section Concrete
open NumberField.IsCMField
abbrev K3 := CyclotomicField 3 ℚ
instance : IsCMField K3 :=
  haveI : IsCyclotomicExtension {3} ℚ K3 := CyclotomicField.isCyclotomicExtension 3 ℚ
  IsCyclotomicExtension.Rat.isCMField K3 (S := {3}) ⟨3, rfl, by norm_num⟩
instance : StarRing K3 where
  star := complexConj K3
  star_involutive := complexConj_apply_apply K3
  star_mul := fun a b => by simp [mul_comm]
  star_add := fun a b => map_add _ a b
def coreOne (v0 : InfinitePlace K3) :
    IndefCore (one.df K3 v0) (one.df K3 v0) (one.dc K3 v0) (one.sp K3 v0) (one.num K3 v0) :=
  ⟨one.side K3 v0, one.cols K3 v0, one.extra K3 v0⟩
def coreTwo (v0 : InfinitePlace K3) (w : HeightOneSpectrum (𝓞 K3)) :
    IndefCore (two.df K3 v0) (two.df K3 v0) (two.dc K3 v0 3) (two.sp K3 v0 3)
      (two.num K3 v0 (pairSet w) 3 (fun _ => 2) (fun _ => 5)) :=
  ⟨two.side (pairSet_conj w) (by norm_num) (fun _ => by norm_num) (fun _ => by norm_num),
    two.cols (pairSet_conj w) (by norm_num) (fun _ => by norm_num) (fun _ => by norm_num),
    two.extra (pairSet_conj w) (by norm_num) (fun _ => by norm_num) (fun _ => by norm_num)⟩
def faceTwo (v0 : InfinitePlace K3) (w : HeightOneSpectrum (𝓞 K3)) : IndefFace where
  K := K3
  Bs := two.base K3 v0
  A := amb (two.base K3 v0)
  fc := fun _ => ⟨two.df K3 v0, two.df K3 v0, two.dc K3 v0 3, two.sp K3 v0 3,
    scaleOf (two.num K3 v0 (pairSet w) 3 (fun _ => 2) (fun _ => 5))⟩
end Concrete
end Formalism.L2.Indef.Examples₂


