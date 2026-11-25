-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_QuadraticExampleRankThreePackage
-- name    : Formalism_LocalToGlobal_IndefiniteForms_QuadraticExampleRankThreePackage
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T01:00:02.512591+00:00
-- url     : https://prove2.me/theorems/b31cfe8b-75b2-4de6-9829-6a7d6a29bd8a
-- title:
--   Quadratic Example Rank Three Package
-- statement:
--   Definitions and structural lemmas for Quadratic Example Rank Three Package, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteForms/QuadraticExampleRankThreePackage.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefExample
import Theorems.Thm_Formalism_DivisionValues_LocalCovolumeBasis_key
import Theorems.Thm_Formalism_DivisionValues_ReductionFirst_vw_one
import Theorems.Thm_Formalism_DivisionValues_ValuationRepresentative_vw_one
import Theorems.Thm_Formalism_DivisionValues_scaleFrame_det_isUnit
import Theorems.Thm_Formalism_DivisionValues_sqrt_mul_sqrt_complex
import Theorems.Thm_Formalism_EigenvalueLevelCeiling_ramified_basic_bound
import Theorems.Thm_P2M_Formalism_L2_Indef_Examples__scal_comap_6bb2b35a3d73

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
section Diag
variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable (K) in

def dfr {n : ℕ} (s : Fin n → ℝ) : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ :=
  fun _ => Matrix.diagonal fun i => (((Real.sqrt (s i))⁻¹ : ℝ) : ℂ)
theorem dfr_inv {n : ℕ} (s : Fin n → ℝ) (hs : ∀ i, 0 < s i) (v : InfinitePlace K) :
    (dfr K s v)⁻¹ = Matrix.diagonal fun i => ((Real.sqrt (s i) : ℝ) : ℂ) := by
  apply Matrix.inv_eq_right_inv
  rw [dfr, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  have h : Real.sqrt (s i) ≠ 0 := (Real.sqrt_pos.mpr (hs i)).ne'
  rw [← Complex.ofReal_mul, inv_mul_cancel₀ h, Complex.ofReal_one]
theorem dfr_unit {n : ℕ} (s : Fin n → ℝ) (hs : ∀ i, 0 < s i) (v : InfinitePlace K) :
    IsUnit (dfr K s v).det := by
  rw [dfr, Matrix.det_diagonal]
  refine IsUnit.mk0 _ (Finset.prod_ne_zero_iff.mpr fun i _ => ?_)
  exact_mod_cast (inv_pos.mpr (Real.sqrt_pos.mpr (hs i))).ne'
variable (K) in

def line (n : ℕ) (p : Fin n) : Submodule K (Fin n → K) := LinearMap.range (LinearMap.single K (fun _ => K) p)
theorem line_top (n : ℕ) : (⨆ p, line K n p) = ⊤ := LinearMap.iSup_range_single K (fun _ : Fin n => K)
theorem scal_diag {n : ℕ} (s : Fin n → ℝ) (hs : ∀ i, 0 < s i) (v : InfinitePlace K) (p : Fin n) :
    IsScalarOn (fr K n) (dfr K s) v 1 (line K n p) (s p) := by
  rintro x ⟨c, rfl⟩ y
  rw [Matrix.one_mulVec, Matrix.one_mulVec]
  simp only [Formalism.HermitianLatticesTheory.majAt, Formalism.HermitianLatticesTheory.fcoord, dfr_inv s hs v, fr, inv_one, Matrix.one_mulVec,
    Matrix.mulVec_diagonal, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : i = p
  · subst h
    rw [← sqrt_mul_sqrt_complex (s i) (hs i)]
    simp only [star_mul', Complex.star_def, Complex.conj_ofReal]
    ring
  · have h0 : Formalism.HermitianLatticesTheory.vecAt (Pi.basisFun K (Fin n)) v (LinearMap.single K (fun _ => K) p c) i = 0 := by
      simp [Formalism.HermitianLatticesTheory.vecAt, h]
    rw [h0]; simp
def only0 (V : Type) [AddCommGroup V] [Module K V] : Fin 2 → Submodule K V := ![⊤, ⊥]
theorem singleton_grading_supr_eq_top (V : Type) [AddCommGroup V] [Module K V] : (⨆ p, only0 (K := K) V p) = ⊤ :=
  top_le_iff.1 (le_iSup (only0 (K := K) V) 0)
end Diag
section Only
variable {K : Type} [Field K] [NumberField K] [StarRing K]
theorem maj_zero {d : ℕ} (X : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ) (v : InfinitePlace K) (y : Fin d → K) :
    Formalism.HermitianLatticesTheory.majAt (Pi.basisFun K (Fin d)) X v 0 y = 0 := by
  have h0 : Formalism.HermitianLatticesTheory.vecAt (Pi.basisFun K (Fin d)) v (0 : Fin d → K) = 0 := by
    funext i; simp [Formalism.HermitianLatticesTheory.vecAt]
  simp [Formalism.HermitianLatticesTheory.majAt, Formalism.HermitianLatticesTheory.fcoord, h0]
theorem scal_only0 (t : Fin 2 → ℝ) (ht : 0 < t 0) (v : InfinitePlace K) (p : Fin 2) :
    IsScalarOn (fr K 1) (scaleFrame (fun _ => t 0) (fr K 1)) v 1 (only0 (K := K) (Fin 1 → K) p) (t p) := by
  revert p
  rw [Fin.forall_fin_two]
  refine ⟨fun x _ y => ?_, fun x hx y => ?_⟩
  · rw [Matrix.one_mulVec, Matrix.one_mulVec]
    exact maj_scale _ (fun _ => ht) _ two.fr_unit v x y
  · have h0 : x = 0 := by simpa [only0] using hx
    subst h0
    rw [Matrix.mulVec_zero, maj_zero, maj_zero, mul_zero]
end Only
namespace three
variable (K : Type) [Field K] [NumberField K] [StarRing K] (v0 : InfinitePlace K) (kap : ℝ)
  (l : Fin 2 → Fin 2 → ℝ)
abbrev base : DefBase K where
  K0 := cmMax K
  v0 := v0
  Tup := Unit
  μ0 := ()
  Ix := Fin 2
  fIx := inferInstance
  J := Fin 2
  fJ := inferInstance
abbrev df0 : DefSide (base K v0) where
  nV := fun _ => 2
  HV := fun _ => 1
  Mt := fun _ => sl K 2
  dQ := fun _ => 2
  Pq := fun _ => 1
  XQ := fun _ => fr K 2
  Qp := fun _ => line K 2
  dZ := fun _ _ => 2
  HT := fun _ _ => 1
  XT := fun _ _ => fr K 2
  Tl := fun _ _ => sl K 2
  Zp := fun _ _ => line K 2
abbrev df1 : DefSide (base K v0) where
  nV := fun _ => 1
  HV := fun _ => 1
  Mt := fun _ => sl K 1
  dQ := fun _ => 1
  Pq := fun _ => 1
  XQ := fun _ => fr K 1
  Qp := fun _ => only0 (Fin 1 → K)
  dZ := fun _ _ => 1
  HT := fun _ _ => 1
  XT := fun _ _ => fr K 1
  Tl := fun _ _ => sl K 1
  Zp := fun _ _ => only0 (Fin 1 → K)
abbrev dat0 : IndefData (df0 K v0) where
  μ := fun _ => ()
  Tw := ∅
  D := 2
  XE := dfr K fun p => kap * ∏ j, l j p
  Ep := line K 2
  ι := fun _ => 1
  dW := fun _ => 2
  XW := fun j => dfr K fun p => l j p
  Wp := fun _ => line K 2
  M := fun _ => sl K 2
  θ := fun _ _ => 1
  κ := fun _ => kap
  lam := fun j _ p _ => l j p
  err0 := fun _ _ => 0
abbrev dat1 : IndefData (df1 K v0) where
  μ := fun _ => ()
  Tw := ∅
  D := 1
  XE := scaleFrame (fun _ => kap * ∏ j, l j 0) (fr K 1)
  Ep := only0 (Fin 1 → K)
  ι := fun _ => 1
  dW := fun _ => 1
  XW := fun j => scaleFrame (fun _ => l j 0) (fr K 1)
  Wp := fun _ => only0 (Fin 1 → K)
  M := fun _ => sl K 1
  θ := fun _ _ => 1
  κ := fun _ => kap
  lam := fun j _ p _ => l j p
  err0 := fun _ _ => 0
abbrev num : IndefNum (base K v0) where
  F0 := fun _ _ => 0
  J0 := fun _ _ _ => 0
  E1 := fun _ => 0
  l3 := fun j => lcv (dfr K fun p => l j p) (sl K 2) / ((2 : ℕ) : ℝ)
  l6 := fun j => min (Real.log (l j 0)) (Real.log (l j 1))
  hh := max (dat0 K v0 kap l).muMaxRR (dat1 K v0 kap l).muMaxRR + meanLog (fun _ : InfinitePlace K => kap)
  la := max 0 (max (((dat1 K v0 kap l).muMaxRR - (dat0 K v0 kap l).muMaxRR) / 14)
    (((dat1 K v0 kap l).muCC - (dat0 K v0 kap l).muCC) / 28))
  de := 0
variable {K v0 kap l}
theorem prod_pos' (hk : 0 < kap) (hl : ∀ j p, 0 < l j p) (p : Fin 2) : 0 < kap * ∏ j, l j p :=
  mul_pos hk (Finset.prod_pos fun j _ => hl j p)
theorem map_one_eq {d : ℕ} (A : Submodule K (Fin d → K)) :
    Submodule.map (Matrix.mulVecLin (1 : Matrix (Fin d) (Fin d) K)) A = A := by
  rw [Matrix.mulVecLin_one, Submodule.map_id]
def rows0 (hk : 0 < kap) (hl : ∀ j p, 0 < l j p) : IndefRows (df0 K v0) where
  toIndefData := dat0 K v0 kap l
  pos := two_pos
  proviso := fun _ => std_ratHerm K (cmMax K) 2
  types := fun _ => line_top 2
  h0 := ⟨fun _ => rfl, by intro w; simp⟩
  frames := ⟨fun v => dfr_unit _ (prod_pos' hk hl) v, fun j v => dfr_unit _ (hl j) v, fun _ => sl_lattice K 2⟩
  l1a := ⟨fun _ => map_one_eq _, fun _ _ => map_one_eq _⟩
  l1c := ⟨fun _ => bij_one', fun _ _ => bij_one', fun _ => hk, fun j _ p _ => hl j p,
    fun _ v _ p => scal_comap bij_one' (map_one_eq _) (scal_diag _ (prod_pos' hk hl) v p),
    fun j _ v _ p => scal_comap bij_one' (map_one_eq _) (scal_diag _ (hl j) v p)⟩
  l1d := fun _ _ => rfl
def side (hk : 0 < kap) (hl : ∀ j p, 0 < l j p) : IndefSide (df0 K v0) (num K v0 kap l) where
  toIndefRows := rows0 hk hl
  l3 := fun _ => le_refl _
  on := ⟨fun w hw => by simp [rows0] at hw, fun w hw => by simp [rows0] at hw, fun _ => by simp [rows0]⟩
def rows1 (hk : 0 < kap) (hl : ∀ j p, 0 < l j p) : IndefRows (df1 K v0) where
  toIndefData := dat1 K v0 kap l
  pos := one_pos
  proviso := fun _ => std_ratHerm K (cmMax K) 1
  types := fun _ => singleton_grading_supr_eq_top _
  h0 := ⟨fun _ => rfl, by intro w; simp⟩
  frames := ⟨fun v => scaleFrame_det_isUnit _ (fun _ => prod_pos' hk hl 0) _ two.fr_unit v,
    fun j v => scaleFrame_det_isUnit _ (fun _ => hl j 0) _ two.fr_unit v, fun _ => sl_lattice K 1⟩
  l1a := ⟨fun _ => map_one_eq _, fun _ _ => map_one_eq _⟩
  l1c := ⟨fun _ => bij_one', fun _ _ => bij_one', fun _ => hk, fun j _ p _ => hl j p,
    fun _ v _ p => scal_comap bij_one' (map_one_eq _)
      (scal_only0 (fun p => kap * ∏ j, l j p) (prod_pos' hk hl 0) v p),
    fun j _ v _ p => scal_comap bij_one' (map_one_eq _) (scal_only0 (fun p => l j p) (hl j 0) v p)⟩
  l1d := fun _ _ => rfl
variable (K v0) in

abbrev dc : DefCols (df1 K v0) where
  Mem := Unit
  a := fun _ => 1
  Xc := fun _ => fr K 1
  Pt := fun _ _ => (Pi.basisFun K (Fin 1)).toDual
variable (K v0) in

abbrev sp : SPer (dc K v0) where
  HH := ℂ
  nHH := inferInstance
  iHH := inferInstance
  Pu := fun _ => LinearMap.proj 0
  Rw := ⊤
variable (K v0 kap l) in

abbrev cd : ColData (dc K v0) (sp K v0) (dat1 K v0 kap l) where
  B := fun _ => (Pi.basisFun K (Fin 1)).toDual
  ζ := fun _ _ => 1
  sE := conjLinearRankOne (Real.sqrt (kap * ∏ j, l j 0))
theorem l1b : (cd K v0 kap l).PairingFactorsThroughPeriods := by
  refine ⟨fun _ _ φ F => ?_, fun _ => rfl, fun _ _ => one_ne_zero, fun _ w => ValuationRepresentative.vw_one w⟩
  simp
theorem l1e (hk : 0 < kap) (hl : ∀ j p, 0 < l j p) : (cd K v0 kap l).L1e := by
  have hr : 0 < Real.sqrt (kap * ∏ j, l j 0) := Real.sqrt_pos.mpr (prod_pos' hk hl 0)
  refine ⟨fun y => conj_linear_rank_one_norm _ _ hr.le (scale_inv_one K _ (fun _ => prod_pos' hk hl 0) v0) y, fun _ => Submodule.mem_top, by simp, 1,
    fun y => by rw [Matrix.one_mulVec],
    fun _ => ⟨((Real.sqrt (kap * ∏ j, l j 0) : ℝ) : ℂ)⁻¹, inv_ne_zero (by exact_mod_cast hr.ne'), 1,
      fun x => by rw [Matrix.one_mulVec], fun x y => ?_⟩⟩
  rw [Matrix.one_mulVec, Matrix.one_mulVec]
  exact pairC_std K v0 _ hr x y
def cols (hk : 0 < kap) (hl : ∀ j p, 0 < l j p) : IndefCols (df1 K v0) (dc K v0) (sp K v0) (num K v0 kap l) where
  toIndefRows := rows1 hk hl
  l6 := by
    intro j p v
    revert p
    rw [Fin.forall_fin_two]
    exact ⟨min_le_left _ _, min_le_right _ _⟩
  col := cd K v0 kap l
  l1b := l1b
  l1e := l1e hk hl
theorem untw : (dat0 K v0 kap l).Untwisted (num K v0 kap l) := by
  intro w _ j
  refine ⟨?_, rfl⟩
  show ((idx w (sl K 2) (matLat (1 : Matrix (Fin 2) (Fin 2) K) (sl K 2)) : ℤ) : ℝ) +
    ((idx (conjPl w) (sl K 2) (matLat (1 : Matrix (Fin 2) (Fin 2) K) (sl K 2)) : ℤ) : ℝ) +
    ((jw (1 : Matrix (Fin 2) (Fin 2) K) w (sl K 2) : ℤ) : ℝ) = 0
  rw [matLat_one, idx_std, idx_std, jw_std]; simp
theorem extra (hk : 0 < kap) (hl : ∀ j p, 0 < l j p) :
    IndefExtra (side (K := K) (v0 := v0) hk hl) (cols hk hl) where
  untw := untw
  level := ⟨rfl, rfl, rfl⟩
  passage := fun _ _ HH0 h => by
    have h' : (dat0 K v0 kap l).muMaxRR ≤ HH0 := h
    have h1 : ((dat1 K v0 kap l).muMaxRR - (dat0 K v0 kap l).muMaxRR) / 14 ≤ (num K v0 kap l).la :=
      le_trans (le_max_left _ _) (le_max_right _ _)
    have h2 : ((dat1 K v0 kap l).muCC - (dat0 K v0 kap l).muCC) / 28 ≤ (num K v0 kap l).la :=
      le_trans (le_max_right _ _) (le_max_right _ _)
    refine ⟨?_, ?_⟩
    · show (dat1 K v0 kap l).muMaxRR ≤ HH0 + 14 * (num K v0 kap l).la
      linarith
    · show (dat1 K v0 kap l).muCC ≤ (dat0 K v0 kap l).muCC + 3 * (0 : ℝ) * _ + 28 * (num K v0 kap l).la
      linarith
  fun0 := by
    show (dat0 K v0 kap l).muMaxRR ≤ (max _ _ + meanLog fun _ : InfinitePlace K => kap) - meanLog fun _ => kap
    rw [add_sub_cancel_right]; exact le_max_left _ _
def core (hk : 0 < kap) (hl : ∀ j p, 0 < l j p) :
    IndefCore (df0 K v0) (df1 K v0) (dc K v0) (sp K v0) (num K v0 kap l) :=
  ⟨side hk hl, cols hk hl, extra hk hl⟩
end three
def l4 (j p : Fin 2) : ℝ := 2 + ((j : ℕ) : ℝ) + 2 * ((p : ℕ) : ℝ)
section DiagMaps
variable {K : Type} [Field K] [NumberField K] [StarRing K]
theorem diag_bij {n : ℕ} (a : Fin n → K) (ha : ∀ i, a i ≠ 0) : Function.Bijective (Matrix.diagonal a).mulVec := by
  refine ⟨fun x y h => ?_, fun y => ⟨fun i => (a i)⁻¹ * y i, ?_⟩⟩
  · funext i
    have := congrFun h i
    rw [Matrix.mulVec_diagonal, Matrix.mulVec_diagonal] at this
    exact mul_left_cancel₀ (ha i) this
  · funext i
    rw [Matrix.mulVec_diagonal, mul_inv_cancel_left₀ (ha i)]
theorem diag_map_line {n : ℕ} (a : Fin n → K) (ha : ∀ i, a i ≠ 0) (p : Fin n) :
    Submodule.map (Matrix.diagonal a).mulVecLin (line K n p) = line K n p := by
  ext y
  constructor
  · rintro ⟨_, ⟨c, rfl⟩, rfl⟩
    refine ⟨a p * c, funext fun i => ?_⟩
    by_cases h : i = p
    · subst h; simp [Matrix.mulVec_diagonal]
    · simp [Matrix.mulVec_diagonal, h]
  · rintro ⟨c, rfl⟩
    refine ⟨_, ⟨(a p)⁻¹ * c, rfl⟩, funext fun i => ?_⟩
    by_cases h : i = p
    · subst h; simp [Matrix.mulVec_diagonal, mul_inv_cancel_left₀ (ha i)]
    · simp [Matrix.mulVec_diagonal, h]
theorem scal_diag2 {n : ℕ} (s : Fin n → ℝ) (hs : ∀ i, 0 < s i) (v : InfinitePlace K) (a : Fin n → K) (p : Fin n) :
    IsScalarOn (fr K n) (dfr K s) v (Matrix.diagonal a) (line K n p) (s p * ‖v.embedding (a p)‖ ^ 2) := by
  rintro x ⟨c, rfl⟩ y
  simp only [Formalism.HermitianLatticesTheory.majAt, Formalism.HermitianLatticesTheory.fcoord, dfr_inv s hs v, fr, inv_one, Matrix.one_mulVec,
    Matrix.mulVec_diagonal, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hv : ∀ z : Fin n → K, Formalism.HermitianLatticesTheory.vecAt (Pi.basisFun K (Fin n)) v ((Matrix.diagonal a).mulVec z) i =
      v.embedding (a i) * Formalism.HermitianLatticesTheory.vecAt (Pi.basisFun K (Fin n)) v z i := by
    intro z; simp [Formalism.HermitianLatticesTheory.vecAt, Matrix.mulVec_diagonal]
  rw [hv, hv]
  by_cases h : i = p
  · subst h
    have h2 : ((‖v.embedding (a i)‖ ^ 2 : ℝ) : ℂ) = star (v.embedding (a i)) * v.embedding (a i) := by
      rw [Complex.star_def, Complex.conj_mul']; push_cast; rfl
    rw [Complex.ofReal_mul, h2, ← sqrt_mul_sqrt_complex (s i) (hs i)]
    simp only [star_mul', Complex.star_def, Complex.conj_ofReal]
    ring
  · have h0 : Formalism.HermitianLatticesTheory.vecAt (Pi.basisFun K (Fin n)) v (LinearMap.single K (fun _ => K) p c) i = 0 := by
      simp [Formalism.HermitianLatticesTheory.vecAt, h]
    rw [h0]; simp
theorem mem_line_one (x : Fin 1 → K) : x ∈ line K 1 0 :=
  ⟨x 0, by funext i; rw [Subsingleton.elim i 0]; simp⟩
theorem scal_only0D (s : Fin 2 → ℝ) (hs : 0 < s 0) (v : InfinitePlace K) (a : Fin 2 → K) (p : Fin 2) :
    IsScalarOn (fr K 1) (dfr K fun _ : Fin 1 => s 0) v (Matrix.diagonal fun _ : Fin 1 => a 0)
      (only0 (K := K) (Fin 1 → K) p) (s p * ‖v.embedding (a p)‖ ^ 2) := by
  revert p
  rw [Fin.forall_fin_two]
  refine ⟨fun x _ y => ?_, fun x hx y => ?_⟩
  · exact scal_diag2 (fun _ : Fin 1 => s 0) (fun _ => hs) v (fun _ => a 0) 0 x (mem_line_one x) y
  · have h0 : x = 0 := by simpa [only0] using hx
    subst h0
    rw [Matrix.mulVec_zero, maj_zero, maj_zero, mul_zero]
theorem map_only0 (A : Matrix (Fin 1) (Fin 1) K) (h : Function.Bijective A.mulVec) (p : Fin 2) :
    Submodule.map A.mulVecLin (only0 (K := K) (Fin 1 → K) p) = only0 (K := K) (Fin 1 → K) p := by
  revert p
  rw [Fin.forall_fin_two]
  exact ⟨map_top_of_bij A h, Submodule.map_bot _⟩
end DiagMaps
namespace four
open scoped Classical
variable (K : Type) [Field K] [NumberField K] [StarRing K] (v0 : InfinitePlace K)
  (S : Finset (HeightOneSpectrum (𝓞 K))) (b : Fin 2 → Fin 2 → K) (kap : ℝ) (l : Fin 2 → Fin 2 → ℝ)
abbrev base : DefBase K where
  K0 := cmMax K
  v0 := v0
  Tup := Bool
  μ0 := false
  Ix := Fin 2
  fIx := inferInstance
  J := Fin 2
  fJ := inferInstance
abbrev df0 : DefSide (base K v0) where
  nV := fun _ => 2
  HV := fun _ => 1
  Mt := fun _ => sl K 2
  dQ := fun _ => 2
  Pq := fun _ => 1
  XQ := fun _ => fr K 2
  Qp := fun _ => line K 2
  dZ := fun _ _ => 2
  HT := fun _ _ => 1
  XT := fun _ _ => fr K 2
  Tl := fun _ _ => sl K 2
  Zp := fun _ _ => line K 2
abbrev df1 : DefSide (base K v0) where
  nV := fun _ => 1
  HV := fun _ => 1
  Mt := fun _ => sl K 1
  dQ := fun _ => 1
  Pq := fun _ => 1
  XQ := fun _ => fr K 1
  Qp := fun _ => only0 (Fin 1 → K)
  dZ := fun _ _ => 1
  HT := fun _ _ => 1
  XT := fun _ _ => fr K 1
  Tl := fun _ _ => sl K 1
  Zp := fun _ _ => only0 (Fin 1 → K)
def bT (t : Bool) (j p : Fin 2) : K := cond t (b j p) 1
def aT (t : Bool) (p : Fin 2) : K := ∏ j, bT K b t j p
abbrev dat0 : IndefData (df0 K v0) where
  μ := fun w => decide (w ∈ S)
  Tw := S
  D := 2
  XE := dfr K fun p => kap * ∏ j, l j p
  Ep := line K 2
  ι := fun t => Matrix.diagonal (aT K b t)
  dW := fun _ => 2
  XW := fun j => dfr K fun p => l j p
  Wp := fun _ => line K 2
  M := fun _ => sl K 2
  θ := fun j t => Matrix.diagonal (bT K b t j)
  κ := fun _ => kap
  lam := fun j t p v => l j p * ‖v.embedding (bT K b t j p)‖ ^ 2
  err0 := fun _ _ => 0
abbrev dat1 : IndefData (df1 K v0) where
  μ := fun w => decide (w ∈ S)
  Tw := S
  D := 1
  XE := dfr K fun _ => kap * ∏ j, l j 0
  Ep := only0 (Fin 1 → K)
  ι := fun t => Matrix.diagonal fun _ => aT K b t 0
  dW := fun _ => 1
  XW := fun j => dfr K fun _ => l j 0
  Wp := fun _ => only0 (Fin 1 → K)
  M := fun _ => sl K 1
  θ := fun j t => Matrix.diagonal fun _ => bT K b t j 0
  κ := fun _ => kap
  lam := fun j t p v => l j p * ‖v.embedding (bT K b t j p)‖ ^ 2
  err0 := fun _ _ => 0
abbrev num : IndefNum (base K v0) where
  F0 := fun w j => if w ∈ S then
    (((dat0 K v0 S b kap l).Iw j true w : ℝ) + ((dat0 K v0 S b kap l).Iw j true (conjPl w) : ℝ)) /
      (2 * (ramw w : ℝ) * 2) else 0
  J0 := fun _ _ _ => 0
  E1 := fun _ => 0
  l3 := fun j => lcv (dfr K fun p => l j p) (sl K 2) / ((2 : ℕ) : ℝ)
  l6 := fun j => min (Real.log (l j 0)) (Real.log (l j 1))
  hh := max (dat0 K v0 S b kap l).muMaxRR (dat1 K v0 S b kap l).muMaxRR +
    meanLog (fun _ : InfinitePlace K => kap)
  la := max 0 (max (((dat1 K v0 S b kap l).muMaxRR - (dat0 K v0 S b kap l).muMaxRR) / 14)
    (((dat1 K v0 S b kap l).muCC - (dat0 K v0 S b kap l).muCC) / 28))
  de := 0
variable {K v0 S b kap l}
theorem bT_ne (hb : ∀ j p, b j p ≠ 0) (t : Bool) (j p : Fin 2) : bT K b t j p ≠ 0 := by
  cases t
  · exact one_ne_zero
  · exact hb j p
theorem aT_ne (hb : ∀ j p, b j p ≠ 0) (t : Bool) (p : Fin 2) : aT K b t p ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun j _ => bT_ne hb t j p
theorem lam_pos (hb : ∀ j p, b j p ≠ 0) (hl : ∀ j p, 0 < l j p) (j : Fin 2) (t : Bool) (p : Fin 2)
    (v : InfinitePlace K) : 0 < l j p * ‖v.embedding (bT K b t j p)‖ ^ 2 :=
  mul_pos (hl j p) (pow_pos (norm_pos_iff.mpr ((map_ne_zero _).mpr (bT_ne hb t j p))) 2)
theorem scal_eq (t : Bool) (p : Fin 2) (v : InfinitePlace K) :
    kap * ∏ j, (l j p * ‖v.embedding (bT K b t j p)‖ ^ 2) =
      (kap * ∏ j, l j p) * ‖v.embedding (aT K b t p)‖ ^ 2 := by
  rw [aT, map_prod, norm_prod, Finset.prod_mul_distrib, Finset.prod_pow, mul_assoc]
theorem norm_inner_fF_le_half_sq_add_integral (j p : Fin 2) (v : InfinitePlace K) :
    min (Real.log (l j 0)) (Real.log (l j 1)) ≤ Real.log (l j p * ‖v.embedding (bT K b false j p)‖ ^ 2) := by
  have h1 : l j p * ‖v.embedding (bT K b false j p)‖ ^ 2 = l j p := by simp [bT]
  rw [h1]
  revert p
  rw [Fin.forall_fin_two]
  exact ⟨fun _ => min_le_left _ _, fun _ => min_le_right _ _⟩
variable (S) in
theorem h0 (hS : ∀ w, conjPl w ∈ S ↔ w ∈ S) : (dat0 K v0 S b kap l).H0 :=
  ⟨fun w => decide_eq_decide.mpr (hS w), by intro w; simp⟩
def rows0 (hS : ∀ w, conjPl w ∈ S ↔ w ∈ S) (hb : ∀ j p, b j p ≠ 0) (hk : 0 < kap) (hl : ∀ j p, 0 < l j p) :
    IndefRows (df0 K v0) where
  toIndefData := dat0 K v0 S b kap l
  pos := two_pos
  proviso := fun _ => std_ratHerm K (cmMax K) 2
  types := fun _ => line_top 2
  h0 := h0 S hS
  frames := ⟨fun v => dfr_unit _ (three.prod_pos' hk hl) v, fun j v => dfr_unit _ (hl j) v,
    fun _ => sl_lattice K 2⟩
  l1a := ⟨fun p => diag_map_line _ (aT_ne hb false) p, fun j p => diag_map_line _ (bT_ne hb false j) p⟩
  l1c := ⟨fun t => diag_bij _ (aT_ne hb t), fun j t => diag_bij _ (bT_ne hb t j), fun _ => hk,
    fun j t p v => lam_pos hb hl j t p v,
    fun t v _ p => by
      show IsScalarOn _ _ v _ _ (kap * ∏ j, (l j p * ‖v.embedding (bT K b t j p)‖ ^ 2))
      rw [scal_eq]
      exact scal_comap (diag_bij _ (aT_ne hb t)) (diag_map_line _ (aT_ne hb t) p)
        (scal_diag2 _ (three.prod_pos' hk hl) v (aT K b t) p),
    fun j t v _ p => scal_comap (diag_bij _ (bT_ne hb t j)) (diag_map_line _ (bT_ne hb t j) p)
      (scal_diag2 _ (hl j) v (bT K b t j) p)⟩
  l1d := fun _ _ => rfl
theorem on : (dat0 K v0 S b kap l).ON (num K v0 S b kap l) := by
  refine ⟨fun w hw => ?_, fun w _ _ => le_refl _, fun _ => ?_⟩
  · have hμ : decide (w ∈ S) = true := decide_eq_true hw
    have hr : (1 : ℝ) ≤ (ramw w : ℝ) := by exact_mod_cast (ramified_basic_bound K w).2.1
    have hr0 : (ramw w : ℝ) ≠ 0 := by linarith
    have hp : 0 ≤ (ramw w : ℝ) * (2 / (plc w : ℝ) ^ 2) := by positivity
    have key : ∀ j : Fin 2, 2 * ((ramw w : ℝ) * ((((dat0 K v0 S b kap l).Iw j true w : ℝ) +
        ((dat0 K v0 S b kap l).Iw j true (conjPl w) : ℝ)) / (2 * (ramw w : ℝ) * 2))) =
        (((dat0 K v0 S b kap l).Iw j true w : ℝ) + ((dat0 K v0 S b kap l).Iw j true (conjPl w) : ℝ)) / 2 := by
      intro j; field_simp
    simp only [hμ, if_pos hw, mul_zero, add_zero, key, Fin.sum_univ_two, Nat.cast_ofNat]
    linarith
  · simp
def side (hS : ∀ w, conjPl w ∈ S ↔ w ∈ S) (hb : ∀ j p, b j p ≠ 0) (hk : 0 < kap) (hl : ∀ j p, 0 < l j p) :
    IndefSide (df0 K v0) (num K v0 S b kap l) where
  toIndefRows := rows0 hS hb hk hl
  l3 := fun _ => le_refl _
  on := on
def rows1 (hS : ∀ w, conjPl w ∈ S ↔ w ∈ S) (hb : ∀ j p, b j p ≠ 0) (hk : 0 < kap) (hl : ∀ j p, 0 < l j p) :
    IndefRows (df1 K v0) where
  toIndefData := dat1 K v0 S b kap l
  pos := one_pos
  proviso := fun _ => std_ratHerm K (cmMax K) 1
  types := fun _ => singleton_grading_supr_eq_top _
  h0 := ⟨fun w => decide_eq_decide.mpr (hS w), by intro w; simp⟩
  frames := ⟨fun v => dfr_unit _ (fun _ => three.prod_pos' hk hl 0) v, fun j v => dfr_unit _ (fun _ => hl j 0) v,
    fun _ => sl_lattice K 1⟩
  l1a := ⟨fun p => map_only0 _ (diag_bij _ fun _ => aT_ne hb false 0) p,
    fun j p => map_only0 _ (diag_bij _ fun _ => bT_ne hb false j 0) p⟩
  l1c := ⟨fun t => diag_bij _ fun _ => aT_ne hb t 0, fun j t => diag_bij _ fun _ => bT_ne hb t j 0, fun _ => hk,
    fun j t p v => lam_pos hb hl j t p v,
    fun t v _ p => by
      show IsScalarOn _ _ v _ _ (kap * ∏ j, (l j p * ‖v.embedding (bT K b t j p)‖ ^ 2))
      rw [scal_eq]
      exact scal_comap (diag_bij _ fun _ => aT_ne hb t 0) (map_only0 _ (diag_bij _ fun _ => aT_ne hb t 0) p)
        (scal_only0D (fun p => kap * ∏ j, l j p) (three.prod_pos' hk hl 0) v (aT K b t) p),
    fun j t v _ p => scal_comap (diag_bij _ fun _ => bT_ne hb t j 0)
      (map_only0 _ (diag_bij _ fun _ => bT_ne hb t j 0) p)
      (scal_only0D (fun p => l j p) (hl j 0) v (bT K b t j) p)⟩
  l1d := fun _ _ => rfl
variable (K v0 b) in

abbrev dc : DefCols (df1 K v0) where
  Mem := Unit
  a := fun _ => 1
  Xc := fun _ => fr K 1
  Pt := fun _ t => aT K b t 0 • (Pi.basisFun K (Fin 1)).toDual
variable (K v0 b) in

abbrev sp : SPer (dc K v0 b) where
  HH := ℂ
  nHH := inferInstance
  iHH := inferInstance
  Pu := fun _ => LinearMap.proj 0
  Rw := ⊤
variable (K v0 S b kap l) in

abbrev cd : ColData (dc K v0 b) (sp K v0 b) (dat1 K v0 S b kap l) where
  B := fun _ => (Pi.basisFun K (Fin 1)).toDual
  ζ := fun _ _ => 1
  sE := conjLinearRankOne (Real.sqrt (kap * ∏ j, l j 0))
theorem diag_const_mulVec (a : K) (F : Fin 1 → K) : (Matrix.diagonal fun _ : Fin 1 => a).mulVec F = a • F := by
  funext i; simp [Matrix.mulVec_diagonal]
theorem l1b : (cd K v0 S b kap l).PairingFactorsThroughPeriods := by
  refine ⟨fun _ t φ F => ?_, fun _ => rfl, fun _ _ => one_ne_zero, fun _ w => ValuationRepresentative.vw_one w⟩
  simp only [Matrix.one_mulVec, one_mul, diag_const_mulVec, LinearMap.smul_apply, map_smul]
theorem dfr_inv_one (c : ℝ) (hc : 0 < c) (v : InfinitePlace K) :
    (dfr K (fun _ : Fin 1 => c) v)⁻¹ = ((Real.sqrt c : ℝ) : ℂ) • 1 := by
  rw [dfr_inv _ (fun _ => hc) v]
  ext i j
  fin_cases i; fin_cases j; simp
theorem l1e (hk : 0 < kap) (hl : ∀ j p, 0 < l j p) : (cd K v0 S b kap l).L1e := by
  have hr : 0 < Real.sqrt (kap * ∏ j, l j 0) := Real.sqrt_pos.mpr (three.prod_pos' hk hl 0)
  refine ⟨fun y => conj_linear_rank_one_norm _ _ hr.le (dfr_inv_one _ (three.prod_pos' hk hl 0) v0) y, fun _ => Submodule.mem_top, by simp, 1,
    fun y => by rw [Matrix.one_mulVec],
    fun _ => ⟨((Real.sqrt (kap * ∏ j, l j 0) : ℝ) : ℂ)⁻¹, inv_ne_zero (by exact_mod_cast hr.ne'), 1,
      fun x => by rw [Matrix.one_mulVec], fun x y => ?_⟩⟩
  rw [Matrix.one_mulVec, Matrix.one_mulVec]
  exact pairC_std K v0 _ hr x y
def cols (hS : ∀ w, conjPl w ∈ S ↔ w ∈ S) (hb : ∀ j p, b j p ≠ 0) (hk : 0 < kap) (hl : ∀ j p, 0 < l j p) :
    IndefCols (df1 K v0) (dc K v0 b) (sp K v0 b) (num K v0 S b kap l) where
  toIndefRows := rows1 hS hb hk hl
  l6 := fun j p v => norm_inner_fF_le_half_sq_add_integral j p v
  col := cd K v0 S b kap l
  l1b := l1b
  l1e := l1e hk hl
theorem untw : (dat0 K v0 S b kap l).Untwisted (num K v0 S b kap l) := by
  intro w hw j
  refine ⟨?_, if_neg hw⟩
  have hμ : decide (w ∈ S) = false := decide_eq_false hw
  have h1 : Matrix.diagonal (bT K b false j) = (1 : Matrix (Fin 2) (Fin 2) K) := by
    rw [← Matrix.diagonal_one]; rfl
  simp only [IndefData.Aw, IndefData.Iw, hμ, h1]
  rw [matLat_one, idx_std, idx_std, jw_std]; simp
theorem extra (hS : ∀ w, conjPl w ∈ S ↔ w ∈ S) (hb : ∀ j p, b j p ≠ 0) (hk : 0 < kap) (hl : ∀ j p, 0 < l j p) :
    IndefExtra (side (K := K) (v0 := v0) (S := S) hS hb hk hl) (cols hS hb hk hl) where
  untw := untw
  level := ⟨rfl, rfl, rfl⟩
  passage := fun _ _ HH0 h => by
    have h' : (dat0 K v0 S b kap l).muMaxRR ≤ HH0 := h
    have h1 : ((dat1 K v0 S b kap l).muMaxRR - (dat0 K v0 S b kap l).muMaxRR) / 14 ≤
        (num K v0 S b kap l).la := le_trans (le_max_left _ _) (le_max_right _ _)
    have h2 : ((dat1 K v0 S b kap l).muCC - (dat0 K v0 S b kap l).muCC) / 28 ≤
        (num K v0 S b kap l).la := le_trans (le_max_right _ _) (le_max_right _ _)
    refine ⟨?_, ?_⟩
    · show (dat1 K v0 S b kap l).muMaxRR ≤ HH0 + 14 * (num K v0 S b kap l).la
      linarith
    · show (dat1 K v0 S b kap l).muCC ≤
        (dat0 K v0 S b kap l).muCC + 3 * (0 : ℝ) * _ + 28 * (num K v0 S b kap l).la
      linarith
  fun0 := by
    show (dat0 K v0 S b kap l).muMaxRR ≤
      (max _ _ + meanLog fun _ : InfinitePlace K => kap) - meanLog fun _ => kap
    rw [add_sub_cancel_right]; exact le_max_left _ _
def core (hS : ∀ w, conjPl w ∈ S ↔ w ∈ S) (hb : ∀ j p, b j p ≠ 0) (hk : 0 < kap) (hl : ∀ j p, 0 < l j p) :
    IndefCore (df0 K v0) (df1 K v0) (dc K v0 b) (sp K v0 b) (num K v0 S b kap l) :=
  ⟨side hS hb hk hl, cols hS hb hk hl, extra hS hb hk hl⟩
end four
def b4 (K : Type) [Field K] (j p : Fin 2) : K := ((2 + (j : ℕ) + 2 * (p : ℕ) : ℕ) : K)
end Formalism.L2.Indef.Examples₂


