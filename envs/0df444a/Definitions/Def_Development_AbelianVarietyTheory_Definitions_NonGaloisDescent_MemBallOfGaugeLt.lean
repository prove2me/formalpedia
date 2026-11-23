-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MemBallOfGaugeLt
-- name    : Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MemBallOfGaugeLt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:13:47.710821+00:00
-- url     : https://prove2.me/theorems/30f046a6-4b13-48d6-b73b-ce77d7adffff
-- title:
--   Mem Ball Of Gauge Lt
-- statement:
--   Definitions and structural lemmas for Mem Ball Of Gauge Lt, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/MemBallOfGaugeLt.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped NNReal
namespace GlobalTheory.BSP
variable (l : ℕ) {A : Type} [CommRing A] (u : A) (ρ : ℝ≥0)
def PreDisc (l : ℕ) {A : Type} [CommRing A] (_u : A) (_ρ : ℝ≥0) : Type := Localization.Away (l : A)
instance : CommRing (PreDisc l u ρ) := inferInstanceAs (CommRing (Localization.Away (l : A)))
instance : Algebra A (PreDisc l u ρ) := inferInstanceAs (Algebra A (Localization.Away (l : A)))
instance : IsLocalization.Away (l : A) (PreDisc l u ρ) :=
  inferInstanceAs (IsLocalization.Away (l : A) (Localization.Away (l : A)))
def monos (r : ℝ) : Set (PreDisc l u ρ) :=
  {y | ∃ a b c : ℕ, (l : ℝ) ^ c * (ρ : ℝ) ^ b ≤ r * (l : ℝ) ^ a ∧
    y = algebraMap A (PreDisc l u ρ) ((l : A) ^ a * u ^ b) * IsLocalization.Away.invSelf (l : A) ^ c}
def ball (r : ℝ) : Submodule A (PreDisc l u ρ) := Submodule.span A (monos l u ρ r)
open scoped NNReal in
variable (l : ℕ) {A : Type} [CommRing A] (u : A) (ρ : ℝ≥0) in

theorem _root_.GlobalTheory.BSP.ball_mono {r s : ℝ} (h : r ≤ s) :
    _root_.GlobalTheory.BSP.ball l u ρ r ≤ _root_.GlobalTheory.BSP.ball l u ρ s := by
  refine Submodule.span_mono ?_
  rintro y ⟨a, b, c, hle, rfl⟩
  exact ⟨a, b, c, hle.trans (mul_le_mul_of_nonneg_right h (by positivity)), rfl⟩
open scoped NNReal in
variable (l : ℕ) {A : Type} [CommRing A] (u : A) (ρ : ℝ≥0) in

theorem _root_.GlobalTheory.BSP.mul_mem_ball {r s : ℝ} (hr : 0 ≤ r) {x y : _root_.GlobalTheory.BSP.PreDisc l u ρ}
    (hx : x ∈ _root_.GlobalTheory.BSP.ball l u ρ r) (hy : y ∈ _root_.GlobalTheory.BSP.ball l u ρ s) :
    x * y ∈ _root_.GlobalTheory.BSP.ball l u ρ (r * s) := by
  have hxy := Submodule.mul_mem_mul hx hy
  rw [_root_.GlobalTheory.BSP.ball, _root_.GlobalTheory.BSP.ball, Submodule.span_mul_span] at hxy
  refine Submodule.span_mono ?_ hxy
  rintro _ ⟨y₁, ⟨a, b, c, h₁, rfl⟩, y₂, ⟨a', b', c', h₂, rfl⟩, rfl⟩
  refine ⟨a + a', b + b', c + c', ?_, ?_⟩
  · calc (l : ℝ) ^ (c + c') * (ρ : ℝ) ^ (b + b')
          = ((l : ℝ) ^ c * (ρ : ℝ) ^ b) * ((l : ℝ) ^ c' * (ρ : ℝ) ^ b') := by ring
      _ ≤ (r * (l : ℝ) ^ a) * (s * (l : ℝ) ^ a') :=
          mul_le_mul h₁ h₂ (by positivity) (mul_nonneg hr (by positivity))
      _ = r * s * (l : ℝ) ^ (a + a') := by ring
  · simp only [map_mul, map_pow]
    ring
def gauge (y : PreDisc l u ρ) : ℝ := sInf {r : ℝ | 0 < r ∧ y ∈ ball l u ρ r}
open scoped NNReal in
variable (l : ℕ) {A : Type} [CommRing A] (u : A) (ρ : ℝ≥0) in

theorem _root_.GlobalTheory.BSP.gauge_nonneg (y : _root_.GlobalTheory.BSP.PreDisc l u ρ) :
    0 ≤ _root_.GlobalTheory.BSP.gauge l u ρ y :=
  Real.sInf_nonneg fun _ h => h.1.le
open scoped NNReal in
variable (l : ℕ) {A : Type} [CommRing A] (u : A) (ρ : ℝ≥0) in

theorem _root_.GlobalTheory.BSP.gauge_le {y : _root_.GlobalTheory.BSP.PreDisc l u ρ} {r : ℝ} (hr : 0 < r)
    (h : y ∈ _root_.GlobalTheory.BSP.ball l u ρ r) : _root_.GlobalTheory.BSP.gauge l u ρ y ≤ r :=
  csInf_le ⟨0, fun _ h => h.1.le⟩ ⟨hr, h⟩
open scoped NNReal in
variable (l : ℕ) {A : Type} [CommRing A] (u : A) (ρ : ℝ≥0) in
lemma preDisc_exists_eq_algebraMap_mul_invSelf_pow (y : _root_.GlobalTheory.BSP.PreDisc l u ρ) :
    ∃ (a : A) (n : ℕ), y = algebraMap A _ a * IsLocalization.Away.invSelf (l : A) ^ n := by
  obtain ⟨n, a, h⟩ := IsLocalization.Away.surj (l : A) y
  refine ⟨a, n, ?_⟩
  rw [← h, mul_assoc, ← mul_pow, IsLocalization.Away.mul_invSelf, one_pow, mul_one]
open scoped NNReal in
variable (l : ℕ) {A : Type} [CommRing A] (u : A) (ρ : ℝ≥0) in
lemma preDisc_exists_pos_mem_ball (y : _root_.GlobalTheory.BSP.PreDisc l u ρ) :
    ∃ r : ℝ, 0 < r ∧ y ∈ _root_.GlobalTheory.BSP.ball l u ρ r := by
  obtain ⟨a, n, rfl⟩ := preDisc_exists_eq_algebraMap_mul_invSelf_pow l u ρ y
  refine ⟨(l : ℝ) ^ n + 1, by positivity, ?_⟩
  have hy : algebraMap A (_root_.GlobalTheory.BSP.PreDisc l u ρ) a * IsLocalization.Away.invSelf (l : A) ^ n
      = a • (algebraMap A _ ((l : A) ^ 0 * u ^ 0) * IsLocalization.Away.invSelf (l : A) ^ n) := by
    rw [Algebra.smul_def, pow_zero, pow_zero, mul_one, map_one, one_mul]
  rw [hy]
  refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, 0, n, ?_, rfl⟩)
  rw [pow_zero, pow_zero, mul_one, mul_one]
  linarith
open scoped NNReal in
variable (l : ℕ) {A : Type} [CommRing A] (u : A) (ρ : ℝ≥0) in

theorem _root_.GlobalTheory.BSP.mem_ball_of_gauge_lt {y : _root_.GlobalTheory.BSP.PreDisc l u ρ} {r : ℝ}
    (h : _root_.GlobalTheory.BSP.gauge l u ρ y < r) : y ∈ _root_.GlobalTheory.BSP.ball l u ρ r := by
  obtain ⟨r₀, hr₀, hy⟩ := preDisc_exists_pos_mem_ball l u ρ y
  obtain ⟨t, ⟨_, hyt⟩, htr⟩ := exists_lt_of_csInf_lt
    (s := {r : ℝ | 0 < r ∧ y ∈ _root_.GlobalTheory.BSP.ball l u ρ r}) ⟨r₀, hr₀, hy⟩ h
  exact _root_.GlobalTheory.BSP.ball_mono l u ρ htr.le hyt
open scoped NNReal in
variable (l : ℕ) {A : Type} [CommRing A] (u : A) (ρ : ℝ≥0) in

theorem _root_.GlobalTheory.BSP.gauge_add_le_max (x y : _root_.GlobalTheory.BSP.PreDisc l u ρ) :
    _root_.GlobalTheory.BSP.gauge l u ρ (x + y) ≤
      max (_root_.GlobalTheory.BSP.gauge l u ρ x) (_root_.GlobalTheory.BSP.gauge l u ρ y) := by
  refine le_of_forall_gt_imp_ge_of_dense fun t ht => ?_
  have ht₀ : 0 < t := ((_root_.GlobalTheory.BSP.gauge_nonneg l u ρ x).trans (le_max_left _ _)).trans_lt ht
  exact _root_.GlobalTheory.BSP.gauge_le l u ρ ht₀ (add_mem
    (_root_.GlobalTheory.BSP.mem_ball_of_gauge_lt l u ρ ((le_max_left _ _).trans_lt ht))
    (_root_.GlobalTheory.BSP.mem_ball_of_gauge_lt l u ρ ((le_max_right _ _).trans_lt ht)))
def gaugeSeminorm : RingSeminorm (PreDisc l u ρ) where
  toFun := gauge l u ρ
  map_zero' := le_antisymm (le_of_forall_gt_imp_ge_of_dense fun _ hr => gauge_le l u ρ hr (zero_mem _))
    (gauge_nonneg l u ρ 0)
  add_le' x y := (gauge_add_le_max l u ρ x y).trans
    (max_le_add_of_nonneg (gauge_nonneg l u ρ x) (gauge_nonneg l u ρ y))
  neg' x := by simp only [gauge, neg_mem_iff]
  mul_le' x y := by
    have hx := gauge_nonneg l u ρ x
    have hy := gauge_nonneg l u ρ y
    refine le_mul_of_forall_lt₀ ?_
    intro r hr s hs
    exact gauge_le l u ρ (mul_pos (hx.trans_lt hr) (hy.trans_lt hs))
      (mul_mem_ball l u ρ (hx.trans hr.le) (mem_ball_of_gauge_lt l u ρ hr) (mem_ball_of_gauge_lt l u ρ hs))
instance : SeminormedCommRing (PreDisc l u ρ) :=
  { (gaugeSeminorm l u ρ).toAddGroupSeminorm.toSeminormedAddCommGroup,
    (inferInstance : CommRing (PreDisc l u ρ)) with
    norm_mul_le := (gaugeSeminorm l u ρ).mul_le' }
theorem norm_preDisc (y : PreDisc l u ρ) : ‖y‖ = gauge l u ρ y := rfl
def Disc : Type := UniformSpace.Completion (PreDisc l u ρ)
instance : NormedRing (Disc l u ρ) := inferInstanceAs (NormedRing (UniformSpace.Completion (PreDisc l u ρ)))
instance : NormedCommRing (Disc l u ρ) :=
  { (inferInstance : NormedRing (Disc l u ρ)) with
    mul_comm := fun x y : UniformSpace.Completion (PreDisc l u ρ) => mul_comm x y }
instance : CompleteSpace (Disc l u ρ) :=
  inferInstanceAs (CompleteSpace (UniformSpace.Completion (PreDisc l u ρ)))
def ofPre : PreDisc l u ρ →+* Disc l u ρ := UniformSpace.Completion.coeRingHom
def toDisc : A →+* Disc l u ρ := (ofPre l u ρ).comp (algebraMap A (PreDisc l u ρ))
open scoped NNReal in
variable (l : ℕ) {A : Type} [CommRing A] (u : A) (ρ : ℝ≥0) in

theorem _root_.GlobalTheory.BSP.norm_ofPre (y : _root_.GlobalTheory.BSP.PreDisc l u ρ) :
    ‖_root_.GlobalTheory.BSP.ofPre l u ρ y‖ = _root_.GlobalTheory.BSP.gauge l u ρ y :=
  UniformSpace.Completion.norm_coe y
variable {l u ρ} in

structure IsDiscMap {A' : Type} [CommRing A'] {u' : A'} {ρ' : ℝ≥0} (f : A →+* A')
    (F : Disc l u ρ →+* Disc l u' ρ') : Prop where
  ext : ∀ a, F (toDisc l u ρ a) = toDisc l u' ρ' (f a)
  norm_le : ∀ x, ‖F x‖ ≤ ‖x‖
section Map
variable {l u ρ} {A' : Type} [CommRing A'] {u' : A'} {ρ' : ℝ≥0}
open scoped NNReal in
variable (l : ℕ) {A : Type} [CommRing A] (u : A) (ρ : ℝ≥0) in
variable {l u ρ} {A' : Type} [CommRing A'] {u' : A'} {ρ' : ℝ≥0} in

theorem _root_.GlobalTheory.BSP.norm_algebraMap_le (a : A) :
    ‖algebraMap A (_root_.GlobalTheory.BSP.PreDisc l u ρ) a‖ ≤ 1 := by
  rw [_root_.GlobalTheory.BSP.norm_preDisc]
  refine _root_.GlobalTheory.BSP.gauge_le l u ρ one_pos ?_
  have ha : algebraMap A (_root_.GlobalTheory.BSP.PreDisc l u ρ) a =
      a • (algebraMap A _ ((l : A) ^ 0 * u ^ 0) * IsLocalization.Away.invSelf (l : A) ^ 0) := by
    simp [Algebra.smul_def]
  rw [ha]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, 0, 0, by simp, rfl⟩)
variable (l u ρ u' ρ') in

def preMap (f : A →+* A') : PreDisc l u ρ →+* PreDisc l u' ρ' :=
  IsLocalization.Away.lift (l : A) (g := (algebraMap A' (PreDisc l u' ρ')).comp f) (by
    rw [map_natCast, ← map_natCast (algebraMap A' (PreDisc l u' ρ'))]
    exact IsLocalization.Away.algebraMap_isUnit _)
open scoped NNReal in
variable (l : ℕ) {A : Type} [CommRing A] (u : A) (ρ : ℝ≥0) in
variable {l u ρ} {A' : Type} [CommRing A'] {u' : A'} {ρ' : ℝ≥0} in

theorem _root_.GlobalTheory.BSP.preMap_alg (f : A →+* A') (a : A) :
    _root_.GlobalTheory.BSP.preMap l u ρ u' ρ' f (algebraMap A _ a) = algebraMap A' _ (f a) :=
  IsLocalization.Away.lift_eq _ _ a
open scoped NNReal in
variable (l : ℕ) {A : Type} [CommRing A] (u : A) (ρ : ℝ≥0) in
variable {l u ρ} {A' : Type} [CommRing A'] {u' : A'} {ρ' : ℝ≥0} in

theorem _root_.GlobalTheory.BSP.preMap_inv (f : A →+* A') :
    _root_.GlobalTheory.BSP.preMap l u ρ u' ρ' f (IsLocalization.Away.invSelf (l : A)) =
      IsLocalization.Away.invSelf (l : A') := by
  have h := congrArg (_root_.GlobalTheory.BSP.preMap l u ρ u' ρ' f)
    (IsLocalization.Away.mul_invSelf (S := _root_.GlobalTheory.BSP.PreDisc l u ρ) (l : A))
  rw [map_mul, map_one, _root_.GlobalTheory.BSP.preMap_alg, map_natCast] at h
  exact (IsLocalization.Away.algebraMap_isUnit (S := _root_.GlobalTheory.BSP.PreDisc l u' ρ') (l : A')).mul_left_cancel
    (h.trans (IsLocalization.Away.mul_invSelf _).symm)
open scoped NNReal in
variable (l : ℕ) {A : Type} [CommRing A] (u : A) (ρ : ℝ≥0) in
variable {l u ρ} {A' : Type} [CommRing A'] {u' : A'} {ρ' : ℝ≥0} in
lemma preDisc_norm_pow_le_norm_pow (x : _root_.GlobalTheory.BSP.PreDisc l u ρ) (k : ℕ) : ‖x ^ k‖ ≤ ‖x‖ ^ k := by
  induction k with
  | zero =>
    simpa using _root_.GlobalTheory.BSP.norm_algebraMap_le (l := l) (u := u) (ρ := ρ) (1 : A)
  | succ k ih =>
    rw [pow_succ, pow_succ]
    exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right ih (norm_nonneg _))
open scoped NNReal in
variable (l : ℕ) {A : Type} [CommRing A] (u : A) (ρ : ℝ≥0) in
variable {l u ρ} {A' : Type} [CommRing A'] {u' : A'} {ρ' : ℝ≥0} in

theorem _root_.GlobalTheory.BSP.norm_preMap_le [hl : Fact l.Prime] (f : A →+* A')
    (h : ‖_root_.GlobalTheory.BSP.toDisc l u' ρ' (f u)‖ ≤ ρ) (y : _root_.GlobalTheory.BSP.PreDisc l u ρ) :
    ‖_root_.GlobalTheory.BSP.preMap l u ρ u' ρ' f y‖ ≤ ‖y‖ := by
  have hl0 : (0 : ℝ) < l := Nat.cast_pos.mpr hl.out.pos
  have hfu : ‖algebraMap A' (_root_.GlobalTheory.BSP.PreDisc l u' ρ') (f u)‖ ≤ ρ := by
    have h' := h
    change ‖_root_.GlobalTheory.BSP.ofPre l u' ρ' (algebraMap A' _ (f u))‖ ≤ _ at h'
    rwa [_root_.GlobalTheory.BSP.norm_ofPre] at h'
  have key : ∀ r : ℝ, 0 ≤ r → ∀ z ∈ _root_.GlobalTheory.BSP.ball l u ρ r,
      ‖_root_.GlobalTheory.BSP.preMap l u ρ u' ρ' f z‖ ≤ r := by
    intro r hr z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨a, b, c, hle, rfl⟩ := hz
      have hmono : ‖algebraMap A' (_root_.GlobalTheory.BSP.PreDisc l u' ρ') ((l : A') ^ a) *
          IsLocalization.Away.invSelf (l : A') ^ c‖ ≤ (l : ℝ) ^ c / (l : ℝ) ^ a := by
        refine _root_.GlobalTheory.BSP.gauge_le l u' ρ' (by positivity) ?_
        refine Submodule.subset_span ⟨a, 0, c, ?_, by simp⟩
        rw [pow_zero, mul_one, div_mul_cancel₀ _ (by positivity)]
      have hpow : ‖algebraMap A' (_root_.GlobalTheory.BSP.PreDisc l u' ρ') (f u) ^ b‖ ≤ (ρ : ℝ) ^ b :=
        (preDisc_norm_pow_le_norm_pow _ b).trans (pow_le_pow_left₀ (norm_nonneg _) hfu b)
      have himg : _root_.GlobalTheory.BSP.preMap l u ρ u' ρ' f
          (algebraMap A _ ((l : A) ^ a * u ^ b) * IsLocalization.Away.invSelf (l : A) ^ c) =
          (algebraMap A' (_root_.GlobalTheory.BSP.PreDisc l u' ρ') ((l : A') ^ a) *
            IsLocalization.Away.invSelf (l : A') ^ c) *
            algebraMap A' (_root_.GlobalTheory.BSP.PreDisc l u' ρ') (f u) ^ b := by
        simp only [map_mul, map_pow, map_natCast, _root_.GlobalTheory.BSP.preMap_alg,
          _root_.GlobalTheory.BSP.preMap_inv]
        ring
      rw [himg]
      refine (norm_mul_le _ _).trans ((mul_le_mul hmono hpow (norm_nonneg _) (by positivity)).trans ?_)
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      exact hle
    | zero => simpa using hr
    | add x y _ _ hx hy =>
      rw [map_add]
      exact (_root_.GlobalTheory.BSP.gauge_add_le_max l u' ρ' _ _).trans (max_le hx hy)
    | smul a x _ hx =>
      rw [Algebra.smul_def, map_mul, _root_.GlobalTheory.BSP.preMap_alg]
      refine (norm_mul_le _ _).trans ?_
      calc _ ≤ 1 * r := mul_le_mul (_root_.GlobalTheory.BSP.norm_algebraMap_le (f a)) hx
            (norm_nonneg _) zero_le_one
        _ = r := one_mul r
  refine le_of_forall_gt_imp_ge_of_dense fun t ht => ?_
  exact key t ((norm_nonneg y).trans ht.le) y (_root_.GlobalTheory.BSP.mem_ball_of_gauge_lt l u ρ ht)
def Disc.map [Fact l.Prime] (f : A →+* A') (h : ‖toDisc l u' ρ' (f u)‖ ≤ ρ) : Disc l u ρ →+* Disc l u' ρ' :=
  UniformSpace.Completion.mapRingHom (preMap l u ρ u' ρ' f)
    (AddMonoidHomClass.continuous_of_bound _ 1 fun y => (norm_preMap_le f h y).trans (one_mul _).ge)
end Map
structure TopBasis {S A : Type} [CommRing S] [CommRing A] (s : S →+* A) (I : Ideal S) (ι : Type) where

  b : ι → A

  c : ι → A →+ S
  c_mul : ∀ i a x, c i (s a * x) = a * c i x
  c_self : ∀ i, c i (b i) = 1
  c_ne : ∀ i j, i ≠ j → c i (b j) = 0
  fin : ∀ x (n : ℕ), {i | c i x ∉ I ^ n}.Finite
  approx : ∀ x (n : ℕ) (F : Finset ι), (∀ i, i ∉ F → c i x ∈ I ^ n) →
    x - ∑ i ∈ F, s (c i x) * b i ∈ (I ^ n).map s
  complete : IsAdicComplete (I.map s) A

  i₀ : ι
  b_i₀ : b i₀ = 1
def TopBasis.self {S : Type} [CommRing S] (I : Ideal S) [h : IsAdicComplete I S] :
    TopBasis (RingHom.id S) I Unit where
  b _ := 1
  c _ := AddMonoidHom.id S
  c_mul _ _ _ := rfl
  c_self _ := rfl
  c_ne _ _ h := (h rfl).elim
  fin _ _ := Set.toFinite _
  approx x n F hF := by
    rw [Ideal.map_id]
    by_cases h : () ∈ F
    · rw [Finset.sum_eq_single () (fun _ _ h => (h rfl).elim) (fun h' => (h' h).elim)]; simp
    · have : F = ∅ := Finset.eq_empty_of_forall_notMem fun _ => h
      simpa [this] using hF () h
  complete := by rwa [Ideal.map_id]
  i₀ := ()
  b_i₀ := rfl
end GlobalTheory.BSP


