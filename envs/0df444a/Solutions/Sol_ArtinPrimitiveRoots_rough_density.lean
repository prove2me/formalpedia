-- Prove2me | solution 1 for ArtinPrimitiveRoots.rough_density
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T10:53:26.359597+00:00
-- url     : https://prove2.me/submissions/067169d3-b247-4cc3-bbd0-6bb1d52ca395

import Mathlib
import Definitions.Def_ArtinSieve
import Theorems.Thm_ArtinPrimitiveRoots_block_sieve
import Theorems.Thm_ArtinPrimitiveRoots_mertens_product
import Theorems.Thm_ArtinPrimitiveRoots_mertens_prime_reciprocals

/-!
# Rough-number density (OpenAI, "Primitive roots for every admissible integer base", Lemma 11.2)

Part (1), the identity `∫_b^{1/2} D_t(1-t) dt/t = D_b(1) - 1`, is proved by writing each term of
`D_b(1)` as an integral over the simplex, splitting it according to which extended coordinate
is minimal (ties are null), moving each piece to the piece where coordinate `0` is minimal by an
affine involution of determinant `±1`, and integrating out the minimal coordinate (Fubini).

Part (2), the upper bound `D_b(1) ≤ (e^{-γ}/b)(1 + C_d e^{-1/(20b)})`, compares `D_b(1)` with
rough integers: with logarithmic weights `1/n` on `(x, x^c]`, the rough count is bounded below
(via ordered prime tuples, dyadic cubes in exponent space and Mertens' reciprocal-prime sums)
by `∑_j (1/j!) ∫_{U_j} ∏ dt_i/t_i ≥ (b/(b+c-1)) (c-1) D_b(1)`, and above by the block sieve with
`H = 2⌊1/(40b)⌋` and Mertens' product. Letting `x → ∞` and then `c → 1` gives the bound.
-/

namespace ArtinPrimitiveRoots.RD

open Real MeasureTheory Set Filter Topology

/-! ## Basic objects -/

/-- The integrand `(w - ∑ x)⁻¹ ∏ (x i)⁻¹`. -/
noncomputable def F (w : ℝ) {m : ℕ} (x : Fin m → ℝ) : ℝ := (w - ∑ i, x i)⁻¹ * ∏ i, (x i)⁻¹

/-- The simplex region `x i ≥ γ`, `∑ x ≤ w - γ`. -/
def Om (γ w : ℝ) (m : ℕ) : Set (Fin m → ℝ) := {x | (∀ i, γ ≤ x i) ∧ ∑ i, x i ≤ w - γ}

/-- The simplex integral. -/
noncomputable def I (γ w : ℝ) (m : ℕ) : ℝ := ∫ x in Om γ w m, F w x

lemma isClosed_Om (γ w : ℝ) (m : ℕ) : IsClosed (Om γ w m) := by
  have h1 : IsClosed {x : Fin m → ℝ | ∀ i, γ ≤ x i} := by
    simp only [setOf_forall]
    exact isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)
  have h2 : IsClosed {x : Fin m → ℝ | ∑ i, x i ≤ w - γ} :=
    isClosed_le (continuous_finset_sum _ fun i _ => continuous_apply i) continuous_const
  exact h1.inter h2

lemma measurableSet_Om (γ w : ℝ) (m : ℕ) : MeasurableSet (Om γ w m) :=
  (isClosed_Om γ w m).measurableSet

lemma measurable_F (w : ℝ) (m : ℕ) : Measurable (fun x : Fin m → ℝ => F w x) := by
  unfold F
  apply Measurable.mul
  · exact (measurable_const.sub (Finset.measurable_sum _ fun i _ => measurable_pi_apply i)).inv
  · exact Finset.measurable_prod _ fun i _ => (measurable_pi_apply i).inv

lemma Om_subset (γ w : ℝ) (hγ : 0 < γ) (m : ℕ) :
    Om γ w m ⊆ Set.pi univ (fun _ => Icc γ w) := by
  intro x hx i _
  refine ⟨hx.1 i, ?_⟩
  have : x i ≤ ∑ j, x j :=
    Finset.single_le_sum (fun j _ => (hγ.le.trans (hx.1 j))) (Finset.mem_univ i)
  linarith [hx.2]

lemma volume_Om_ne_top (γ w : ℝ) (hγ : 0 < γ) (m : ℕ) : volume (Om γ w m) ≠ ⊤ := by
  refine ne_top_of_le_ne_top ?_ (measure_mono (Om_subset γ w hγ m))
  exact ((isCompact_univ_pi fun _ => isCompact_Icc).measure_lt_top).ne

lemma F_bound (γ w : ℝ) (hγ : 0 < γ) (m : ℕ) (x : Fin m → ℝ) (hx : x ∈ Om γ w m) :
    0 ≤ F w x ∧ F w x ≤ γ⁻¹ ^ (m + 1) := by
  have h1 : γ ≤ w - ∑ i, x i := by linarith [hx.2]
  have hpos : 0 < w - ∑ i, x i := by linarith
  have hi : ∀ i, 0 < x i := fun i => lt_of_lt_of_le hγ (hx.1 i)
  refine ⟨mul_nonneg (inv_nonneg.2 hpos.le) (Finset.prod_nonneg fun i _ => (inv_pos.2 (hi i)).le),
    ?_⟩
  unfold F
  rw [pow_succ']
  apply mul_le_mul (inv_anti₀ hγ h1) _ (Finset.prod_nonneg fun i _ => (inv_pos.2 (hi i)).le)
    (inv_pos.2 hγ).le
  calc ∏ i, (x i)⁻¹ ≤ ∏ _i : Fin m, γ⁻¹ :=
        Finset.prod_le_prod (fun i _ => (inv_pos.2 (hi i)).le) fun i _ => inv_anti₀ hγ (hx.1 i)
    _ = γ⁻¹ ^ m := by simp

lemma integrableOn_F (γ w : ℝ) (hγ : 0 < γ) (m : ℕ) : IntegrableOn (F w) (Om γ w m) := by
  refine Measure.integrableOn_of_bounded (M := γ⁻¹ ^ (m + 1)) (volume_Om_ne_top γ w hγ m)
    (measurable_F w m).aestronglyMeasurable ?_
  refine (ae_restrict_iff' (measurableSet_Om γ w m)).2 (Eventually.of_forall fun x hx => ?_)
  have := F_bound γ w hγ m x hx
  rw [Real.norm_eq_abs, abs_of_nonneg this.1]
  exact this.2

lemma I_nonneg (γ w : ℝ) (hγ : 0 < γ) (m : ℕ) : 0 ≤ I γ w m :=
  setIntegral_nonneg (measurableSet_Om γ w m) fun x hx => (F_bound γ w hγ m x hx).1

lemma I_zero (γ w : ℝ) (h : γ ≤ w) : I γ w 0 = w⁻¹ := by
  have hO : Om γ w 0 = univ := by
    ext x; simp [Om]; linarith
  simp [I, hO, F, Measure.real, volume_pi, Measure.pi_of_empty]

lemma I_eq_zero (γ w : ℝ) (hγ : 0 < γ) (n : ℕ) (h : w < (n + 1) * γ) : I γ w n = 0 := by
  have hO : Om γ w n = ∅ := by
    ext x
    simp only [Om, mem_setOf_eq, mem_empty_iff_false, iff_false, not_and, not_le]
    intro hx
    have : ∑ _i : Fin n, γ ≤ ∑ i, x i := Finset.sum_le_sum fun i _ => hx i
    simp at this
    nlinarith
  simp [I, hO]

lemma term_succ (γ w : ℝ) (hγ : γ ≤ w) (n : ℕ) :
    roughDensityTerm γ w (n + 1) = I γ w n / ((n + 1).factorial : ℝ) := by
  rcases n with _ | n
  · simp [roughDensityTerm, I_zero γ w hγ]
  · simp only [roughDensityTerm, I, Om, F]
    ring

lemma roughDensity_eq_sum (γ w : ℝ) (hγ : 0 < γ) (hw : γ ≤ w) (N : ℕ)
    (hN : w < (N + 1) * γ) :
    roughDensity γ w = ∑ n ∈ Finset.range N, I γ w n / ((n + 1).factorial : ℝ) := by
  unfold roughDensity
  rw [tsum_eq_sum (s := Finset.range (N + 1))]
  · rw [Finset.sum_range_succ']
    simp only [roughDensityTerm, add_zero]
    exact Finset.sum_congr rfl fun n _ => term_succ γ w hw n
  · intro j hj
    simp only [Finset.mem_range, not_lt] at hj
    obtain ⟨n, rfl⟩ : ∃ n, j = n + 1 := ⟨j - 1, by omega⟩
    rw [term_succ γ w hw n, I_eq_zero γ w hγ n, zero_div]
    have : (N : ℝ) + 1 ≤ n + 1 := by exact_mod_cast (by omega : N + 1 ≤ n + 1)
    nlinarith

/-! ## The extended coordinates and the swap maps -/

/-- Append the dependent coordinate `1 - ∑ x`. -/
noncomputable def ext (n : ℕ) (x : Fin (n + 1) → ℝ) : Fin (n + 2) → ℝ :=
  fun j => if h : (j : ℕ) < n + 1 then x ⟨j, h⟩ else 1 - ∑ i, x i

@[simp] lemma ext_castSucc (n : ℕ) (x : Fin (n + 1) → ℝ) (i : Fin (n + 1)) :
    ext n x (Fin.castSucc i) = x i := by
  simp [ext, i.2]

@[simp] lemma ext_last (n : ℕ) (x : Fin (n + 1) → ℝ) :
    ext n x (Fin.last _) = 1 - ∑ i, x i := by
  simp [ext]

lemma sum_ext (n : ℕ) (x : Fin (n + 1) → ℝ) : ∑ j, ext n x j = 1 := by
  rw [Fin.sum_univ_castSucc]; simp

lemma prod_ext_inv (n : ℕ) (x : Fin (n + 1) → ℝ) : ∏ j, (ext n x j)⁻¹ = F 1 x := by
  rw [Fin.prod_univ_castSucc]; simp [F, mul_comm]

lemma Om_eq (b : ℝ) (n : ℕ) : Om b 1 (n + 1) = {x | ∀ j, b ≤ ext n x j} := by
  ext x
  simp only [Om, mem_setOf_eq, Fin.forall_fin_succ' (P := fun j => b ≤ ext n x j),
    ext_castSucc, ext_last]
  constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1, by linarith⟩

lemma continuous_ext_apply (n : ℕ) (j : Fin (n + 2)) : Continuous (fun x => ext n x j) := by
  unfold ext
  by_cases h : (j : ℕ) < n + 1
  · simp only [h, dite_true]; exact continuous_apply _
  · simp only [h, dite_false]
    exact continuous_const.sub (continuous_finset_sum _ fun i _ => continuous_apply i)

lemma ext_add (n : ℕ) (x y : Fin (n + 1) → ℝ) (j : Fin (n + 2)) :
    ext n (x + y) j = ext n x j + ext n y j - ext n 0 j := by
  unfold ext
  split_ifs <;> simp [Finset.sum_add_distrib] <;> ring

lemma ext_smul (n : ℕ) (a : ℝ) (x : Fin (n + 1) → ℝ) (j : Fin (n + 2)) :
    ext n (a • x) j - ext n 0 j = a * (ext n x j - ext n 0 j) := by
  unfold ext
  split_ifs <;> simp [← Finset.mul_sum] <;> ring

/-- Swap coordinates `0` and `k` of the extended vector. -/
noncomputable def Tsw (n : ℕ) (k : Fin (n + 2)) (x : Fin (n + 1) → ℝ) : Fin (n + 1) → ℝ :=
  fun i => ext n x (Equiv.swap 0 k (Fin.castSucc i))

lemma ext_Tsw (n : ℕ) (k : Fin (n + 2)) (x : Fin (n + 1) → ℝ) :
    ext n (Tsw n k x) = ext n x ∘ Equiv.swap 0 k := by
  funext j
  rcases Fin.eq_castSucc_or_eq_last j with ⟨i, rfl⟩ | rfl
  · simp [Tsw]
  · rw [ext_last]
    have h1 : ∑ j, ext n x (Equiv.swap 0 k j) = 1 := by
      rw [Equiv.sum_comp (Equiv.swap 0 k) (ext n x)]; exact sum_ext n x
    rw [Fin.sum_univ_castSucc] at h1
    simp only [Function.comp_apply, Tsw]
    linarith

lemma Tsw_Tsw (n : ℕ) (k : Fin (n + 2)) (x : Fin (n + 1) → ℝ) : Tsw n k (Tsw n k x) = x := by
  funext i
  have := congrFun (ext_Tsw n k (Tsw n k x)) (Fin.castSucc i)
  rw [ext_castSucc] at this
  rw [this]
  simp [ext_Tsw]

/-- The linear part of `Tsw`. -/
noncomputable def Lsw (n : ℕ) (k : Fin (n + 2)) :
    (Fin (n + 1) → ℝ) →ₗ[ℝ] (Fin (n + 1) → ℝ) where
  toFun x := fun i => ext n x (Equiv.swap 0 k (Fin.castSucc i)) -
    ext n 0 (Equiv.swap 0 k (Fin.castSucc i))
  map_add' x y := by funext i; simp only [Pi.add_apply, ext_add]; ring
  map_smul' a x := by funext i; simp only [Pi.smul_apply, smul_eq_mul, ext_smul, RingHom.id_apply]

lemma Tsw_eq (n : ℕ) (k : Fin (n + 2)) (x : Fin (n + 1) → ℝ) :
    Tsw n k x = Lsw n k x + Tsw n k 0 := by
  funext i; simp [Lsw, Tsw]

lemma Lsw_Lsw (n : ℕ) (k : Fin (n + 2)) (x : Fin (n + 1) → ℝ) :
    Lsw n k (Lsw n k x) = x := by
  have hc := Tsw_eq n k (Tsw n k 0)
  rw [Tsw_Tsw] at hc
  have h1 := Tsw_eq n k (Tsw n k x)
  rw [Tsw_Tsw, Tsw_eq n k x, map_add, add_assoc, ← hc, add_zero] at h1
  exact h1.symm

lemma measurePreserving_Tsw (n : ℕ) (k : Fin (n + 2)) :
    MeasurePreserving (Tsw n k) volume volume := by
  have hdet : LinearMap.det (Lsw n k) * LinearMap.det (Lsw n k) = 1 := by
    rw [← LinearMap.det_comp]
    have : Lsw n k ∘ₗ Lsw n k = LinearMap.id := by
      exact LinearMap.ext fun x => Lsw_Lsw n k x
    rw [this, LinearMap.det_id]
  have hne : LinearMap.det (Lsw n k) ≠ 0 := by
    intro h; rw [h, zero_mul] at hdet; exact zero_ne_one hdet
  have habs : |(LinearMap.det (Lsw n k))⁻¹| = 1 := by
    have : |LinearMap.det (Lsw n k)| * |LinearMap.det (Lsw n k)| = 1 := by
      rw [← abs_mul, hdet, abs_one]
    have hpos : 0 ≤ |LinearMap.det (Lsw n k)| := abs_nonneg _
    have : |LinearMap.det (Lsw n k)| = 1 := by nlinarith
    rw [abs_inv, this, inv_one]
  have hL : MeasurePreserving (Lsw n k) volume volume := by
    refine ⟨(Lsw n k).continuous_of_finiteDimensional.measurable, ?_⟩
    rw [Measure.map_linearMap_addHaar_eq_smul_addHaar volume hne, habs, ENNReal.ofReal_one,
      one_smul]
  have := (measurePreserving_add_right (volume : Measure (Fin (n + 1) → ℝ)) (Tsw n k 0)).comp hL
  convert this using 1
  funext x; exact Tsw_eq n k x

lemma measurable_Tsw (n : ℕ) (k : Fin (n + 2)) : Measurable (Tsw n k) :=
  (measurePreserving_Tsw n k).measurable

/-- `Tsw` as a measurable equivalence. -/
noncomputable def TswEquiv (n : ℕ) (k : Fin (n + 2)) : (Fin (n + 1) → ℝ) ≃ᵐ (Fin (n + 1) → ℝ) where
  toFun := Tsw n k
  invFun := Tsw n k
  left_inv := Tsw_Tsw n k
  right_inv := Tsw_Tsw n k
  measurable_toFun := measurable_Tsw n k
  measurable_invFun := measurable_Tsw n k

lemma F_Tsw (n : ℕ) (k : Fin (n + 2)) (x : Fin (n + 1) → ℝ) : F 1 (Tsw n k x) = F 1 x := by
  rw [← prod_ext_inv, ← prod_ext_inv, ext_Tsw]
  exact Equiv.prod_comp (Equiv.swap 0 k) (fun j => (ext n x j)⁻¹)

/-! ## The minimum-coordinate pieces -/

/-- The piece where the extended coordinate `k` is minimal. -/
def A (n : ℕ) (b : ℝ) (k : Fin (n + 2)) : Set (Fin (n + 1) → ℝ) :=
  {x | (∀ j, b ≤ ext n x j) ∧ ∀ j, ext n x k ≤ ext n x j}

lemma isClosed_A (n : ℕ) (b : ℝ) (k : Fin (n + 2)) : IsClosed (A n b k) := by
  have h1 : IsClosed {x : Fin (n + 1) → ℝ | ∀ j, b ≤ ext n x j} := by
    simp only [setOf_forall]
    exact isClosed_iInter fun j => isClosed_le continuous_const (continuous_ext_apply n j)
  have h2 : IsClosed {x : Fin (n + 1) → ℝ | ∀ j, ext n x k ≤ ext n x j} := by
    simp only [setOf_forall]
    exact isClosed_iInter fun j => isClosed_le (continuous_ext_apply n k) (continuous_ext_apply n j)
  exact h1.inter h2

lemma preimage_A (n : ℕ) (b : ℝ) (k : Fin (n + 2)) : Tsw n k ⁻¹' A n b k = A n b 0 := by
  ext x
  simp only [A, mem_preimage, mem_setOf_eq, ext_Tsw, Function.comp_apply,
    Equiv.swap_apply_right]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun j => by simpa using h1 (Equiv.swap 0 k j),
      fun j => by simpa using h2 (Equiv.swap 0 k j)⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun j => h1 _, fun j => h2 _⟩

lemma integral_A (n : ℕ) (b : ℝ) (k : Fin (n + 2)) :
    ∫ x in A n b k, F 1 x = ∫ x in A n b 0, F 1 x := by
  have h := (measurePreserving_Tsw n k).setIntegral_preimage_emb
    (TswEquiv n k).measurableEmbedding (F 1) (A n b k)
  rw [← h, preimage_A]
  exact setIntegral_congr_fun (isClosed_A n b 0).measurableSet fun x _ => F_Tsw n k x

lemma null_level {m : ℕ} (φ : (Fin m → ℝ) →ₗ[ℝ] ℝ) (hφ : φ ≠ 0) (c : ℝ) :
    volume {x : Fin m → ℝ | φ x = c} = 0 := by
  obtain ⟨v, hv⟩ : ∃ v, φ v ≠ 0 := by
    by_contra h; push_neg at h; exact hφ (LinearMap.ext h)
  set p : Fin m → ℝ := (c / φ v) • v
  have hp : φ p = c := by simp [p, map_smul, div_mul_cancel₀ c hv]
  have hker : volume ((LinearMap.ker φ : Submodule ℝ (Fin m → ℝ)) : Set (Fin m → ℝ)) = 0 := by
    apply Measure.addHaar_submodule
    intro h
    apply hv
    have : v ∈ LinearMap.ker φ := by rw [h]; trivial
    exact this
  have : {x : Fin m → ℝ | φ x = c} =
      (fun x => x + (-p)) ⁻¹' ((LinearMap.ker φ : Submodule ℝ (Fin m → ℝ)) : Set (Fin m → ℝ)) := by
    ext x; simp [hp, sub_eq_zero, ← sub_eq_add_neg]
  rw [this, measure_preimage_add_right, hker]

lemma null_tie (n : ℕ) (k l : Fin (n + 2)) (hkl : k ≠ l) :
    volume {x : Fin (n + 1) → ℝ | ext n x k = ext n x l} = 0 := by
  let φ : (Fin (n + 1) → ℝ) →ₗ[ℝ] ℝ :=
    { toFun := fun x => (ext n x k - ext n 0 k) - (ext n x l - ext n 0 l)
      map_add' := fun x y => by simp only [ext_add]; ring
      map_smul' := fun a x => by simp only [ext_smul, smul_eq_mul, RingHom.id_apply]; ring }
  have hset : {x : Fin (n + 1) → ℝ | ext n x k = ext n x l} =
      {x | φ x = ext n 0 l - ext n 0 k} := by
    ext x; simp only [mem_setOf_eq, φ, LinearMap.coe_mk, AddHom.coe_mk]
    constructor <;> intro h <;> linarith
  rw [hset]
  apply null_level
  intro h0
  have key : ∀ x, φ x = 0 := fun x => by rw [h0]; rfl
  rcases Fin.eq_castSucc_or_eq_last k with ⟨i, rfl⟩ | rfl
  · have := key (Pi.single i 1)
    simp only [φ, LinearMap.coe_mk, AddHom.coe_mk, ext_castSucc] at this
    rcases Fin.eq_castSucc_or_eq_last l with ⟨i', rfl⟩ | rfl
    · have hii : i ≠ i' := fun h => hkl (by rw [h])
      simp [Pi.single_apply, hii.symm] at this
    · simp at this
      try norm_num at this
  · rcases Fin.eq_castSucc_or_eq_last l with ⟨i', rfl⟩ | rfl
    · have := key (Pi.single i' 1)
      simp [φ] at this
      try norm_num at this
    · exact hkl rfl

lemma Om_eq_iUnion (n : ℕ) (b : ℝ) : Om b 1 (n + 1) = ⋃ k, A n b k := by
  rw [Om_eq]
  ext x
  simp only [mem_setOf_eq, mem_iUnion, A]
  constructor
  · intro h
    obtain ⟨k, -, hk⟩ := Finset.exists_min_image Finset.univ (ext n x) Finset.univ_nonempty
    exact ⟨k, h, fun j => hk j (Finset.mem_univ j)⟩
  · rintro ⟨k, h, -⟩; exact h

lemma integral_Om_eq (n : ℕ) (b : ℝ) (hb : 0 < b) :
    I b 1 (n + 1) = (n + 2) * ∫ x in A n b 0, F 1 x := by
  unfold I
  rw [Om_eq_iUnion]
  rw [integral_iUnion_ae (fun k => (isClosed_A n b k).measurableSet.nullMeasurableSet)]
  · rw [tsum_fintype]
    simp_rw [integral_A n b]
    simp
  · intro k l hkl
    refine measure_mono_null ?_ (null_tie n k l hkl)
    rintro x ⟨⟨_, hk⟩, ⟨_, hl⟩⟩
    exact le_antisymm (hk l) (hl k)
  · rw [← Om_eq_iUnion]; exact integrableOn_F b 1 hb (n + 1)

/-! ## Fubini in the minimal coordinate -/

lemma cons_mem_A0 (n : ℕ) (b t : ℝ) (y : Fin n → ℝ) :
    (Fin.cons t y : Fin (n + 1) → ℝ) ∈ A n b 0 ↔ b ≤ t ∧ y ∈ Om t (1 - t) n := by
  have h0 : ext n (Fin.cons t y : Fin (n + 1) → ℝ) 0 = t := by
    rw [← Fin.castSucc_zero, ext_castSucc]; rfl
  constructor
  · rintro ⟨h1, h2⟩
    have ht := h1 0
    rw [h0] at ht
    refine ⟨ht, fun i => ?_, ?_⟩
    · have := h2 (Fin.castSucc i.succ)
      rwa [h0, ext_castSucc, Fin.cons_succ] at this
    · have := h2 (Fin.last _)
      rw [h0, ext_last, Fin.sum_univ_succ, Fin.cons_zero] at this
      simp only [Fin.cons_succ] at this
      linarith
  · rintro ⟨hbt, hty, hs⟩
    have hall : ∀ j, t ≤ ext n (Fin.cons t y : Fin (n + 1) → ℝ) j := by
      intro j
      rcases Fin.eq_castSucc_or_eq_last j with ⟨i, rfl⟩ | rfl
      · rw [ext_castSucc]
        cases i using Fin.cases with
        | zero => simp
        | succ i => simp [hty i]
      · rw [ext_last, Fin.sum_univ_succ]
        simp only [Fin.cons_zero, Fin.cons_succ]
        linarith
    exact ⟨fun j => hbt.trans (hall j), fun j => h0 ▸ hall j⟩

lemma F_cons (n : ℕ) (t : ℝ) (y : Fin n → ℝ) :
    F 1 (Fin.cons t y : Fin (n + 1) → ℝ) = t⁻¹ * F (1 - t) y := by
  simp only [F, Fin.sum_univ_succ, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
  rw [show 1 - (t + ∑ i, y i) = 1 - t - ∑ i, y i by ring]
  ring

lemma inner_eq (n : ℕ) (b : ℝ) (t : ℝ) :
    ∫ y, (A n b 0).indicator (F 1) (Fin.cons t y : Fin (n + 1) → ℝ) =
      (Icc b (1 / 2)).indicator (fun t => I t (1 - t) n / t) t := by
  classical
  have hpt : ∀ y : Fin n → ℝ, (A n b 0).indicator (F 1) (Fin.cons t y : Fin (n + 1) → ℝ) =
      if b ≤ t then (Om t (1 - t) n).indicator (fun y => t⁻¹ * F (1 - t) y) y else 0 := by
    intro y
    by_cases hbt : b ≤ t
    · rw [indicator_apply, indicator_apply, cons_mem_A0]
      simp [hbt, F_cons]
    · rw [indicator_apply, cons_mem_A0]
      simp [hbt]
  simp_rw [hpt]
  by_cases hbt : b ≤ t
  · simp only [hbt, if_true]
    rw [integral_indicator (measurableSet_Om t (1 - t) n), integral_const_mul]
    by_cases ht2 : t ≤ 1 / 2
    · rw [indicator_of_mem (show t ∈ Icc b (1 / 2) from ⟨hbt, ht2⟩)]
      simp only [I]; ring
    · rw [indicator_of_notMem (fun h => ht2 h.2)]
      have : I t (1 - t) n = 0 := by
        apply I_eq_zero
        · push_neg at ht2; linarith
        · push_neg at ht2; nlinarith
      simp only [I] at this
      rw [this, mul_zero]
  · simp only [hbt, if_false, integral_zero]
    rw [indicator_of_notMem (fun h => hbt h.1)]

lemma A0_integral (n : ℕ) (b : ℝ) (hb : 0 < b) (hb2 : b < 1 / 2) :
    ∫ x in A n b 0, F 1 x = ∫ t in b..(1 / 2), I t (1 - t) n / t ∧
    IntervalIntegrable (fun t => I t (1 - t) n / t) volume b (1 / 2) := by
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0
  have hmp : MeasurePreserving e volume (volume.prod volume) :=
    volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0
  set G : Fin (n + 1) → ℝ → ℝ := fun _ => 0
  have hint : Integrable ((A n b 0).indicator (F 1)) volume := by
    rw [integrable_indicator_iff (isClosed_A n b 0).measurableSet]
    refine (integrableOn_F b 1 hb (n + 1)).mono_set ?_
    rw [Om_eq_iUnion]; exact subset_iUnion (A n b) 0
  have hint2 : Integrable (fun p => (A n b 0).indicator (F 1) (e.symm p)) (volume.prod volume) :=
    (hmp.symm e).integrable_comp_emb e.symm.measurableEmbedding |>.2 hint
  have hsymm : ∀ p : ℝ × (Fin n → ℝ), e.symm p = (Fin.cons p.1 p.2 : Fin (n + 1) → ℝ) := by
    intro p
    simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv, Fin.insertNth_zero']
  have heq : ∫ x in A n b 0, F 1 x =
      ∫ t, (Icc b (1 / 2)).indicator (fun t => I t (1 - t) n / t) t := by
    rw [← integral_indicator (isClosed_A n b 0).measurableSet,
      ← (hmp.symm e).integral_comp' (g := (A n b 0).indicator (F 1)), integral_prod _ hint2]
    congr 1; funext t
    rw [← inner_eq n b t]
    congr 1; funext y; rw [hsymm]
  have hii : Integrable (fun t => (Icc b (1 / 2)).indicator (fun t => I t (1 - t) n / t) t) := by
    have := hint2.integral_prod_left
    refine this.congr (Eventually.of_forall fun t => ?_)
    simp only
    rw [← inner_eq n b t]
    congr 1; funext y; rw [hsymm]
  rw [integrable_indicator_iff measurableSet_Icc] at hii
  refine ⟨?_, ?_⟩
  · rw [heq, integral_indicator measurableSet_Icc, intervalIntegral.integral_of_le (by linarith),
      integral_Icc_eq_integral_Ioc]
  · rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)]
    exact hii.mono_set Ioc_subset_Icc_self

lemma key (b : ℝ) (hb : 0 < b) (hb2 : b < 1 / 2) (n : ℕ) :
    I b 1 (n + 1) = (n + 2) * ∫ t in b..(1 / 2), I t (1 - t) n / t ∧
    IntervalIntegrable (fun t => I t (1 - t) n / t) volume b (1 / 2) := by
  obtain ⟨h1, h2⟩ := A0_integral n b hb hb2
  exact ⟨by rw [integral_Om_eq n b hb, h1], h2⟩

/-! ## Part (1) -/

theorem part1 (b : ℝ) (hb : 0 < b) (hb2 : b < 1 / 2) :
    ∫ t in b..(1 / 2), roughDensity t (1 - t) / t = roughDensity b 1 - 1 := by
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / b)
  have hNb : 1 < N * b := by rwa [div_lt_iff₀ hb] at hN
  have hD : roughDensity b 1 = ∑ n ∈ Finset.range (N + 1), I b 1 n / ((n + 1).factorial : ℝ) :=
    roughDensity_eq_sum b 1 hb (by linarith) (N + 1) (by push_cast; nlinarith)
  rw [hD, Finset.sum_range_succ', I_zero b 1 (by linarith)]
  simp only [zero_add, Nat.factorial_one, Nat.cast_one, inv_one, div_one, add_sub_cancel_right]
  have hcongr : ∀ t ∈ uIcc b (1 / 2), roughDensity t (1 - t) / t =
      ∑ n ∈ Finset.range N, ((1 : ℝ) / ((n + 1).factorial : ℝ)) * (I t (1 - t) n / t) := by
    intro t ht
    rw [uIcc_of_le (by linarith)] at ht
    have ht0 : 0 < t := by linarith [ht.1]
    rw [roughDensity_eq_sum t (1 - t) ht0 (by linarith [ht.2]) N (by nlinarith [ht.1]),
      Finset.sum_div]
    refine Finset.sum_congr rfl fun n _ => ?_
    ring
  rw [intervalIntegral.integral_congr hcongr, intervalIntegral.integral_finset_sum]
  · refine Finset.sum_congr rfl fun n _ => ?_
    rw [intervalIntegral.integral_const_mul, (key b hb hb2 n).1]
    rw [show (n + 1 + 1).factorial = (n + 2) * (n + 1).factorial from rfl]
    push_cast
    field_simp
  · intro n _
    exact (key b hb hb2 n).2.const_mul _

end ArtinPrimitiveRoots.RD

namespace ArtinPrimitiveRoots.RD

open Real MeasureTheory Set Filter Topology

/-! ## Part (2), analytic side: dyadic cubes and Fubini -/

/-- The open region of `j`-tuples of exponents. -/
def U (b c : ℝ) (j : ℕ) : Set (Fin j → ℝ) :=
  {t | (∀ i, b < t i) ∧ 1 < ∑ i, t i ∧ ∑ i, t i < c}

/-- Left end of a dyadic interval. -/
noncomputable def lo (m : ℕ) (k : ℤ) : ℝ := k / 2 ^ m

/-- Right end of a dyadic interval. -/
noncomputable def hi (m : ℕ) (k : ℤ) : ℝ := (k + 1) / 2 ^ m

/-- Half-open dyadic cube. -/
def Q {j : ℕ} (m : ℕ) (k : Fin j → ℤ) : Set (Fin j → ℝ) :=
  Set.pi univ fun i => Ioc (lo m (k i)) (hi m (k i))

/-- Closed dyadic cube. -/
def Qc {j : ℕ} (m : ℕ) (k : Fin j → ℤ) : Set (Fin j → ℝ) :=
  Set.pi univ fun i => Icc (lo m (k i)) (hi m (k i))

/-- Good cubes at level `m`. -/
noncomputable def G (b c : ℝ) (j m : ℕ) : Finset (Fin j → ℤ) := by
  classical
  exact (Fintype.piFinset fun _ => Finset.Icc (0 : ℤ) (2 ^ m * ⌈c⌉)).filter
    (fun k => Qc m k ⊆ U b c j)

/-- The density `∏ (t i)⁻¹`. -/
noncomputable def g {j : ℕ} (t : Fin j → ℝ) : ℝ := ∏ i, (t i)⁻¹

lemma mem_G {b c : ℝ} {j m : ℕ} {k : Fin j → ℤ} :
    k ∈ G b c j m ↔ (∀ i, 0 ≤ k i ∧ k i ≤ 2 ^ m * ⌈c⌉) ∧ Qc m k ⊆ U b c j := by
  classical
  simp [G, Fintype.mem_piFinset]

lemma two_pow_pos (m : ℕ) : (0 : ℝ) < 2 ^ m := by positivity

lemma mem_Ioc_iff_ceil (m : ℕ) (z : ℤ) (s : ℝ) :
    s ∈ Ioc (lo m z) (hi m z) ↔ z = ⌈2 ^ m * s⌉ - 1 := by
  have h2 := two_pow_pos m
  rw [mem_Ioc, lo, hi, div_lt_iff₀ h2, le_div_iff₀ h2, eq_sub_iff_add_eq, eq_comm,
    Int.ceil_eq_iff]
  push_cast
  constructor <;> rintro ⟨h1, h3⟩ <;> constructor <;> linarith

lemma mem_Q_iff {j m : ℕ} (k : Fin j → ℤ) (t : Fin j → ℝ) :
    t ∈ Q m k ↔ ∀ i, k i = ⌈2 ^ m * t i⌉ - 1 := by
  simp only [Q, Set.mem_pi, mem_univ, true_implies]
  exact forall_congr' fun i => mem_Ioc_iff_ceil m (k i) (t i)

lemma Q_disjoint {j m : ℕ} {k k' : Fin j → ℤ} (h : k ≠ k') : Disjoint (Q m k) (Q m k') := by
  rw [Set.disjoint_left]
  intro t h1 h2
  rw [mem_Q_iff] at h1 h2
  exact h (funext fun i => (h1 i).trans (h2 i).symm)

lemma Q_subset_Qc {j m : ℕ} (k : Fin j → ℤ) : Q m k ⊆ Qc m k :=
  Set.pi_mono fun _ _ => Ioc_subset_Icc_self

lemma isOpen_U (b c : ℝ) (j : ℕ) : IsOpen (U b c j) := by
  have h1 : IsOpen {t : Fin j → ℝ | ∀ i, b < t i} := by
    simp only [setOf_forall]
    exact isOpen_iInter_of_finite fun i => isOpen_lt continuous_const (continuous_apply i)
  have hs : Continuous fun t : Fin j → ℝ => ∑ i, t i :=
    continuous_finset_sum _ fun i _ => continuous_apply i
  exact h1.inter ((isOpen_lt continuous_const hs).inter (isOpen_lt hs continuous_const))

lemma U_coord_lt {b c : ℝ} (hb : 0 ≤ b) {j : ℕ} {t : Fin j → ℝ} (ht : t ∈ U b c j) (i : Fin j) :
    0 < t i ∧ t i < c := by
  have hpos : ∀ i, 0 < t i := fun i => lt_of_le_of_lt hb (ht.1 i)
  refine ⟨hpos i, ?_⟩
  have : t i ≤ ∑ i, t i := Finset.single_le_sum (fun i _ => (hpos i).le) (Finset.mem_univ i)
  linarith [ht.2.2]

/-- The cube index of a point at level `m`. -/
noncomputable def idx {j : ℕ} (m : ℕ) (t : Fin j → ℝ) : Fin j → ℤ := fun i => ⌈2 ^ m * t i⌉ - 1

lemma mem_Q_idx {j : ℕ} (m : ℕ) (t : Fin j → ℝ) : t ∈ Q m (idx m t) := by
  rw [mem_Q_iff]; intro i; rfl

lemma idx_bounds {b c : ℝ} (hb : 0 ≤ b) {j : ℕ} (m : ℕ) {t : Fin j → ℝ} (ht : t ∈ U b c j)
    (i : Fin j) : 0 ≤ idx m t i ∧ idx m t i ≤ 2 ^ m * ⌈c⌉ := by
  obtain ⟨h0, hc⟩ := U_coord_lt hb ht i
  have h2 := two_pow_pos m
  constructor
  · have : (0 : ℤ) < ⌈2 ^ m * t i⌉ := Int.lt_ceil.2 (by push_cast; positivity)
    simp only [idx]; omega
  · have : ⌈2 ^ m * t i⌉ ≤ 2 ^ m * ⌈c⌉ := by
      rw [Int.ceil_le]; push_cast
      exact mul_le_mul_of_nonneg_left (hc.le.trans (Int.le_ceil c)) h2.le
    simp only [idx]; omega

/-- Union of the good cubes at level `m`. -/
def Ucube (b c : ℝ) (j m : ℕ) : Set (Fin j → ℝ) := ⋃ k ∈ G b c j m, Q m k

lemma Ucube_subset (b c : ℝ) (j m : ℕ) : Ucube b c j m ⊆ U b c j := by
  intro t ht
  simp only [Ucube, mem_iUnion] at ht
  obtain ⟨k, hk, htk⟩ := ht
  exact (mem_G.1 hk).2 (Q_subset_Qc k htk)

lemma Qc_mono {j : ℕ} (m : ℕ) (k : Fin j → ℤ) (t : Fin j → ℝ) (ht : t ∈ Q m k) :
    Qc (m + 1) (idx (m + 1) t) ⊆ Qc m k := by
  intro s hs i _
  have hti := (mem_Q_iff k t).1 ht i
  have hsi := hs i (mem_univ i)
  have h2 := two_pow_pos m
  have htQ := ht i (mem_univ i)
  simp only [lo, hi, mem_Icc, mem_Ioc] at hsi htQ ⊢
  rw [div_lt_iff₀ h2] at htQ
  rw [le_div_iff₀ h2] at htQ
  have e2 : (2 : ℝ) ^ (m + 1) = 2 * 2 ^ m := by ring
  have hA : 2 * k i + 1 ≤ ⌈2 ^ (m + 1) * t i⌉ := by
    rw [Int.add_one_le_iff, Int.lt_ceil]; push_cast; rw [e2]; nlinarith
  have hB : ⌈2 ^ (m + 1) * t i⌉ ≤ 2 * k i + 2 := by
    rw [Int.ceil_le]; push_cast; rw [e2]; nlinarith
  have hA' : (2 * k i + 1 : ℝ) ≤ (⌈2 ^ (m + 1) * t i⌉ : ℝ) := by exact_mod_cast hA
  have hB' : (⌈2 ^ (m + 1) * t i⌉ : ℝ) ≤ 2 * k i + 2 := by exact_mod_cast hB
  simp only [idx] at hsi
  push_cast at hsi
  obtain ⟨hs1, hs2⟩ := hsi
  rw [div_le_iff₀ (two_pow_pos _)] at hs1
  rw [le_div_iff₀ (two_pow_pos _)] at hs2
  rw [e2] at hA' hB' hs1 hs2
  constructor
  · rw [div_le_iff₀ h2]; linarith
  · rw [le_div_iff₀ h2]; linarith

lemma Ucube_mono (b c : ℝ) (hb : 0 ≤ b) (j : ℕ) : Monotone (Ucube b c j) := by
  refine monotone_nat_of_le_succ fun m => ?_
  intro t ht
  have htU := Ucube_subset b c j m ht
  simp only [Ucube, mem_iUnion] at ht ⊢
  obtain ⟨k, hk, htk⟩ := ht
  refine ⟨idx (m + 1) t, ?_, mem_Q_idx _ t⟩
  rw [mem_G]
  exact ⟨fun i => idx_bounds hb (m + 1) htU i, (Qc_mono m k t htk).trans (mem_G.1 hk).2⟩

lemma iUnion_Ucube (b c : ℝ) (hb : 0 ≤ b) (j : ℕ) : ⋃ m, Ucube b c j m = U b c j := by
  apply Subset.antisymm (iUnion_subset fun m => Ucube_subset b c j m)
  intro t ht
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 (isOpen_U b c j) t ht
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one hr (by norm_num : (1 / 2 : ℝ) < 1)
  simp only [mem_iUnion, Ucube]
  refine ⟨m, idx m t, ?_, mem_Q_idx m t⟩
  rw [mem_G]
  refine ⟨fun i => idx_bounds hb m ht i, ?_⟩
  intro s hs
  apply hball
  rw [Metric.mem_ball, dist_pi_lt_iff hr]
  intro i
  have hsi := hs i (mem_univ i)
  have hti := Q_subset_Qc _ (mem_Q_idx m t) i (mem_univ i)
  simp only [mem_Icc] at hsi hti
  have hw : hi m (idx m t i) - lo m (idx m t i) = (1 / 2) ^ m := by
    simp only [hi, lo]; rw [one_div_pow]; field_simp; ring
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith [hsi.1, hsi.2, hti.1, hti.2]

lemma measurableSet_Q {j : ℕ} (m : ℕ) (k : Fin j → ℤ) : MeasurableSet (Q m k) :=
  MeasurableSet.univ_pi fun _ => measurableSet_Ioc

lemma measurableSet_Ucube (b c : ℝ) (j m : ℕ) : MeasurableSet (Ucube b c j m) :=
  Finset.measurableSet_biUnion _ fun k _ => measurableSet_Q m k

lemma measurable_g (j : ℕ) : Measurable (fun t : Fin j → ℝ => g t) :=
  Finset.measurable_prod _ fun i _ => (measurable_pi_apply i).inv

lemma g_nonneg_of_pos {j : ℕ} (t : Fin j → ℝ) (h : ∀ i, 0 < t i) : 0 ≤ g t :=
  Finset.prod_nonneg fun i _ => (inv_pos.2 (h i)).le

lemma integrableOn_g_U (b c : ℝ) (hb : 0 < b) (j : ℕ) : IntegrableOn g (U b c j) := by
  have hsub : U b c j ⊆ Set.pi univ (fun _ => Icc b c) := fun t ht i _ =>
    ⟨(ht.1 i).le, (U_coord_lt hb.le ht i).2.le⟩
  have hfin : volume (U b c j) ≠ ⊤ :=
    ne_top_of_le_ne_top ((isCompact_univ_pi fun _ => isCompact_Icc).measure_lt_top).ne
      (measure_mono hsub)
  refine Measure.integrableOn_of_bounded (M := b⁻¹ ^ j) hfin
    (measurable_g j).aestronglyMeasurable ?_
  refine (ae_restrict_iff' (isOpen_U b c j).measurableSet).2 (Eventually.of_forall fun t ht => ?_)
  have hpos : ∀ i, 0 < t i := fun i => (U_coord_lt hb.le ht i).1
  rw [Real.norm_eq_abs, abs_of_nonneg (g_nonneg_of_pos t hpos)]
  calc g t ≤ ∏ _i : Fin j, b⁻¹ :=
        Finset.prod_le_prod (fun i _ => (inv_pos.2 (hpos i)).le) fun i _ =>
          inv_anti₀ hb (ht.1 i).le
    _ = b⁻¹ ^ j := by simp

lemma integral_Q {j : ℕ} (m : ℕ) (k : Fin j → ℤ) (hk : ∀ i, 0 < lo m (k i)) :
    ∫ t in Q m k, g t = ∏ i, log (hi m (k i) / lo m (k i)) := by
  have hle : ∀ i, lo m (k i) ≤ hi m (k i) := fun i => by
    simp only [lo, hi]; gcongr; linarith
  rw [Q, volume_pi, Measure.restrict_pi_pi]
  unfold g
  rw [integral_fintype_prod_eq_prod (f := fun _ x => x⁻¹)]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← intervalIntegral.integral_of_le (hle i),
    integral_inv_of_pos (hk i) ((hk i).trans_le (hle i))]

lemma lo_pos_of_G {b c : ℝ} (hb : 0 ≤ b) {j m : ℕ} {k : Fin j → ℤ} (hk : k ∈ G b c j m)
    (i : Fin j) : b < lo m (k i) := by
  have hmem : (fun i => lo m (k i)) ∈ Qc m k := fun i _ => by
    simp only [mem_Icc, le_refl, true_and, lo, hi]; gcongr; linarith
  exact ((mem_G.1 hk).2 hmem).1 i

lemma lo_lt_hi (m : ℕ) (z : ℤ) : lo m z < hi m z := by
  simp only [lo, hi]; gcongr; linarith

lemma tendsto_cubes (b c : ℝ) (hb : 0 < b) (j : ℕ) :
    Tendsto (fun m => ∑ k ∈ G b c j m, ∏ i, log (hi m (k i) / lo m (k i))) atTop
      (𝓝 (∫ t in U b c j, g t)) := by
  have h := tendsto_setIntegral_of_monotone (μ := volume) (f := g)
    (measurableSet_Ucube b c j) (Ucube_mono b c hb.le j)
    (by rw [iUnion_Ucube b c hb.le j]; exact integrableOn_g_U b c hb j)
  rw [iUnion_Ucube b c hb.le j] at h
  refine h.congr fun m => ?_
  rw [Ucube, integral_biUnion_finset _ (fun k _ => measurableSet_Q m k)]
  · exact Finset.sum_congr rfl fun k hk =>
      integral_Q m k fun i => hb.trans (lo_pos_of_G hb.le hk i)
  · intro k _ k' _ hkk'
    exact Q_disjoint hkk'
  · intro k _
    exact (integrableOn_g_U b c hb j).mono_set ((Set.subset_biUnion_of_mem (u := fun k => Q m k)
      (by assumption)).trans (Ucube_subset b c j m))

lemma integral_U_nonneg (b c : ℝ) (hb : 0 ≤ b) (j : ℕ) : 0 ≤ ∫ t in U b c j, g t :=
  setIntegral_nonneg (isOpen_U b c j).measurableSet fun t ht =>
    g_nonneg_of_pos t fun i => (U_coord_lt hb ht i).1

/-! ### Fubini in the last coordinate -/

/-- The region with strict lower bounds. -/
def Om' (b : ℝ) (n : ℕ) : Set (Fin n → ℝ) := {y | (∀ i, b < y i) ∧ ∑ i, y i ≤ 1 - b}

lemma I_eq_Om' (b : ℝ) (n : ℕ) : I b 1 n = ∫ y in Om' b n, F 1 y := by
  unfold I
  refine setIntegral_congr_set ?_
  rw [ae_eq_set]
  constructor
  · refine measure_mono_null (t := ⋃ i, {y : Fin n → ℝ | LinearMap.proj (R := ℝ) i y = b}) ?_ ?_
    · rintro y ⟨⟨h1, h2⟩, h3⟩
      have h4 : ¬ ∀ i, b < y i := fun h => h3 ⟨h, h2⟩
      push_neg at h4
      obtain ⟨i, hi⟩ := h4
      simp only [mem_iUnion, mem_setOf_eq, LinearMap.coe_proj, Function.eval]
      exact ⟨i, le_antisymm hi (h1 i)⟩
    · refine measure_iUnion_null fun i => null_level _ ?_ b
      intro h
      have := congrArg (fun f => f (Pi.single i 1)) h
      simp at this
  · refine measure_mono_null ?_ (measure_empty (μ := volume))
    rintro y ⟨⟨h1, h2⟩, h3⟩
    exact h3 ⟨fun i => (h1 i).le, h2⟩

lemma log_lower (b c w : ℝ) (hb : 0 < b) (hc : 1 < c) (hw : b ≤ w) :
    b / (b + c - 1) * (c - 1) / w ≤ log ((c - 1 + w) / w) := by
  have hw0 : 0 < w := hb.trans_le hw
  have h1 := Real.one_sub_inv_le_log_of_pos (x := (c - 1 + w) / w) (by positivity)
  refine le_trans ?_ h1
  rw [inv_div, div_le_iff₀ hw0]
  have hcw : 0 < c - 1 + w := by linarith
  rw [show (1 - w / (c - 1 + w)) * w = (c - 1) * w / (c - 1 + w) by field_simp; ring]
  rw [le_div_iff₀ hcw, div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
  nlinarith [mul_le_mul_of_nonneg_left hw (by linarith : (0 : ℝ) ≤ c - 1)]

lemma fubini_lower (b c : ℝ) (hb : 0 < b) (hb2 : b < 1 / 2) (hc : 1 < c) (n : ℕ) :
    b / (b + c - 1) * (c - 1) * I b 1 n ≤ ∫ t in U b c (n + 1), g t := by
  set θ := b / (b + c - 1) * (c - 1) with hθ
  have hθ0 : 0 ≤ θ := by rw [hθ]; apply mul_nonneg (div_nonneg hb.le (by linarith)); linarith
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) (Fin.last n)
  have hmp : MeasurePreserving e volume (volume.prod volume) :=
    volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) (Fin.last n)
  have hsymm : ∀ p : ℝ × (Fin n → ℝ), e.symm p = (Fin.snoc p.2 p.1 : Fin (n + 1) → ℝ) := by
    intro p
    simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv, Fin.insertNth_last']
  have hint : Integrable ((U b c (n + 1)).indicator g) volume := by
    rw [integrable_indicator_iff (isOpen_U b c (n + 1)).measurableSet]
    exact integrableOn_g_U b c hb (n + 1)
  have hint2 : Integrable (fun p => (U b c (n + 1)).indicator g (e.symm p)) (volume.prod volume) :=
    (hmp.symm e).integrable_comp_emb e.symm.measurableEmbedding |>.2 hint
  have hΦ : ∫ t in U b c (n + 1), g t =
      ∫ y, ∫ s, (U b c (n + 1)).indicator g (Fin.snoc y s : Fin (n + 1) → ℝ) := by
    rw [← integral_indicator (isOpen_U b c (n + 1)).measurableSet,
      ← (hmp.symm e).integral_comp' (g := (U b c (n + 1)).indicator g), integral_prod_symm _ hint2]
    simp_rw [hsymm]
  have hinner_int : Integrable
      (fun y => ∫ s, (U b c (n + 1)).indicator g (Fin.snoc y s : Fin (n + 1) → ℝ)) := by
    have := hint2.integral_prod_right
    simpa only [hsymm] using this
  -- pointwise lower bound
  have hpt : ∀ y : Fin n → ℝ, (Om' b n).indicator (fun y => θ * F 1 y) y ≤
      ∫ s, (U b c (n + 1)).indicator g (Fin.snoc y s : Fin (n + 1) → ℝ) := by
    intro y
    by_cases hy : y ∈ Om' b n
    · rw [indicator_of_mem hy]
      have hypos : ∀ i, 0 < y i := fun i => hb.trans (hy.1 i)
      set σ := ∑ i, y i
      have hw : b ≤ 1 - σ := by linarith [hy.2]
      have hset : ∀ s, (Fin.snoc y s : Fin (n + 1) → ℝ) ∈ U b c (n + 1) ↔
          s ∈ Ioo (1 - σ) (c - σ) := by
        intro s
        simp only [U, mem_setOf_eq, Fin.forall_fin_succ', Fin.snoc_castSucc, Fin.snoc_last,
          Fin.sum_univ_castSucc, mem_Ioo]
        constructor
        · rintro ⟨⟨_, _⟩, h1, h2⟩; constructor <;> linarith
        · rintro ⟨h1, h2⟩; exact ⟨⟨hy.1, by linarith⟩, by linarith, by linarith⟩
      have hg : ∀ s, g (Fin.snoc y s : Fin (n + 1) → ℝ) = (∏ i, (y i)⁻¹) * s⁻¹ := by
        intro s; simp [g, Fin.prod_univ_castSucc, mul_comm]
      have : ∀ s, (U b c (n + 1)).indicator g (Fin.snoc y s : Fin (n + 1) → ℝ) =
          (Ioo (1 - σ) (c - σ)).indicator (fun s => (∏ i, (y i)⁻¹) * s⁻¹) s := by
        intro s
        by_cases hs : s ∈ Ioo (1 - σ) (c - σ)
        · rw [indicator_of_mem ((hset s).2 hs), indicator_of_mem hs, hg]
        · rw [indicator_of_notMem (fun h => hs ((hset s).1 h)), indicator_of_notMem hs]
      simp_rw [this]
      rw [integral_indicator measurableSet_Ioo, integral_const_mul,
        ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by linarith),
        integral_inv_of_pos (by linarith) (by linarith)]
      have hlog := log_lower b c (1 - σ) hb hc hw
      rw [show c - 1 + (1 - σ) = c - σ by ring] at hlog
      have hP : 0 ≤ ∏ i, (y i)⁻¹ := Finset.prod_nonneg fun i _ => (inv_pos.2 (hypos i)).le
      calc θ * F 1 y = (∏ i, (y i)⁻¹) * (θ / (1 - σ)) := by
            simp only [F]; ring
        _ ≤ (∏ i, (y i)⁻¹) * log ((c - σ) / (1 - σ)) := by
            apply mul_le_mul_of_nonneg_left _ hP
            simpa [hθ] using hlog
    · rw [indicator_of_notMem hy]
      apply integral_nonneg
      intro s
      apply indicator_nonneg
      intro t ht
      exact g_nonneg_of_pos t fun i => (U_coord_lt hb.le ht i).1
  have hOm'int : Integrable ((Om' b n).indicator (fun y => θ * F 1 y)) := by
    have hm : MeasurableSet (Om' b n) := by
      have : Om' b n = {y : Fin n → ℝ | ∀ i, b < y i} ∩ {y | ∑ i, y i ≤ 1 - b} := rfl
      rw [this]
      refine MeasurableSet.inter ?_ ?_
      · simp only [setOf_forall]
        exact MeasurableSet.iInter fun i => measurableSet_lt measurable_const (measurable_pi_apply i)
      · exact measurableSet_le (Finset.measurable_sum _ fun i _ => measurable_pi_apply i)
          measurable_const
    rw [integrable_indicator_iff hm]
    refine ((integrableOn_F b 1 hb n).mono_set ?_).const_mul θ
    intro y hy; exact ⟨fun i => (hy.1 i).le, hy.2⟩
  calc θ * I b 1 n = ∫ y, (Om' b n).indicator (fun y => θ * F 1 y) y := by
        rw [I_eq_Om', integral_indicator, integral_const_mul]
        have : Om' b n = {y : Fin n → ℝ | ∀ i, b < y i} ∩ {y | ∑ i, y i ≤ 1 - b} := rfl
        rw [this]
        refine MeasurableSet.inter ?_ ?_
        · simp only [setOf_forall]
          exact MeasurableSet.iInter fun i => measurableSet_lt measurable_const
            (measurable_pi_apply i)
        · exact measurableSet_le (Finset.measurable_sum _ fun i _ => measurable_pi_apply i)
            measurable_const
    _ ≤ ∫ y, ∫ s, (U b c (n + 1)).indicator g (Fin.snoc y s : Fin (n + 1) → ℝ) :=
        integral_mono hOm'int hinner_int hpt
    _ = ∫ t in U b c (n + 1), g t := hΦ.symm

end ArtinPrimitiveRoots.RD

namespace ArtinPrimitiveRoots.RD

open Real MeasureTheory Set Filter Topology

/-! ## Part (2), arithmetic side -/

/-- Primes in `(x^α, x^β]`, in the form of the Mertens black box. -/
noncomputable def Pr (x α β : ℝ) : Finset ℕ :=
  (Finset.range (⌊x ^ β⌋₊ + 1)).filter (fun p : ℕ => p.Prime ∧ x ^ α < p)

/-- Reciprocal sum over `Pr`. -/
noncomputable def σx (x α β : ℝ) : ℝ := ∑ p ∈ Pr x α β, (1 : ℝ) / p

/-- The sieve primes `p ≤ y`. -/
noncomputable def Ps (y : ℝ) : Finset ℕ := (Finset.range (⌊y⌋₊ + 1)).filter Nat.Prime

/-- The rough-number log-weighted count over `(x, x^c]`. -/
noncomputable def Ssum (x b c : ℝ) : ℝ :=
  ∑ n ∈ (Finset.Ioc ⌊x⌋₊ ⌊x ^ c⌋₊).filter (fun n => ∀ p ∈ Ps (x ^ b), ¬ p ∣ n), (1 : ℝ) / n

lemma mem_Pr {x α β : ℝ} (hx : 0 < x) {p : ℕ} :
    p ∈ Pr x α β ↔ p.Prime ∧ x ^ α < p ∧ (p : ℝ) ≤ x ^ β := by
  simp only [Pr, Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff]
  rw [Nat.le_floor_iff (by positivity)]
  tauto

lemma rpow_lt_iff_log {x α : ℝ} (hx : 1 < x) {y : ℝ} (hy : 0 < y) :
    x ^ α < y ↔ α < log y / log x := by
  rw [lt_div_iff₀ (log_pos hx), ← log_lt_log_iff (by positivity) hy, log_rpow (by linarith)]

lemma le_rpow_iff_log {x β : ℝ} (hx : 1 < x) {y : ℝ} (hy : 0 < y) :
    y ≤ x ^ β ↔ log y / log x ≤ β := by
  rw [div_le_iff₀ (log_pos hx), ← log_le_log_iff hy (by positivity), log_rpow (by linarith)]

/-! ### Fibres of the product map -/

lemma ofFn_perm_primeFactorsList {j n : ℕ} (t : Fin j → ℕ) (hp : ∀ i, (t i).Prime)
    (hn : ∏ i, t i = n) : (List.ofFn t).Perm n.primeFactorsList := by
  apply Nat.primeFactorsList_unique
  · rw [List.prod_ofFn, hn]
  · intro p hp'
    rw [List.mem_ofFn] at hp'
    obtain ⟨i, rfl⟩ := hp'
    exact hp i

lemma length_eq_of_prod {j n : ℕ} (t : Fin j → ℕ) (hp : ∀ i, (t i).Prime)
    (hn : ∏ i, t i = n) : j = n.primeFactorsList.length := by
  have := (ofFn_perm_primeFactorsList t hp hn).length_eq
  rwa [List.length_ofFn] at this

lemma fiber_card_le {j n : ℕ} (T : Finset (Fin j → ℕ)) (hT : ∀ t ∈ T, ∀ i, (t i).Prime) :
    (T.filter (fun t => ∏ i, t i = n)).card ≤ j.factorial := by
  have hcard : (Finset.univ : Finset (Equiv.Perm (Fin j))).card = j.factorial := by
    rw [Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
  rw [← hcard]
  refine Finset.card_le_card_of_injOn (fun t => Tuple.sort t) (fun _ _ => Finset.mem_univ _) ?_
  intro t ht t' ht' hsort
  simp only [Finset.coe_filter, mem_setOf_eq] at ht ht'
  simp only at hsort
  have h1 := ofFn_perm_primeFactorsList t (hT t ht.1) ht.2
  have h2 := ofFn_perm_primeFactorsList t' (hT t' ht'.1) ht'.2
  set σ := Tuple.sort t
  have hm1 : Monotone (t ∘ σ) := Tuple.monotone_sort t
  have hm2 : Monotone (t' ∘ σ) := by rw [hsort]; exact Tuple.monotone_sort t'
  have hperm : (List.ofFn (t ∘ σ)).Perm (List.ofFn (t' ∘ σ)) :=
    ((σ.ofFn_comp_perm t).trans h1).trans (h2.symm.trans (σ.ofFn_comp_perm t').symm)
  have heq : t ∘ σ = t' ∘ σ :=
    List.ofFn_injective (hperm.eq_of_pairwise' hm1.sortedLE_ofFn.pairwise
      hm2.sortedLE_ofFn.pairwise)
  funext i
  have := congrFun heq (σ.symm i)
  simpa using this

lemma fiber_bound (x b c : ℝ) (hx : 0 ≤ x) (J : ℕ) (T : (j : ℕ) → Finset (Fin j → ℕ))
    (hT : ∀ j, ∀ t ∈ T j, (∀ i, (t i).Prime ∧ x ^ b < (t i : ℝ)) ∧
      x < ∏ i, (t i : ℝ) ∧ ∏ i, (t i : ℝ) ≤ x ^ c) :
    ∑ j ∈ Finset.range J, (1 / (j.factorial : ℝ)) * ∑ t ∈ T j, ∏ i, (1 : ℝ) / (t i) ≤
      Ssum x b c := by
  set R := (Finset.Ioc ⌊x⌋₊ ⌊x ^ c⌋₊).filter (fun n => ∀ p ∈ Ps (x ^ b), ¬ p ∣ n)
  have hmaps : ∀ j, ∀ t ∈ T j, ∏ i, t i ∈ R := by
    intro j t ht
    obtain ⟨hp, h1, h2⟩ := hT j t ht
    simp only [R, Finset.mem_filter, Finset.mem_Ioc]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [Nat.floor_lt hx]; exact_mod_cast h1
    · rw [Nat.le_floor_iff (by positivity)]; exact_mod_cast h2
    · intro p hpP hdvd
      simp only [Ps, Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff] at hpP
      obtain ⟨hpl, hpp⟩ := hpP
      rw [Nat.le_floor_iff (by positivity)] at hpl
      obtain ⟨i, -, hi⟩ := (Prime.dvd_finset_prod_iff hpp.prime _).1 hdvd
      have := (Nat.prime_dvd_prime_iff_eq hpp (hp i).1).1 hi
      have h3 := (hp i).2
      rw [← this] at h3
      linarith
  have hfib : ∀ j, ∑ t ∈ T j, ∏ i, (1 : ℝ) / (t i) =
      ∑ n ∈ R, ((T j).filter (fun t => ∏ i, t i = n)).card * ((1 : ℝ) / n) := by
    intro j
    rw [← Finset.sum_fiberwise_of_maps_to (hmaps j)]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun t ht => ?_
    rw [Finset.mem_filter] at ht
    rw [← ht.2]; push_cast
    simp [Finset.prod_inv_distrib]
  simp_rw [hfib, Finset.mul_sum]
  rw [Finset.sum_comm]
  unfold Ssum
  refine Finset.sum_le_sum fun n hn => ?_
  have hn0 : (0 : ℝ) ≤ 1 / n := by positivity
  calc ∑ j ∈ Finset.range J, 1 / (j.factorial : ℝ) *
        (((T j).filter (fun t => ∏ i, t i = n)).card * (1 / n))
      = (∑ j ∈ Finset.range J, (((T j).filter (fun t => ∏ i, t i = n)).card : ℝ) /
          j.factorial) * (1 / n) := by
        rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun j _ => ?_; ring
    _ ≤ 1 * (1 / n) := by
        apply mul_le_mul_of_nonneg_right _ hn0
        set L := n.primeFactorsList.length
        calc ∑ j ∈ Finset.range J, (((T j).filter (fun t => ∏ i, t i = n)).card : ℝ) /
              j.factorial ≤ ∑ j ∈ Finset.range J, (if j = L then (1 : ℝ) else 0) := by
              refine Finset.sum_le_sum fun j _ => ?_
              split_ifs with hjL
              · rw [div_le_one (by positivity)]
                exact_mod_cast fiber_card_le (T j) fun t ht i => ((hT j t ht).1 i).1
              · have : (T j).filter (fun t => ∏ i, t i = n) = ∅ := by
                  rw [Finset.filter_eq_empty_iff]
                  intro t ht hprod
                  exact hjL (length_eq_of_prod t (fun i => ((hT j t ht).1 i).1) hprod)
                rw [this]; simp
          _ ≤ 1 := by
              rw [Finset.sum_ite_eq']; split_ifs <;> norm_num
    _ = 1 / n := one_mul _

/-! ### The lower bound by cubes -/

lemma lower_arith (b c : ℝ) (hb : 0 < b) (x : ℝ) (hx : 1 < x) (J m : ℕ) :
    ∑ j ∈ Finset.range J, (1 / (j.factorial : ℝ)) *
      ∑ k ∈ G b c j m, ∏ i, σx x (lo m (k i)) (hi m (k i)) ≤ Ssum x b c := by
  classical
  have hx0 : 0 < x := by linarith
  set T : (j : ℕ) → Finset (Fin j → ℕ) := fun j =>
    (G b c j m).biUnion fun k => Fintype.piFinset fun i => Pr x (lo m (k i)) (hi m (k i))
  -- the exponent vector of a tuple
  have hτ : ∀ j (k : Fin j → ℤ) (t : Fin j → ℕ),
      t ∈ Fintype.piFinset (fun i => Pr x (lo m (k i)) (hi m (k i))) →
      (∀ i, (t i).Prime) ∧ (fun i => log (t i) / log x) ∈ Q m k := by
    intro j k t ht
    rw [Fintype.mem_piFinset] at ht
    refine ⟨fun i => ((mem_Pr hx0).1 (ht i)).1, fun i _ => ?_⟩
    obtain ⟨hp, h1, h2⟩ := (mem_Pr hx0).1 (ht i)
    have hp0 : (0 : ℝ) < t i := by exact_mod_cast hp.pos
    exact ⟨(rpow_lt_iff_log hx hp0).1 h1, (le_rpow_iff_log hx hp0).1 h2⟩
  have hsum : ∀ j, ∑ k ∈ G b c j m, ∏ i, σx x (lo m (k i)) (hi m (k i)) =
      ∑ t ∈ T j, ∏ i, (1 : ℝ) / (t i) := by
    intro j
    rw [Finset.sum_biUnion]
    · refine Finset.sum_congr rfl fun k _ => ?_
      unfold σx
      exact Finset.prod_univ_sum _ _
    · intro k _ k' _ hkk'
      rw [Function.onFun, Finset.disjoint_left]
      intro t h1 h2
      exact Set.disjoint_left.1 (Q_disjoint hkk') (hτ j k t h1).2 (hτ j k' t h2).2
  simp_rw [hsum]
  apply fiber_bound x b c hx0.le J T
  intro j t ht
  simp only [T, Finset.mem_biUnion] at ht
  obtain ⟨k, hk, htk⟩ := ht
  obtain ⟨hp, hQ⟩ := hτ j k t htk
  have hU := (mem_G.1 hk).2 (Q_subset_Qc k hQ)
  have hpos : ∀ i, (0 : ℝ) < t i := fun i => by exact_mod_cast (hp i).pos
  have hlogprod : log (∏ i, (t i : ℝ)) = ∑ i, log (t i) := by
    rw [Real.log_prod]; intro i _; exact (hpos i).ne'
  have hprodpos : 0 < ∏ i, (t i : ℝ) := Finset.prod_pos fun i _ => hpos i
  have hlx := log_pos hx
  have hsumτ : ∑ i, log (t i : ℝ) / log x = log (∏ i, (t i : ℝ)) / log x := by
    rw [hlogprod, Finset.sum_div]
  refine ⟨fun i => ⟨hp i, (rpow_lt_iff_log hx (hpos i)).2 (hU.1 i)⟩, ?_, ?_⟩
  · have h1 := hU.2.1
    simp only at h1
    rw [hsumτ, lt_div_iff₀ hlx, one_mul] at h1
    exact (log_lt_log_iff hx0 hprodpos).1 h1
  · have h2 := hU.2.2
    simp only at h2
    rw [hsumτ] at h2
    exact ((le_rpow_iff_log hx hprodpos).2 h2.le)

/-! ### The harmonic estimate -/

lemma harm (K M : ℕ) (hK : 1 ≤ K) (hKM : K ≤ M) :
    log (M + 1) - log (K + 1) ≤ ∑ m ∈ Finset.Ioc K M, (1 : ℝ) / m ∧
      ∑ m ∈ Finset.Ioc K M, (1 : ℝ) / m ≤ log M - log K := by
  induction M, hKM using Nat.le_induction with
  | base => simp
  | succ M hKM ih =>
    rw [Finset.sum_Ioc_succ_top hKM]
    have hM : (1 : ℝ) ≤ M := by exact_mod_cast hK.trans hKM
    have h1 : log ((M : ℝ) + 1 + 1) - log (M + 1) ≤ 1 / (M + 1) := by
      rw [← log_div (by positivity) (by positivity)]
      have := Real.log_le_sub_one_of_pos (x := ((M : ℝ) + 1 + 1) / (M + 1)) (by positivity)
      have h' : ((M : ℝ) + 1 + 1) / (M + 1) - 1 = 1 / (M + 1) := by field_simp; ring
      linarith
    have h2 : 1 / ((M : ℝ) + 1) ≤ log (M + 1) - log M := by
      rw [← log_div (by positivity) (by positivity)]
      have := Real.one_sub_inv_le_log_of_pos (x := ((M : ℝ) + 1) / M) (by positivity)
      have h' : 1 - (((M : ℝ) + 1) / M)⁻¹ = 1 / (M + 1) := by field_simp; ring
      linarith
    push_cast
    constructor <;> linarith [ih.1, ih.2]

/-- Reindexing multiples of `d`. -/
lemma sum_multiples (A B d : ℕ) (hd : 0 < d) (f : ℕ → ℝ) :
    ∑ n ∈ (Finset.Ioc A B).filter (d ∣ ·), f n = ∑ m ∈ Finset.Ioc (A / d) (B / d), f (d * m) := by
  have himg : (Finset.Ioc (A / d) (B / d)).image (d * ·) = (Finset.Ioc A B).filter (d ∣ ·) := by
    ext n
    simp only [Finset.mem_image, Finset.mem_Ioc, Finset.mem_filter]
    constructor
    · rintro ⟨m, ⟨h1, h2⟩, rfl⟩
      refine ⟨⟨?_, ?_⟩, dvd_mul_right d m⟩
      · rw [Nat.div_lt_iff_lt_mul hd] at h1; linarith [mul_comm m d]
      · rw [Nat.le_div_iff_mul_le hd] at h2; linarith [mul_comm m d]
    · rintro ⟨⟨h1, h2⟩, ⟨m, rfl⟩⟩
      refine ⟨m, ⟨?_, ?_⟩, rfl⟩
      · rw [Nat.div_lt_iff_lt_mul hd]; linarith [mul_comm m d]
      · rw [Nat.le_div_iff_mul_le hd]; linarith [mul_comm m d]
  rw [← himg, Finset.sum_image]
  intro m _ m' _ h
  exact Nat.eq_of_mul_eq_mul_left hd h

lemma E_bound (x c : ℝ) (hc : 1 < c) (hx : 1 ≤ x) (d : ℕ) (hd : 1 ≤ d) (hdx : 2 * (d : ℝ) ≤ x) :
    |(∑ n ∈ (Finset.Ioc ⌊x⌋₊ ⌊x ^ c⌋₊).filter (d ∣ ·), (1 : ℝ) / n) - (c - 1) * log x / d| ≤
      2 / x := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hx0 : 0 < x := by linarith
  rw [sum_multiples _ _ d hd]
  set a := x / d with ha
  set X := x ^ c / d with hX
  have ha2 : 2 ≤ a := by rw [ha, le_div_iff₀ hd0]; linarith
  have hxc : x ≤ x ^ c := by
    calc x = x ^ (1 : ℝ) := (rpow_one x).symm
      _ ≤ x ^ c := rpow_le_rpow_of_exponent_le hx hc.le
  have haX : a ≤ X := by rw [ha, hX]; gcongr
  have hK : ⌊x⌋₊ / d = ⌊a⌋₊ := by rw [ha, Nat.floor_div_natCast]
  have hM : ⌊x ^ c⌋₊ / d = ⌊X⌋₊ := by rw [hX, Nat.floor_div_natCast]
  rw [hK, hM]
  set K := ⌊a⌋₊
  set M := ⌊X⌋₊
  have hK1 : 1 ≤ K := Nat.le_floor (by push_cast; linarith)
  have hKM : K ≤ M := Nat.floor_le_floor haX
  have hKa : (K : ℝ) ≤ a := Nat.floor_le (by linarith)
  have haK : a < K + 1 := Nat.lt_floor_add_one a
  have hMX : (M : ℝ) ≤ X := Nat.floor_le (by linarith)
  have hXM : X < M + 1 := Nat.lt_floor_add_one X
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hK1
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hK1.trans hKM
  obtain ⟨hlow, hup⟩ := harm K M hK1 hKM
  have hsum : ∑ m ∈ Finset.Ioc K M, (1 : ℝ) / ((d * m : ℕ) : ℝ) =
      (1 / d) * ∑ m ∈ Finset.Ioc K M, (1 : ℝ) / m := by
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun m _ => ?_; push_cast
    rw [one_div_mul_one_div]
  rw [hsum]
  have hcl : (c - 1) * log x = log X - log a := by
    rw [hX, ha, log_div (by positivity) hd0.ne', log_div hx0.ne' hd0.ne', log_rpow hx0]; ring
  set Hs := ∑ m ∈ Finset.Ioc K M, (1 : ℝ) / m
  -- lower and upper bounds for Hs - (log X - log a)
  have hl1 : log X ≤ log (M + 1) := log_le_log (by positivity) hXM.le
  have hl2 : log (K + 1) ≤ log (a + 1) := log_le_log (by positivity) (by linarith)
  have hl3 : log (a + 1) - log a ≤ 1 / a := by
    rw [← log_div (by positivity) (by positivity)]
    have := Real.log_le_sub_one_of_pos (x := (a + 1) / a) (by positivity)
    have h' : (a + 1) / a - 1 = 1 / a := by field_simp; ring
    linarith
  have hu1 : log M ≤ log X := log_le_log hM0 hMX
  have hu2 : log (a - 1) ≤ log K := log_le_log (by linarith) (by linarith)
  have hu3 : log a - log (a - 1) ≤ 2 / a := by
    rw [← log_div (by positivity) (by linarith)]
    have := Real.log_le_sub_one_of_pos (x := a / (a - 1)) (by
      apply div_pos <;> linarith)
    have h' : a / (a - 1) - 1 = 1 / (a - 1) := by
      rw [div_sub_one (by linarith)]; congr 1; ring
    have h'' : 1 / (a - 1) ≤ 2 / a := by
      rw [div_le_div_iff₀ (by linarith) (by linarith)]; linarith
    linarith
  have h1a : 1 / a ≤ 2 / a := by gcongr; norm_num
  have habs : |Hs - (log X - log a)| ≤ 2 / a := by
    rw [abs_le]; constructor <;> linarith
  have : (1 / d) * Hs - (c - 1) * log x / d = (1 / d) * (Hs - (log X - log a)) := by
    rw [hcl]; ring
  rw [this, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / d)]
  calc 1 / (d : ℝ) * |Hs - (log X - log a)| ≤ 1 / d * (2 / a) := by gcongr
    _ = 2 / x := by rw [ha]; field_simp

/-! ### The Mertens window constant -/

lemma C0_exists : ∃ C₀ : ℝ, ∀ v : ℝ, 1 < v →
    ∑ p ∈ (Finset.range (⌊v ^ (2 : ℝ)⌋₊ + 1)).filter (fun p : ℕ => p.Prime ∧ v ^ (1 : ℝ) < p),
      (1 : ℝ) / p ≤ C₀ := by
  have h := mertens_prime_reciprocals 1 2 one_pos one_lt_two
  have hev := (h.eventually (gt_mem_nhds (show log (2 / 1) < log 2 + 1 by norm_num)))
  obtain ⟨v₀, hv₀⟩ := eventually_atTop.1 hev
  refine ⟨max (log 2 + 1) (v₀ ^ 2 + 1), fun v hv => ?_⟩
  by_cases hvv : v₀ ≤ v
  · exact (hv₀ v hvv).le.trans (le_max_left _ _)
  · push_neg at hvv
    refine le_trans ?_ (le_max_right _ _)
    calc ∑ p ∈ (Finset.range (⌊v ^ (2 : ℝ)⌋₊ + 1)).filter (fun p : ℕ => p.Prime ∧ v ^ (1 : ℝ) < p),
          (1 : ℝ) / p
        ≤ ∑ p ∈ (Finset.range (⌊v ^ (2 : ℝ)⌋₊ + 1)).filter
            (fun p : ℕ => p.Prime ∧ v ^ (1 : ℝ) < p), (1 : ℝ) := by
          refine Finset.sum_le_sum fun p hp => ?_
          simp only [Finset.mem_filter] at hp
          have : (1 : ℝ) ≤ p := by exact_mod_cast hp.2.1.one_lt.le
          exact div_le_one_of_le₀ this (by positivity)
      _ ≤ ⌊v ^ (2 : ℝ)⌋₊ + 1 := by
          rw [Finset.sum_const, nsmul_one]
          exact_mod_cast (Finset.card_filter_le _ _).trans (by simp)
      _ ≤ v₀ ^ 2 + 1 := by
          have h1 : (⌊v ^ (2 : ℝ)⌋₊ : ℝ) ≤ v ^ (2 : ℝ) := Nat.floor_le (by positivity)
          have h2 : v ^ (2 : ℝ) = v ^ 2 := by norm_cast
          have h3 : v ^ 2 ≤ v₀ ^ 2 := by nlinarith
          have h4 : (⌊v ^ (2 : ℝ)⌋₊ : ℝ) ≤ v₀ ^ 2 := h1.trans (h2.trans_le h3)
          exact add_le_add h4 le_rfl

/-! ### The sieve upper bound -/

lemma Ps_prod_squarefree (y : ℝ) : Squarefree (∏ p ∈ Ps y, p) := by
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro p hp q hq hpq
    simp only [Ps, Finset.coe_filter, mem_setOf_eq] at hp hq
    exact (Nat.coprime_iff_isRelPrime).1 ((Nat.coprime_primes hp.2 hq.2).2 hpq)
  · intro p hp
    simp only [Ps, Finset.mem_filter] at hp
    exact hp.2.prime.squarefree

lemma Ed_bound (x c : ℝ) (hc : 1 < c) (hx1 : 1 ≤ x) (d : ℕ) (hsq : Squarefree d)
    (hdx : 2 * (d : ℝ) ≤ x) (P : ℕ → Prop) {_ : DecidablePred P}
    (hP : ∀ a, P a ↔ ∀ p ∈ d.primeFactors, p ∣ a) :
    |(∑ a ∈ (Finset.Ioc ⌊x⌋₊ ⌊x ^ c⌋₊).filter P, (1 : ℝ) / a) -
      (c - 1) * log x * ∏ p ∈ d.primeFactors, (1 : ℝ) / p| ≤ 2 / x := by
  have hd0 : d ≠ 0 := hsq.ne_zero
  have hprod : ∏ p ∈ d.primeFactors, p = d := Nat.prod_primeFactors_of_squarefree hsq
  have hfilt : (Finset.Ioc ⌊x⌋₊ ⌊x ^ c⌋₊).filter P = (Finset.Ioc ⌊x⌋₊ ⌊x ^ c⌋₊).filter (d ∣ ·) := by
    refine Finset.filter_congr fun a _ => ?_
    rw [hP]
    constructor
    · intro h
      rw [← hprod]
      exact Finset.prod_primes_dvd a (fun p hp => (Nat.prime_of_mem_primeFactors hp).prime) h
    · intro h p hp
      exact (Nat.dvd_of_mem_primeFactors hp).trans h
  have hrec : ∏ p ∈ d.primeFactors, (1 : ℝ) / p = 1 / d := by
    rw [Finset.prod_div_distrib, Finset.prod_const_one]
    congr 1
    have := congrArg (Nat.cast : ℕ → ℝ) hprod
    push_cast at this
    exact this
  rw [hfilt, hrec, ← mul_div_assoc, mul_one]
  exact E_bound x c hc hx1 d (Nat.one_le_iff_ne_zero.2 hd0) hdx

lemma final_arith (S0 XV B₀ B e Es W : ℝ) (h : |S0 - XV| ≤ B₀ * XV * e + B₀ * Es)
    (hB : B₀ ≤ B) (hB0 : 0 ≤ B) (hXV : 0 ≤ XV) (he : 0 ≤ e) (hEs0 : 0 ≤ Es) (hEs : Es ≤ W) :
    S0 ≤ XV * (1 + B * e) + B * W := by
  have h1 := le_abs_self (S0 - XV)
  have k1 : B₀ * XV * e ≤ B * XV * e :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hB hXV) he
  have k2 : B₀ * Es ≤ B * W :=
    (mul_le_mul_of_nonneg_right hB hEs0).trans (mul_le_mul_of_nonneg_left hEs hB0)
  nlinarith

lemma sieve_bound : ∃ B : ℝ, 0 ≤ B ∧ ∃ H₀ : ℕ, ∀ b c : ℝ, 0 < b → 1 < c → ∀ H : ℕ, H₀ ≤ H →
    Even H → (4 * H + 2) * b ≤ 1 / 4 → ∀ x : ℝ, 16 ≤ x → 2 ≤ x ^ b →
    Ssum x b c ≤ (c - 1) * log x * mertensProduct (x ^ b) * (1 + B * exp (-(H : ℝ))) +
      B * (2 * (x ^ (1 / 4 : ℝ) + 1) / x) := by
  obtain ⟨C₀, hC₀⟩ := C0_exists
  obtain ⟨H₀, B₀, hBS⟩ := (block_sieve.{0, 0} (1 / 2) C₀ (by norm_num)).1
  refine ⟨max B₀ 0, le_max_right _ _, H₀, fun b c hb hc H hH hEven hHb x hx hz => ?_⟩
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hX' : 0 ≤ (c - 1) * log x := mul_nonneg (by linarith) (log_nonneg hx1)
  have hmain := hBS H hH hEven (Finset.Ioc ⌊x⌋₊ ⌊x ^ c⌋₊) (fun n : ℕ => (1 : ℝ) / n)
    (fun n _ => by positivity) (x ^ b) hz (Ps (x ^ b))
    (fun p hp => by
      simp only [Ps, Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff] at hp
      exact ⟨hp.2, (Nat.le_floor_iff (by positivity)).1 hp.1⟩)
    (fun p n => p ∣ n) ((c - 1) * log x) hX' (fun p => (1 : ℝ) / p)
    (fun p hp => by
      simp only [Ps, Finset.mem_filter] at hp
      have : (2 : ℝ) ≤ p := by exact_mod_cast hp.2.two_le
      constructor
      · positivity
      · rw [div_le_iff₀ (by linarith)]; linarith)
    (fun v hv => by
      refine le_trans ?_ (hC₀ v hv)
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro p hp
        simp only [Ps, Finset.mem_filter, Finset.mem_range] at hp ⊢
        refine ⟨?_, hp.1.2, by rw [rpow_one]; exact hp.2.1⟩
        rw [Nat.lt_succ_iff, Nat.le_floor_iff (by positivity)]
        have : v ^ (2 : ℝ) = v ^ 2 := by norm_cast
        rw [this]; exact hp.2.2
      · intro p _ _; positivity)
  simp only at hmain
  have hV : ∏ p ∈ Ps (x ^ b), (1 - (1 : ℝ) / p) = mertensProduct (x ^ b) := rfl
  rw [hV] at hmain
  have hVnn : 0 ≤ mertensProduct (x ^ b) := by
    rw [← hV]
    refine Finset.prod_nonneg fun p hp => ?_
    simp only [Ps, Finset.mem_filter] at hp
    have : (1 : ℝ) ≤ p := by exact_mod_cast hp.2.one_lt.le
    rw [sub_nonneg]; exact div_le_one_of_le₀ this (by linarith)
  have hD : (x ^ b) ^ (4 * H + 2) ≤ x ^ (1 / 4 : ℝ) := by
    rw [← rpow_natCast, ← rpow_mul hx0.le]
    apply rpow_le_rpow_of_exponent_le hx1
    push_cast; linarith
  have hy : 2 ≤ x ^ (1 / 4 : ℝ) := by
    calc (2 : ℝ) = 16 ^ (1 / 4 : ℝ) := by
          rw [show (16 : ℝ) = 2 ^ (4 : ℝ) by norm_num, ← rpow_mul (by norm_num)]; norm_num
      _ ≤ x ^ (1 / 4 : ℝ) := rpow_le_rpow (by norm_num) hx (by norm_num)
  have hy4 : (x ^ (1 / 4 : ℝ)) ^ 4 = x := by
    rw [← rpow_natCast, ← rpow_mul hx0.le]; norm_num
  have h2y : 2 * x ^ (1 / 4 : ℝ) ≤ x := by
    set y := x ^ (1 / 4 : ℝ)
    have h8 : (2 : ℝ) ^ 3 ≤ y ^ 3 := pow_le_pow_left₀ (by norm_num) hy 3
    calc 2 * y ≤ y * 8 := by linarith
      _ ≤ y * y ^ 3 := mul_le_mul_of_nonneg_left (by linarith) (by linarith)
      _ = y ^ 4 := by ring
      _ = x := hy4
  have hcard : (((∏ p ∈ Ps (x ^ b), p).divisors.filter
      (fun d : ℕ => (d : ℝ) ≤ (x ^ b) ^ (4 * H + 2))).card : ℝ) ≤ x ^ (1 / 4 : ℝ) + 1 := by
    have hsub : (∏ p ∈ Ps (x ^ b), p).divisors.filter
        (fun d : ℕ => (d : ℝ) ≤ (x ^ b) ^ (4 * H + 2)) ⊆
        Finset.range (⌊(x ^ b) ^ (4 * H + 2)⌋₊ + 1) := by
      intro d hd
      simp only [Finset.mem_filter] at hd
      rw [Finset.mem_range, Nat.lt_succ_iff]
      exact Nat.le_floor hd.2
    have h1 := Finset.card_le_card hsub
    rw [Finset.card_range] at h1
    have h2 : (⌊(x ^ b) ^ (4 * H + 2)⌋₊ : ℝ) ≤ (x ^ b) ^ (4 * H + 2) :=
      Nat.floor_le (by positivity)
    calc (((∏ p ∈ Ps (x ^ b), p).divisors.filter
          (fun d : ℕ => (d : ℝ) ≤ (x ^ b) ^ (4 * H + 2))).card : ℝ)
        ≤ ⌊(x ^ b) ^ (4 * H + 2)⌋₊ + 1 := by exact_mod_cast h1
      _ ≤ x ^ (1 / 4 : ℝ) + 1 := by linarith
  refine le_trans (le_of_eq ?_) (final_arith _ _ B₀ (max B₀ 0) _ _
    (2 * (x ^ (1 / 4 : ℝ) + 1) / x) hmain (le_max_left _ _) (le_max_right _ _)
    (mul_nonneg hX' hVnn) (exp_pos _).le (Finset.sum_nonneg fun _ _ => abs_nonneg _) ?_)
  · unfold Ssum; congr 1; ext a; simp only [Finset.mem_filter]
  · calc _ ≤ ∑ d ∈ (∏ p ∈ Ps (x ^ b), p).divisors.filter
          (fun d : ℕ => (d : ℝ) ≤ (x ^ b) ^ (4 * H + 2)), 2 / x := by
          refine Finset.sum_le_sum fun d hd => ?_
          simp only [Finset.mem_filter, Nat.mem_divisors] at hd
          obtain ⟨⟨hdvd, -⟩, hdD⟩ := hd
          exact Ed_bound x c hc hx1 d ((Ps_prod_squarefree (x ^ b)).squarefree_of_dvd hdvd)
            (by linarith [hdD.trans hD]) _ (fun a => Iff.rfl)
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (x ^ (1 / 4 : ℝ) + 1) * (2 / x) := by gcongr
      _ = 2 * (x ^ (1 / 4 : ℝ) + 1) / x := by ring

end ArtinPrimitiveRoots.RD

namespace ArtinPrimitiveRoots.RD

open Real MeasureTheory Set Filter Topology

/-! ## Part (2), assembly -/

lemma tendsto_upper (B b c : ℝ) (hb : 0 < b) (H : ℕ) :
    Tendsto (fun x : ℝ => (c - 1) * log x * mertensProduct (x ^ b) * (1 + B * exp (-(H : ℝ))) +
      B * (2 * (x ^ (1 / 4 : ℝ) + 1) / x)) atTop
      (𝓝 ((c - 1) * exp (-eulerMascheroniConstant) / b * (1 + B * exp (-(H : ℝ))))) := by
  have hM : Tendsto (fun x : ℝ => mertensProduct (x ^ b) * log (x ^ b)) atTop
      (𝓝 (exp (-eulerMascheroniConstant))) :=
    (mertens_product).comp (tendsto_rpow_atTop hb)
  have h1 : Tendsto (fun x : ℝ => (c - 1) * log x * mertensProduct (x ^ b)) atTop
      (𝓝 ((c - 1) / b * exp (-eulerMascheroniConstant))) := by
    refine (hM.const_mul ((c - 1) / b)).congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    rw [log_rpow hx]; field_simp
  have h2 : Tendsto (fun x : ℝ => 2 * (x ^ (1 / 4 : ℝ) + 1) / x) atTop (𝓝 0) := by
    have ha : Tendsto (fun x : ℝ => 2 * x ^ (-(3 / 4 : ℝ)) + 2 * x⁻¹) atTop (𝓝 0) := by
      have := ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 3 / 4)).const_mul 2).add
        (tendsto_inv_atTop_zero.const_mul 2)
      simpa using this
    refine ha.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    have : x ^ (-(3 / 4 : ℝ)) = x ^ (1 / 4 : ℝ) / x := by
      rw [← rpow_sub_one hx.ne']; norm_num
    rw [this]; field_simp
  have := (h1.mul_const (1 + B * exp (-(H : ℝ)))).add (h2.const_mul B)
  convert this using 2
  field_simp
  ring

lemma tendsto_lower (b c : ℝ) (hb : 0 < b) (J m : ℕ) :
    Tendsto (fun x => ∑ j ∈ Finset.range J, (1 / (j.factorial : ℝ)) *
      ∑ k ∈ G b c j m, ∏ i, σx x (lo m (k i)) (hi m (k i))) atTop
      (𝓝 (∑ j ∈ Finset.range J, (1 / (j.factorial : ℝ)) *
        ∑ k ∈ G b c j m, ∏ i, log (hi m (k i) / lo m (k i)))) := by
  refine tendsto_finset_sum _ fun j _ => (tendsto_finset_sum _ fun k hk => ?_).const_mul _
  refine tendsto_finset_prod _ fun i _ => ?_
  have hlo : 0 < lo m (k i) := hb.trans (lo_pos_of_G hb.le hk i)
  exact mertens_prime_reciprocals _ _ hlo (lo_lt_hi m (k i))

lemma main_ineq (B : ℝ) (H₀ : ℕ)
    (hup : ∀ b c : ℝ, 0 < b → 1 < c → ∀ H : ℕ, H₀ ≤ H → Even H → (4 * H + 2) * b ≤ 1 / 4 →
      ∀ x : ℝ, 16 ≤ x → 2 ≤ x ^ b →
      Ssum x b c ≤ (c - 1) * log x * mertensProduct (x ^ b) * (1 + B * exp (-(H : ℝ))) +
        B * (2 * (x ^ (1 / 4 : ℝ) + 1) / x))
    (b c : ℝ) (hb : 0 < b) (hb2 : b < 1 / 2) (hc : 1 < c) (H : ℕ) (hH : H₀ ≤ H) (hE : Even H)
    (hHb : (4 * H + 2) * b ≤ 1 / 4) :
    b / (b + c - 1) * (c - 1) * roughDensity b 1 ≤
      (c - 1) * exp (-eulerMascheroniConstant) / b * (1 + B * exp (-(H : ℝ))) := by
  set Λ := (c - 1) * exp (-eulerMascheroniConstant) / b * (1 + B * exp (-(H : ℝ)))
  have hstep1 : ∀ J m, ∑ j ∈ Finset.range J, (1 / (j.factorial : ℝ)) *
      ∑ k ∈ G b c j m, ∏ i, log (hi m (k i) / lo m (k i)) ≤ Λ := by
    intro J m
    refine le_of_tendsto_of_tendsto (tendsto_lower b c hb J m) (tendsto_upper B b c hb H) ?_
    filter_upwards [eventually_ge_atTop (16 : ℝ),
      (tendsto_rpow_atTop hb).eventually_ge_atTop (2 : ℝ)] with x hx hxb
    exact (lower_arith b c hb x (by linarith) J m).trans (hup b c hb hc H hH hE hHb x hx hxb)
  have hstep2 : ∀ J, ∑ j ∈ Finset.range J, (1 / (j.factorial : ℝ)) *
      ∫ t in U b c j, g t ≤ Λ := by
    intro J
    refine le_of_tendsto' (tendsto_finset_sum _ fun j _ =>
      (tendsto_cubes b c hb j).const_mul (1 / (j.factorial : ℝ))) fun m => hstep1 J m
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / b)
  have hNb : 1 < N * b := by rwa [div_lt_iff₀ hb] at hN
  rw [roughDensity_eq_sum b 1 hb (by linarith) N (by nlinarith), Finset.mul_sum]
  calc ∑ n ∈ Finset.range N, b / (b + c - 1) * (c - 1) * (I b 1 n / ((n + 1).factorial : ℝ))
      ≤ ∑ n ∈ Finset.range N, (1 / ((n + 1).factorial : ℝ)) * ∫ t in U b c (n + 1), g t := by
        refine Finset.sum_le_sum fun n _ => ?_
        have := fubini_lower b c hb hb2 hc n
        have hf : (0 : ℝ) < (n + 1).factorial := by positivity
        rw [← mul_div_assoc, div_le_iff₀ hf]
        rw [one_div_mul_eq_div, div_mul_cancel₀ _ hf.ne']
        exact this
    _ ≤ ∑ j ∈ Finset.range (N + 1), (1 / (j.factorial : ℝ)) * ∫ t in U b c j, g t := by
        rw [Finset.sum_range_succ' _ N]
        have h0 : 0 ≤ (1 / ((0 : ℕ).factorial : ℝ)) * ∫ t in U b c 0, g t :=
          mul_nonneg (by positivity) (integral_U_nonneg b c hb.le 0)
        linarith
    _ ≤ Λ := hstep2 (N + 1)

theorem part2 : ∃ b₀ C_d : ℝ, 0 < b₀ ∧ 0 < C_d ∧ ∀ b : ℝ, 0 < b → b < b₀ →
      roughDensity b 1 ≤
        exp (-eulerMascheroniConstant) / b * (1 + C_d * exp (-(1 / 20) / b)) := by
  obtain ⟨B, hB0, H₀, hup⟩ := sieve_bound
  refine ⟨1 / (40 * (H₀ + 1)), B * exp 2 + 1, by positivity, by positivity, fun b hb hbb => ?_⟩
  have hH1 : (1 : ℝ) ≤ H₀ + 1 := by have : (0 : ℝ) ≤ H₀ := Nat.cast_nonneg _; linarith
  have hb40 : b < 1 / 40 := by
    refine hbb.trans_le ?_
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  have hy : (H₀ : ℝ) + 1 < 1 / (40 * b) := by
    rw [lt_div_iff₀ (by positivity)]
    rw [lt_div_iff₀ (by positivity)] at hbb
    linarith
  set y := 1 / (40 * b) with hy_def
  set H := 2 * ⌊y⌋₊ with hH_def
  have hfl : H₀ + 1 ≤ ⌊y⌋₊ := Nat.le_floor (by push_cast; linarith)
  have hHH : H₀ ≤ H := by omega
  have hEven : Even H := even_two_mul _
  have hfle : (⌊y⌋₊ : ℝ) ≤ y := Nat.floor_le (by positivity)
  have hflt : y < ⌊y⌋₊ + 1 := Nat.lt_floor_add_one y
  have hHr : (H : ℝ) = 2 * ⌊y⌋₊ := by rw [hH_def]; push_cast; ring
  have hyb : y * b = 1 / 40 := by rw [hy_def]; field_simp
  have hHb : (4 * (H : ℝ) + 2) * b ≤ 1 / 4 := by
    rw [hHr]
    have : (⌊y⌋₊ : ℝ) * b ≤ 1 / 40 := by rw [← hyb]; exact mul_le_mul_of_nonneg_right hfle hb.le
    nlinarith
  set K := exp (-eulerMascheroniConstant) / b * (1 + B * exp (-(H : ℝ)))
  have hK0 : 0 ≤ K := by positivity
  -- the inequality for every `c ∈ (1, 2]`
  have hc_all : ∀ δ : ℝ, 0 < δ → roughDensity b 1 ≤ K + K * δ / b := by
    intro δ hδ
    have h := main_ineq B H₀ hup b (1 + δ) hb (by linarith) (by linarith) H hHH hEven hHb
    rw [show (1 + δ - 1) = δ by ring, show b + (1 + δ) - 1 = b + δ by ring] at h
    have h' : b / (b + δ) * roughDensity b 1 ≤ K := by
      have : δ * (b / (b + δ) * roughDensity b 1) ≤ δ * K := by
        calc δ * (b / (b + δ) * roughDensity b 1) = b / (b + δ) * δ * roughDensity b 1 := by ring
          _ ≤ δ * exp (-eulerMascheroniConstant) / b * (1 + B * exp (-(H : ℝ))) := h
          _ = δ * K := by simp only [K]; ring
      exact le_of_mul_le_mul_left this hδ
    rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)] at h'
    have : K * (b + δ) = b * (K + K * δ / b) := by field_simp
    rw [this] at h'
    exact le_of_mul_le_mul_left h' hb
  have hDK : roughDensity b 1 ≤ K := by
    by_contra hcon
    push_neg at hcon
    set D := roughDensity b 1
    set δ := b * (D - K) / (2 * (K + 1))
    have hδ : 0 < δ := by
      apply div_pos (mul_pos hb (by linarith)) (by linarith)
    have h := hc_all δ hδ
    have : K * δ / b = K * (D - K) / (2 * (K + 1)) := by
      simp only [δ]; field_simp
    rw [this] at h
    have h3 : K * (D - K) / (2 * (K + 1)) < D - K := by
      rw [div_lt_iff₀ (by linarith)]
      nlinarith
    linarith
  refine hDK.trans ?_
  simp only [K]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have hexp : exp (-(H : ℝ)) ≤ exp 2 * exp (-(1 / 20) / b) := by
    rw [← exp_add]
    apply exp_le_exp.2
    rw [hHr]
    have : (1 / 20) / b = 2 * y := by rw [hy_def]; field_simp; ring
    rw [neg_div, this]
    linarith
  have hB2 : B * exp (-(H : ℝ)) ≤ (B * exp 2 + 1) * exp (-(1 / 20) / b) := by
    calc B * exp (-(H : ℝ)) ≤ B * (exp 2 * exp (-(1 / 20) / b)) :=
          mul_le_mul_of_nonneg_left hexp hB0
      _ ≤ (B * exp 2 + 1) * exp (-(1 / 20) / b) := by
          have := (exp_pos (-(1 / 20) / b)).le
          nlinarith
  linarith

/-! ## The theorem -/

theorem main :
    (∀ b : ℝ, 0 < b → b < 1 / 2 →
      ∫ t in b..(1 / 2), roughDensity t (1 - t) / t = roughDensity b 1 - 1) ∧
    ∃ b₀ C_d : ℝ, 0 < b₀ ∧ 0 < C_d ∧ ∀ b : ℝ, 0 < b → b < b₀ →
      roughDensity b 1 ≤
        exp (-eulerMascheroniConstant) / b * (1 + C_d * exp (-(1 / 20) / b)) :=
  ⟨fun b hb hb2 => part1 b hb hb2, part2⟩

end ArtinPrimitiveRoots.RD

open Real ArtinPrimitiveRoots

theorem solution :
    (∀ b : ℝ, 0 < b → b < 1 / 2 →
      ∫ t in b..(1 / 2), roughDensity t (1 - t) / t = roughDensity b 1 - 1) ∧
    ∃ b₀ C_d : ℝ, 0 < b₀ ∧ 0 < C_d ∧ ∀ b : ℝ, 0 < b → b < b₀ →
      roughDensity b 1 ≤
        exp (-eulerMascheroniConstant) / b * (1 + C_d * exp (-(1 / 20) / b)) :=
  ArtinPrimitiveRoots.RD.main
