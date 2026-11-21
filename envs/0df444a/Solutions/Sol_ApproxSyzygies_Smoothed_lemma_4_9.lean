-- Prove2me | solution 1 for ApproxSyzygies.Smoothed.lemma_4_9
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-20T13:09:23.986943+00:00
-- url     : https://prove2.me/submissions/aedeaf6e-9e82-42b4-96c7-fce84fe0c8e4

import Mathlib
import Definitions.Def_ApproxSyzygies_Smoothed_Anticoncentration

section
open Module

namespace ApproxSyzygies.Smoothed.Dev.L49

section Gram
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

noncomputable def G {k : ℕ} (v : Fin k → E) : ℝ := (Matrix.gram ℝ v).det

lemma G_nonneg {k : ℕ} (v : Fin k → E) : 0 ≤ G v :=
  (Matrix.posSemidef_gram ℝ v).det_nonneg

lemma G_perm {k : ℕ} (v : Fin k → E) (σ : Equiv.Perm (Fin k)) : G (v ∘ σ) = G v := by
  unfold G
  have : Matrix.gram ℝ (v ∘ σ) = (Matrix.gram ℝ v).submatrix σ σ := by
    ext i j; simp [Matrix.gram_apply]
  rw [this, Matrix.det_submatrix_equiv_self]

lemma gram_comb {k : ℕ} (S : Matrix (Fin k) (Fin k) ℝ) (w : Fin k → E) :
    Matrix.gram ℝ (fun j => ∑ l, S j l • w l) = S * Matrix.gram ℝ w * S.transpose := by
  ext i j
  simp only [Matrix.gram_apply, Matrix.mul_apply, Matrix.transpose_apply, sum_inner, inner_sum,
    inner_smul_left, inner_smul_right, Finset.sum_mul, Finset.mul_sum]
  simp only [RCLike.conj_to_real]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

lemma G_cons_aux {k : ℕ} (h : E) (a : Fin k → ℝ) (v : Fin k → E)
    (hh : ∀ i, inner ℝ h (v i) = 0) :
    G (Fin.cons (h + ∑ i, a i • v i) v : Fin (k+1) → E) = ‖h‖ ^ 2 * G v := by
  classical
  set w : Fin (k+1) → E := Fin.cons h v with hw
  let S : Matrix (Fin (k+1)) (Fin (k+1)) ℝ :=
    Matrix.of fun i l => if i = 0 then (Fin.cons 1 a : Fin (k+1) → ℝ) l else if i = l then 1 else 0
  have hy : (Fin.cons (h + ∑ i, a i • v i) v : Fin (k+1) → E) = fun j => ∑ l, S j l • w l := by
    ext j : 1
    refine Fin.cases ?_ (fun j => ?_) j
    · simp [S, hw, Fin.sum_univ_succ]
    · simp [S, hw, Fin.succ_ne_zero, Fin.sum_univ_succ, Finset.sum_ite_eq]
  have hS : S.det = 1 := by
    rw [Matrix.det_of_isUpperTriangular]
    · simp only [S, Matrix.of_apply]
      refine Finset.prod_eq_one fun i _ => ?_
      refine Fin.cases ?_ (fun i => ?_) i <;> simp
    · intro i j hij
      have : i ≠ 0 := by
        intro h0; subst h0; exact absurd hij (by simp)
      have hne : i ≠ j := fun h => by subst h; exact lt_irrefl _ hij
      simp [S, this, hne]
  unfold G
  rw [hy, gram_comb, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hS]
  have hg : (Matrix.gram ℝ w).det = ‖h‖ ^ 2 * (Matrix.gram ℝ v).det := by
    rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
    have h0 : ∀ j : Fin k, (Matrix.gram ℝ w) 0 j.succ = 0 := by
      intro j; simp [Matrix.gram_apply, hw, hh]
    simp only [Fin.val_zero, pow_zero, one_mul, Fin.val_succ, h0, mul_zero, zero_mul,
      Finset.sum_const_zero, add_zero]
    have : (Matrix.gram ℝ w).submatrix Fin.succ (Fin.succAbove 0) = Matrix.gram ℝ v := by
      ext i j; simp [Matrix.gram_apply, hw]
    rw [this]
    simp [Matrix.gram_apply, hw, real_inner_self_eq_norm_sq]
  rw [hg]; ring

lemma norm_sub_proj_le [FiniteDimensional ℝ E] (S : Submodule ℝ E) (x : E) {s : E} (hs : s ∈ S) :
    ‖x - S.starProjection x‖ ≤ ‖x - s‖ := by
  rw [Submodule.starProjection_minimal]
  exact ciInf_le (f := fun y : S => ‖x - (y : E)‖) ⟨0, by rintro _ ⟨y, rfl⟩; positivity⟩ ⟨s, hs⟩

lemma infDist_eq_norm_proj [FiniteDimensional ℝ E] (S : Submodule ℝ E) (x : E) :
    Metric.infDist x (S : Set E) = ‖x - S.starProjection x‖ := by
  apply le_antisymm
  · rw [← dist_eq_norm]
    exact Metric.infDist_le_dist_of_mem (by simp)
  · refine (Metric.le_infDist ⟨0, S.zero_mem⟩).2 fun s hs => ?_
    rw [dist_eq_norm]; exact norm_sub_proj_le S x hs

lemma G_cons [FiniteDimensional ℝ E] {k : ℕ} (x : E) (v : Fin k → E) :
    G (Fin.cons x v : Fin (k+1) → E)
      = (Metric.infDist x (Submodule.span ℝ (Set.range v) : Set E)) ^ 2 * G v := by
  set S := Submodule.span ℝ (Set.range v)
  have hp : S.starProjection x ∈ S := Submodule.starProjection_apply_mem S x
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 hp
  have hh : ∀ i, inner ℝ (x - S.starProjection x) (v i) = 0 := by
    intro i
    have h1 : x - S.starProjection x ∈ Sᗮ := Submodule.sub_starProjection_mem_orthogonal x
    rw [real_inner_comm]
    exact Submodule.inner_right_of_mem_orthogonal (Submodule.subset_span (Set.mem_range_self i) : v i ∈ S) h1
  have := G_cons_aux (x - S.starProjection x) a v hh
  rw [ha, sub_add_cancel] at this
  rw [this, infDist_eq_norm_proj]

lemma G_succAbove [FiniteDimensional ℝ E] {k : ℕ} (v : Fin (k+1) → E) (p : Fin (k+1)) :
    G v = (Metric.infDist (v p) (Submodule.span ℝ (Set.range (v ∘ p.succAbove)) : Set E)) ^ 2
      * G (v ∘ p.succAbove) := by
  have h := Fin.cons_removeNth_eq_comp_cycleRange_symm v p  -- 
  have h2 : G v = G (Fin.cons (v p) (v ∘ p.succAbove) : Fin (k+1) → E) := by
    have : (Fin.cons (v p) (v ∘ p.succAbove) : Fin (k+1) → E) = v ∘ p.cycleRange.symm := by
      rw [← h]; rfl
    rw [this, G_perm]
  rw [h2, G_cons]

/-- `M` is a lower bound for the squared "ℓ²-conditioning" of the family `u`. -/
def Good {r : ℕ} (M : ℝ) (u : Fin r → E) : Prop :=
  ∀ c : Fin r → ℝ, M * ∑ i, c i ^ 2 ≤ ‖∑ i, c i • u i‖ ^ 2

lemma continuous_G {k : ℕ} : Continuous (fun v : Fin k → E => G v) := by
  unfold G
  refine Continuous.matrix_det ?_
  refine continuous_matrix fun i j => ?_
  simp only [Matrix.gram_apply]
  fun_prop

lemma leave_one_out {r : ℕ} (u : Fin (r+1) → E) (c : Fin (r+1) → ℝ) (p : Fin (r+1)) :
    |c p| * Metric.infDist (u p) (Submodule.span ℝ (Set.range (u ∘ p.succAbove)) : Set E)
      ≤ ‖∑ i, c i • u i‖ := by
  by_cases hc : c p = 0
  · simp [hc]
  set T := Submodule.span ℝ (Set.range (u ∘ p.succAbove))
  have hsum : ∑ i, c i • u i = c p • (u p - (-(∑ i : Fin r, (c (p.succAbove i) / c p) • u (p.succAbove i)))) := by
    rw [Fin.sum_univ_succAbove _ p, sub_neg_eq_add, smul_add, Finset.smul_sum]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_smul]; congr 1; field_simp
  have hmem : -(∑ i : Fin r, (c (p.succAbove i) / c p) • u (p.succAbove i)) ∈ T := by
    refine T.neg_mem (T.sum_mem fun i _ => T.smul_mem _ ?_)
    exact Submodule.subset_span ⟨i, rfl⟩
  rw [hsum, norm_smul, Real.norm_eq_abs]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  rw [← dist_eq_norm]
  exact Metric.infDist_le_dist_of_mem hmem

lemma extremal [FiniteDimensional ℝ E] (k : ℕ) (lam : ℝ) (hlam : 0 ≤ lam) (K : Set E)
    (hK : IsCompact K)
    (hgood : ∀ u : Fin (k+1) → E, (∀ i, u i ∈ K) → ∀ M : ℝ, 0 ≤ M → Good M u →
      M ≤ (k+1) * lam ^ 2) :
    ∃ S : Submodule ℝ E, finrank ℝ S ≤ k ∧ ∀ u ∈ K, ∃ s ∈ S, ‖u - s‖ ≤ (k+1) * lam := by
  by_cases hs : finrank ℝ (Submodule.span ℝ K) ≤ k
  · exact ⟨Submodule.span ℝ K, hs, fun u hu => ⟨u, Submodule.subset_span hu, by
      simp; positivity⟩⟩
  push_neg at hs
  -- an independent k-tuple in K
  obtain ⟨b, hbK, hbspan, hbli⟩ := exists_linearIndependent ℝ K
  have hbli' : LinearIndependent ℝ (fun x : b => (x : E)) := hbli
  haveI : Finite b := hbli'.finite
  haveI : Fintype b := Fintype.ofFinite b
  have hcard : k < Fintype.card b := by
    have := finrank_span_eq_card hbli'
    have h2 : Submodule.span ℝ (Set.range (fun x : b => (x : E))) = Submodule.span ℝ K := by
      rw [Subtype.range_coe]; exact hbspan
    rw [h2] at this; omega
  let e := Fintype.equivFin b
  let f : Fin k → b := fun i => e.symm (Fin.castLE hcard.le i)
  have hfinj : Function.Injective f := fun i j h => by
    have := e.symm.injective h
    exact Fin.castLE_injective _ this
  have hind : LinearIndependent ℝ (fun i : Fin k => ((f i : b) : E)) := hbli'.comp f hfinj
  have hne : K.Nonempty := by
    by_contra hK0
    rw [Set.not_nonempty_iff_eq_empty] at hK0
    subst hK0
    rw [Submodule.span_empty, finrank_bot] at hs
    omega
  obtain ⟨x0, hx0⟩ := hne
  have hKk : IsCompact (Set.pi Set.univ fun _ : Fin k => K) := isCompact_univ_pi fun _ => hK
  obtain ⟨A, hAK, hAmax⟩ := hKk.exists_isMaxOn ⟨fun _ => x0, fun _ _ => hx0⟩
    (continuous_G (k := k)).continuousOn
  have hAK' : ∀ i, A i ∈ K := fun i => hAK i (Set.mem_univ _)
  have hApos : 0 < G A := by
    refine lt_of_le_of_ne (G_nonneg A) fun h0 => ?_
    have hle := hAmax (show (fun i : Fin k => ((f i : b) : E)) ∈ Set.pi Set.univ fun _ => K from
      fun i _ => hbK (f i).2)
    have hne0 : G (fun i : Fin k => ((f i : b) : E)) ≠ 0 :=
      (Matrix.det_gram_ne_zero_iff_linearIndependent).2 hind
    have := G_nonneg (fun i : Fin k => ((f i : b) : E))
    simp only [Set.mem_setOf_eq] at hle
    exact hne0 (le_antisymm (by simpa [← h0] using hle) this)
  refine ⟨Submodule.span ℝ (Set.range A), (finrank_range_le_card A).trans (by simp), fun u hu => ?_⟩
  set S := Submodule.span ℝ (Set.range A)
  set uu : Fin (k+1) → E := Fin.cons u A with huu
  have huuK : ∀ i, uu i ∈ K := fun i => by
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa [huu] using hu
    · simpa [huu] using hAK' j
  set δ := Metric.infDist u (S : Set E) with hδ
  have hG0 : G uu = δ ^ 2 * G A := G_cons u A
  have hD : ∀ p : Fin (k+1), δ ≤ Metric.infDist (uu p)
      (Submodule.span ℝ (Set.range (uu ∘ p.succAbove)) : Set E) := by
    intro p
    have h1 := G_succAbove uu p
    have h2 : G (uu ∘ p.succAbove) ≤ G A := by
      have := hAmax (show (uu ∘ p.succAbove) ∈ Set.pi Set.univ fun _ => K from
        fun i _ => huuK _)
      simpa using this
    have h3 : δ ^ 2 * G A ≤ (Metric.infDist (uu p)
      (Submodule.span ℝ (Set.range (uu ∘ p.succAbove)) : Set E)) ^ 2 * G A := by
      calc δ ^ 2 * G A = _ := by rw [← hG0, h1]
        _ ≤ _ := mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
    have h4 := le_of_mul_le_mul_right h3 hApos
    exact le_of_sq_le_sq (by simpa using h4) Metric.infDist_nonneg
  have hgd : Good (δ ^ 2 / (k+1)) uu := by
    intro c
    obtain ⟨p, -, hp⟩ := Finset.exists_max_image Finset.univ (fun i => |c i|) ⟨0, Finset.mem_univ _⟩
    have h1 : ∑ i, c i ^ 2 ≤ (k+1) * c p ^ 2 := by
      calc ∑ i, c i ^ 2 ≤ ∑ _i : Fin (k+1), c p ^ 2 := Finset.sum_le_sum fun i _ => by
            have := hp i (Finset.mem_univ _)
            exact sq_le_sq.2 (by simpa using this)
        _ = (k+1) * c p ^ 2 := by simp
    have h2 := leave_one_out uu c p
    have h3 : δ * |c p| ≤ ‖∑ i, c i • uu i‖ :=
      (mul_le_mul_of_nonneg_right (hD p) (abs_nonneg _)).trans (by rw [mul_comm]; exact h2)
    have h4 : (δ * |c p|) ^ 2 ≤ ‖∑ i, c i • uu i‖ ^ 2 :=
      pow_le_pow_left₀ (mul_nonneg Metric.infDist_nonneg (abs_nonneg _)) h3 2
    have hk : (0 : ℝ) < k + 1 := by positivity
    calc δ ^ 2 / (k+1) * ∑ i, c i ^ 2 ≤ δ ^ 2 / (k+1) * ((k+1) * c p ^ 2) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = (δ * |c p|) ^ 2 := by rw [mul_pow, sq_abs]; field_simp
      _ ≤ _ := h4
  have hM := hgood uu huuK _ (by positivity) hgd
  have hk : (0 : ℝ) < k + 1 := by positivity
  have h5 : δ ^ 2 ≤ ((k+1) * lam) ^ 2 := by
    rw [div_le_iff₀ hk] at hM; nlinarith
  have h6 : δ ≤ (k+1) * lam := le_of_sq_le_sq h5 (by positivity)
  refine ⟨S.starProjection u, Submodule.starProjection_apply_mem S u, ?_⟩
  rw [← infDist_eq_norm_proj]; exact h6

lemma good_closure {k : ℕ} (lam : ℝ) (hlam : 0 ≤ lam) (B : Set E)
    (hB : ∀ u : Fin (k+1) → E, (∀ i, u i ∈ B) → ∀ M : ℝ, 0 ≤ M → Good M u →
      M ≤ (k+1) * lam ^ 2) :
    ∀ u : Fin (k+1) → E, (∀ i, u i ∈ closure B) → ∀ M : ℝ, 0 ≤ M → Good M u →
      M ≤ (k+1) * lam ^ 2 := by
  intro u hu M hM hgood
  by_contra hlt
  push_neg at hlt
  have hk : (0 : ℝ) < k + 1 := by positivity
  set a := Real.sqrt ((k+1) * lam ^ 2) with ha
  set m := Real.sqrt M with hm
  have ham : a < m := Real.sqrt_lt_sqrt (by positivity) hlt
  have ha0 : 0 ≤ a := Real.sqrt_nonneg _
  set ε := (m - a) / 2 with hε
  have hεpos : 0 < ε := by rw [hε]; linarith
  have hex : ∀ i, ∃ b ∈ B, dist (u i) b < ε / (k+1) := fun i =>
    Metric.mem_closure_iff.1 (hu i) _ (by positivity)
  choose u' hu'B hu'd using hex
  have hgood' : Good ((m - ε) ^ 2) u' := by
    intro c
    set R := Real.sqrt (∑ i, c i ^ 2) with hR
    have hR0 : 0 ≤ R := Real.sqrt_nonneg _
    have hRsq : R ^ 2 = ∑ i, c i ^ 2 := Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)
    have h1 : m * R ≤ ‖∑ i, c i • u i‖ := by
      have := hgood c
      rw [← hRsq] at this
      refine le_of_sq_le_sq ?_ (norm_nonneg _)
      rw [mul_pow, hm, Real.sq_sqrt hM]; exact this
    have hcR : ∀ i, |c i| ≤ R := fun i => Real.abs_le_sqrt
      (Finset.single_le_sum (f := fun i => c i ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i))
    have h2 : ‖∑ i, c i • u i - ∑ i, c i • u' i‖ ≤ R * ε := by
      rw [← Finset.sum_sub_distrib]
      refine (norm_sum_le _ _).trans ?_
      calc ∑ i, ‖c i • u i - c i • u' i‖ ≤ ∑ _i : Fin (k+1), R * (ε / (k+1)) :=
            Finset.sum_le_sum fun i _ => by
              rw [← smul_sub, norm_smul, Real.norm_eq_abs, ← dist_eq_norm]
              exact mul_le_mul (hcR i) (hu'd i).le dist_nonneg hR0
        _ = R * ε := by simp; field_simp
    have h3 := norm_sub_norm_le (∑ i, c i • u i) (∑ i, c i • u' i)
    have h4 : (m - ε) * R ≤ ‖∑ i, c i • u' i‖ := by nlinarith
    have h5 : 0 ≤ (m - ε) * R := mul_nonneg (by rw [hε]; linarith) hR0
    calc (m - ε) ^ 2 * ∑ i, c i ^ 2 = ((m - ε) * R) ^ 2 := by rw [mul_pow, hRsq]
      _ ≤ _ := pow_le_pow_left₀ h5 h4 2
  have := hB u' hu'B ((m - ε) ^ 2) (sq_nonneg _) hgood'
  have h2 : a < m - ε := by rw [hε]; linarith
  have h3 : (m - ε) ^ 2 ≤ a ^ 2 := by
    rw [ha, Real.sq_sqrt (by positivity)]; exact this
  nlinarith

lemma pad [FiniteDimensional ℝ E] (k : ℕ) (hk : k ≤ finrank ℝ E) :
    ∀ (n : ℕ) (S : Submodule ℝ E), finrank ℝ S + n = k → ∃ S' : Submodule ℝ E, S ≤ S' ∧ finrank ℝ S' = k := by
  intro n
  induction n with
  | zero => intro S h; exact ⟨S, le_rfl, by simpa using h⟩
  | succ n ih =>
    intro S h
    have hS : S ≠ ⊤ := by
      intro h0; subst h0; rw [finrank_top] at h; omega
    obtain ⟨x, hx⟩ : ∃ x, x ∉ S := by
      by_contra hc; push_neg at hc; exact hS (eq_top_iff.2 fun x _ => hc x)
    obtain ⟨S', hle, hf⟩ := ih (S ⊔ Submodule.span ℝ {x}) (by
      rw [Submodule.finrank_sup_span_singleton hx]; omega)
    exact ⟨S', le_trans le_sup_left hle, hf⟩

lemma frame_exists [FiniteDimensional ℝ E] {k : ℕ} (S : Submodule ℝ E) (h : finrank ℝ S = k) :
    ∃ v : Fin k → E, Orthonormal ℝ v ∧ ∀ u, ((S.starProjection u : E)) = ∑ i, inner ℝ (v i) u • v i := by
  let b := (stdOrthonormalBasis ℝ S).reindex (finCongr h)
  refine ⟨fun i => (b i : E), b.orthonormal.comp_linearIsometry S.subtypeₗᵢ, fun u => ?_⟩
  rw [Submodule.starProjection_apply, b.orthogonalProjectionOnto_apply_eq_sum]
  simp

lemma isCompact_frames [FiniteDimensional ℝ E] (k : ℕ) :
    IsCompact {v : Fin k → E | Orthonormal ℝ v} := by
  classical
  have hcl : IsClosed {v : Fin k → E | Orthonormal ℝ v} := by
    have : {v : Fin k → E | Orthonormal ℝ v} =
        ⋂ i, ⋂ j, {v : Fin k → E | inner ℝ (v i) (v j) = if i = j then (1:ℝ) else 0} := by
      ext v; simp [orthonormal_iff_ite]
    rw [this]
    exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_eq (by fun_prop) continuous_const
  refine Metric.isCompact_of_isClosed_isBounded hcl ?_
  refine (Metric.isBounded_closedBall (x := (0 : Fin k → E)) (r := 1)).subset fun v hv => ?_
  rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one]
  intro i; simpa using (hv.1 i).le

lemma shrink [FiniteDimensional ℝ E] (k : ℕ) (hk : k ≤ finrank ℝ E) (lam : ℝ) (hlam : 0 ≤ lam)
    (B : Set E)
    (hB : ∀ u : Fin (k+1) → E, (∀ i, u i ∈ B) → ∀ M : ℝ, 0 ≤ M → Good M u →
      M ≤ (k+1) * lam ^ 2) :
    ∃ S : Submodule ℝ E, finrank ℝ S ≤ k ∧ ∀ u ∈ B, ∃ s ∈ S, ‖u - s‖ ≤ (k+1) * lam := by
  set D : ℝ := (k+1) * lam
  let t : ℕ → Set (Fin k → E) := fun n => {v | Orthonormal ℝ v} ∩
    ⋂ (u : E) (_ : u ∈ B ∧ ‖u‖ ≤ n), {v | ‖u - ∑ i, inner ℝ (v i) u • v i‖ ≤ D}
  have htn : ∀ n, (t n).Nonempty := by
    intro n
    set Bn := B ∩ Metric.closedBall (0 : E) n
    have hKc : IsCompact (closure Bn) :=
      (isCompact_closedBall (0 : E) (n : ℝ)).of_isClosed_subset isClosed_closure
        (closure_minimal Set.inter_subset_right Metric.isClosed_closedBall)
    obtain ⟨S, hSk, hS⟩ := extremal k lam hlam (closure Bn) hKc
      (good_closure lam hlam Bn (fun u hu => hB u fun i => (hu i).1))
    obtain ⟨S', hle, hf⟩ := pad k hk (k - finrank ℝ S) S (by omega)
    obtain ⟨v, hv, hproj⟩ := frame_exists S' hf
    refine ⟨v, hv, ?_⟩
    simp only [Set.mem_iInter, Set.mem_setOf_eq]
    rintro u ⟨huB, hun⟩
    obtain ⟨s, hs, hsd⟩ := hS u (subset_closure ⟨huB, by simpa using hun⟩)
    rw [← hproj u]
    exact (norm_sub_proj_le S' u (hle hs)).trans hsd
  have htd : ∀ n, t (n+1) ⊆ t n := by
    intro n v hv
    obtain ⟨hv1, hv2⟩ := hv
    refine ⟨hv1, ?_⟩
    simp only [Set.mem_iInter, Set.mem_setOf_eq] at hv2 ⊢
    intro u ⟨huB, hun⟩
    exact hv2 u ⟨huB, hun.trans (by push_cast; linarith)⟩
  have htcl : ∀ n, IsClosed (t n) := by
    intro n
    refine (isCompact_frames k).isClosed.inter (isClosed_iInter fun u => isClosed_iInter fun _ => ?_)
    exact isClosed_le (by fun_prop) continuous_const
  have ht0 : IsCompact (t 0) :=
    (isCompact_frames k).of_isClosed_subset (htcl 0) Set.inter_subset_left
  obtain ⟨v, hv⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed t htd htn ht0 htcl
  refine ⟨Submodule.span ℝ (Set.range v), (finrank_range_le_card v).trans (by simp), fun u hu => ?_⟩
  refine ⟨∑ i, inner ℝ (v i) u • v i, Submodule.sum_mem _ fun i _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i)), ?_⟩
  have := (Set.mem_iInter.1 hv ⌈‖u‖⌉₊).2
  simp only [Set.mem_iInter, Set.mem_setOf_eq] at this
  exact this u ⟨hu, Nat.le_ceil _⟩

end Gram

lemma small_subspace {W V : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    [FiniteDimensional ℝ W] [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] (M : W →ₗ[ℝ] V) (lam : ℝ) (hlam : 0 ≤ lam) (q : ℕ)
    (hq : q ≤ numSmallSV M lam) :
    ∃ U : Submodule ℝ W, q ≤ finrank ℝ U ∧ ∀ w ∈ U, ‖M w‖ ≤ lam * ‖w‖ := by
  classical
  set n := finrank ℝ W with hn
  have hT := M.isSymmetric_adjoint_comp_self
  set b := hT.eigenvectorBasis rfl with hb
  set e := hT.eigenvalues (n := n) rfl with he
  set I : Finset (Fin n) := Finset.univ.filter fun i : Fin n => M.singularValues i ≤ lam with hI
  have hcard : numSmallSV M lam = I.card := by
    unfold numSmallSV
    refine (Finset.card_bij (fun k hk => (⟨k, Finset.mem_range.1 (Finset.mem_filter.1 hk).1⟩ : Fin n))
      ?_ ?_ ?_).trans rfl
    · intro k hk; simp only [hI, Finset.mem_filter, Finset.mem_univ, true_and]; exact (Finset.mem_filter.1 hk).2
    · intro a _ b _ h; simpa using h
    · intro j hj
      refine ⟨j.val, ?_, by simp⟩
      simp only [hI, Finset.mem_filter, Finset.mem_univ, true_and] at hj
      simp [Finset.mem_range, hj]
  refine ⟨Submodule.span ℝ (Set.range fun j : I => (b j : W)), ?_, ?_⟩
  · have hli : LinearIndependent ℝ (fun j : I => (b j : W)) :=
      b.orthonormal.linearIndependent.comp (fun j : I => (j : Fin n)) Subtype.val_injective
    rw [finrank_span_eq_card hli]
    simp [← hcard, hq]
  · intro w hw
    have hzero : ∀ i, i ∉ I → inner ℝ (b i : W) w = 0 := by
      intro i hi
      have : Submodule.span ℝ (Set.range fun j : I => (b j : W)) ≤ LinearMap.ker (innerₛₗ ℝ (b i : W)) := by
        rw [Submodule.span_le]
        rintro _ ⟨j, rfl⟩
        have hij : (j : Fin n) ≠ i := fun h => hi (h ▸ j.2)
        simpa using b.orthonormal.inner_eq_zero hij.symm
      simpa using this hw
    have hnorm : ‖w‖ ^ 2 = ∑ i, inner ℝ (b i : W) w ^ 2 := by
      rw [← real_inner_self_eq_norm_sq, ← b.sum_inner_mul_inner w w]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [real_inner_comm w (b i : W)]; ring
    have hMn : ‖M w‖ ^ 2 = ∑ i, e i * inner ℝ (b i : W) w ^ 2 := by
      rw [← real_inner_self_eq_norm_sq, ← LinearMap.adjoint_inner_left, ← b.sum_inner_mul_inner _ w]
      refine Finset.sum_congr rfl fun i _ => ?_
      have h1 : inner ℝ ((LinearMap.adjoint M) (M w)) (b i : W) = e i * inner ℝ (b i : W) w := by
        have h2 := hT w (b i)
        have h3 : (LinearMap.adjoint M ∘ₗ M) (b i : W) = e i • (b i : W) := by
          have := hT.apply_eigenvectorBasis (n := n) rfl i
          simpa [hb, he] using this
        rw [LinearMap.comp_apply] at h2
        rw [h2, h3, real_inner_smul_right, real_inner_comm]
      rw [h1]; ring
    have hle : ‖M w‖ ^ 2 ≤ (lam * ‖w‖) ^ 2 := by
      rw [hMn, mul_pow, hnorm, Finset.mul_sum]
      refine Finset.sum_le_sum fun i _ => ?_
      by_cases hi : i ∈ I
      · have hs : M.singularValues i ≤ lam := (Finset.mem_filter.1 hi).2
        have h0 := M.singularValues_nonneg i
        have hsq : e i ≤ lam ^ 2 := by
          have h4 : M.singularValues i ^ 2 = e i := M.sq_singularValues_fin rfl i
          rw [← h4]
          exact pow_le_pow_left₀ h0 hs 2
        nlinarith [sq_nonneg (inner ℝ (b i : W) w)]
      · rw [hzero i hi]; simp
    exact le_of_sq_le_sq hle (by positivity)

lemma tens_sum_norm_sq {ι κ : Type} [Fintype ι] [Fintype κ] {r : ℕ}
    (u : Fin r → EuclideanSpace ℝ ι) (w : Fin r → EuclideanSpace ℝ κ) :
    ‖∑ i, tens (u i) (w i)‖ ^ 2 = ∑ b : κ, ‖∑ i, w i b • u i‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type_right]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [EuclideanSpace.norm_sq_eq]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp [tens, mul_comm]

lemma claimA {ι κ : Type} [Fintype ι] [Fintype κ]
    (X : Submodule ℝ (EuclideanSpace ℝ (ι × κ))) (NX : ℕ) (hX : Module.finrank ℝ X ≤ NX)
    (q : ℕ) (hq : 1 ≤ q) (r : ℕ) (hr : NX < r * q) (lam : ℝ) (hlam : 0 ≤ lam)
    (u : Fin r → EuclideanSpace ℝ ι)
    (hu : ∀ i, q ≤ numSmallSV
      ((Xᗮ.starProjection : EuclideanSpace ℝ (ι × κ) →L[ℝ] EuclideanSpace ℝ (ι × κ)).toLinearMap ∘ₗ
        tensLeft (u i)) lam)
    (M : ℝ) (hM : Good M u) : M ≤ (r : ℝ) * lam ^ 2 := by
  classical
  have hsub : ∀ i, ∃ U : Submodule ℝ (EuclideanSpace ℝ κ), q ≤ finrank ℝ U ∧
      ∀ w ∈ U, ‖Xᗮ.starProjection (tens (u i) w)‖ ≤ lam * ‖w‖ := fun i => by
    obtain ⟨U, h1, h2⟩ := small_subspace _ lam hlam q (hu i)
    exact ⟨U, h1, fun w hw => by simpa [tensLeft] using h2 w hw⟩
  choose U hUq hUb using hsub
  let L : (∀ i : Fin r, U i) →ₗ[ℝ] EuclideanSpace ℝ (ι × κ) :=
    X.starProjection.toLinearMap ∘ₗ
      (∑ i : Fin r, (tensLeft (u i)) ∘ₗ (U i).subtype ∘ₗ LinearMap.proj i)
  have hrange : LinearMap.range L ≤ X := by
    rintro _ ⟨y, rfl⟩
    exact Submodule.starProjection_apply_mem X _
  have hdim : NX < finrank ℝ (∀ i : Fin r, U i) := by
    rw [Module.finrank_pi_fintype]
    have h1 : r * q ≤ ∑ i : Fin r, finrank ℝ (U i) := by
      have := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hUq i)
      simpa using this
    omega
  have hker : ∃ y ∈ LinearMap.ker L, y ≠ 0 := by
    have h1 := LinearMap.finrank_range_add_finrank_ker L
    have h2 : finrank ℝ (LinearMap.range L) ≤ NX :=
      (Submodule.finrank_mono hrange).trans hX
    have h3 : 0 < finrank ℝ (LinearMap.ker L) := by omega
    obtain ⟨y, hy0⟩ := (Module.finrank_pos_iff_exists_ne_zero (R := ℝ)).1 h3
    exact ⟨y, y.2, fun h => hy0 (Subtype.ext h)⟩
  obtain ⟨y, hyker, hy0⟩ := hker
  set w : Fin r → EuclideanSpace ℝ κ := fun i => (y i : EuclideanSpace ℝ κ) with hw
  set F := ∑ i : Fin r, tens (u i) (w i) with hF
  have hLy : L y = X.starProjection F := by
    simp [L, hF, hw, tensLeft, LinearMap.sum_apply]
  have hFX : F ∈ Xᗮ := by
    have : X.starProjection F = 0 := by rw [← hLy]; exact hyker
    exact (Submodule.starProjection_apply_eq_zero_iff X).1 this
  have hFeq : Xᗮ.starProjection F = F := Submodule.starProjection_eq_self_iff.2 hFX
  have hupper : ‖F‖ ≤ lam * ∑ i, ‖w i‖ := by
    calc ‖F‖ = ‖Xᗮ.starProjection F‖ := by rw [hFeq]
      _ = ‖∑ i, Xᗮ.starProjection (tens (u i) (w i))‖ := by rw [hF, map_sum]
      _ ≤ ∑ i, ‖Xᗮ.starProjection (tens (u i) (w i))‖ := norm_sum_le _ _
      _ ≤ ∑ i, lam * ‖w i‖ := Finset.sum_le_sum fun i _ => hUb i _ (y i).2
      _ = _ := by rw [Finset.mul_sum]
  have hlower : M * ∑ i, ‖w i‖ ^ 2 ≤ ‖F‖ ^ 2 := by
    rw [hF, tens_sum_norm_sq]
    have h1 : ∑ i, ‖w i‖ ^ 2 = ∑ b : κ, ∑ i, w i b ^ 2 := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [EuclideanSpace.norm_sq_eq]
      simp
    rw [h1, Finset.mul_sum]
    exact Finset.sum_le_sum fun b _ => hM (fun i => w i b)
  have hS : 0 < ∑ i, ‖w i‖ ^ 2 := by
    obtain ⟨i, hi⟩ : ∃ i, y i ≠ 0 := by
      by_contra h; push_neg at h; exact hy0 (funext h)
    refine lt_of_lt_of_le (b := ‖w i‖ ^ 2) ?_ (Finset.single_le_sum (f := fun i => ‖w i‖ ^ 2)
      (fun j _ => sq_nonneg _) (Finset.mem_univ i))
    have : w i ≠ 0 := fun h => hi (Subtype.ext h)
    positivity
  have hcs : (∑ i, ‖w i‖) ^ 2 ≤ r * ∑ i, ‖w i‖ ^ 2 := by
    simpa using sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i => ‖w i‖)
  have h5 : ‖F‖ ^ 2 ≤ lam ^ 2 * (r * ∑ i, ‖w i‖ ^ 2) := by
    calc ‖F‖ ^ 2 ≤ (lam * ∑ i, ‖w i‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hupper 2
      _ = lam ^ 2 * (∑ i, ‖w i‖) ^ 2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hcs (sq_nonneg _)
  have h6 : M * ∑ i, ‖w i‖ ^ 2 ≤ (r * lam ^ 2) * ∑ i, ‖w i‖ ^ 2 := by
    nlinarith
  exact le_of_mul_le_mul_right h6 hS

end ApproxSyzygies.Smoothed.Dev.L49

namespace ApproxSyzygies.Smoothed

open ApproxSyzygies.Smoothed.Dev.L49 in
theorem chk_lemma_4_9 {ι κ : Type} [Fintype ι] [Fintype κ]
    (X : Submodule ℝ (EuclideanSpace ℝ (ι × κ))) (NX : ℕ) (hX : Module.finrank ℝ X ≤ NX)
    (q : ℕ) (hq : 1 ≤ q) (hqU : NX / q + 1 ≤ Fintype.card ι) (lam : ℝ) (hlam : 0 ≤ lam) :
    ∃ Unull : Submodule ℝ (EuclideanSpace ℝ ι), Module.finrank ℝ Unull ≤ NX / q ∧
      ∀ u : EuclideanSpace ℝ ι,
        q ≤ numSmallSV
            ((Xᗮ.starProjection : EuclideanSpace ℝ (ι × κ) →L[ℝ] EuclideanSpace ℝ (ι × κ)).toLinearMap ∘ₗ
              tensLeft u) lam →
          Metric.infDist u Unull ≤ lam * ((NX : ℝ) / q + 1) := by
  classical
  set k := NX / q with hk
  let B : Set (EuclideanSpace ℝ ι) := {u | q ≤ numSmallSV
            ((Xᗮ.starProjection : EuclideanSpace ℝ (ι × κ) →L[ℝ] EuclideanSpace ℝ (ι × κ)).toLinearMap ∘ₗ
              tensLeft u) lam}
  have hkE : k ≤ Module.finrank ℝ (EuclideanSpace ℝ ι) := by
    rw [finrank_euclideanSpace]; omega
  have hB : ∀ u : Fin (k+1) → EuclideanSpace ℝ ι, (∀ i, u i ∈ B) → ∀ M : ℝ, 0 ≤ M → Good M u →
      M ≤ ((k : ℝ) + 1) * lam ^ 2 := by
    intro u hu M _ hM
    have hlt : NX < (k + 1) * q := by
      have h2 := Nat.div_add_mod NX q
      have h3 := Nat.mod_lt NX (show 0 < q by omega)
      nlinarith
    have := claimA X NX hX q hq (k+1) hlt lam hlam u hu M hM
    simpa using this
  obtain ⟨S, hS, hSu⟩ := shrink k hkE lam hlam B hB
  refine ⟨S, hS, fun u hu => ?_⟩
  obtain ⟨s, hs, hsd⟩ := hSu u hu
  have h1 : Metric.infDist u (S : Set (EuclideanSpace ℝ ι)) ≤ ((k : ℝ) + 1) * lam :=
    (Metric.infDist_le_dist_of_mem hs).trans (by rw [dist_eq_norm]; exact hsd)
  have h2 : (k : ℝ) ≤ (NX : ℝ) / q := Nat.cast_div_le
  calc _ ≤ ((k : ℝ) + 1) * lam := h1
    _ ≤ lam * ((NX : ℝ) / q + 1) := by nlinarith

end ApproxSyzygies.Smoothed
end

theorem solution : type_of% @ApproxSyzygies.Smoothed.chk_lemma_4_9 := @ApproxSyzygies.Smoothed.chk_lemma_4_9
