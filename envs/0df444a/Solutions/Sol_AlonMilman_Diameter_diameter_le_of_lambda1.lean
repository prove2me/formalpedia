-- Prove2me | solution 1 for AlonMilman.Diameter.diameter_le_of_lambda1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-28T12:39:03.967188+00:00
-- url     : https://prove2.me/submissions/f7d57fe8-59bd-4273-a382-5e2c52f28568

import Mathlib
import Definitions.Def_AlonMilman_Diameter_lambda1

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

open Matrix WithLp in
theorem am67_spec {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.Connected) (hn : 2 ≤ Fintype.card V) :
    0 < AlonMilman.Diameter.lambda1 G ∧ ∀ f : V → ℝ, ∑ v, f v = 0 →
      AlonMilman.Diameter.lambda1 G * ∑ v, f v ^ 2 ≤
        (∑ i, ∑ j, if G.Adj i j then (f i - f j) ^ 2 else 0) / 2 := by
  classical
  set n := Fintype.card V with hn_def
  have hA := G.isHermitian_lapMatrix ℝ
  set T := Matrix.toEuclideanLin (G.lapMatrix ℝ) with hT_def
  have hT : T.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr hA
  have hfin : Module.finrank ℝ (EuclideanSpace ℝ V) = n := finrank_euclideanSpace
  set b := hT.eigenvectorBasis hfin with hb
  set μ := hT.eigenvalues hfin with hμ
  have hlam : AlonMilman.Diameter.lambda1 G = μ ⟨n - 2, by omega⟩ := by
    unfold AlonMilman.Diameter.lambda1
    rw [dif_pos (by omega)]
    rfl
  -- quadratic form
  have hQ : ∀ f : V → ℝ, inner ℝ (T (toLp 2 f)) (toLp 2 f) =
      (∑ i, ∑ j, if G.Adj i j then (f i - f j) ^ 2 else 0) / 2 := by
    intro f
    rw [← SimpleGraph.lapMatrix_toLinearMap₂', Matrix.toLinearMap₂'_apply']
    simp [T, EuclideanSpace.inner_toLp_toLp]
  have hexp : ∀ x : EuclideanSpace ℝ V, inner ℝ (T x) x = ∑ i, μ i * (inner ℝ (b i) x) ^ 2 := by
    intro x
    rw [← b.sum_inner_mul_inner (T x) x]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hT x (b i), hT.apply_eigenvectorBasis hfin i, inner_smul_right, real_inner_comm x (b i)]
    simp only [RCLike.ofReal_real_eq_id, id]
    ring
  have hnorm : ∀ x : EuclideanSpace ℝ V, ∑ i, (inner ℝ (b i) x) ^ 2 = inner ℝ x x := by
    intro x
    rw [← b.sum_inner_mul_inner x x]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [real_inner_comm x (b i)]; ring

  have hQnn : ∀ x : EuclideanSpace ℝ V, 0 ≤ inner ℝ (T x) x := by
    intro x
    have := hQ (ofLp x)
    rw [toLp_ofLp] at this
    rw [this]; positivity
  have hQzero : ∀ x : EuclideanSpace ℝ V, inner ℝ (T x) x = 0 →
      ∀ v w, ofLp x v = ofLp x w := by
    intro x hx v w
    have h2 : Matrix.toLinearMap₂' ℝ (G.lapMatrix ℝ) (ofLp x) (ofLp x) = 0 := by
      rw [SimpleGraph.lapMatrix_toLinearMap₂', ← hQ, toLp_ofLp, hx]
    exact (SimpleGraph.lapMatrix_toLinearMap₂'_apply'_eq_zero_iff_forall_reachable G _).1 h2
      v w (hG.preconnected v w)
  have hQb : ∀ i, inner ℝ (T (b i)) (b i) = μ i := by
    intro i
    rw [hT.apply_eigenvectorBasis hfin i, real_inner_smul_left, real_inner_self_eq_norm_sq,
      b.norm_eq_one]
    simp [μ]
  have hin : ∀ i j, inner ℝ (b i) (b j) = ∑ v, ofLp (b j) v * ofLp (b i) v := by
    intro i j
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simp [dotProduct]
  obtain ⟨v0⟩ : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  have hanti := hT.eigenvalues_antitone hfin
  set last : Fin n := ⟨n - 1, by omega⟩ with hlast
  set sec : Fin n := ⟨n - 2, by omega⟩ with hsec
  have hμlast : ∀ i, μ last ≤ μ i := by
    intro i
    apply hanti
    rw [Fin.le_iff_val_le_val]
    have := i.isLt
    simp only [last]
    omega
  have hμsec : ∀ i, i ≠ last → μ sec ≤ μ i := by
    intro i hi
    apply hanti
    rw [Fin.le_iff_val_le_val]
    have h1 := i.isLt
    have h2 : i.val ≠ n - 1 := fun h => hi (Fin.ext h)
    simp only [sec]
    omega
  have hμlast_nonpos : μ last ≤ 0 := by
    have h0 : inner ℝ (T (toLp 2 (fun _ : V => (1:ℝ)))) (toLp 2 (fun _ : V => (1:ℝ))) = 0 := by
      rw [hQ]; simp
    have h1 : inner ℝ (toLp 2 (fun _ : V => (1:ℝ))) (toLp 2 (fun _ : V => (1:ℝ))) = n := by
      rw [EuclideanSpace.inner_toLp_toLp]
      simp [dotProduct, n]
    rw [hexp] at h0
    have h2 : μ last * inner ℝ (toLp 2 (fun _ : V => (1:ℝ))) (toLp 2 (fun _ : V => (1:ℝ))) ≤ 0 := by
      rw [← hnorm, Finset.mul_sum, ← h0]
      exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hμlast i) (sq_nonneg _)
    rw [h1] at h2
    have hnpos : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    nlinarith
  have hblast : ∀ v w, ofLp (b last) v = ofLp (b last) w := by
    apply hQzero
    have := hQnn (b last)
    rw [hQb] at this ⊢
    linarith
  have hray : ∀ f : V → ℝ, ∑ v, f v = 0 →
      μ sec * ∑ v, f v ^ 2 ≤ inner ℝ (T (toLp 2 f)) (toLp 2 f) := by
    intro f hf
    have hc : inner ℝ (b last) (toLp 2 f) = 0 := by
      rw [EuclideanSpace.inner_eq_star_dotProduct]
      simp only [star_trivial, dotProduct, ofLp_toLp]
      have : ∀ v, f v * ofLp (b last) v = f v * ofLp (b last) v0 := fun v => by
        rw [hblast v v0]
      rw [Finset.sum_congr rfl (fun v _ => this v), ← Finset.sum_mul, hf, zero_mul]
    have hff : inner ℝ (toLp 2 f) (toLp 2 f) = ∑ v, f v ^ 2 := by
      rw [EuclideanSpace.inner_toLp_toLp]
      simp [dotProduct, sq]
    rw [hexp, ← hff, ← hnorm, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    by_cases hi : i = last
    · rw [hi, hc]; simp
    · exact mul_le_mul_of_nonneg_right (hμsec i hi) (sq_nonneg _)
  have hpos : 0 < μ sec := by
    by_contra hle
    have hle : μ sec ≤ 0 := not_lt.mp hle
    have hsec_const : ∀ v w, ofLp (b sec) v = ofLp (b sec) w := by
      apply hQzero
      have := hQnn (b sec)
      rw [hQb] at this ⊢
      linarith
    have hne : sec ≠ last := by
      intro h
      have := congrArg Fin.val h
      simp only [sec, last] at this
      omega
    have h1 : inner ℝ (b last) (b last) = 1 := by
      rw [real_inner_self_eq_norm_sq, b.norm_eq_one]; norm_num
    have h3 : inner ℝ (b sec) (b sec) = 1 := by
      rw [real_inner_self_eq_norm_sq, b.norm_eq_one]; norm_num
    have h2 : inner ℝ (b last) (b sec) = 0 := b.orthonormal.2 hne.symm
    rw [hin] at h1 h2 h3
    have e1 : ∀ i j : Fin n, (∀ v w, ofLp (b i) v = ofLp (b i) w) →
        (∀ v w, ofLp (b j) v = ofLp (b j) w) →
        ∑ v, ofLp (b j) v * ofLp (b i) v = (n : ℝ) * (ofLp (b j) v0 * ofLp (b i) v0) := by
      intro i j hi hj
      rw [Finset.sum_congr rfl (fun v _ => by rw [hi v v0, hj v v0]), Finset.sum_const,
        Finset.card_univ, nsmul_eq_mul]
    rw [e1 last last hblast hblast] at h1
    rw [e1 last sec hblast hsec_const] at h2
    rw [e1 sec sec hsec_const hsec_const] at h3
    have key : ((n : ℝ) * (ofLp (b sec) v0 * ofLp (b last) v0)) *
        ((n : ℝ) * (ofLp (b sec) v0 * ofLp (b last) v0)) =
        ((n : ℝ) * (ofLp (b last) v0 * ofLp (b last) v0)) *
        ((n : ℝ) * (ofLp (b sec) v0 * ofLp (b sec) v0)) := by ring
    rw [h1, h2, h3] at key
    norm_num at key
  refine ⟨hlam ▸ hpos, fun f hf => ?_⟩
  rw [hlam, ← hQ]
  exact hray f hf

theorem am67_Q_le {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (f : V → ℝ) (C : V → Prop) [DecidablePred C]
    (hf : ∀ i j, G.Adj i j → (f i - f j) ^ 2 ≤ (if C i then 1 else 0) + (if C j then 1 else 0)) :
    (∑ i, ∑ j, if G.Adj i j then (f i - f j) ^ 2 else 0) / 2 ≤
      (G.maxDegree : ℝ) * ((Finset.univ.filter C).card : ℝ) := by
  have h1 : ∀ i j, (if G.Adj i j then (f i - f j) ^ 2 else 0) ≤
      (if G.Adj i j then (1:ℝ) else 0) * (if C i then 1 else 0) +
      (if G.Adj j i then (1:ℝ) else 0) * (if C j then 1 else 0) := by
    intro i j
    by_cases h : G.Adj i j
    · simp only [h, h.symm, if_true, one_mul]
      exact hf i j h
    · have h' : ¬ G.Adj j i := fun h' => h h'.symm
      simp [h, h']
  have h2 : ∑ i, ∑ j, (if G.Adj i j then (f i - f j) ^ 2 else 0) ≤
      ∑ i, ∑ j, ((if G.Adj i j then (1:ℝ) else 0) * (if C i then 1 else 0) +
      (if G.Adj j i then (1:ℝ) else 0) * (if C j then 1 else 0)) :=
    Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => h1 i j
  have h3a : ∑ i, ∑ j, (if G.Adj i j then (1:ℝ) else 0) * (if C i then 1 else 0) =
      ∑ i, (G.degree i : ℝ) * (if C i then 1 else 0) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_mul, ← G.degree_eq_sum_if_adj]
  have h3b : ∑ i, ∑ j, (if G.Adj j i then (1:ℝ) else 0) * (if C j then 1 else 0) =
      ∑ i, (G.degree i : ℝ) * (if C i then 1 else 0) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_mul, ← G.degree_eq_sum_if_adj]
  have h3 : ∑ i, ∑ j, ((if G.Adj i j then (1:ℝ) else 0) * (if C i then 1 else 0) +
      (if G.Adj j i then (1:ℝ) else 0) * (if C j then 1 else 0)) =
      2 * ∑ i, (G.degree i : ℝ) * (if C i then 1 else 0) := by
    simp only [Finset.sum_add_distrib]
    rw [h3a, h3b]
    ring
  have h4 : ∑ i, (G.degree i : ℝ) * (if C i then 1 else 0) ≤
      ∑ i, (G.maxDegree : ℝ) * (if C i then 1 else 0) := by
    apply Finset.sum_le_sum
    intro i _
    apply mul_le_mul_of_nonneg_right _ (by split_ifs <;> norm_num)
    exact_mod_cast G.degree_le_maxDegree i
  have h5 : ∑ i, (G.maxDegree : ℝ) * (if C i then 1 else 0) =
      (G.maxDegree : ℝ) * ((Finset.univ.filter C).card : ℝ) := by
    rw [← Finset.mul_sum, Finset.sum_boole]
  linarith

theorem am67_two_set {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.Connected) (hn : 2 ≤ Fintype.card V)
    (f : V → ℝ) (P R C : V → Prop) [DecidablePred P] [DecidablePred R] [DecidablePred C]
    (p r : ℝ) (hP : ∀ v, P v → f v = p) (hR : ∀ v, R v → f v = r) (hPR : ∀ v, P v → ¬ R v)
    (hf : ∀ i j, G.Adj i j → (f i - f j) ^ 2 ≤ (if C i then 1 else 0) + (if C j then 1 else 0)) :
    AlonMilman.Diameter.lambda1 G *
        (((Finset.univ.filter P).card : ℝ) * ((Finset.univ.filter R).card : ℝ) * (p - r) ^ 2) ≤
      (((Finset.univ.filter P).card : ℝ) + ((Finset.univ.filter R).card : ℝ)) *
        ((G.maxDegree : ℝ) * ((Finset.univ.filter C).card : ℝ)) := by
  obtain ⟨hpos, hray⟩ := am67_spec G hG hn
  set n := Fintype.card V with hn_def
  have hnpos : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  set M : ℝ := (∑ v, f v) / n with hM
  set g : V → ℝ := fun v => f v - M with hg_def
  have hg : ∑ v, g v = 0 := by
    simp only [g, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [hM]
    field_simp
    ring
  have hQg : (∑ i, ∑ j, if G.Adj i j then (g i - g j) ^ 2 else 0) =
      (∑ i, ∑ j, if G.Adj i j then (f i - f j) ^ 2 else 0) := by
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [g]
    ring_nf
  have h1 := hray g hg
  rw [hQg] at h1
  have h2 := am67_Q_le G f C hf
  set α : ℝ := ((Finset.univ.filter P).card : ℝ) with hα
  set β : ℝ := ((Finset.univ.filter R).card : ℝ) with hβ
  set γ : ℝ := ((Finset.univ.filter C).card : ℝ) with hγ
  set d : ℝ := (G.maxDegree : ℝ) with hd
  have h3 : ∀ v, (if P v then (1:ℝ) else 0) * (p - M) ^ 2 +
      (if R v then (1:ℝ) else 0) * (r - M) ^ 2 ≤ g v ^ 2 := by
    intro v
    by_cases hp : P v
    · have hr : ¬ R v := hPR v hp
      simp only [hp, hr, if_true, if_false, one_mul, zero_mul, add_zero, g, hP v hp]
      exact le_refl _
    · by_cases hr : R v
      · simp only [hp, hr, if_true, if_false, one_mul, zero_mul, zero_add, g, hR v hr]
        exact le_refl _
      · simp only [hp, hr, if_false, zero_mul, add_zero]
        positivity
  have h4 : α * (p - M) ^ 2 + β * (r - M) ^ 2 ≤ ∑ v, g v ^ 2 := by
    have := Finset.sum_le_sum fun v (_ : v ∈ Finset.univ) => h3 v
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul, Finset.sum_boole,
      Finset.sum_boole] at this
    simpa [α, β] using this
  have hα0 : 0 ≤ α := by positivity
  have hβ0 : 0 ≤ β := by positivity
  have hγ0 : 0 ≤ γ := by positivity
  have hd0 : 0 ≤ d := by positivity
  have h5 : α * β * (p - r) ^ 2 ≤ (α + β) * (α * (p - M) ^ 2 + β * (r - M) ^ 2) := by
    nlinarith [sq_nonneg (α * (p - M) + β * (r - M))]
  have h6 : AlonMilman.Diameter.lambda1 G * (α * β * (p - r) ^ 2) ≤
      AlonMilman.Diameter.lambda1 G * ((α + β) * ∑ v, g v ^ 2) := by
    apply mul_le_mul_of_nonneg_left _ hpos.le
    calc α * β * (p - r) ^ 2 ≤ (α + β) * (α * (p - M) ^ 2 + β * (r - M) ^ 2) := h5
      _ ≤ (α + β) * ∑ v, g v ^ 2 := mul_le_mul_of_nonneg_left h4 (by positivity)
  calc AlonMilman.Diameter.lambda1 G * (α * β * (p - r) ^ 2)
      ≤ AlonMilman.Diameter.lambda1 G * ((α + β) * ∑ v, g v ^ 2) := h6
    _ = (α + β) * (AlonMilman.Diameter.lambda1 G * ∑ v, g v ^ 2) := by ring
    _ ≤ (α + β) * ((∑ i, ∑ j, if G.Adj i j then (f i - f j) ^ 2 else 0) / 2) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ ≤ (α + β) * (d * γ) := mul_le_mul_of_nonneg_left h2 (by positivity)

theorem am67_step {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.Connected) (hn : 2 ≤ Fintype.card V)
    (u : V) (k k0 : ℕ) (hk : 1 ≤ k)
    (hkl : 2 * (G.maxDegree : ℝ) ≤ AlonMilman.Diameter.lambda1 G * ((k : ℝ) + 1) ^ 2)
    (hd : 0 < (G.maxDegree : ℝ)) :
    3 * (Finset.univ.filter (fun v => G.dist u v ≤ k0)).card *
        (Finset.univ.filter (fun v => k0 + k < G.dist u v)).card ≤
      (Finset.univ.filter (fun v => G.dist u v ≤ k0 + k)).card *
        (Finset.univ.filter (fun v => k0 < G.dist u v)).card := by
  have hlip : ∀ i j, G.Adj i j → G.dist u j ≤ G.dist u i + 1 := by
    intro i j hij
    have h1 := hG.dist_triangle (u := u) (v := i) (w := j)
    rw [SimpleGraph.dist_eq_one_iff_adj.mpr hij] at h1
    exact h1
  have H := am67_two_set G hG hn (fun v => ((min (G.dist u v - k0) (k + 1) : ℕ) : ℝ))
    (fun v => G.dist u v ≤ k0) (fun v => k0 + k < G.dist u v)
    (fun v => k0 < G.dist u v ∧ G.dist u v < k0 + (k + 1)) 0 ((k : ℝ) + 1)
    (by
      intro v hv
      have : min (G.dist u v - k0) (k + 1) = 0 := by omega
      simp [this])
    (by
      intro v hv
      have : min (G.dist u v - k0) (k + 1) = k + 1 := by omega
      simp [this])
    (by intro v h1 h2; omega)
    (by
      intro i j hij
      have h1 := hlip i j hij
      have h2 := hlip j i hij.symm
      have key : min (G.dist u i - k0) (k + 1) = min (G.dist u j - k0) (k + 1) ∨
          ((min (G.dist u i - k0) (k + 1) = min (G.dist u j - k0) (k + 1) + 1 ∨
            min (G.dist u j - k0) (k + 1) = min (G.dist u i - k0) (k + 1) + 1) ∧
           ((k0 < G.dist u i ∧ G.dist u i < k0 + (k + 1)) ∨
            (k0 < G.dist u j ∧ G.dist u j < k0 + (k + 1)))) := by omega
      rcases key with h | ⟨h, hC⟩
      · rw [h, sub_self]
        have e1 : (0:ℝ) ≤ (if k0 < G.dist u i ∧ G.dist u i < k0 + (k + 1) then 1 else 0) := by
          split_ifs <;> norm_num
        have e2 : (0:ℝ) ≤ (if k0 < G.dist u j ∧ G.dist u j < k0 + (k + 1) then 1 else 0) := by
          split_ifs <;> norm_num
        nlinarith
      · have hsq : (((min (G.dist u i - k0) (k + 1) : ℕ) : ℝ) -
            ((min (G.dist u j - k0) (k + 1) : ℕ) : ℝ)) ^ 2 = 1 := by
          rcases h with h | h
          · rw [h]; push_cast; ring
          · rw [h]; push_cast; ring
        rw [hsq]
        rcases hC with hC | hC
        · rw [if_pos hC]
          have : (0:ℝ) ≤ (if k0 < G.dist u j ∧ G.dist u j < k0 + (k + 1) then 1 else 0) := by
            split_ifs <;> norm_num
          linarith
        · rw [if_pos hC]
          have : (0:ℝ) ≤ (if k0 < G.dist u i ∧ G.dist u i < k0 + (k + 1) then 1 else 0) := by
            split_ifs <;> norm_num
          linarith)
  set α := (Finset.univ.filter (fun v => G.dist u v ≤ k0)).card with hα
  set β := (Finset.univ.filter (fun v => k0 + k < G.dist u v)).card with hβ
  set γ := (Finset.univ.filter (fun v => k0 < G.dist u v ∧ G.dist u v < k0 + (k + 1))).card
    with hγ
  set n := Fintype.card V with hn_def
  have hcnt : ∀ (Q : V → Prop) [DecidablePred Q],
      (Finset.univ.filter Q).card = ∑ v, if Q v then 1 else 0 := by
    intro Q _
    rw [Finset.card_filter]
  have hpart : α + β + γ = n := by
    rw [hα, hβ, hγ, hcnt, hcnt, hcnt, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    have : ∀ v, ((if G.dist u v ≤ k0 then 1 else 0) + (if k0 + k < G.dist u v then 1 else 0) +
        (if k0 < G.dist u v ∧ G.dist u v < k0 + (k + 1) then 1 else 0) : ℕ) = 1 := by
      intro v
      split_ifs <;> omega
    rw [Finset.sum_congr rfl (fun v _ => this v)]
    simp [n]
  have hA1 : (Finset.univ.filter (fun v => G.dist u v ≤ k0 + k)).card = α + γ := by
    rw [hα, hγ, hcnt, hcnt, hcnt, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun v _ => ?_
    split_ifs <;> omega
  have hB0 : (Finset.univ.filter (fun v => k0 < G.dist u v)).card = β + γ := by
    rw [hβ, hγ, hcnt, hcnt, hcnt, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun v _ => ?_
    split_ifs <;> omega
  have hsum : (α : ℝ) + β ≤ n := by
    have : α + β ≤ n := by omega
    exact_mod_cast this
  have hkey : 2 * α * β ≤ n * γ := by
    have hl := (show (0:ℝ) ≤ α * β by positivity)
    have hγ0 : (0:ℝ) ≤ γ := by positivity
    have e1 : 2 * (G.maxDegree : ℝ) * ((α : ℝ) * β) ≤
        AlonMilman.Diameter.lambda1 G * ((k : ℝ) + 1) ^ 2 * ((α : ℝ) * β) :=
      mul_le_mul_of_nonneg_right hkl hl
    have e2 : AlonMilman.Diameter.lambda1 G * ((k : ℝ) + 1) ^ 2 * ((α : ℝ) * β) =
        AlonMilman.Diameter.lambda1 G * ((α : ℝ) * β * (0 - ((k : ℝ) + 1)) ^ 2) := by ring
    have e3 : ((α : ℝ) + β) * ((G.maxDegree : ℝ) * γ) ≤ (n : ℝ) * ((G.maxDegree : ℝ) * γ) :=
      mul_le_mul_of_nonneg_right hsum (by positivity)
    have e4 : 2 * ((α : ℝ) * β) ≤ (n : ℝ) * γ := by
      have : (G.maxDegree : ℝ) * (2 * ((α : ℝ) * β)) ≤ (G.maxDegree : ℝ) * ((n : ℝ) * γ) := by
        nlinarith
      exact le_of_mul_le_mul_left this hd
    have : ((2 * α * β : ℕ) : ℝ) ≤ ((n * γ : ℕ) : ℝ) := by
      push_cast
      linarith
    exact_mod_cast this
  rw [hA1, hB0]
  have e : (α + γ) * (β + γ) = α * β + n * γ := by
    rw [← hpart]; ring
  rw [e]
  nlinarith

theorem am67_chain (A B : ℕ → ℕ) (t : ℕ) (hstep : ∀ j, 3 * A j * B (j + 1) ≤ A (j + 1) * B j)
    (hB : ∀ j ≤ t, 0 < B j) : ∀ j ≤ t, 3 ^ j * A 0 * B j ≤ A j * B 0 := by
  intro j
  induction j with
  | zero => intro _; simp
  | succ j ih =>
    intro hj
    have ih' := ih (by omega)
    have hBj := hB j (by omega)
    have hs := hstep j
    apply Nat.le_of_mul_le_mul_right _ hBj
    calc 3 ^ (j + 1) * A 0 * B (j + 1) * B j = 3 * B (j + 1) * (3 ^ j * A 0 * B j) := by ring
      _ ≤ 3 * B (j + 1) * (A j * B 0) := Nat.mul_le_mul_left _ ih'
      _ = B 0 * (3 * A j * B (j + 1)) := by ring
      _ ≤ B 0 * (A (j + 1) * B j) := Nat.mul_le_mul_left _ hs
      _ = A (j + 1) * B 0 * B j := by ring

theorem am67_pow (t m : ℕ) (hm : 1 ≤ m) (h : 3 ^ t ≤ m * m) :
    2 ^ (t + 2) ≤ (m + 1) * (m + 1) := by
  rcases Nat.lt_or_ge t 4 with ht | ht
  · interval_cases t
    · norm_num; nlinarith
    · have : 2 ≤ m := by
        by_contra hc
        have : m = 1 := by omega
        subst this; norm_num at h
      norm_num; nlinarith
    · have : 3 ≤ m := by
        by_contra hc
        have : m * m ≤ 2 * 2 := Nat.mul_le_mul (by omega) (by omega)
        norm_num at h; omega
      norm_num; nlinarith
    · have : 3 ≤ m := by
        by_contra hc
        have : m * m ≤ 2 * 2 := Nat.mul_le_mul (by omega) (by omega)
        norm_num at h; omega
      norm_num at h ⊢; nlinarith
  · obtain ⟨s, rfl⟩ : ∃ s, t = s + 4 := ⟨t - 4, by omega⟩
    have h4 : ∀ s : ℕ, 2 ^ (s + 4 + 2) ≤ 3 ^ (s + 4) := by
      intro s
      induction s with
      | zero => norm_num
      | succ s ih =>
        have e1 : 2 ^ (s + 1 + 4 + 2) = 2 * 2 ^ (s + 4 + 2) := by ring
        have e2 : 3 ^ (s + 1 + 4) = 3 * 3 ^ (s + 4) := by ring
        rw [e1, e2]; omega
    have := h4 s
    nlinarith

open AlonMilman.Diameter in
theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.Connected) (hn : 1 < Fintype.card V) :
    ∀ u v : V, G.dist u v ≤
      2 * ⌊Real.sqrt (2 * (G.maxDegree : ℝ) / lambda1 G) *
        Real.logb 2 (Fintype.card V : ℝ)⌋₊ := by
  intro u v
  have hn2 : 2 ≤ Fintype.card V := hn
  obtain ⟨hpos, -⟩ := am67_spec G hG hn2
  have hind := am67_two_set G hG hn2 (fun w => if w = u then (1:ℝ) else 0)
    (fun w => w = u) (fun w => w ≠ u) (fun w => w = u) 1 0
    (by intro w hw; simp [hw]) (by intro w hw; simp [hw]) (by intro w h1 h2; exact h2 h1)
    (by
      intro i j hij
      have hne : i ≠ j := G.ne_of_adj hij
      by_cases hi : i = u
      · have hj : j ≠ u := fun hj => hne (hi.trans hj.symm)
        simp [hi, hj]
      · by_cases hj : j = u
        · simp [hi, hj]
        · simp [hi, hj])
  have hcu : (Finset.univ.filter (fun w => w = u)).card = 1 := by simp [Finset.filter_eq']
  have hcnu : (Finset.univ.filter (fun w => w ≠ u)).card = Fintype.card V - 1 := by
    simp [Finset.filter_ne', Finset.card_erase_of_mem]
  rw [hcu, hcnu] at hind
  have hn1 : ((Fintype.card V - 1 : ℕ) : ℝ) = (Fintype.card V : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; simp
  rw [hn1] at hind
  have hnR : (2:ℝ) ≤ (Fintype.card V : ℝ) := by exact_mod_cast hn2
  norm_num at hind
  have hd0 : 0 < (G.maxDegree : ℝ) := by nlinarith
  have hlam2 : lambda1 G ≤ 2 * (G.maxDegree : ℝ) := by nlinarith
  set s := Real.sqrt (2 * (G.maxDegree : ℝ) / lambda1 G) with hs
  have hs2 : s ^ 2 = 2 * (G.maxDegree : ℝ) / lambda1 G := Real.sq_sqrt (by positivity)
  have hs1 : 1 ≤ s := by
    rw [hs, show (1:ℝ) = Real.sqrt 1 by simp]
    apply Real.sqrt_le_sqrt
    rw [le_div_iff₀ hpos]; linarith
  set k := ⌊s⌋₊ with hk
  have hk1 : 1 ≤ k := (Nat.one_le_floor_iff s).mpr hs1
  have hks : (k : ℝ) ≤ s := Nat.floor_le (by linarith)
  have hsk : s < (k : ℝ) + 1 := Nat.lt_floor_add_one s
  have hkl : 2 * (G.maxDegree : ℝ) ≤ lambda1 G * ((k : ℝ) + 1) ^ 2 := by
    have h1 : s ^ 2 ≤ ((k : ℝ) + 1) ^ 2 := by nlinarith
    rw [hs2, div_le_iff₀ hpos] at h1
    linarith
  set D := G.dist u v with hD
  rcases Nat.eq_zero_or_pos D with hD0 | hDpos
  · rw [hD0]; exact Nat.zero_le _
  set t := (D - 1) / k with ht
  have hDle : D ≤ (t + 1) * k := by
    have h1 := Nat.div_add_mod (D - 1) k
    have h2 := Nat.mod_lt (D - 1) (show 0 < k by omega)
    rw [← ht] at h1
    have e : (t + 1) * k = k * t + k := by ring
    rw [e]
    omega
  have htk : t * k < D := by
    have := Nat.div_mul_le_self (D - 1) k
    rw [← ht] at this
    omega
  have hstep : ∀ j, 3 * (Finset.univ.filter (fun w => G.dist u w ≤ j * k)).card *
      (Finset.univ.filter (fun w => (j + 1) * k < G.dist u w)).card ≤
      (Finset.univ.filter (fun w => G.dist u w ≤ (j + 1) * k)).card *
      (Finset.univ.filter (fun w => j * k < G.dist u w)).card := by
    intro j
    have := am67_step G hG hn2 u k (j * k) hk1 hkl hd0
    have e : (j + 1) * k = j * k + k := by ring
    rw [e]
    exact this
  have hBpos : ∀ j ≤ t, 0 < (Finset.univ.filter (fun w => j * k < G.dist u w)).card := by
    intro j hj
    apply Finset.card_pos.mpr
    refine ⟨v, ?_⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have : j * k ≤ t * k := Nat.mul_le_mul_right _ hj
    omega
  have hch := am67_chain (fun j => (Finset.univ.filter (fun w => G.dist u w ≤ j * k)).card)
    (fun j => (Finset.univ.filter (fun w => j * k < G.dist u w)).card) t hstep hBpos t le_rfl
  have hAB : ∀ j, (Finset.univ.filter (fun w => G.dist u w ≤ j * k)).card +
      (Finset.univ.filter (fun w => j * k < G.dist u w)).card = Fintype.card V := by
    intro j
    have h := Finset.card_filter_add_card_filter_not (s := Finset.univ)
      (fun w => G.dist u w ≤ j * k)
    have e : Finset.univ.filter (fun w => ¬ (G.dist u w ≤ j * k)) =
        Finset.univ.filter (fun w => j * k < G.dist u w) := by
      ext w; simp
    rw [e, Finset.card_univ] at h
    exact h
  have hA0 : 1 ≤ (Finset.univ.filter (fun w => G.dist u w ≤ 0 * k)).card := by
    apply Finset.card_pos.mpr
    exact ⟨u, by simp⟩
  have hBt := hBpos t le_rfl
  have hAt : (Finset.univ.filter (fun w => G.dist u w ≤ t * k)).card ≤ Fintype.card V - 1 := by
    have := hAB t; omega
  have hB0 : (Finset.univ.filter (fun w => 0 * k < G.dist u w)).card ≤ Fintype.card V - 1 := by
    have := hAB 0; omega
  have h3t : 3 ^ t ≤ (Fintype.card V - 1) * (Fintype.card V - 1) := by
    calc 3 ^ t = 3 ^ t * 1 * 1 := by ring
      _ ≤ 3 ^ t * (Finset.univ.filter (fun w => G.dist u w ≤ 0 * k)).card *
          (Finset.univ.filter (fun w => t * k < G.dist u w)).card :=
        Nat.mul_le_mul (Nat.mul_le_mul le_rfl hA0) hBt
      _ ≤ (Finset.univ.filter (fun w => G.dist u w ≤ t * k)).card *
          (Finset.univ.filter (fun w => 0 * k < G.dist u w)).card := hch
      _ ≤ (Fintype.card V - 1) * (Fintype.card V - 1) := Nat.mul_le_mul hAt hB0
  have hpow := am67_pow t (Fintype.card V - 1) (by omega) h3t
  have hn' : Fintype.card V - 1 + 1 = Fintype.card V := by omega
  rw [hn'] at hpow
  set L := Real.logb 2 (Fintype.card V : ℝ) with hL
  have hL2 : ((t : ℝ) + 2) ≤ 2 * L := by
    have h1 : ((2:ℝ) ^ (t + 2)) ≤ (Fintype.card V : ℝ) ^ 2 := by
      rw [sq]; exact_mod_cast hpow
    have h2 := Real.logb_le_logb_of_le (b := 2) (by norm_num) (by positivity) h1
    rw [Real.logb_pow, Real.logb_pow, Real.logb_self_eq_one (by norm_num)] at h2
    push_cast at h2
    linarith
  have hh : (D + 1) / 2 ≤ ⌊s * L⌋₊ := by
    apply Nat.le_floor
    have e1 : ((D + 1) / 2) * 2 ≤ D + 1 := Nat.div_mul_le_self _ _
    have e2 : D + 1 ≤ (t + 2) * k := by
      have e : (t + 2) * k = (t + 1) * k + k := by ring
      rw [e]; omega
    have e3 : (((D + 1) / 2 : ℕ) : ℝ) * 2 ≤ ((t : ℝ) + 2) * k := by
      have : ((D + 1) / 2) * 2 ≤ (t + 2) * k := le_trans e1 e2
      exact_mod_cast this
    have ht0 : (0:ℝ) ≤ t := Nat.cast_nonneg t
    have e4 : ((t : ℝ) + 2) * k ≤ 2 * L * s := by
      calc ((t : ℝ) + 2) * k ≤ 2 * L * k := mul_le_mul_of_nonneg_right hL2 (by positivity)
        _ ≤ 2 * L * s := mul_le_mul_of_nonneg_left hks (by linarith)
    nlinarith
  omega
