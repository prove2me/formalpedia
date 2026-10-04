-- Prove2me | solution 1 for AlonMilman.PropertyT.rayleigh_cayley
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T09:44:49.611392+00:00
-- url     : https://prove2.me/submissions/22335214-3822-43fd-a059-8503a22dfeac

import Mathlib
import Definitions.Def_AlonMilman_PropertyT_lambda1
import Definitions.Def_AlonMilman_PropertyT_laplacian
import Definitions.Def_AlonMilman_PropertyT_cayleyMultigraph

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

open Matrix WithLp in
theorem rc48_general {n : Type} [Fintype n] [DecidableEq n] (Q : Matrix n n ℝ)
    (hA : Q.IsHermitian) (hn : 2 ≤ Fintype.card n)
    (hpsd : ∀ y : n → ℝ, 0 ≤ y ⬝ᵥ (Q *ᵥ y)) (h1 : Q *ᵥ (fun _ => (1:ℝ)) = 0) :
    IsLeast {r : ℝ | ∃ y : n → ℝ, ∑ t, y t = 0 ∧ y ⬝ᵥ y = 1 ∧ r = y ⬝ᵥ (Q *ᵥ y)}
      (AlonMilman.PropertyT.lambda1 Q) := by
  classical
  set N := Fintype.card n with hN_def
  set T := Matrix.toEuclideanLin Q with hT_def
  have hT : T.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr hA
  have hfin : Module.finrank ℝ (EuclideanSpace ℝ n) = N := finrank_euclideanSpace
  set b := hT.eigenvectorBasis hfin with hb
  set μ := hT.eigenvalues hfin with hμ
  set last : Fin N := ⟨N - 1, by omega⟩ with hlast
  set sec : Fin N := ⟨N - 2, by omega⟩ with hsec
  have hlam : AlonMilman.PropertyT.lambda1 Q = μ sec := by
    unfold AlonMilman.PropertyT.lambda1
    rw [dif_pos ⟨hA, hn⟩]
    rfl
  -- conversions
  set one : EuclideanSpace ℝ n := toLp 2 (fun _ => (1:ℝ)) with hone
  have cQ : ∀ x : EuclideanSpace ℝ n, ofLp x ⬝ᵥ (Q *ᵥ ofLp x) = inner ℝ (T x) x := by
    intro x
    change _ = ofLp x ⬝ᵥ star (Q *ᵥ ofLp x)
    simp
  have cN : ∀ x : EuclideanSpace ℝ n, ofLp x ⬝ᵥ ofLp x = inner ℝ x x := by
    intro x
    change _ = ofLp x ⬝ᵥ star (ofLp x)
    simp
  have cS : ∀ x : EuclideanSpace ℝ n, ∑ t, ofLp x t = inner ℝ x one := by
    intro x
    change _ = (fun _ => (1:ℝ)) ⬝ᵥ star (ofLp x)
    simp [dotProduct]
  have hTone : T one = 0 := by
    change toLp 2 (Q *ᵥ (fun _ => (1:ℝ))) = 0
    rw [h1]; rfl
  have hQb : ∀ i, inner ℝ (T (b i)) (b i) = μ i := by
    intro i
    rw [hT.apply_eigenvectorBasis hfin i, real_inner_smul_left, real_inner_self_eq_norm_sq,
      b.norm_eq_one]
    simp [μ]
  have hμnn : ∀ i, 0 ≤ μ i := by
    intro i
    rw [← hQb, ← cQ]
    exact hpsd _
  have hzero : ∀ i, μ i * inner ℝ (b i) one = 0 := by
    intro i
    have := hT (b i) one
    rw [hTone, inner_zero_right, hT.apply_eigenvectorBasis hfin i, real_inner_smul_left] at this
    simpa [μ] using this
  have hexp : ∀ x : EuclideanSpace ℝ n, inner ℝ (T x) x = ∑ i, μ i * (inner ℝ (b i) x) ^ 2 := by
    intro x
    rw [← b.sum_inner_mul_inner (T x) x]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hT x (b i), hT.apply_eigenvectorBasis hfin i, inner_smul_right, real_inner_comm x (b i)]
    simp only [RCLike.ofReal_real_eq_id, id]
    ring
  have hnorm : ∀ x : EuclideanSpace ℝ n, ∑ i, (inner ℝ (b i) x) ^ 2 = inner ℝ x x := by
    intro x
    rw [← b.sum_inner_mul_inner x x]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [real_inner_comm x (b i)]; ring
  have hanti := hT.eigenvalues_antitone hfin
  have hμsec : ∀ i, i ≠ last → μ sec ≤ μ i := by
    intro i hi
    apply hanti
    rw [Fin.le_iff_val_le_val]
    have h1 := i.isLt
    have h2 : i.val ≠ N - 1 := fun h => hi (Fin.ext h)
    simp only [sec]
    omega
  have hlast_le : μ last ≤ μ sec := by
    apply hanti
    rw [Fin.le_iff_val_le_val]
    simp only [sec, last]
    omega
  have hne : sec ≠ last := by
    intro h
    have := congrArg Fin.val h
    simp only [sec, last] at this
    omega
  have hone_ne : inner ℝ one one = (N : ℝ) := by
    change (fun _ => (1:ℝ)) ⬝ᵥ star (fun _ => (1:ℝ)) = _
    simp [dotProduct, N]
  rw [hlam]
  constructor
  · -- membership
    by_cases hbs : inner ℝ (b sec) one = 0
    · refine ⟨ofLp (b sec), ?_, ?_, ?_⟩
      · rw [cS]; exact hbs
      · rw [cN, real_inner_self_eq_norm_sq, b.norm_eq_one]; norm_num
      · rw [cQ, hQb]
    · have hs0 : μ sec = 0 := by
        rcases mul_eq_zero.1 (hzero sec) with h | h
        · exact h
        · exact absurd h hbs
      have hl0 : μ last = 0 := le_antisymm (hs0 ▸ hlast_le) (hμnn last)
      set α := inner ℝ (b last) one with hα
      set β := inner ℝ (b sec) one with hβ
      set x : EuclideanSpace ℝ n := α • b sec - β • b last with hx
      have hTx : T x = 0 := by
        rw [hx, map_sub, map_smul, map_smul, hT.apply_eigenvectorBasis hfin,
          hT.apply_eigenvectorBasis hfin]
        simp [μ] at hs0 hl0 ⊢
        rw [hs0, hl0]; simp
      have hD : inner ℝ x x = α ^ 2 + β ^ 2 := by
        have e1 : inner ℝ (b sec) (b sec) = 1 := by
          rw [real_inner_self_eq_norm_sq, b.norm_eq_one]; norm_num
        have e2 : inner ℝ (b last) (b last) = 1 := by
          rw [real_inner_self_eq_norm_sq, b.norm_eq_one]; norm_num
        have e3 : inner ℝ (b sec) (b last) = 0 := b.orthonormal.2 hne
        have e4 : inner ℝ (b last) (b sec) = 0 := b.orthonormal.2 hne.symm
        rw [hx]
        simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right,
          e1, e2, e3, e4]
        ring
      have hxo : inner ℝ x one = 0 := by
        rw [hx, inner_sub_left, real_inner_smul_left, real_inner_smul_left]
        ring
      have hDpos : 0 < α ^ 2 + β ^ 2 := by positivity
      set c : ℝ := 1 / Real.sqrt (α ^ 2 + β ^ 2) with hc
      have hc2 : c ^ 2 * (α ^ 2 + β ^ 2) = 1 := by
        rw [hc, div_pow, Real.sq_sqrt hDpos.le]
        field_simp
      refine ⟨ofLp (c • x), ?_, ?_, ?_⟩
      · rw [cS, real_inner_smul_left, hxo, mul_zero]
      · rw [cN, real_inner_smul_left, real_inner_smul_right, hD, ← hc2]; ring
      · rw [cQ, map_smul, hTx, smul_zero, inner_zero_left, hs0]
  · -- lower bound
    rintro r ⟨y, hy0, hy1, rfl⟩
    set x : EuclideanSpace ℝ n := toLp 2 y with hx
    have hy0' : inner ℝ x one = 0 := by rw [← cS]; exact hy0
    have hy1' : inner ℝ x x = 1 := by rw [← cN]; exact hy1
    rw [show y = ofLp x from rfl, cQ]
    by_cases hs : μ sec = 0
    · rw [hs, ← cQ]; exact hpsd _
    have hspos : 0 < μ sec := lt_of_le_of_ne (hμnn sec) (Ne.symm hs)
    have hoth : ∀ i, i ≠ last → inner ℝ (b i) one = 0 := by
      intro i hi
      rcases mul_eq_zero.1 (hzero i) with h | h
      · have := hμsec i hi; linarith
      · exact h
    have hsum1 : ∀ z : EuclideanSpace ℝ n,
        inner ℝ z one = inner ℝ z (b last) * inner ℝ (b last) one := by
      intro z
      rw [← b.sum_inner_mul_inner z one]
      rw [Finset.sum_eq_single last]
      · intro i _ hi; rw [hoth i hi, mul_zero]
      · intro h; exact absurd (Finset.mem_univ _) h
    have hlo : inner ℝ (b last) one ≠ 0 := by
      intro h
      have := hsum1 one
      rw [h, mul_zero, hone_ne] at this
      have : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
      linarith
    have hxl : inner ℝ (b last) x = 0 := by
      have := hsum1 x
      rw [hy0'] at this
      rcases mul_eq_zero.1 this.symm with h | h
      · rw [real_inner_comm]; exact h
      · exact absurd h hlo
    rw [hexp, ← mul_one (μ sec), ← hy1', ← hnorm, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    by_cases hi : i = last
    · rw [hi, hxl]; simp
    · exact mul_le_mul_of_nonneg_right (hμsec i hi) (sq_nonneg _)

open Matrix in
theorem rc48_lap_facts {n : Type} [Fintype n] [DecidableEq n] (M : Matrix n n ℕ)
    (hM : ∀ v w, M v w = M w v) :
    (AlonMilman.PropertyT.laplacian M).IsHermitian ∧
    (∀ y : n → ℝ, 0 ≤ y ⬝ᵥ (AlonMilman.PropertyT.laplacian M *ᵥ y)) ∧
    AlonMilman.PropertyT.laplacian M *ᵥ (fun _ => (1:ℝ)) = 0 := by
  have hent : ∀ i j, AlonMilman.PropertyT.laplacian M i j =
      (if i = j then ∑ w, (M i w : ℝ) else 0) - (M i j : ℝ) := by
    intro i j
    simp [AlonMilman.PropertyT.laplacian, Matrix.sub_apply, diagonal_apply]
  have hL : ∀ (y : n → ℝ) v, (AlonMilman.PropertyT.laplacian M *ᵥ y) v =
      (∑ w, (M v w : ℝ)) * y v - ∑ w, (M v w : ℝ) * y w := by
    intro y v
    simp only [mulVec, dotProduct, hent, sub_mul, Finset.sum_sub_distrib, ite_mul, zero_mul,
      Finset.sum_ite_eq, Finset.mem_univ, if_true]
  refine ⟨?_, ?_, ?_⟩
  · ext i j
    rw [conjTranspose_apply, star_trivial, hent, hent, hM j i]
    by_cases h : i = j
    · subst h; rfl
    · rw [if_neg h, if_neg (Ne.symm h)]
  · intro y
    have key : y ⬝ᵥ (AlonMilman.PropertyT.laplacian M *ᵥ y) =
        (∑ v, ∑ w, (M v w : ℝ) * (y v - y w) ^ 2) / 2 := by
      simp only [dotProduct, hL]
      have hsw : ∑ v, ∑ w, (M v w : ℝ) * y w ^ 2 = ∑ v, ∑ w, (M v w : ℝ) * y v ^ 2 := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun w _ => ?_
        rw [hM w v]
      have hexp : ∑ v, ∑ w, (M v w : ℝ) * (y v - y w) ^ 2 =
          ∑ v, ∑ w, (M v w : ℝ) * y v ^ 2 + ∑ v, ∑ w, (M v w : ℝ) * y w ^ 2
            - 2 * ∑ v, ∑ w, (M v w : ℝ) * (y v * y w) := by
        simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun w _ => ?_
        ring
      rw [hexp, hsw]
      have a3 : ∑ v, y v * ((∑ w, (M v w : ℝ)) * y v - ∑ w, (M v w : ℝ) * y w) =
          ∑ v, ∑ w, (M v w : ℝ) * y v ^ 2 - ∑ v, ∑ w, (M v w : ℝ) * (y v * y w) := by
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun v _ => ?_
        rw [mul_sub, Finset.sum_mul, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
          ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun w _ => ?_
        ring
      rw [a3]
      ring
    rw [key]
    apply div_nonneg _ (by norm_num)
    exact Finset.sum_nonneg fun v _ => Finset.sum_nonneg fun w _ => by positivity
  · ext v
    rw [hL]
    simp

theorem rc48_symm {H T : Type} [Group H] [Group T] [DecidableEq T]
    (φ : H →* T) (S : Finset H) (hSinv : ∀ s ∈ S, s⁻¹ ∈ S) (v w : T) :
    AlonMilman.PropertyT.cayleyMultigraph φ S v w = AlonMilman.PropertyT.cayleyMultigraph φ S w v := by
  unfold AlonMilman.PropertyT.cayleyMultigraph
  refine Finset.card_bij' (fun s _ => s⁻¹) (fun s _ => s⁻¹) ?_ ?_ ?_ ?_
  · intro s hs
    simp only [Finset.mem_filter] at hs ⊢
    refine ⟨hSinv s hs.1, ?_⟩
    rw [map_inv, ← hs.2]; group
  · intro s hs
    simp only [Finset.mem_filter] at hs ⊢
    refine ⟨hSinv s hs.1, ?_⟩
    rw [map_inv, ← hs.2]; group
  · intro s _; simp
  · intro s _; simp

open Matrix AlonMilman.PropertyT in
theorem solution {H T : Type} [Group H] [Group T] [Fintype T] [DecidableEq T]
    (φ : H →* T) (S : Finset H) (hSinv : ∀ s ∈ S, s⁻¹ ∈ S) (hT : 2 ≤ Fintype.card T) :
    IsLeast {r : ℝ | ∃ y : T → ℝ, ∑ t, y t = 0 ∧ y ⬝ᵥ y = 1 ∧
        r = y ⬝ᵥ (laplacian (cayleyMultigraph φ S) *ᵥ y)}
      (lambda1 (laplacian (cayleyMultigraph φ S))) := by
  obtain ⟨h1, h2, h3⟩ := rc48_lap_facts (cayleyMultigraph φ S) (rc48_symm φ S hSinv)
  exact rc48_general _ h1 hT h2 h3
