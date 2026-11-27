-- Prove2me | solution 1 for AlonMilman.PropertyT.Supplement.theorem_4_3
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:06:21.336675+00:00
-- url     : https://prove2.me/submissions/5d7e7cb7-8278-4c77-bedb-c2cb3e0edb49

import Mathlib
import Definitions.Def_AlonMilman_PropertyT_IsEnlarger
import Definitions.Def_AlonMilman_PropertyT_Supplement_extendedDoubleCover
import Definitions.Def_AlonMilman_PropertyT_Supplement_IsExpander

open AlonMilman
open AlonMilman.PropertyT
open AlonMilman.PropertyT.Supplement

/-- Theorem 4.3 (Alon–Milman 1985, p. 83). Let `G = (V, E)` be an `(n, k, ε)`-enlarger with
`ε > 0` (a `k`-regular, possibly multi-, graph on `n` vertices with `λ₁(G) ≥ ε`) and let `H` be
its extended double cover. Then `H` is an `(n, k + 1, c)`-expander for `c = 4ε / (k + 4ε)`. -/
theorem solution {V : Type} [Fintype V] [DecidableEq V] (n k : ℕ) (ε : ℝ) (hε : 0 < ε)
    (M : Matrix V V ℕ) (hM : AlonMilman.PropertyT.IsEnlarger n k ε M) :
    IsExpander n (k + 1) (4 * ε / ((k : ℝ) + 4 * ε)) (extendedDoubleCover M) := by
      open Matrix in
      focus
        classical
        obtain ⟨hcard, hsymm, hreg, hlam⟩ := hM
        set Q := AlonMilman.PropertyT.laplacian M with hQ
        have hQe : ∀ v w, Q v w = (if v = w then ∑ u, (M v u : ℝ) else 0) - (M v w : ℝ) := by
          intro v w
          simp [hQ, AlonMilman.PropertyT.laplacian, Matrix.diagonal_apply]
        have hdeg : ∀ v, ∑ u, (M v u : ℝ) = k := by
          intro v; exact_mod_cast hreg v
        have hMs : ∀ v w, M v w = M w v := fun v w => by
          have := congrFun (congrFun hsymm w) v
          simpa [Matrix.transpose_apply] using this
        have hquad : ∀ h : V → ℝ, h ⬝ᵥ (Q *ᵥ h) = (1/2) * ∑ v, ∑ w, (M v w : ℝ) * (h v - h w)^2 := by
          intro h
          have e1 : h ⬝ᵥ (Q *ᵥ h) = ∑ v, ∑ w, (M v w : ℝ) * (h v ^2 - h v * h w) := by
            simp only [dotProduct, mulVec]
            refine Finset.sum_congr rfl fun v _ => ?_
            have hrow : ∑ w, Q v w * h w = (∑ u, (M v u : ℝ)) * h v - ∑ w, (M v w : ℝ) * h w := by
              simp [hQe, sub_mul, Finset.sum_sub_distrib, ite_mul, Finset.sum_ite_eq]
            rw [hrow, mul_sub, Finset.sum_mul, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
            refine Finset.sum_congr rfl fun w _ => ?_
            ring
          have e2 : ∑ v, ∑ w, (M v w : ℝ) * (h w^2 - h v * h w)
              = ∑ v, ∑ w, (M v w : ℝ) * (h v^2 - h v * h w) := by
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun w _ => ?_
            rw [hMs]; ring
          have e3 : ∑ v, ∑ w, (M v w : ℝ) * (h v - h w)^2
              = ∑ v, ∑ w, (M v w : ℝ) * (h v^2 - h v * h w)
                + ∑ v, ∑ w, (M v w : ℝ) * (h w^2 - h v * h w) := by
            rw [← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl fun v _ => ?_
            rw [← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl fun w _ => ?_
            ring
          rw [e1, e3, e2]; ring
        have hH : Q.IsHermitian := by
          ext v w
          simp only [Matrix.conjTranspose_apply, star_trivial, hQe]
          by_cases hvw : v = w
          · subst hvw; simp
          · have : ¬ w = v := fun h => hvw h.symm
            simp [hvw, this, hMs]
        have hc2 : 2 ≤ Fintype.card V := by
          by_contra hc
          have : AlonMilman.PropertyT.lambda1 Q = 0 := by
            unfold AlonMilman.PropertyT.lambda1
            rw [dif_neg (fun h => hc h.2)]
          linarith
        set L := hH.eigenvalues₀ ⟨Fintype.card V - 2, by omega⟩ with hL
        have hlamL : AlonMilman.PropertyT.lambda1 Q = L := by
          unfold AlonMilman.PropertyT.lambda1
          rw [dif_pos ⟨hH, hc2⟩]
        rw [hlamL] at hlam
        -- spectral Rayleigh bound
        set b := hH.eigenvectorBasis with hb
        set E := (Fintype.equivOfCardEq (Fintype.card_fin _) : Fin (Fintype.card V) ≃ V) with hE
        have hμ : ∀ i, hH.eigenvalues i = hH.eigenvalues₀ (E.symm i) := fun i => rfl
        set i₀ := E ⟨Fintype.card V - 1, by omega⟩ with hi₀
        have hμL : ∀ i, i ≠ i₀ → L ≤ hH.eigenvalues i := by
          intro i hi
          rw [hμ]
          apply hH.eigenvalues₀_antitone
          have h1 : E.symm i ≠ ⟨Fintype.card V - 1, by omega⟩ := by
            intro h; apply hi; rw [hi₀, ← h]; simp
          have h2 := (E.symm i).isLt
          have h3 : (E.symm i).val ≠ Fintype.card V - 1 := fun h => h1 (Fin.ext h)
          show (E.symm i).val ≤ Fintype.card V - 2
          omega
        have hexp : ∀ h : V → ℝ, h = ∑ i, ((b i).ofLp ⬝ᵥ h) • (b i).ofLp := by
          intro h
          have := b.sum_repr' (WithLp.toLp 2 h)
          have := congrArg WithLp.ofLp this
          simp only [WithLp.ofLp_sum, WithLp.ofLp_smul] at this
          conv_lhs => rw [← this]
          refine Finset.sum_congr rfl fun i _ => ?_
          congr 1
          simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
        have hR : ∀ h : V → ℝ, (hH.eigenvalues i₀ - L) * ((b i₀).ofLp ⬝ᵥ h)^2
            ≤ h ⬝ᵥ (Q *ᵥ h) - L * (h ⬝ᵥ h) := by
          intro h
          have hQh : Q *ᵥ h = ∑ i, (((b i).ofLp ⬝ᵥ h) * hH.eigenvalues i) • (b i).ofLp := by
            conv_lhs => rw [hexp h]
            rw [Matrix.mulVec_sum]
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [Matrix.mulVec_smul, hb, hH.mulVec_eigenvectorBasis, smul_smul]
          have q1 : h ⬝ᵥ (Q *ᵥ h) = ∑ i, hH.eigenvalues i * ((b i).ofLp ⬝ᵥ h)^2 := by
            rw [hQh, dotProduct_sum]
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [dotProduct_smul, dotProduct_comm h, smul_eq_mul]; ring
          have q2 : h ⬝ᵥ h = ∑ i, ((b i).ofLp ⬝ᵥ h)^2 := by
            conv_lhs => arg 2; rw [hexp h]
            rw [dotProduct_sum]
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [dotProduct_smul, dotProduct_comm h, smul_eq_mul]; ring
          rw [q1, q2, Finset.mul_sum, ← Finset.sum_sub_distrib]
          have : ∀ i ∈ Finset.univ, (if i = i₀ then (hH.eigenvalues i₀ - L) * ((b i₀).ofLp ⬝ᵥ h)^2 else 0)
              ≤ hH.eigenvalues i * ((b i).ofLp ⬝ᵥ h)^2 - L * ((b i).ofLp ⬝ᵥ h)^2 := by
            intro i _
            by_cases hi : i = i₀
            · subst hi; simp; ring_nf; rfl
            · simp only [hi, if_false]
              have := hμL i hi
              nlinarith [sq_nonneg ((b i).ofLp ⬝ᵥ h)]
          have := Finset.sum_le_sum this
          simpa using this
        -- consequences of the quadratic form
        have hLpos : 0 < L := lt_of_lt_of_le hε hlam
        have hnpos : (0:ℝ) < Fintype.card V := by exact_mod_cast (show 0 < Fintype.card V by omega)
        have hshift : ∀ (f : V → ℝ) (t : ℝ), (fun v => f v + t) ⬝ᵥ (Q *ᵥ (fun v => f v + t))
            = f ⬝ᵥ (Q *ᵥ f) := by
          intro f t
          rw [hquad, hquad]
          congr 1
          refine Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun w _ => ?_
          ring
        have hc1 : (b i₀).ofLp ⬝ᵥ (fun _ => (1:ℝ)) ≠ 0 := by
          intro h0
          have := hR (fun _ => (1:ℝ))
          rw [h0, hquad] at this
          simp [dotProduct] at this
          nlinarith
        have hRay : ∀ f : V → ℝ, ∃ t : ℝ, L * ((fun v => f v + t) ⬝ᵥ (fun v => f v + t)) ≤ f ⬝ᵥ (Q *ᵥ f) := by
          intro f
          refine ⟨-((b i₀).ofLp ⬝ᵥ f) / ((b i₀).ofLp ⬝ᵥ (fun _ => (1:ℝ))), ?_⟩
          have := hR (fun v => f v + -((b i₀).ofLp ⬝ᵥ f) / ((b i₀).ofLp ⬝ᵥ (fun _ => (1:ℝ))))
          have hz : (b i₀).ofLp ⬝ᵥ (fun v => f v + -((b i₀).ofLp ⬝ᵥ f) / ((b i₀).ofLp ⬝ᵥ (fun _ => (1:ℝ)))) = 0 := by
            have : (fun v => f v + -((b i₀).ofLp ⬝ᵥ f) / ((b i₀).ofLp ⬝ᵥ (fun _ => (1:ℝ))))
                = f + (-((b i₀).ofLp ⬝ᵥ f) / ((b i₀).ofLp ⬝ᵥ (fun _ => (1:ℝ)))) • (fun _ => (1:ℝ)) := by
              ext v; simp
            rw [this, dotProduct_add, dotProduct_smul, smul_eq_mul]
            field_simp
            ring
          rw [hz, hshift] at this
          linarith
        -- the expander property
        refine ⟨hcard, hcard, ?_, ?_⟩
        · -- edge count
          have h1 : (extendedDoubleCover M).card
              = ∑ v, ∑ w, (if v = w ∨ 0 < M v w then 1 else 0) := by
            unfold extendedDoubleCover
            rw [Finset.card_filter, ← Finset.univ_product_univ, Finset.sum_product]
          rw [h1, ← hcard]
          have h2 : ∀ v, ∑ w, (if v = w ∨ 0 < M v w then 1 else 0) ≤ k + 1 := by
            intro v
            calc ∑ w, (if v = w ∨ 0 < M v w then 1 else 0)
                ≤ ∑ w, ((if v = w then 1 else 0) + M v w) := by
                  refine Finset.sum_le_sum fun w _ => ?_
                  by_cases h : v = w
                  · simp [h]
                  · by_cases h' : 0 < M v w
                    · simp [h, h']; omega
                    · simp [h, h']
              _ = k + 1 := by
                  rw [Finset.sum_add_distrib, hreg]; simp; ring
          calc ∑ v, ∑ w, (if v = w ∨ 0 < M v w then 1 else 0) ≤ ∑ _v : V, (k + 1) :=
                Finset.sum_le_sum fun v _ => h2 v
            _ = (k + 1) * Fintype.card V := by simp [mul_comm]
        · intro A
          set N := bipNeighbors (extendedDoubleCover M) A with hN
          have hmemN : ∀ w, w ∈ N ↔ ∃ v ∈ A, v = w ∨ 0 < M v w := by
            intro w
            simp [hN, bipNeighbors, extendedDoubleCover]
            constructor
            · rintro (h | ⟨v, h1, h2⟩)
              · exact ⟨w, h, Or.inl rfl⟩
              · exact ⟨v, h2, Or.inr h1⟩
            · rintro ⟨v, hv, rfl | h⟩
              · exact Or.inl hv
              · exact Or.inr ⟨v, h, hv⟩
          have hAN : A ⊆ N := fun v hv => (hmemN v).2 ⟨v, hv, Or.inl rfl⟩
          obtain ⟨C, hC⟩ : ∃ C : Finset V, C = N \ A := ⟨_, rfl⟩
          obtain ⟨B, hB⟩ : ∃ B : Finset V, B = Finset.univ \ N := ⟨_, rfl⟩
          obtain ⟨a, ha⟩ : ∃ a : ℝ, a = (A.card : ℝ) := ⟨_, rfl⟩
          obtain ⟨x, hx⟩ : ∃ x : ℝ, x = (C.card : ℝ) := ⟨_, rfl⟩
          obtain ⟨bb, hbb⟩ : ∃ bb : ℝ, bb = (B.card : ℝ) := ⟨_, rfl⟩
          have hsize : a + x + bb = Fintype.card V := by
            have h1 : (N \ A).card + A.card = N.card := Finset.card_sdiff_add_card_eq_card hAN
            have h2 : (Finset.univ \ N).card + N.card = Fintype.card V := by
              rw [Finset.card_sdiff_add_card_eq_card (Finset.subset_univ _), Finset.card_univ]
            rw [ha, hx, hbb, hC, hB]
            have h3 : A.card + (N \ A).card + (Finset.univ \ N).card = Fintype.card V := by omega
            exact_mod_cast h3
          have hNcard : (N.card : ℝ) = a + x := by
            have h1 : (N \ A).card + A.card = N.card := Finset.card_sdiff_add_card_eq_card hAN
            rw [ha, hx, hC, ← h1]; push_cast; ring
          -- test vector
          obtain ⟨f, hf⟩ : ∃ f : V → ℝ, f = fun v => if v ∈ A then 2 * bb else if v ∈ N then bb - a else -2 * a := ⟨_, rfl⟩
          have ha0 : 0 ≤ a := by rw [ha]; exact Nat.cast_nonneg _
          have hx0 : 0 ≤ x := by rw [hx]; exact Nat.cast_nonneg _
          have hb0 : 0 ≤ bb := by rw [hbb]; exact Nat.cast_nonneg _
          have hpt : ∀ v w, 0 < M v w → (f v - f w)^2 ≤ (a + bb)^2 *
              ((if v ∈ C then 1 else 0) + (if w ∈ C then 1 else 0)) := by
            intro v w hvw
            have h1 : v ∈ A → w ∈ N := fun hv => (hmemN w).2 ⟨v, hv, Or.inr hvw⟩
            have h2 : w ∈ A → v ∈ N := fun hw => (hmemN v).2 ⟨w, hw, Or.inr (by rw [hMs]; exact hvw)⟩
            have h3 : v ∈ A → v ∈ N := fun h => hAN h
            have h4 : w ∈ A → w ∈ N := fun h => hAN h
            by_cases hvA : v ∈ A <;> by_cases hvN : v ∈ N <;> by_cases hwA : w ∈ A <;>
              by_cases hwN : w ∈ N <;> simp [hf, hC, hvA, hvN, hwA, hwN] at h1 h2 h3 h4 ⊢ <;>
              nlinarith [sq_nonneg (a + bb)]
          have hpt2 : ∀ v w, (M v w : ℝ) * (f v - f w)^2 ≤ (a + bb)^2 *
              ((M v w : ℝ) * (if v ∈ C then 1 else 0) + (M v w : ℝ) * (if w ∈ C then 1 else 0)) := by
            intro v w
            rcases Nat.eq_zero_or_pos (M v w) with h0 | hpos
            · simp [h0]
            · have := hpt v w hpos
              have hm : (0:ℝ) ≤ M v w := Nat.cast_nonneg _
              calc (M v w : ℝ) * (f v - f w)^2 ≤ (M v w : ℝ) * ((a + bb)^2 *
                  ((if v ∈ C then 1 else 0) + (if w ∈ C then 1 else 0))) :=
                    mul_le_mul_of_nonneg_left this hm
                _ = _ := by ring
          have hS1 : ∑ v, ∑ w, (M v w : ℝ) * (if v ∈ C then 1 else 0) = k * x := by
            simp_rw [← Finset.sum_mul, hdeg]
            rw [← Finset.mul_sum, hx]
            simp
          have hS2 : ∑ v, ∑ w, (M v w : ℝ) * (if w ∈ C then 1 else 0) = k * x := by
            rw [Finset.sum_comm]
            simp_rw [← Finset.sum_mul]
            have : ∀ w, ∑ v, (M v w : ℝ) = k := fun w => by
              rw [← hdeg w]; exact Finset.sum_congr rfl fun v _ => by rw [hMs]
            simp_rw [this]
            rw [← Finset.mul_sum, hx]
            simp
          have hQf : f ⬝ᵥ (Q *ᵥ f) ≤ (a + bb)^2 * k * x := by
            rw [hquad]
            have := Finset.sum_le_sum fun v (_ : v ∈ Finset.univ) =>
              Finset.sum_le_sum fun w (_ : w ∈ Finset.univ) => hpt2 v w
            simp only [← Finset.mul_sum, Finset.sum_add_distrib, hS1, hS2] at this
            nlinarith
          have hnorm : ∀ t : ℝ, 4 * a * bb * (a + bb) ≤ (fun v => f v + t) ⬝ᵥ (fun v => f v + t) := by
            intro t
            have hle : ∀ v ∈ Finset.univ, (if v ∈ A then (2 * bb + t)^2 else 0)
                + (if v ∈ B then (t - 2 * a)^2 else 0) ≤ (f v + t) * (f v + t) := by
              intro v _
              by_cases hvA : v ∈ A
              · have : v ∈ N := hAN hvA
                simp [hf, hB, hvA, this]; nlinarith
              · by_cases hvN : v ∈ N
                · simp [hf, hB, hvA, hvN]; nlinarith
                · simp [hf, hB, hvA, hvN]; nlinarith
            have := Finset.sum_le_sum hle
            rw [Finset.sum_add_distrib, Finset.sum_ite_mem, Finset.sum_ite_mem] at this
            simp only [Finset.univ_inter, Finset.sum_const, nsmul_eq_mul] at this
            simp only [dotProduct]
            rw [← ha, ← hbb] at this
            nlinarith [sq_nonneg t, mul_nonneg ha0 hb0]
          obtain ⟨t, ht⟩ := hRay f
          have hmain : 4 * ε * a * bb * (a + bb) ≤ (a + bb)^2 * k * x := by
            have := hnorm t
            have h4 : 0 ≤ 4 * a * bb * (a + bb) := mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) ha0) hb0) (add_nonneg ha0 hb0)
            nlinarith
          clear * - hmain hNcard ha hcard hx0 ha0 hb0 hsize hnpos hε
          rw [hNcard, ← ha, ← hcard]
          have hk : (0:ℝ) ≤ k := Nat.cast_nonneg _
          by_cases ha' : a = 0
          · rw [ha']; simp; exact hx0
          have hapos : 0 < a := lt_of_le_of_ne ha0 (Ne.symm ha')
          have hab : 0 < a + bb := by linarith
          have h5 : 4 * ε * a * bb ≤ (a + bb) * k * x := by
            have : (a + bb) * (4 * ε * a * bb) ≤ (a + bb) * ((a + bb) * k * x) := by nlinarith
            exact le_of_mul_le_mul_left this hab
          have h6 : 4 * ε * a * ((Fintype.card V : ℝ) - a) ≤ x * (Fintype.card V : ℝ) * (k + 4 * ε) := by
            have e : (Fintype.card V : ℝ) - a = x + bb := by linarith
            rw [e]
            have hle : a + bb ≤ (Fintype.card V : ℝ) := by linarith
            have hle2 : a ≤ (Fintype.card V : ℝ) := by linarith
            have h7 : (a + bb) * k * x ≤ (Fintype.card V : ℝ) * k * x :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hle hk) hx0
            have h8 : 4 * ε * a * x ≤ 4 * ε * (Fintype.card V : ℝ) * x :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hle2 (by linarith)) hx0
            have r1 : 4 * ε * a * (x + bb) = 4 * ε * a * x + 4 * ε * a * bb := by ring
            have r2 : x * (Fintype.card V : ℝ) * (k + 4 * ε)
                = (Fintype.card V : ℝ) * k * x + 4 * ε * (Fintype.card V : ℝ) * x := by ring
            rw [r1, r2]
            linarith
          have hden : 0 < ((k : ℝ) + 4 * ε) * (Fintype.card V : ℝ) := by
            exact mul_pos (by linarith) hnpos
          have e2 : (1 + 4 * ε / ((k : ℝ) + 4 * ε) * (1 - a / (Fintype.card V : ℝ))) * a
              = a + 4 * ε * a * ((Fintype.card V : ℝ) - a) / (((k : ℝ) + 4 * ε) * (Fintype.card V : ℝ)) := by
            have : (k : ℝ) + 4 * ε ≠ 0 := (by linarith : (0:ℝ) < (k : ℝ) + 4 * ε).ne'
            have : (Fintype.card V : ℝ) ≠ 0 := hnpos.ne'
            field_simp
          rw [e2]
          have : 4 * ε * a * ((Fintype.card V : ℝ) - a) / (((k : ℝ) + 4 * ε) * (Fintype.card V : ℝ)) ≤ x := by
            rw [div_le_iff₀ hden]; linarith
          linarith
