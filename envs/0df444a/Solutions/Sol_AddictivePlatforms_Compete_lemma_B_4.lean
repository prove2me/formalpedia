-- Prove2me | solution 1 for AddictivePlatforms.Compete.lemma_B_4
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-20T13:58:43.941634+00:00
-- url     : https://prove2.me/submissions/a9b24d0e-fd65-4f81-add3-0d245caff57d

import Mathlib
import Definitions.Def_AddictivePlatforms_Compete_Model
open Set Finset
open scoped ENNReal
open AddictivePlatforms.Compete
set_option autoImplicit false
namespace AttentionB4
lemma cost_increment_monotone (C : ℝ → ℝ) (hf : DifferentiableOn ℝ C (Ici 0))
    (hc : ConvexOn ℝ (Ici 0) C) {r : ℝ} (hr : 0 ≤ r) :
    MonotoneOn (fun t => C (t+r)-C t) (Ici 0) := by
  have hcont : ContinuousOn (fun t => C (t+r)) (Ici 0) :=
    hf.continuousOn.comp (continuousOn_id.add continuousOn_const) (fun t ht => add_nonneg ht hr)
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0) (hcont.sub hf.continuousOn)
    (f' := fun t => derivWithin C (Ici 0) (t+r)-derivWithin C (Ici 0) t)
  · intro t ht
    have ht' : 0 < t := by simpa only [interior_Ici, Set.mem_Ioi] using ht
    have htr : 0 < t+r := by linarith
    have h1 := (hf (t+r) htr.le).hasDerivWithinAt.hasDerivAt (Ici_mem_nhds htr)
    have h2 := (hf t ht'.le).hasDerivWithinAt.hasDerivAt (Ici_mem_nhds ht')
    have h3 : HasDerivAt (fun t => C (t+r)) (derivWithin C (Ici 0) (t+r)) t := by
      convert h1.comp t ((hasDerivAt_id t).add_const r) using 1 <;> first | rfl | ring
    exact (h3.sub h2).hasDerivWithinAt
  · intro t ht
    have ht' : 0 ≤ t := (show 0 < t by simpa only [interior_Ici, Set.mem_Ioi] using ht).le
    exact sub_nonneg.2 (hc.monotoneOn_derivWithin hf ht' (add_nonneg ht' hr)
      (le_add_of_nonneg_right hr))

lemma cost_cross (C : ℝ → ℝ) (hf : DifferentiableOn ℝ C (Ici 0))
    (hc : ConvexOn ℝ (Ici 0) C) {a b c d : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hac : a ≤ c) (hbd : b ≤ d) :
    C (c+b)+C (a+d) ≤ C (a+b)+C (c+d) := by
  have h := cost_increment_monotone C hf hc (sub_nonneg.2 hac)
    (add_nonneg ha hb) (add_nonneg ha (hb.trans hbd)) (add_le_add le_rfl hbd)
  have h1 : a+b+(c-a) = c+b := by ring
  have h2 : a+d+(c-a) = c+d := by ring
  dsimp only at h
  rw [h1,h2] at h
  linarith


lemma concave_pair (f : ℝ → ℝ) (hf : ConcaveOn ℝ (Ici 0) f)
    {x y θ : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    let v := θ*x+(1-θ)*min x y
    0 ≤ v ∧ 0 ≤ x+y-v ∧ f x + f y ≤ f v + f (x+y-v) := by
  dsimp
  by_cases hxy : x ≤ y
  · rw [min_eq_left hxy]
    have hv : θ*x+(1-θ)*x = x := by ring
    rw [hv]
    simpa using And.intro hx (And.intro hy (le_refl (f x+f y)))
  · rw [min_eq_right (le_of_not_ge hxy)]
    have hθ' : 0 ≤ 1-θ := sub_nonneg.mpr hθ1
    have hv := add_nonneg (mul_nonneg hθ hx) (mul_nonneg hθ' hy)
    have hw := add_nonneg (mul_nonneg hθ' hx) (mul_nonneg hθ hy)
    have h1 := hf.2 hx hy hθ hθ' (by ring : θ+(1-θ)=1)
    have h2 := hf.2 hx hy hθ' hθ (by ring : (1-θ)+θ=1)
    dsimp only [smul_eq_mul] at h1 h2
    have he : x+y-(θ*x+(1-θ)*y) = (1-θ)*x+θ*y := by ring
    rw [he]
    exact ⟨hv,hw,by nlinarith⟩

lemma rebalance {ι : Type*} [DecidableEq ι] (I : Finset ι)
    (u : ι → ℝ → ℝ) (hu : ∀ k ∈ I, ConcaveOn ℝ (Ici 0) (u k))
    (C : ℝ → ℝ) (hCd : DifferentiableOn ℝ C (Ici 0)) (hCc : ConvexOn ℝ (Ici 0) C)
    (x y : ι → ℝ) (hx : ∀ k ∈ I, 0 ≤ x k) (hy : ∀ k ∈ I, 0 ≤ y k)
    (a b L : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hL : 0 ≤ L) :
    ∃ v w : ι → ℝ,
      (∀ k ∈ I, 0 ≤ v k ∧ 0 ≤ w k ∧ u k (x k)+u k (y k) ≤ u k (v k)+u k (w k)) ∧
      b+∑ k ∈ I, v k ≤ max (a+∑ k ∈ I, x k) (b+(∑ k ∈ I, y k)+L) ∧
      a+(∑ k ∈ I, w k)+L ≤ max (a+∑ k ∈ I, x k) (b+(∑ k ∈ I, y k)+L) ∧
      C (b+∑ k ∈ I, v k)+C (a+(∑ k ∈ I, w k)+L) ≤
        C (a+∑ k ∈ I, x k)+C (b+(∑ k ∈ I, y k)+L) := by
  have hxsum : 0 ≤ ∑ k ∈ I, x k := sum_nonneg hx
  have hysum : 0 ≤ ∑ k ∈ I, y k := sum_nonneg hy
  by_cases h : b+(∑ k ∈ I, x k) ≤ b+(∑ k ∈ I, y k)+L
  · refine ⟨x,y,fun k hk => ⟨hx k hk,hy k hk,le_rfl⟩, h.trans (le_max_right _ _), ?_, ?_⟩
    · exact (by linarith : a+(∑ k ∈ I, y k)+L ≤ b+(∑ k ∈ I, y k)+L).trans (le_max_right _ _)
    · have hc := cost_cross C hCd hCc ha hxsum hab
        (by linarith : (∑ k ∈ I, x k) ≤ (∑ k ∈ I, y k)+L)
      simpa only [add_assoc] using hc
  · let m : ι → ℝ := fun k => min (x k) (y k)
    have hmx : (∑ k ∈ I, m k) ≤ ∑ k ∈ I, x k := sum_le_sum (fun k _ => min_le_left _ _)
    have hmy : (∑ k ∈ I, m k) ≤ ∑ k ∈ I, y k := sum_le_sum (fun k _ => min_le_right _ _)
    have hden : 0 < (∑ k ∈ I, x k)-(∑ k ∈ I, m k) := by linarith
    let θ := ((∑ k ∈ I, y k)+L-(∑ k ∈ I, m k))/((∑ k ∈ I, x k)-(∑ k ∈ I, m k))
    have hθ : 0 ≤ θ := div_nonneg (by linarith) hden.le
    have hθ1 : θ ≤ 1 := (div_le_one hden).mpr (by linarith)
    let v : ι → ℝ := fun k => θ*x k+(1-θ)*m k
    let w : ι → ℝ := fun k => x k+y k-v k
    have hv : (∑ k ∈ I, v k) = (∑ k ∈ I, y k)+L := by
      simp only [v, sum_add_distrib, ← mul_sum]
      have he : θ*((∑ k ∈ I, x k)-(∑ k ∈ I, m k)) = (∑ k ∈ I, y k)+L-(∑ k ∈ I, m k) :=
        div_mul_cancel₀ _ hden.ne'
      nlinarith
    have hw : (∑ k ∈ I, w k) = (∑ k ∈ I, x k)-L := by
      simp only [w, sum_sub_distrib, sum_add_distrib, hv]
      ring
    refine ⟨v,w,fun k hk => concave_pair (u k) (hu k hk) (hx k hk) (hy k hk) hθ hθ1, ?_, ?_, ?_⟩
    · rw [hv]
      simpa only [add_assoc] using le_max_right (a+∑ k ∈ I, x k) (b+(∑ k ∈ I, y k)+L)
    · rw [hw]
      have he : a+((∑ k ∈ I, x k)-L)+L = a+∑ k ∈ I, x k := by ring
      rw [he]
      exact le_max_left _ _
    · rw [hv,hw]
      have he : a+((∑ k ∈ I, x k)-L)+L = a+∑ k ∈ I, x k := by ring
      rw [he]
      simp only [add_assoc]
      exact le_of_eq (add_comm _ _)

lemma split_sum {ι : Type*} [DecidableEq ι] {I S : Finset ι} (h : I ⊆ S) (f : ι → ℝ) :
    (∑ k ∈ S, f k) = (∑ k ∈ I, f k)+(∑ k ∈ S \ I, f k) := by
  simpa only [add_comm] using (sum_sdiff (f := f) h).symm

lemma value_cross (u : ℝ → ℝ → ℝ) (C : ℝ → ℝ) (hS : Standing u C)
    {K : ℕ} [NeZero K] (Abar : ℝ≥0∞) (d : Fin K → ℝ) (hd : ∀ k, 0 ≤ d k)
    (I S : Finset (Fin K)) (hsub : I ⊆ S) (hzS : 0 ∉ S)
    (y₁ y₂ : ℝ) (hyy : y₁ ≤ y₂) (A B M N : Fin K → ℝ)
    (hA : IsB4Max u C Abar d y₁ I A) (hB : IsB4Max u C Abar d y₂ S B)
    (hM : IsB4Max u C Abar d y₂ I M) (hN : IsB4Max u C Abar d y₁ S N) :
    objB4 u C d y₁ I A + objB4 u C d y₂ S B ≤
      objB4 u C d y₂ I M + objB4 u C d y₁ S N := by
  have hzI : 0 ∉ I := fun h => hzS (hsub h)
  have hA0 : 0 ≤ A 0 := hA.1 0 (mem_insert_self _ _)
  have hB0 : 0 ≤ B 0 := hB.1 0 (mem_insert_self _ _)
  by_cases hab : A 0 ≤ B 0
  · let L := ∑ k ∈ S \ I, B k
    have hAn (k : Fin K) (hk : k ∈ I) : 0 ≤ A k := hA.1 k (mem_insert_of_mem hk)
    have hBn (k : Fin K) (hk : k ∈ I) : 0 ≤ B k := hB.1 k (mem_insert_of_mem (hsub hk))
    have hLn : 0 ≤ L := sum_nonneg (fun k hk => hB.1 k (mem_insert_of_mem (mem_sdiff.mp hk).1))
    obtain ⟨v,w,hvw,hvcap,hwcap,hcost⟩ := rebalance I (fun k a => u a (d k))
      (fun k _ => hS.assumption1.concaveOn_a (d k) (hd k)) C
      hS.assumption2.differentiableOn hS.assumption2.convexOn A B hAn hBn
      (A 0) (B 0) L hA0 hab hLn
    let V : Fin K → ℝ := fun k => if k=0 then B 0 else v k
    let W : Fin K → ℝ := fun k => if k=0 then A 0 else if k ∈ I then w k else B k
    have hV0 : V 0 = B 0 := by simp [V]
    have hW0 : W 0 = A 0 := by simp [W]
    have hVI (k : Fin K) (hk : k ∈ I) : V k = v k := by
      have hn : k ≠ 0 := fun h => hzI (h ▸ hk)
      simp [V,hn]
    have hWI (k : Fin K) (hk : k ∈ I) : W k = w k := by
      have hn : k ≠ 0 := fun h => hzI (h ▸ hk)
      simp [W,hn,hk]
    have hWE (k : Fin K) (hk : k ∈ S \ I) : W k = B k := by
      have hn : k ≠ 0 := fun h => hzS (h ▸ (mem_sdiff.mp hk).1)
      simp [W,hn,(mem_sdiff.mp hk).2]
    have hAt : (∑ k ∈ insert 0 I, A k) = A 0+(∑ k ∈ I, A k) := sum_insert hzI
    have hBt : (∑ k ∈ insert 0 S, B k) = B 0+(∑ k ∈ I, B k)+L := by
      rw [sum_insert hzS, split_sum hsub B]; dsimp [L]; ring
    have hVt : (∑ k ∈ insert 0 I, V k) = B 0+(∑ k ∈ I, v k) := by
      rw [sum_insert hzI,hV0]; congr 1; exact sum_congr rfl hVI
    have hWt : (∑ k ∈ insert 0 S, W k) = A 0+(∑ k ∈ I, w k)+L := by
      rw [sum_insert hzS,hW0,split_sum hsub W]
      rw [sum_congr rfl hWI, sum_congr rfl hWE]
      dsimp [L]; ring
    have hVu : (∑ k ∈ I, u (V k) (d k)) = ∑ k ∈ I, u (v k) (d k) :=
      sum_congr rfl (fun k hk => by rw [hVI k hk])
    have hWu : (∑ k ∈ S, u (W k) (d k)) =
        (∑ k ∈ I, u (w k) (d k))+(∑ k ∈ S \ I, u (B k) (d k)) := by
      rw [split_sum hsub]
      congr 1
      · exact sum_congr rfl (fun k hk => by rw [hWI k hk])
      · exact sum_congr rfl (fun k hk => by rw [hWE k hk])
    have hmax : ENNReal.ofReal (max (A 0+∑ k ∈ I, A k) (B 0+(∑ k ∈ I, B k)+L)) ≤ Abar := by
      rcases le_total (A 0+∑ k ∈ I, A k) (B 0+(∑ k ∈ I, B k)+L) with h | h
      · rw [max_eq_right h,←hBt]; exact hB.2.1
      · rw [max_eq_left h,←hAt]; exact hA.2.1
    have hVn (k : Fin K) (hk : k ∈ insert 0 I) : 0 ≤ V k := by
      rcases mem_insert.mp hk with rfl | hk
      · rw [hV0]; exact hB0
      · rw [hVI k hk]; exact (hvw k hk).1
    have hWn (k : Fin K) (hk : k ∈ insert 0 S) : 0 ≤ W k := by
      rcases mem_insert.mp hk with rfl | hk
      · rw [hW0]; exact hA0
      · by_cases hi : k ∈ I
        · rw [hWI k hi]; exact (hvw k hi).2.1
        · rw [hWE k (mem_sdiff.mpr ⟨hk,hi⟩)]; exact hB.1 k (mem_insert_of_mem hk)
    have hm := hM.2.2 V hVn (by rw [hVt]; exact (ENNReal.ofReal_le_ofReal hvcap).trans hmax)
    have hn := hN.2.2 W hWn (by rw [hWt]; exact (ENNReal.ofReal_le_ofReal hwcap).trans hmax)
    have hu := sum_le_sum (fun k hk => (hvw k hk).2.2)
    simp only [sum_add_distrib] at hu
    dsimp only [objB4] at hm hn ⊢
    rw [hVu,hV0,hVt] at hm
    rw [hWu,hW0,hWt] at hn
    rw [hAt,hBt,split_sum hsub (fun k => u (B k) (d k))]
    linarith
  · have hba : B 0 ≤ A 0 := le_of_not_ge hab
    have hu := (hS.assumption1.strictMonoOn_a (d 0) (hd 0)).monotoneOn hB0 hA0 hba
    have hm := hM.2.2 A hA.1 hA.2.1
    have hn := hN.2.2 B hB.1 hB.2.1
    dsimp only [objB4] at hm hn ⊢
    nlinarith

end AttentionB4



/-- Lemma B.4 (p. 30), weak part. Fix `(d_1, …, d_K) ∈ ℝ₊^K` and let `a(y, S)` solve (A.4) for every
`y ∈ [0, 1]` and `S ⊆ K₋₁ = K ∖ {1}`, with value `V(y, S)`. For `S′ ⊊ S ⊆ K₋₁`, (A.5) in integrated
form: `V(y₂, S) − V(y₁, S) ≤ V(y₂, S′) − V(y₁, S′)` for `0 ≤ y₁ ≤ y₂ ≤ 1`; in particular
`V(1, S) − V(0, S) ≤ V(1, S′) − V(0, S′)`. Platform "1" is the index `0`. -/
theorem solution (u : ℝ → ℝ → ℝ) (C : ℝ → ℝ) (hS : Standing u C) {K : ℕ} [NeZero K]
    (Abar : ℝ≥0∞) (d : Fin K → ℝ) (hd : ∀ k, 0 ≤ d k)
    (a : ℝ → Finset (Fin K) → (Fin K → ℝ))
    (ha : ∀ y ∈ Icc (0 : ℝ) 1, ∀ S : Finset (Fin K), S ⊆ Finset.univ.erase 0 →
      IsB4Max u C Abar d y S (a y S))
    (S S' : Finset (Fin K)) (hSsub : S ⊆ Finset.univ.erase 0) (hS'S : S' ⊂ S) :
    (∀ y₁ ∈ Icc (0 : ℝ) 1, ∀ y₂ ∈ Icc (0 : ℝ) 1, y₁ ≤ y₂ →
      objB4 u C d y₂ S (a y₂ S) - objB4 u C d y₁ S (a y₁ S) ≤
        objB4 u C d y₂ S' (a y₂ S') - objB4 u C d y₁ S' (a y₁ S')) ∧
    objB4 u C d 1 S (a 1 S) - objB4 u C d 0 S (a 0 S) ≤
      objB4 u C d 1 S' (a 1 S') - objB4 u C d 0 S' (a 0 S') := by
  have hsub : S' ⊆ S := hS'S.subset
  have hsub' : S' ⊆ Finset.univ.erase 0 := hsub.trans hSsub
  have hz : (0 : Fin K) ∉ S := by
    intro h
    have he := hSsub h
    simp only [Finset.mem_erase, ne_eq, not_true_eq_false, false_and] at he
  have hi : ∀ y₁ ∈ Set.Icc (0 : ℝ) 1, ∀ y₂ ∈ Set.Icc (0 : ℝ) 1, y₁ ≤ y₂ →
      objB4 u C d y₂ S (a y₂ S) - objB4 u C d y₁ S (a y₁ S) ≤
        objB4 u C d y₂ S' (a y₂ S') - objB4 u C d y₁ S' (a y₁ S') := by
    intro y₁ hy₁ y₂ hy₂ hyy
    have h := AttentionB4.value_cross u C hS Abar d hd S' S hsub hz y₁ y₂ hyy
      (a y₁ S') (a y₂ S) (a y₂ S') (a y₁ S)
      (ha y₁ hy₁ S' hsub') (ha y₂ hy₂ S hSsub)
      (ha y₂ hy₂ S' hsub') (ha y₁ hy₁ S hSsub)
    linarith
  exact ⟨hi, hi 0 (by constructor <;> norm_num) 1 (by constructor <;> norm_num) (by norm_num)⟩


#print axioms solution
