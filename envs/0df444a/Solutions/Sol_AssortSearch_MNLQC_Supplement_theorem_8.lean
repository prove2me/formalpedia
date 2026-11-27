-- Prove2me | solution 1 for AssortSearch.MNLQC.Supplement.theorem_8
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:16:44.100214+00:00
-- url     : https://prove2.me/submissions/80063b3d-ca7d-4306-93a8-31c207833181

import Mathlib
import Definitions.Def_RetailVariety_Structure_Model
import Definitions.Def_AssortSearch_Cannibal_Model
import Definitions.Def_AssortSearch_FullAssort_Model
import Definitions.Def_AssortSearch_HeurEq_Model
import Definitions.Def_AssortSearch_MNLQC_Supplement_Model

open MeasureTheory RetailVariety.Structure

open AssortSearch
open AssortSearch.MNLQC
open AssortSearch.MNLQC.Supplement

/-- **Theorem 8** (p. 23), in both search models: the heuristic equilibrium resulting from the
iterative application of the no-search assortment planning model never contains more variants than
the optimal assortment, `x* ≤ x^o`. In each model `x^o` maximises the true profit over the depths
`0, …, n` and every deeper depth is strictly worse; the first conjunct is the independent
assortment model, the second the overlapping assortment model. -/
theorem solution {n : ℕ} (lam μ b : ℝ) (m : Fin n → ℝ) (c : ℝ → ℝ)
    (v : Fin n → ℝ) (v0 : ℝ)
    (hv : ∀ i, 0 < v i) (hanti : Antitone v) (hv0 : 0 < v0) (hlam : 0 < lam)
    (hμ : 0 < μ) (hb : 0 < b)
    (hm : ∀ j k : Fin n, v k ≤ v j → m k ≤ m j)
    (hcc : ConcaveOn ℝ (Set.Icc 0 1) c) (hcm : MonotoneOn c (Set.Icc 0 1))
    (hc0 : 0 ≤ c 0) :
    (∀ xstar xo : ℕ, AssortSearch.HeurEq.IsHeuristicEquilibrium lam m c v v0 xstar →
      AssortSearch.HeurEq.IsOptimalDepth lam m c v v0 xo →
      (∀ x : ℕ, xo < x → x ≤ n →
        AssortSearch.HeurEq.trueProfit lam m c v v0 x <
          AssortSearch.HeurEq.trueProfit lam m c v v0 xo) →
      xstar ≤ xo) ∧
    (∀ xstar xo : ℕ, IsHeuristicEquilibriumOv μ b m c v v0 xstar →
      IsOptimalDepthOv μ b m c v v0 xo →
      (∀ x : ℕ, xo < x → x ≤ n → trueProfitOv μ b m c v v0 x < trueProfitOv μ b m c v v0 xo) →
      xstar ≤ xo) := by
        -- concavity of c from 0
        have KC : ∀ q θ : ℝ, 0 ≤ q → q ≤ 1 → 0 ≤ θ → θ ≤ 1 →
            θ * c q + (1 - θ) * c 0 ≤ c (θ * q) := by
          intro q θ hq0 hq1 hθ0 hθ1
          have h := hcc.2 (show q ∈ Set.Icc (0:ℝ) 1 from ⟨hq0, hq1⟩)
            (show (0:ℝ) ∈ Set.Icc (0:ℝ) 1 from ⟨le_rfl, zero_le_one⟩) hθ0
            (show (0:ℝ) ≤ 1 - θ by linarith) (show θ + (1 - θ) = 1 by ring)
          simpa [smul_eq_mul] using h
        have hmemP : ∀ x (i : Fin n), i ∈ popularSet n x ↔ i.val < x := by
          intro x i; simp [popularSet]
        have hsub : ∀ x y, x ≤ y → popularSet n x ⊆ popularSet n y := by
          intro x y hxy i hi; rw [hmemP] at hi ⊢; omega
        have hV0 : ∀ x, 0 ≤ ∑ j ∈ popularSet n x, v j :=
          fun x => Finset.sum_nonneg (fun j _ => (hv j).le)
        have hVmono : ∀ x y, x ≤ y → ∑ j ∈ popularSet n x, v j ≤ ∑ j ∈ popularSet n y, v j :=
          fun x y hxy => Finset.sum_le_sum_of_subset_of_nonneg (hsub x y hxy)
            (fun j _ _ => (hv j).le)
        have key : ∀ (d : ℕ → Fin n → ℝ) (β : ℕ → ℝ) (xs xo : ℕ),
            (∀ x i, d x i = v i * β x) →
            (∀ x, 1 ≤ x → x ≤ n → 0 < β x ∧ β x * ∑ j ∈ popularSet n x, v j < 1) →
            (1 ≤ xo → xo < xs → xs ≤ n →
              1 / β xs - ∑ j ∈ popularSet n xs, v j ≤ 1 / β xo - ∑ j ∈ popularSet n xo, v j) →
            1 ≤ xs → xs ≤ n →
            (∀ x, x ≤ n → AssortSearch.HeurEq.estProfit m c
                (fun i => if i.val < xs then d xs i / (if h : 0 < n then d xs ⟨0, h⟩ else 0)
                  else d n i / (if h : 0 < n then d n ⟨0, h⟩ else 0))
                ((1 - ∑ i ∈ popularSet n xs, d xs i) / (if h : 0 < n then d xs ⟨0, h⟩ else 0)) x ≤
              AssortSearch.HeurEq.estProfit m c
                (fun i => if i.val < xs then d xs i / (if h : 0 < n then d xs ⟨0, h⟩ else 0)
                  else d n i / (if h : 0 < n then d n ⟨0, h⟩ else 0))
                ((1 - ∑ i ∈ popularSet n xs, d xs i) / (if h : 0 < n then d xs ⟨0, h⟩ else 0)) xs) →
            xo ≤ n →
            (∀ x, xo < x → x ≤ n → ∑ i ∈ popularSet n x, (m i * d x i - c (d x i)) <
                ∑ i ∈ popularSet n xo, (m i * d xo i - c (d xo i))) →
            xs ≤ xo := by
          intro d β xs xo hd hpos hcond h1 hsn hE hxon hstrict
          by_contra hlt
          push Not at hlt
          have hn : 0 < n := by omega
          obtain ⟨V, hV⟩ : ∃ V : ℕ → ℝ, ∀ x, V x = ∑ j ∈ popularSet n x, v j := ⟨_, fun _ => rfl⟩
          obtain ⟨bs, hbs⟩ : ∃ bs, bs = β xs := ⟨_, rfl⟩
          obtain ⟨hbs0, hbs1⟩ := hpos xs h1 hsn
          rw [← hbs] at hbs0 hbs1
          rw [← hV] at hbs1
          have hVs : 0 ≤ V xs := by rw [hV]; exact hV0 xs
          have hinv : V xs < 1 / bs := by rw [lt_div_iff₀ hbs0]; linarith
          obtain ⟨α, hα⟩ : ∃ α : ℕ → ℝ, ∀ x, α x = 1 / (V x - V xs + 1 / bs) := ⟨_, fun _ => rfl⟩
          have hDpos : ∀ x, 0 < V x - V xs + 1 / bs := by
            intro x; have := hV0 x; rw [← hV] at this; linarith
          have hαpos : ∀ x, 0 < α x := fun x => by rw [hα]; exact one_div_pos.2 (hDpos x)
          have hαs : α xs = bs := by rw [hα]; simp
          have hvf := hv ⟨0, hn⟩
          -- estimated profit formula
          have hEform : ∀ x, x ≤ xs → AssortSearch.HeurEq.estProfit m c
                (fun i => if i.val < xs then d xs i / (if h : 0 < n then d xs ⟨0, h⟩ else 0)
                  else d n i / (if h : 0 < n then d n ⟨0, h⟩ else 0))
                ((1 - ∑ i ∈ popularSet n xs, d xs i) / (if h : 0 < n then d xs ⟨0, h⟩ else 0)) x =
              ∑ i ∈ popularSet n x, (m i * (α x * v i) - c (α x * v i)) := by
            intro x hx
            unfold AssortSearch.HeurEq.estProfit
            rw [dif_pos hn]
            have hw : ∀ j ∈ popularSet n x, (fun i : Fin n => if i.val < xs then d xs i / d xs ⟨0, hn⟩
                  else d n i / (if h : 0 < n then d n ⟨0, h⟩ else 0)) j = v j / v ⟨0, hn⟩ := by
              intro j hj
              rw [hmemP] at hj
              simp only [if_pos (show j.val < xs by omega), hd, ← hbs]
              field_simp
            have hsumw : ∑ j ∈ popularSet n x, (fun i : Fin n => if i.val < xs then d xs i / d xs ⟨0, hn⟩
                  else d n i / (if h : 0 < n then d n ⟨0, h⟩ else 0)) j = V x / v ⟨0, hn⟩ := by
              rw [Finset.sum_congr rfl hw, ← Finset.sum_div, hV]
            have hsd : ∑ i ∈ popularSet n xs, d xs i = V xs * bs := by
              rw [hV, Finset.sum_mul]; exact Finset.sum_congr rfl (fun i _ => by rw [hd, hbs])
            apply Finset.sum_congr rfl
            intro i hi
            have hsh : share (fun i : Fin n => if i.val < xs then d xs i / d xs ⟨0, hn⟩
                  else d n i / (if h : 0 < n then d n ⟨0, h⟩ else 0))
                  ((1 - ∑ i ∈ popularSet n xs, d xs i) / d xs ⟨0, hn⟩) (popularSet n x) i
                  = α x * v i := by
              unfold share
              rw [hsumw, hw i hi, hsd, hd, ← hbs, hα]
              have := hDpos x
              field_simp
              ring
            rw [hsh]
          have hE0 : AssortSearch.HeurEq.estProfit m c
                (fun i => if i.val < xs then d xs i / (if h : 0 < n then d xs ⟨0, h⟩ else 0)
                  else d n i / (if h : 0 < n then d n ⟨0, h⟩ else 0))
                ((1 - ∑ i ∈ popularSet n xs, d xs i) / (if h : 0 < n then d xs ⟨0, h⟩ else 0)) 0 = 0 := by
            unfold AssortSearch.HeurEq.estProfit; simp [popularSet]
          have hP0 : ∑ i ∈ popularSet n 0, (m i * d 0 i - c (d 0 i)) = 0 := by simp [popularSet]
          have hPs : ∑ i ∈ popularSet n xs, (m i * d xs i - c (d xs i)) =
              ∑ i ∈ popularSet n xs, (m i * (α xs * v i) - c (α xs * v i)) := by
            apply Finset.sum_congr rfl; intro i _; rw [hd, hαs, hbs, mul_comm (v i)]
          have hEs := hEform xs le_rfl
          have hEo := hEform xo hlt.le
          have hEx0 := hE 0 (Nat.zero_le _)
          have hExo := hE xo hxon
          rw [hE0, hEs] at hEx0
          rw [hEs, hEo] at hExo
          have hst := hstrict xs hlt hsn
          rw [hPs] at hst
          rcases Nat.eq_zero_or_pos xo with h0 | hxo1
          · subst h0; rw [hP0] at hst; linarith
          -- main: P xo ≤ E xo
          obtain ⟨φ, hφ⟩ : ∃ φ : Fin n → ℝ → ℝ, ∀ i q, φ i q = m i * q - c q + c 0 :=
            ⟨_, fun _ _ => rfl⟩
          have PHI : ∀ i q θ, 0 ≤ q → q ≤ 1 → 0 ≤ θ → θ ≤ 1 → φ i (θ * q) ≤ θ * φ i q := by
            intro i q θ h1 h2 h3 h4
            have := KC q θ h1 h2 h3 h4
            rw [hφ, hφ]; nlinarith
          obtain ⟨hbo0, _⟩ := hpos xo hxo1 hxon
          have hc := hcond hxo1 hlt hsn
          rw [← hbs, ← hV, ← hV] at hc
          have hVle : V xo ≤ V xs := by rw [hV, hV]; exact hVmono _ _ hlt.le
          have hVo0 : 0 ≤ V xo := by rw [hV]; exact hV0 _
          have hbo_le : β xo ≤ α xo := by
            rw [hα]
            rw [le_div_iff₀ (hDpos xo)]
            have : V xo - V xs + 1 / bs ≤ 1 / β xo := by linarith
            calc β xo * (V xo - V xs + 1 / bs) ≤ β xo * (1 / β xo) :=
                  mul_le_mul_of_nonneg_left this hbo0.le
              _ = 1 := by field_simp
          have hbs_le : bs ≤ α xo := by
            rw [← hαs, hα, hα]
            apply one_div_le_one_div_of_le (hDpos xo); linarith
          have hvle : ∀ x, ∀ i ∈ popularSet n x, v i ≤ V x := by
            intro x i hi; rw [hV]
            exact Finset.single_le_sum (f := v) (fun j _ => (hv j).le) hi
          have haq : ∀ i ∈ popularSet n xo, α xo * v i ≤ 1 := by
            intro i hi
            rw [hα, one_div_mul_eq_div, div_le_one (hDpos xo)]
            have := hvle xo i hi; linarith
          have hbq : ∀ i ∈ popularSet n xs, bs * v i ≤ 1 := by
            intro i hi
            have := hvle xs i hi
            nlinarith
          -- Step 1
          have S1 : 0 ≤ ∑ i ∈ popularSet n xs, φ i (bs * v i) := by
            have : ∑ i ∈ popularSet n xs, (m i * (α xs * v i) - c (α xs * v i)) ≤
                ∑ i ∈ popularSet n xs, φ i (bs * v i) := by
              apply Finset.sum_le_sum; intro i _; rw [hφ, hαs]; linarith
            linarith
          -- Step 2
          have S2 : 0 ≤ ∑ i ∈ popularSet n xo, φ i (bs * v i) := by
            by_cases hall : ∀ j ∈ popularSet n xs \ popularSet n xo, φ j (bs * v j) ≤ 0
            · have hsplit := Finset.sum_sdiff (f := fun i => φ i (bs * v i)) (hsub xo xs hlt.le)
              have : ∑ i ∈ popularSet n xs \ popularSet n xo, φ i (bs * v i) ≤ 0 :=
                Finset.sum_nonpos hall
              linarith
            · push Not at hall
              obtain ⟨j, hj, hφj⟩ := hall
              rw [Finset.mem_sdiff, hmemP, hmemP] at hj
              apply Finset.sum_nonneg
              intro i hi
              have hi' := (hmemP _ _).1 hi
              have hij : i ≤ j := by rw [Fin.le_iff_val_le_val]; omega
              have hvji : v j ≤ v i := hanti hij
              have hmji : m j ≤ m i := hm i j hvji
              have hvi := hv i
              have hvj := hv j
              have hqi : bs * v i ≤ 1 := hbq i ((hsub xo xs hlt.le) hi)
              have hk := KC (bs * v i) (v j / v i) (by positivity) hqi (by positivity)
                ((div_le_one hvi).2 hvji)
              have he : v j / v i * (bs * v i) = bs * v j := by field_simp
              rw [he] at hk
              rw [hφ] at hφj ⊢
              have hmq : m j * (bs * v j) ≤ m i * (bs * v j) :=
                mul_le_mul_of_nonneg_right hmji (by positivity)
              have hθ : 0 < v j / v i := by positivity
              have key2 : 0 < v j / v i * (m i * (bs * v i) - c (bs * v i) + c 0) := by
                have he2 : v j / v i * (m i * (bs * v i)) = m i * (bs * v j) := by
                  field_simp
                nlinarith
              exact (pos_of_mul_pos_right key2 hθ.le).le
          -- Step 3
          have S3 : 0 ≤ ∑ i ∈ popularSet n xo, φ i (α xo * v i) := by
            have hθ0 : 0 < bs / α xo := div_pos hbs0 (hαpos xo)
            have hθ1 : bs / α xo ≤ 1 := (div_le_one (hαpos xo)).2 hbs_le
            have : ∑ i ∈ popularSet n xo, φ i (bs * v i) ≤
                bs / α xo * ∑ i ∈ popularSet n xo, φ i (α xo * v i) := by
              rw [Finset.mul_sum]
              apply Finset.sum_le_sum; intro i hi
              have h := PHI i (α xo * v i) (bs / α xo) (by have := hv i; have := hαpos xo; positivity)
                (haq i hi) hθ0.le hθ1
              have he : bs / α xo * (α xo * v i) = bs * v i := by
                have := hαpos xo; field_simp
              rwa [he] at h
            have := mul_nonneg_iff_of_pos_left hθ0 |>.1 (le_trans S2 this)
            exact this
          -- Step 4
          have S4 : ∑ i ∈ popularSet n xo, φ i (β xo * v i) ≤ ∑ i ∈ popularSet n xo, φ i (α xo * v i) := by
            have hθ0 : 0 < β xo / α xo := div_pos hbo0 (hαpos xo)
            have hθ1 : β xo / α xo ≤ 1 := (div_le_one (hαpos xo)).2 hbo_le
            have : ∑ i ∈ popularSet n xo, φ i (β xo * v i) ≤
                β xo / α xo * ∑ i ∈ popularSet n xo, φ i (α xo * v i) := by
              rw [Finset.mul_sum]
              apply Finset.sum_le_sum; intro i hi
              have h := PHI i (α xo * v i) (β xo / α xo) (by have := hv i; have := hαpos xo; positivity)
                (haq i hi) hθ0.le hθ1
              have he : β xo / α xo * (α xo * v i) = β xo * v i := by
                have := hαpos xo; field_simp
              rwa [he] at h
            nlinarith
          have hPo : ∑ i ∈ popularSet n xo, (m i * d xo i - c (d xo i)) =
              ∑ i ∈ popularSet n xo, φ i (β xo * v i) - ∑ i ∈ popularSet n xo, c 0 := by
            rw [← Finset.sum_sub_distrib]; apply Finset.sum_congr rfl; intro i _
            rw [hφ, hd, mul_comm (v i)]; ring
          have hEo' : ∑ i ∈ popularSet n xo, (m i * (α xo * v i) - c (α xo * v i)) =
              ∑ i ∈ popularSet n xo, φ i (α xo * v i) - ∑ i ∈ popularSet n xo, c 0 := by
            rw [← Finset.sum_sub_distrib]; apply Finset.sum_congr rfl; intro i _
            rw [hφ]; ring
          linarith
        have hexp : ∀ l1 l2 W1 W2 : ℝ, 0 < l1 → l1 ≤ l2 → 0 < W1 → W1 ≤ W2 →
            W2 / (1 - Real.exp (-(l2 * W2))) - W2 ≤ W1 / (1 - Real.exp (-(l1 * W1))) - W1 := by
          intro l1 l2 W1 W2 hl1 hl12 hW1 hW12
          have conv : ∀ W a : ℝ, 0 < a → W / (1 - Real.exp (-a)) - W = W / (Real.exp a - 1) := by
            intro W a ha
            have h1 : 1 < Real.exp a := by have := Real.add_one_lt_exp (ne_of_gt ha); linarith
            have h2 : 0 < Real.exp a - 1 := by linarith
            have h3 : 0 < 1 - Real.exp (-a) := by
              rw [Real.exp_neg]; have := inv_lt_one_of_one_lt₀ h1; linarith
            rw [Real.exp_neg] at h3 ⊢
            field_simp
            ring
          have hW2 : 0 < W2 := lt_of_lt_of_le hW1 hW12
          have hl2 : 0 < l2 := lt_of_lt_of_le hl1 hl12
          rw [conv _ _ (by positivity), conv _ _ (by positivity)]
          have ht0 : 0 ≤ W1 / W2 := by positivity
          have ht1 : W1 / W2 ≤ 1 := (div_le_one hW2).2 hW12
          have hcv := convexOn_exp.2 (Set.mem_univ (l2 * W2)) (Set.mem_univ 0) ht0
            (show 0 ≤ 1 - W1 / W2 by linarith) (show W1 / W2 + (1 - W1 / W2) = 1 by ring)
          simp only [smul_eq_mul, mul_zero, add_zero, Real.exp_zero, mul_one] at hcv
          have he : W1 / W2 * (l2 * W2) = l2 * W1 := by field_simp
          rw [he] at hcv
          have hmono : Real.exp (l1 * W1) ≤ Real.exp (l2 * W1) :=
            Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right hl12 hW1.le)
          have hp1 : 0 < Real.exp (l1 * W1) - 1 := by
            have h0 : 0 < l1 * W1 := by positivity
            have := Real.add_one_lt_exp (ne_of_gt h0); linarith
          have hp2 : 0 < Real.exp (l2 * W2) - 1 := by
            have h0 : 0 < l2 * W2 := by positivity
            have := Real.add_one_lt_exp (ne_of_gt h0); linarith
          rw [div_le_div_iff₀ hp2 hp1]
          have : W2 * (Real.exp (l1 * W1) - 1) ≤ W2 * (W1 / W2 * (Real.exp (l2 * W2) - 1)) :=
            mul_le_mul_of_nonneg_left (by linarith) hW2.le
          have he2 : W2 * (W1 / W2 * (Real.exp (l2 * W2) - 1)) = W1 * (Real.exp (l2 * W2) - 1) := by
            field_simp
          linarith
        -- generic condition from exp form
        have hcondE : ∀ l1 l2 V1 V2 : ℝ, 0 < l1 → l1 ≤ l2 → 0 ≤ V1 → V1 ≤ V2 →
            1 / ((1 - Real.exp (-(l2 * (v0 + V2)))) / (v0 + V2)) - V2 ≤
              1 / ((1 - Real.exp (-(l1 * (v0 + V1)))) / (v0 + V1)) - V1 := by
          intro l1 l2 V1 V2 hl1 hl12 hV1 hV12
          rw [one_div_div, one_div_div]
          have := hexp l1 l2 (v0 + V1) (v0 + V2) hl1 hl12 (by linarith) (by linarith)
          linarith
        have hposE : ∀ l V : ℝ, 0 < l → 0 ≤ V →
            0 < (1 - Real.exp (-(l * (v0 + V)))) / (v0 + V) ∧
              (1 - Real.exp (-(l * (v0 + V)))) / (v0 + V) * V < 1 := by
          intro l V hl hV
          have hW : 0 < v0 + V := by linarith
          have hH : Real.exp (-(l * (v0 + V))) < 1 := by
            rw [← Real.exp_zero]; exact Real.exp_lt_exp.2 (by have := mul_pos hl hW; linarith)
          have hH0 := Real.exp_pos (-(l * (v0 + V)))
          refine ⟨div_pos (by linarith) hW, ?_⟩
          rw [div_mul_eq_mul_div, div_lt_one hW]
          nlinarith
        refine ⟨?_, ?_⟩
        · intro xs xo hHE hOD hstr
          refine key (AssortSearch.HeurEq.demand lam v v0)
            (fun x => (1 - Real.exp (-(lam * (v0 + ∑ j ∈ popularSet n x, v j)))) /
              (v0 + ∑ j ∈ popularSet n x, v j)) xs xo ?_ ?_ ?_ hHE.1 hHE.2.1 hHE.2.2 hOD.1 hstr
          · intro x i
            simp only [AssortSearch.HeurEq.demand, share, AssortSearch.HeurEq.searchH,
              AssortSearch.HeurEq.prefTotal]
            rw [add_comm (∑ j ∈ popularSet n x, v j) v0]; ring
          · intro x _ _
            exact hposE lam _ hlam (hV0 x)
          · intro _ hlt _
            exact hcondE lam lam _ _ hlam le_rfl (hV0 _) (hVmono _ _ hlt.le)
        · intro xs xo hHE hOD hstr
          have htrans : ∀ (f : ℝ → ℝ) (u d : ℝ),
              ∫ y in Set.Ioi (u + d), f y = ∫ y in Set.Ioi u, f (y + d) := by
            intro f u d
            have := (measurePreserving_add_right volume d).setIntegral_preimage_emb
              (measurableEmbedding_addRight d) f (Set.Ioi (u + d))
            rw [← this, Set.preimage_add_const_Ioi, add_sub_cancel_right]
          have hUbar : ∀ S T : Finset (Fin n), 0 < AssortSearch.FullAssort.outsidePref v T →
              AssortSearch.FullAssort.outsidePref v T ≤ AssortSearch.FullAssort.outsidePref v S →
              AssortSearch.FullAssort.Ubar μ v T b ≤ AssortSearch.FullAssort.Ubar μ v S b := by
            intro S T hT hTS
            obtain ⟨A, hA⟩ : ∃ A, A = AssortSearch.FullAssort.outsidePref v S := ⟨_, rfl⟩
            obtain ⟨B, hB⟩ : ∃ B, B = AssortSearch.FullAssort.outsidePref v T := ⟨_, rfl⟩
            rw [← hA, ← hB] at hTS; rw [← hB] at hT
            have hA0 : 0 < A := lt_of_lt_of_le hT hTS
            obtain ⟨d, hdd⟩ : ∃ d, d = μ * Real.log (A / B) := ⟨_, rfl⟩
            have hd : 0 ≤ d := by
              rw [hdd]; exact mul_nonneg hμ.le (Real.log_nonneg ((one_le_div hT).2 hTS))
            have hw : ∀ y, AssortSearch.FullAssort.w μ v S (y + d) = AssortSearch.FullAssort.w μ v T y := by
              intro y
              have hl : AssortSearch.Cannibal.lam μ (y + d) = AssortSearch.Cannibal.lam μ y * (B / A) := by
                unfold AssortSearch.Cannibal.lam
                rw [show -((y + d) / μ + Real.eulerMascheroniConstant) =
                    -(y / μ + Real.eulerMascheroniConstant) + -(Real.log (A / B)) by
                      rw [hdd]; field_simp; ring,
                  Real.exp_add, Real.exp_neg (Real.log (A / B)), Real.exp_log (div_pos hA0 hT), inv_div]
              simp only [AssortSearch.FullAssort.w, AssortSearch.FullAssort.outsideCdf, hl, ← hA, ← hB]
              have : AssortSearch.Cannibal.lam μ y * (B / A) * A = AssortSearch.Cannibal.lam μ y * B := by
                field_simp
              rw [this]
              field_simp
            have hΦ : ∀ u, AssortSearch.FullAssort.searchGain μ v T u =
                AssortSearch.FullAssort.searchGain μ v S (u + d) := by
              intro u
              unfold AssortSearch.FullAssort.searchGain
              rw [htrans]
              congr 1; ext y; rw [hw]; ring
            unfold AssortSearch.FullAssort.Ubar
            have hmem : ∀ u, u ∈ {u | AssortSearch.FullAssort.searchGain μ v T u ≤ b} ↔
                u + d ∈ {u | AssortSearch.FullAssort.searchGain μ v S u ≤ b} := by
              intro u; simp only [Set.mem_setOf_eq, hΦ]
            by_cases hne : ({u | AssortSearch.FullAssort.searchGain μ v S u ≤ b} : Set ℝ).Nonempty
            · by_cases hbdd : BddBelow ({u | AssortSearch.FullAssort.searchGain μ v S u ≤ b} : Set ℝ)
              · have hbT : BddBelow ({u | AssortSearch.FullAssort.searchGain μ v T u ≤ b} : Set ℝ) := by
                  obtain ⟨L, hL⟩ := hbdd
                  exact ⟨L - d, fun u hu => by have := hL ((hmem u).1 hu); linarith⟩
                apply le_csInf hne
                intro u hu
                have h2 : u - d ∈ ({u | AssortSearch.FullAssort.searchGain μ v T u ≤ b} : Set ℝ) :=
                  (hmem _).2 (by simpa using hu)
                have := csInf_le hbT h2
                linarith
              · have hnT : ¬ BddBelow ({u | AssortSearch.FullAssort.searchGain μ v T u ≤ b} : Set ℝ) := by
                  rintro ⟨L, hL⟩
                  apply hbdd
                  exact ⟨L + d, fun u hu => by
                    have := hL ((hmem (u - d)).2 (by simpa using hu)); linarith⟩
                rw [Real.sInf_of_not_bddBelow hbdd, Real.sInf_of_not_bddBelow hnT]
            · have hAS : ({u | AssortSearch.FullAssort.searchGain μ v S u ≤ b} : Set ℝ) = ∅ :=
                Set.not_nonempty_iff_eq_empty.1 hne
              have hAT : ({u | AssortSearch.FullAssort.searchGain μ v T u ≤ b} : Set ℝ) = ∅ :=
                Set.eq_empty_iff_forall_notMem.2 (fun u hu => hne ⟨_, (hmem u).1 hu⟩)
              rw [hAS, hAT]
          refine key (demandOv μ b v v0)
            (fun x => if popularSet n x = Finset.univ then 1 / (v0 + ∑ j ∈ popularSet n x, v j) else
              (1 - Real.exp (-(AssortSearch.Cannibal.lam μ
                (AssortSearch.FullAssort.Ubar μ v (popularSet n x) b) * (v0 + ∑ j ∈ popularSet n x, v j)))) /
              (v0 + ∑ j ∈ popularSet n x, v j)) xs xo ?_ ?_ ?_ hHE.1 hHE.2.1 hHE.2.2 hOD.1 hstr
          · intro x i
            simp only [demandOv, AssortSearch.FullAssort.demandSO, share, AssortSearch.Cannibal.H]
            rw [add_comm (∑ j ∈ popularSet n x, v j) v0]
            split_ifs <;> ring
          · intro x _ _
            split_ifs
            · have := hV0 x
              refine ⟨by positivity, ?_⟩
              rw [one_div_mul_eq_div, div_lt_one (by linarith)]; linarith
            · exact hposE _ _ (Real.exp_pos _) (hV0 x)
          · intro hxo1 hlt hsn
            have hno : popularSet n xo ≠ Finset.univ := by
              intro h
              have : (⟨xo, by omega⟩ : Fin n) ∈ popularSet n xo := by rw [h]; exact Finset.mem_univ _
              rw [hmemP] at this; simp at this
            simp only [if_neg hno]
            split_ifs with hs
            · have hVo := hV0 xo
              have hW : 0 < v0 + ∑ j ∈ popularSet n xo, v j := by linarith
              obtain ⟨hp, _⟩ := hposE (AssortSearch.Cannibal.lam μ
                (AssortSearch.FullAssort.Ubar μ v (popularSet n xo) b)) _ (Real.exp_pos _) hVo
              rw [one_div_one_div, one_div_div]
              have hH0 := Real.exp_pos (-(AssortSearch.Cannibal.lam μ
                (AssortSearch.FullAssort.Ubar μ v (popularSet n xo) b) * (v0 + ∑ j ∈ popularSet n xo, v j)))
              have h1H : 0 < 1 - Real.exp (-(AssortSearch.Cannibal.lam μ
                (AssortSearch.FullAssort.Ubar μ v (popularSet n xo) b) * (v0 + ∑ j ∈ popularSet n xo, v j))) := by
                have := div_pos_iff.1 hp
                rcases this with h | h
                · exact h.1
                · linarith [h.2]
              have : v0 + ∑ j ∈ popularSet n xo, v j ≤ (v0 + ∑ j ∈ popularSet n xo, v j) / (1 - Real.exp (-(AssortSearch.Cannibal.lam μ
                (AssortSearch.FullAssort.Ubar μ v (popularSet n xo) b) * (v0 + ∑ j ∈ popularSet n xo, v j)))) := by
                rw [le_div_iff₀ h1H]; nlinarith
              have := hV0 xs
              linarith
            · apply hcondE _ _ _ _ (Real.exp_pos _) _ (hV0 _) (hVmono _ _ hlt.le)
              have hT : 0 < AssortSearch.FullAssort.outsidePref v (popularSet n xs) := by
                unfold AssortSearch.FullAssort.outsidePref
                have : (popularSet n xs)ᶜ.Nonempty := by
                  by_contra h
                  rw [Finset.not_nonempty_iff_eq_empty, Finset.compl_eq_empty_iff] at h
                  exact hs h
                exact Finset.sum_pos (fun i _ => hv i) this
              have hTS : AssortSearch.FullAssort.outsidePref v (popularSet n xs) ≤
                  AssortSearch.FullAssort.outsidePref v (popularSet n xo) := by
                unfold AssortSearch.FullAssort.outsidePref
                apply Finset.sum_le_sum_of_subset_of_nonneg
                · exact Finset.compl_subset_compl.2 (hsub _ _ hlt.le)
                · intro i _ _; exact (hv i).le
              have hU := hUbar _ _ hT hTS
              unfold AssortSearch.Cannibal.lam
              apply Real.exp_le_exp.2
              have := div_le_div_of_nonneg_right hU hμ.le
              linarith
