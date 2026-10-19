-- Prove2me | solution 1 for ArrowDebreu.ThmII.EtildeEps_has_equilibrium
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-18T07:30:40.476782+00:00
-- url     : https://prove2.me/submissions/5022d9a1-2f40-4c4d-b66a-826db628214e

import Mathlib
import Definitions.Def_ArrowDebreu_Shared_Economy
import Definitions.Def_ArrowDebreu_Shared_IsCompetitiveEquilibrium
import Definitions.Def_ArrowDebreu_ThmII_AssumptionsII
import Definitions.Def_ArrowDebreu_Shared_AbstractEconomy
import Definitions.Def_ArrowDebreu_ThmII_economyEeps
import Definitions.Def_ArrowDebreu_ThmI_AssumptionsItoIV
import Definitions.Def_ArrowDebreu_ThmI_economyE
import Theorems.Thm_ArrowDebreu_ThmI_lemma_2_5
import Theorems.Thm_ArrowDebreu_ThmI_remark_3_3_5
import Theorems.Thm_ArrowDebreu_ThmI_quasiconcave_of_IIIc
open ArrowDebreu.Shared

set_option autoImplicit false

namespace P2M8555

open ArrowDebreu.Shared ArrowDebreu.ThmII Filter Topology

lemma cube_eq (l : ℕ) (c : ℝ) : cube l c = Set.univ.pi (fun _ => Set.Icc (-c) c) := by
  ext x
  simp only [cube, Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Icc, abs_le]

lemma cube_compact (l : ℕ) (c : ℝ) : IsCompact (cube l c) := by
  rw [cube_eq]; exact isCompact_univ_pi fun _ => isCompact_Icc

lemma cube_convex (l : ℕ) (c : ℝ) : Convex ℝ (cube l c) := by
  rw [cube_eq]; exact convex_pi fun _ _ => convex_Icc _ _

lemma zero_mem_cube (l : ℕ) {c : ℝ} (hc : 0 ≤ c) : (0 : Fin l → ℝ) ∈ cube l c := by
  intro h; simpa using hc

lemma simplexEps_closed {l m n : ℕ} (E : Economy l m n) (ε : ℝ) :
    IsClosed (priceSimplexEps E ε) := by
  have e : priceSimplexEps E ε = {p : Fin l → ℝ | 0 ≤ p} ∩ {p | ∑ h, p h = 1} ∩
      ⋂ h ∈ productive E, {p | ε ≤ p h} := by
    ext p; simp [priceSimplexEps, priceSimplex, and_assoc]
  rw [e]
  refine ((isClosed_le continuous_const continuous_id).inter
    (isClosed_eq (continuous_finsetSum _ fun h _ => continuous_apply h) continuous_const)).inter ?_
  exact isClosed_biInter fun h _ => isClosed_le continuous_const (continuous_apply h)

lemma simplexEps_compact {l m n : ℕ} (E : Economy l m n) (ε : ℝ) :
    IsCompact (priceSimplexEps E ε) := by
  refine (cube_compact l 1).of_isClosed_subset (simplexEps_closed E ε) ?_
  intro p hp h
  have h0 : 0 ≤ p h := hp.1.1 h
  have h1 : p h ≤ 1 := by
    rw [← hp.1.2]
    exact Finset.single_le_sum (f := p) (fun k _ => hp.1.1 k) (Finset.mem_univ h)
  rw [abs_le]; constructor <;> linarith

lemma simplexEps_convex {l m n : ℕ} (E : Economy l m n) (ε : ℝ) :
    Convex ℝ (priceSimplexEps E ε) := by
  intro p hp q hq a b ha hb hab
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · exact add_nonneg (smul_nonneg ha hp.1.1) (smul_nonneg hb hq.1.1)
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
      ← Finset.mul_sum, hp.1.2, hq.1.2]
    linarith
  · intro h hh
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have h1 := hp.2 h hh
    have h2 := hq.2 h hh
    have e : a * ε + b * ε = ε := by rw [← add_mul, hab, one_mul]
    nlinarith [mul_le_mul_of_nonneg_left h1 ha, mul_le_mul_of_nonneg_left h2 hb]

lemma simplexEps_nonempty {l m n : ℕ} (E : Economy l m n) (ε : ℝ) (hε : 0 < ε)
    (hε' : ε ≤ 1 / (2 * ((productive E).card : ℝ))) : (priceSimplexEps E ε).Nonempty := by
  classical
  have hcard : 0 < (productive E).card := by
    rcases Nat.eq_zero_or_pos (productive E).card with h | h
    · rw [h] at hε'; simp at hε'; linarith
    · exact h
  set π : ℝ := ((productive E).card : ℝ) with hπ
  obtain ⟨h0, hh0⟩ := Finset.card_pos.mp hcard
  have hπpos : 0 < π := by rw [hπ]; exact_mod_cast hcard
  have hπε : π * ε ≤ 1 / 2 := by
    rw [le_div_iff₀ (by positivity)] at hε'
    nlinarith
  refine ⟨fun h => (if h ∈ productive E then ε else 0) + (if h = h0 then 1 - π * ε else 0),
    ⟨?_, ?_⟩, ?_⟩
  · intro h
    have : 0 ≤ (if h ∈ productive E then ε else 0) := by split_ifs <;> linarith
    have : 0 ≤ (if h = h0 then 1 - π * ε else 0) := by split_ifs <;> linarith
    simp only [Pi.zero_apply]; linarith
  · rw [Finset.sum_add_distrib]
    simp [Finset.sum_ite_mem, hπ]
  · intro h hh
    have : 0 ≤ (if h = h0 then 1 - π * ε else 0) := by split_ifs <;> linarith
    simp only [hh, if_true]; linarith

/-- Linear functions are quasiconcave on convex sets. -/
lemma qc_dot {l : ℕ} (s : Set (Fin l → ℝ)) (hs : Convex ℝ s) (v : Fin l → ℝ) :
    QuasiconcaveOn ℝ s (fun b => v ⬝ᵥ b) := by
  intro r x hx y hy a b ha hb hab
  refine ⟨hs hx.1 hy.1 ha hb hab, ?_⟩
  have h1 : r ≤ v ⬝ᵥ x := hx.2
  have h2 : r ≤ v ⬝ᵥ y := hy.2
  show r ≤ v ⬝ᵥ (a • x + b • y)
  rw [dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul]
  have e : a * r + b * r = r := by rw [← add_mul, hab, one_mul]
  nlinarith [mul_le_mul_of_nonneg_left h1 ha, mul_le_mul_of_nonneg_left h2 hb]

lemma convex_budget {l : ℕ} (S : Set (Fin l → ℝ)) (hS : Convex ℝ S) (p : Fin l → ℝ) (r : ℝ) :
    Convex ℝ {x | x ∈ S ∧ p ⬝ᵥ x ≤ r} := by
  intro x hx y hy a b ha hb hab
  refine ⟨hS hx.1 hy.1 ha hb hab, ?_⟩
  have h1 := hx.2
  have h2 := hy.2
  show p ⬝ᵥ (a • x + b • y) ≤ r
  rw [dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul]
  have e : a * r + b * r = r := by rw [← add_mul, hab, one_mul]
  nlinarith [mul_le_mul_of_nonneg_left h1 ha, mul_le_mul_of_nonneg_left h2 hb]

end P2M8555

open ArrowDebreu.Shared ArrowDebreu.ThmII P2M8555 Filter Topology in
theorem solution {l m n : ℕ} (E : Economy l m n) (hE : AssumptionsIIexceptV E)
    (ξ : Fin m → Fin l → ℝ) (hξ : ∀ i, ∀ x ∈ E.X i, ξ i ≤ x)
    (c' : ℝ) (hc' : 0 < c')
    (hX : ∀ i, XhatPrime E ξ i ⊆ interior (cube l c'))
    (hY : ∀ j, YhatPrime E ξ j ⊆ interior (cube l c'))
    (ε : ℝ) (hε : 0 < ε) (hε' : ε ≤ 1 / (2 * ((productive E).card : ℝ))) :
    ∃ a : Player m n → Fin l → ℝ, (economyEtildeEps E ε c').IsEquilibriumPoint a := by
  classical
  set G := economyEtildeEps E ε c' with hG
  -- the consumption vectors of Assumption IV'a
  choose x0 hx0X hx0le h0 hh0 hlt using hE.IVa'
  have hx0C : ∀ i, x0 i ∈ cube l c' := by
    intro i
    refine interior_subset (hX i ⟨hx0X i, x0, 0, rfl, hx0X, fun j => (hE.Ia j).2.2, ?_⟩)
    intro h
    have hs : ∑ i', x0 i' h ≤ totalEndowment E h := by
      simp only [totalEndowment, Finset.sum_apply]
      exact Finset.sum_le_sum fun i' _ => hx0le i' h
    have hnn : 0 ≤ (1 / ((productive E).card : ℝ)) *
        ∑ k ∈ productive E, (totalEndowment E k - ∑ i, ξ i k) := by
      refine mul_nonneg (by positivity) (Finset.sum_nonneg fun k _ => ?_)
      simp only [totalEndowment, Finset.sum_apply]
      rw [sub_nonneg]
      exact Finset.sum_le_sum fun i' _ => le_trans (hξ i' (x0 i') (hx0X i') k) (hx0le i' k)
    simp only [zetaPrime, Pi.sub_apply, Pi.zero_apply, Finset.sum_apply, Finset.sum_const_zero,
      sub_zero]
    linarith
  have hx0lt : ∀ i (p : Fin l → ℝ), p ∈ priceSimplexEps E ε → p ⬝ᵥ x0 i < p ⬝ᵥ E.ζ i := by
    intro i p hp
    have hpos : 0 < p (h0 i) * (E.ζ i (h0 i) - x0 i (h0 i)) :=
      mul_pos (lt_of_lt_of_le hε (hp.2 _ (hh0 i))) (by linarith [hlt i])
    have hle : p (h0 i) * (E.ζ i (h0 i) - x0 i (h0 i)) ≤
        ∑ k, p k * (E.ζ i k - x0 i k) :=
      Finset.single_le_sum (f := fun k => p k * (E.ζ i k - x0 i k))
        (fun k _ => mul_nonneg (hp.1.1 k) (by linarith [hx0le i k])) (Finset.mem_univ _)
    have he : p ⬝ᵥ E.ζ i - p ⬝ᵥ x0 i = ∑ k, p k * (E.ζ i k - x0 i k) := by
      rw [← dotProduct_sub]; rfl
    linarith
  -- basic facts on the action sets
  have hactClosed : ∀ k, IsClosed (G.act k) := by
    intro k; rcases k with i | j | u
    · exact ((hE.II i).1).inter (cube_compact l c').isClosed
    · exact ((hE.Ia j).1).inter (cube_compact l c').isClosed
    · exact simplexEps_closed E ε
  have hcpt : ∀ k, IsCompact (G.act k) := by
    intro k; rcases k with i | j | u
    · exact (cube_compact l c').inter_left (hE.II i).1
    · exact (cube_compact l c').inter_left (hE.Ia j).1
    · exact simplexEps_compact E ε
  have hconv : ∀ k, Convex ℝ (G.act k) := by
    intro k; rcases k with i | j | u
    · exact ((hE.II i).2.1).inter (cube_convex l c')
    · exact ((hE.Ia j).2.1).inter (cube_convex l c')
    · exact simplexEps_convex E ε
  have hne : ∀ k, (G.act k).Nonempty := by
    intro k; rcases k with i | j | u
    · exact ⟨x0 i, hx0X i, hx0C i⟩
    · exact ⟨0, (hE.Ia j).2.2, zero_mem_cube l hc'.le⟩
    · exact simplexEps_nonempty E ε hε hε'
  have hOthersClosed : ∀ k, IsClosed {a | G.OthersIn k a} := by
    intro k
    have e : {a | G.OthersIn k a} =
        ⋂ k', ⋂ (_ : k' ≠ k), (fun a : Player m n → Fin l → ℝ => a k') ⁻¹' G.act k' := by
      ext a; simp [AbstractEconomy.OthersIn]
    rw [e]
    exact isClosed_iInter fun k' => isClosed_iInter fun _ =>
      (hactClosed k').preimage (continuous_apply k')
  have hprice : ∀ k (a : Player m n → Fin l → ℝ), k ≠ Sum.inr (Sum.inr ()) → G.OthersIn k a →
      priceOf a ∈ priceSimplexEps E ε := fun k a hk ha => ha _ (Ne.symm hk)
  -- budget sets are nonempty
  have hbudget : ∀ i (a : Player m n → Fin l → ℝ), 0 ≤ priceOf a →
      x0 i ∈ G.constr (Sum.inl i) a := by
    intro i a hp
    refine ⟨⟨hx0X i, hx0C i⟩, ?_⟩
    have := dotProduct_le_dotProduct_of_nonneg_left (hx0le i) hp
    have := le_max_left 0 (∑ j, E.α i j * (priceOf a ⬝ᵥ prodOf a j))
    linarith
  refine ArrowDebreu.ThmI.lemma_2_5 G hne hcpt hconv ?hcont ?hqc ?hAcont ?hAgraph ?hAconv ?hAne
  case hcont =>
    intro k; rcases k with i | j | u
    · refine ((hE.IIIa i).comp (continuous_apply _).continuousOn ?_)
      intro a ha
      exact (ha (Sum.inl i) (Set.mem_univ _)).1
    · show ContinuousOn (fun a : Player m n → Fin l → ℝ => a (Sum.inr (Sum.inr ())) ⬝ᵥ
          a (Sum.inr (Sum.inl j))) _
      exact (Continuous.dotProduct (continuous_apply (Sum.inr (Sum.inr ())))
        (continuous_apply (Sum.inr (Sum.inl j)))).continuousOn
    · show ContinuousOn (fun a : Player m n → Fin l → ℝ => a (Sum.inr (Sum.inr ())) ⬝ᵥ
          excessDemand E (consOf a) (prodOf a)) _
      refine (Continuous.dotProduct (continuous_apply (Sum.inr (Sum.inr ()))) ?_).continuousOn
      unfold excessDemand consOf prodOf
      exact ((continuous_finsetSum _ fun i _ =>
          continuous_apply (A := fun _ : Player m n => Fin l → ℝ) (Sum.inl i)).sub
        (continuous_finsetSum _ fun j _ =>
          continuous_apply (A := fun _ : Player m n => Fin l → ℝ) (Sum.inr (Sum.inl j)))).sub
        continuous_const
  case hqc =>
    intro k a _
    rcases k with i | j | u
    · have e : (fun b => G.payoff (Sum.inl i) (Function.update a (Sum.inl i) b)) =
          fun b => E.u i b := by
        funext b; simp [hG, economyEtildeEps, economyE]
      rw [e]
      exact Convex.quasiconcaveOn_restrict
        (ArrowDebreu.ThmI.quasiconcave_of_IIIc E hE.II hE.IIIa hE.IIIc i)
        Set.inter_subset_left (hconv (Sum.inl i))
    · have e : (fun b => G.payoff (Sum.inr (Sum.inl j)) (Function.update a (Sum.inr (Sum.inl j)) b)) =
          fun b => priceOf a ⬝ᵥ b := by
        funext b; simp [hG, economyEtildeEps, economyE, priceOf]
      rw [e]
      exact qc_dot _ (hconv _) _
    · have e : (fun b => G.payoff (Sum.inr (Sum.inr u)) (Function.update a (Sum.inr (Sum.inr u)) b)) =
          fun b => excessDemand E (consOf a) (prodOf a) ⬝ᵥ b := by
        funext b
        have hc : consOf (Function.update a (Sum.inr (Sum.inr u)) b) = consOf a := by
          funext i; simp [consOf]
        have hp : prodOf (Function.update a (Sum.inr (Sum.inr u)) b) = prodOf a := by
          funext j; simp [prodOf]
        rw [dotProduct_comm]
        simp [hG, economyEtildeEps, economyE, priceOf, hc, hp]
      rw [e]
      exact qc_dot _ (hconv _) _
  case hAcont =>
    intro k a₀ ha₀
    rcases k with i | j | u
    · have hneI : ∀ b, (ArrowDebreu.ThmI.economyEtilde E c').OthersIn (Sum.inl i) b →
          ((ArrowDebreu.ThmI.economyEtilde E c').constr (Sum.inl i) b).Nonempty := by
        intro b hb
        exact ⟨x0 i, hbudget i b (hb (Sum.inr (Sum.inr ())) (by simp)).1⟩
      have hOI : ∀ b, G.OthersIn (Sum.inl i) b →
          (ArrowDebreu.ThmI.economyEtilde E c').OthersIn (Sum.inl i) b := by
        intro b hb κ hκ
        rcases κ with i' | j' | u'
        · exact hb _ hκ
        · exact hb _ hκ
        · exact (hb _ hκ).1
      have hmin : ∃ x' ∈ E.X i ∩ ArrowDebreu.ThmI.cube l c',
          ArrowDebreu.ThmI.priceOf a₀ ⬝ᵥ x' < ArrowDebreu.ThmI.priceOf a₀ ⬝ᵥ E.ζ i :=
        ⟨x0 i, ⟨hx0X i, hx0C i⟩, hx0lt i _ (hprice _ a₀ (by simp) ha₀)⟩
      have hR := ArrowDebreu.ThmI.remark_3_3_5 E hE.II c' i hneI a₀ (hOI a₀ ha₀) hmin
      intro b₀ hb₀ s hs hconvs
      obtain ⟨t, ht, htk⟩ := hR b₀ hb₀ s (fun k => hOI (s k) (hs k)) hconvs
      exact ⟨t, ht, htk⟩
    · intro b₀ hb₀ s _ _
      exact ⟨fun _ => b₀, tendsto_const_nhds, fun _ => hb₀⟩
    · intro b₀ hb₀ s _ _
      exact ⟨fun _ => b₀, tendsto_const_nhds, fun _ => hb₀⟩
  case hAgraph =>
    intro k
    rcases k with i | j | u
    · have e : G.graph (Sum.inl i) = {a | G.OthersIn (Sum.inl i) a} ∩
          ((fun a : Player m n → Fin l → ℝ => a (Sum.inl i)) ⁻¹' G.act (Sum.inl i) ∩
          {a | priceOf a ⬝ᵥ a (Sum.inl i) ≤
            priceOf a ⬝ᵥ E.ζ i + max 0 (∑ j, E.α i j * (priceOf a ⬝ᵥ prodOf a j))}) := by
        ext a; rfl
      rw [e]
      refine (hOthersClosed _).inter (((hactClosed _).preimage (continuous_apply _)).inter ?_)
      refine isClosed_le (Continuous.dotProduct (continuous_apply _) (continuous_apply _)) ?_
      refine (Continuous.dotProduct (continuous_apply _) continuous_const).add
        (continuous_const.max (continuous_finsetSum _ fun j _ => continuous_const.mul
          (Continuous.dotProduct (continuous_apply _) (continuous_apply _))))
    · have e : G.graph (Sum.inr (Sum.inl j)) = {a | G.OthersIn (Sum.inr (Sum.inl j)) a} ∩
          ((fun a : Player m n → Fin l → ℝ => a (Sum.inr (Sum.inl j))) ⁻¹'
            G.act (Sum.inr (Sum.inl j))) := by
        ext a; rfl
      rw [e]
      exact (hOthersClosed _).inter ((hactClosed _).preimage (continuous_apply _))
    · have e : G.graph (Sum.inr (Sum.inr u)) = {a | G.OthersIn (Sum.inr (Sum.inr u)) a} ∩
          ((fun a : Player m n → Fin l → ℝ => a (Sum.inr (Sum.inr u))) ⁻¹'
            G.act (Sum.inr (Sum.inr u))) := by
        ext a; rfl
      rw [e]
      exact (hOthersClosed _).inter ((hactClosed _).preimage (continuous_apply _))
  case hAconv =>
    intro k a _
    rcases k with i | j | u
    · exact convex_budget _ (hconv (Sum.inl i)) _ _
    · exact hconv (Sum.inr (Sum.inl j))
    · exact hconv (Sum.inr (Sum.inr u))
  case hAne =>
    intro k a ha
    rcases k with i | j | u
    · exact ⟨x0 i, hbudget i a (hprice _ a (by simp) ha).1.1⟩
    · exact hne (Sum.inr (Sum.inl j))
    · exact hne (Sum.inr (Sum.inr u))
