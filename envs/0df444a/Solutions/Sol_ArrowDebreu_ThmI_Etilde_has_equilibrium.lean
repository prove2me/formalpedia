-- Prove2me | solution 1 for ArrowDebreu.ThmI.Etilde_has_equilibrium
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T21:57:04.511561+00:00
-- url     : https://prove2.me/submissions/cf3698b1-ae5c-4f69-8527-0eff2e18df3a

import Mathlib
import Definitions.Def_ArrowDebreu_Shared_Economy
import Definitions.Def_ArrowDebreu_ThmI_AssumptionsItoIV
import Definitions.Def_ArrowDebreu_Shared_IsCompetitiveEquilibrium
import Definitions.Def_ArrowDebreu_Shared_AbstractEconomy
import Definitions.Def_ArrowDebreu_ThmI_economyE
import Theorems.Thm_ArrowDebreu_ThmI_lemma_2_5
import Theorems.Thm_ArrowDebreu_ThmI_remark_3_3_5
import Theorems.Thm_ArrowDebreu_ThmI_quasiconcave_of_IIIc
open ArrowDebreu.Shared

open Filter Topology

namespace ArrowDebreu.ThmI

namespace HasEqAux

variable {l m n : ℕ}

/-- Updating a producer's or consumer's action does not change the price. -/
theorem priceOf_update_of_ne (a : Player m n → Fin l → ℝ) (k : Player m n)
    (hk : k ≠ Sum.inr (Sum.inr ())) (v : Fin l → ℝ) :
    priceOf (Function.update a k v) = priceOf a := by
  unfold priceOf
  rw [Function.update_of_ne (Ne.symm hk)]

/-- Updating the price does not change the consumption vectors. -/
theorem consOf_update_price (a : Player m n → Fin l → ℝ) (p : Fin l → ℝ) :
    consOf (Function.update a (Sum.inr (Sum.inr ())) p) = consOf a := by
  funext i
  unfold consOf
  rw [Function.update_of_ne (by simp)]

/-- Updating the price does not change the production plans. -/
theorem prodOf_update_price (a : Player m n → Fin l → ℝ) (p : Fin l → ℝ) :
    prodOf (Function.update a (Sum.inr (Sum.inr ())) p) = prodOf a := by
  funext j
  unfold prodOf
  rw [Function.update_of_ne (by simp)]

/-- Updating the price sets the price. -/
theorem priceOf_update_price (a : Player m n → Fin l → ℝ) (p : Fin l → ℝ) :
    priceOf (Function.update a (Sum.inr (Sum.inr ())) p) = p := by
  unfold priceOf
  rw [Function.update_self]

/-- The consumer's constraint set of `economyE`, unfolded. -/
theorem mem_constr_cons_iff (E : Economy l m n) (X' : Fin m → Set (Fin l → ℝ))
    (Y' : Fin n → Set (Fin l → ℝ)) (a : Player m n → Fin l → ℝ) (i : Fin m) (x : Fin l → ℝ) :
    x ∈ (economyE E X' Y').constr (Sum.inl i) a ↔
      x ∈ X' i ∧ priceOf a ⬝ᵥ x ≤
        priceOf a ⬝ᵥ E.ζ i + max 0 (∑ j, E.α i j * (priceOf a ⬝ᵥ prodOf a j)) :=
  Iff.rfl

/-- The cube of §3.3.3 is the closed ball of radius `c` for the sup norm. -/
theorem cube_eq_closedBall (l : ℕ) {c : ℝ} (hc : 0 ≤ c) :
    cube l c = Metric.closedBall (0 : Fin l → ℝ) c := by
  ext x
  rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg hc]
  constructor
  · intro h i
    rw [Real.norm_eq_abs]
    exact h i
  · intro h i
    rw [← Real.norm_eq_abs]
    exact h i

theorem zero_mem_cube (l : ℕ) {c : ℝ} (hc : 0 ≤ c) : (0 : Fin l → ℝ) ∈ cube l c := by
  intro h
  simp [hc]

theorem isClosed_cube (l : ℕ) {c : ℝ} (hc : 0 ≤ c) : IsClosed (cube l c) := by
  rw [cube_eq_closedBall l hc]
  exact Metric.isClosed_closedBall

theorem isCompact_cube (l : ℕ) {c : ℝ} (hc : 0 ≤ c) : IsCompact (cube l c) := by
  rw [cube_eq_closedBall l hc]
  exact isCompact_closedBall _ _

theorem convex_cube (l : ℕ) {c : ℝ} (hc : 0 ≤ c) : Convex ℝ (cube l c) := by
  rw [cube_eq_closedBall l hc]
  exact convex_closedBall _ _

/-- The price simplex is Mathlib's standard simplex. -/
theorem priceSimplex_eq_stdSimplex (l : ℕ) : priceSimplex l = stdSimplex ℝ (Fin l) := by
  ext p
  exact Iff.rfl

theorem isCompact_priceSimplex (l : ℕ) : IsCompact (priceSimplex l) := by
  rw [priceSimplex_eq_stdSimplex]
  exact isCompact_stdSimplex ℝ (Fin l)

theorem isClosed_priceSimplex (l : ℕ) : IsClosed (priceSimplex l) :=
  (isCompact_priceSimplex l).isClosed

theorem convex_priceSimplex (l : ℕ) : Convex ℝ (priceSimplex l) := by
  rw [priceSimplex_eq_stdSimplex]
  exact convex_stdSimplex ℝ (Fin l)

theorem priceSimplex_nonempty {l : ℕ} (hl : 0 < l) : (priceSimplex l).Nonempty := by
  refine ⟨fun _ => (l : ℝ)⁻¹, fun h => ?_, ?_⟩
  · exact inv_nonneg.2 (Nat.cast_nonneg l)
  · simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    exact mul_inv_cancel₀ (by exact_mod_cast hl.ne')

/-- A price in the simplex has a positive coordinate. -/
theorem exists_pos_of_mem_priceSimplex {l : ℕ} {p : Fin l → ℝ} (hp : p ∈ priceSimplex l) :
    ∃ h, 0 < p h := by
  have : ∑ h : Fin l, (0:ℝ) < ∑ h, p h := by
    rw [hp.2]
    simp
  obtain ⟨h, _, hh⟩ := Finset.exists_lt_of_sum_lt this
  exact ⟨h, hh⟩

/-- If `x < ζ` componentwise and `p ∈ P`, then `p·x < p·ζ`. -/
theorem dot_lt_of_lt {l : ℕ} {p x ζ : Fin l → ℝ} (hp : p ∈ priceSimplex l)
    (hlt : ∀ h, x h < ζ h) : p ⬝ᵥ x < p ⬝ᵥ ζ := by
  obtain ⟨h₀, hh₀⟩ := exists_pos_of_mem_priceSimplex hp
  unfold dotProduct
  refine Finset.sum_lt_sum (fun h _ => mul_le_mul_of_nonneg_left (hlt h).le (hp.1 h))
    ⟨h₀, Finset.mem_univ _, mul_lt_mul_of_pos_left (hlt h₀) hh₀⟩

theorem isLinearMap_dot_right {l : ℕ} (p : Fin l → ℝ) :
    IsLinearMap ℝ (fun b : Fin l → ℝ => p ⬝ᵥ b) :=
  ⟨dotProduct_add p, fun c x => by simp [dotProduct_smul]⟩

theorem isLinearMap_dot_left {l : ℕ} (z : Fin l → ℝ) :
    IsLinearMap ℝ (fun p : Fin l → ℝ => p ⬝ᵥ z) :=
  ⟨fun x y => add_dotProduct x y z, fun c x => by simp [smul_dotProduct]⟩

theorem continuous_priceOf : Continuous (priceOf : (Player m n → Fin l → ℝ) → Fin l → ℝ) :=
  continuous_apply _

theorem continuous_prodOf (j : Fin n) :
    Continuous (fun a : Player m n → Fin l → ℝ => prodOf a j) :=
  continuous_apply _

theorem continuous_excess (E : Economy l m n) :
    Continuous (fun a : Player m n → Fin l → ℝ => excessDemand E (consOf a) (prodOf a)) := by
  have h1 : Continuous (fun a : Player m n → Fin l → ℝ => ∑ i, a (Sum.inl i)) :=
    continuous_finsetSum _ (fun i _ => continuous_apply _)
  have h2 : Continuous (fun a : Player m n → Fin l → ℝ => ∑ j, a (Sum.inr (Sum.inl j))) :=
    continuous_finsetSum _ (fun j _ => continuous_apply _)
  exact (h1.sub h2).sub continuous_const

/-- The consumption vectors of Assumption IV.a are attainable (with `y = 0`). -/
theorem IVa_mem_Xhat (E : Economy l m n) (hIa : AssumptionIa E) (x₀ : Fin m → Fin l → ℝ)
    (hx₀ : ∀ i, x₀ i ∈ E.X i ∧ ∀ h, x₀ i h < E.ζ i h) (i : Fin m) : x₀ i ∈ Xhat E i := by
  refine ⟨(hx₀ i).1, x₀, 0, rfl, fun i' => (hx₀ i').1, fun j => ?_, ?_⟩
  · show (0 : Fin l → ℝ) ∈ E.Y j
    exact (hIa j).2.2
  · intro h
    have hs : ∑ i', x₀ i' h ≤ ∑ i', E.ζ i' h :=
      Finset.sum_le_sum (fun i' _ => ((hx₀ i').2 h).le)
    simp only [excessDemand, Pi.sub_apply, Finset.sum_apply, Pi.zero_apply,
      Finset.sum_const_zero]
    linarith

end HasEqAux

end ArrowDebreu.ThmI

open ArrowDebreu.ThmI ArrowDebreu.ThmI.HasEqAux
open ArrowDebreu.Shared

theorem solution {l m n : ℕ} (hl : 0 < l) (E : Economy l m n)
    (hE : AssumptionsItoIV E) (c : ℝ) (hc : 0 < c)
    (hX : ∀ i, Xhat E i ⊆ interior (cube l c)) (hY : ∀ j, Yhat E j ⊆ interior (cube l c)) :
    ∃ a, (economyEtilde E c).IsEquilibriumPoint a := by
  classical
  choose x₀ hx₀ using hE.IVa
  have hx₀C : ∀ i, x₀ i ∈ E.X i ∩ cube l c :=
    fun i => ⟨(hx₀ i).1, interior_subset (hX i (IVa_mem_Xhat E hE.Ia x₀ hx₀ i))⟩
  have h0C : (0 : Fin l → ℝ) ∈ cube l c := zero_mem_cube l hc.le
  have hact_closed : ∀ k, IsClosed ((economyEtilde E c).act k) := by
    intro k
    rcases k with i | j | ⟨⟩
    · exact (hE.II i).1.inter (isClosed_cube l hc.le)
    · exact (hE.Ia j).1.inter (isClosed_cube l hc.le)
    · exact isClosed_priceSimplex l
  have hprice_of_others : ∀ i (a : Player m n → Fin l → ℝ),
      (economyEtilde E c).OthersIn (Sum.inl i) a → priceOf a ∈ priceSimplex l :=
    fun i a ha => ha (Sum.inr (Sum.inr ())) (by simp)
  have hne_cons : ∀ i (a : Player m n → Fin l → ℝ), (economyEtilde E c).OthersIn (Sum.inl i) a →
      ((economyEtilde E c).constr (Sum.inl i) a).Nonempty := by
    intro i a ha
    refine ⟨x₀ i, ?_⟩
    rw [economyEtilde, mem_constr_cons_iff]
    refine ⟨hx₀C i, ?_⟩
    have h1 := dot_lt_of_lt (hprice_of_others i a ha) (hx₀ i).2
    have h2 := le_max_left (0:ℝ) (∑ j, E.α i j * (priceOf a ⬝ᵥ prodOf a j))
    linarith
  refine lemma_2_5 (economyEtilde E c) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · -- nonempty action sets
    intro k
    rcases k with i | j | ⟨⟩
    · exact ⟨x₀ i, hx₀C i⟩
    · exact ⟨0, (hE.Ia j).2.2, h0C⟩
    · exact priceSimplex_nonempty hl
  · -- compact action sets
    intro k
    rcases k with i | j | ⟨⟩
    · exact (isCompact_cube l hc.le).inter_left (hE.II i).1
    · exact (isCompact_cube l hc.le).inter_left (hE.Ia j).1
    · exact isCompact_priceSimplex l
  · -- convex action sets
    intro k
    rcases k with i | j | ⟨⟩
    · exact (hE.II i).2.1.inter (convex_cube l hc.le)
    · exact (hE.Ia j).2.1.inter (convex_cube l hc.le)
    · exact convex_priceSimplex l
  · -- continuity of the pay-offs on `𝔄`
    intro k
    rcases k with i | j | ⟨⟩
    · show ContinuousOn (fun a : Player m n → Fin l → ℝ => E.u i (a (Sum.inl i)))
        (economyEtilde E c).profiles
      refine (hE.IIIa i).comp (continuous_apply (Sum.inl i)).continuousOn ?_
      intro a ha
      exact (Set.mem_univ_pi.1 ha (Sum.inl i)).1
    · show ContinuousOn (fun a : Player m n → Fin l → ℝ =>
        priceOf a ⬝ᵥ a (Sum.inr (Sum.inl j))) (economyEtilde E c).profiles
      exact (continuous_priceOf.dotProduct (continuous_apply _)).continuousOn
    · show ContinuousOn (fun a : Player m n → Fin l → ℝ =>
        priceOf a ⬝ᵥ excessDemand E (consOf a) (prodOf a)) (economyEtilde E c).profiles
      exact (continuous_priceOf.dotProduct (continuous_excess E)).continuousOn
  · -- quasi-concavity in the own action
    intro k a _
    rcases k with i | j | ⟨⟩
    · show QuasiconcaveOn ℝ (E.X i ∩ cube l c)
        (fun b => E.u i ((Function.update a (Sum.inl i) b) (Sum.inl i)))
      simp only [Function.update_self]
      intro r
      have hq := quasiconcave_of_IIIc E hE.II hE.IIIa hE.IIIc i r
      have heq : {x | x ∈ E.X i ∩ cube l c ∧ r ≤ E.u i x} =
          {x | x ∈ E.X i ∧ r ≤ E.u i x} ∩ cube l c := by
        ext x
        constructor
        · rintro ⟨⟨h1, h2⟩, h3⟩
          exact ⟨⟨h1, h3⟩, h2⟩
        · rintro ⟨⟨h1, h3⟩, h2⟩
          exact ⟨⟨h1, h2⟩, h3⟩
      rw [heq]
      exact hq.inter (convex_cube l hc.le)
    · show QuasiconcaveOn ℝ (E.Y j ∩ cube l c)
        (fun b => priceOf (Function.update a (Sum.inr (Sum.inl j)) b) ⬝ᵥ
          (Function.update a (Sum.inr (Sum.inl j)) b) (Sum.inr (Sum.inl j)))
      simp only [priceOf_update_of_ne a (Sum.inr (Sum.inl j)) (by simp), Function.update_self]
      intro r
      exact ((hE.Ia j).2.1.inter (convex_cube l hc.le)).inter
        (convex_halfSpace_ge (isLinearMap_dot_right (priceOf a)) r)
    · show QuasiconcaveOn ℝ (priceSimplex l)
        (fun p => priceOf (Function.update a (Sum.inr (Sum.inr ())) p) ⬝ᵥ
          excessDemand E (consOf (Function.update a (Sum.inr (Sum.inr ())) p))
            (prodOf (Function.update a (Sum.inr (Sum.inr ())) p)))
      simp only [priceOf_update_price, consOf_update_price, prodOf_update_price]
      intro r
      exact (convex_priceSimplex l).inter
        (convex_halfSpace_ge (isLinearMap_dot_left _) r)
  · -- continuity (lower hemicontinuity) of the constraint correspondences
    intro k
    rcases k with i | j | ⟨⟩
    · intro a₀ ha₀
      exact remark_3_3_5 E hE.II c i (hne_cons i) a₀ ha₀
        ⟨x₀ i, hx₀C i, dot_lt_of_lt (hprice_of_others i a₀ ha₀) (hx₀ i).2⟩
    · intro a₀ _ b₀ hb₀ s _ _
      exact ⟨fun _ => b₀, tendsto_const_nhds, fun _ => hb₀⟩
    · intro a₀ _ b₀ hb₀ s _ _
      exact ⟨fun _ => b₀, tendsto_const_nhds, fun _ => hb₀⟩
  · -- closed graphs
    intro k
    have hOthers : IsClosed {a : Player m n → Fin l → ℝ | (economyEtilde E c).OthersIn k a} := by
      have heq : {a : Player m n → Fin l → ℝ | (economyEtilde E c).OthersIn k a} =
          ⋂ k', ⋂ (_ : k' ≠ k), (fun a : Player m n → Fin l → ℝ => a k') ⁻¹'
            (economyEtilde E c).act k' := by
        ext a
        simp only [Set.mem_iInter, Set.mem_preimage]
        exact Iff.rfl
      rw [heq]
      exact isClosed_iInter (fun k' => isClosed_iInter
        (fun _ => (hact_closed k').preimage (continuous_apply k')))
    have hown : IsClosed {a : Player m n → Fin l → ℝ |
        a k ∈ (economyEtilde E c).constr k a} := by
      rcases k with i | j | ⟨⟩
      · show IsClosed {a : Player m n → Fin l → ℝ | a (Sum.inl i) ∈ E.X i ∩ cube l c ∧
          priceOf a ⬝ᵥ a (Sum.inl i) ≤
            priceOf a ⬝ᵥ E.ζ i + max 0 (∑ j, E.α i j * (priceOf a ⬝ᵥ prodOf a j))}
        have hcl1 : IsClosed {a : Player m n → Fin l → ℝ | a (Sum.inl i) ∈ E.X i ∩ cube l c} :=
          ((hE.II i).1.inter (isClosed_cube l hc.le)).preimage (continuous_apply _)
        have hf : Continuous (fun a : Player m n → Fin l → ℝ => priceOf a ⬝ᵥ a (Sum.inl i)) :=
          continuous_priceOf.dotProduct (continuous_apply _)
        have hg : Continuous (fun a : Player m n → Fin l → ℝ =>
            priceOf a ⬝ᵥ E.ζ i + max 0 (∑ j, E.α i j * (priceOf a ⬝ᵥ prodOf a j))) := by
          refine (continuous_priceOf.dotProduct continuous_const).add
            (continuous_const.max (continuous_finsetSum _ (fun j _ => ?_)))
          exact continuous_const.mul (continuous_priceOf.dotProduct (continuous_prodOf j))
        have hcl2 : IsClosed {a : Player m n → Fin l → ℝ | priceOf a ⬝ᵥ a (Sum.inl i) ≤
            priceOf a ⬝ᵥ E.ζ i + max 0 (∑ j, E.α i j * (priceOf a ⬝ᵥ prodOf a j))} :=
          isClosed_le hf hg
        exact hcl1.inter hcl2
      · show IsClosed {a : Player m n → Fin l → ℝ | a (Sum.inr (Sum.inl j)) ∈ E.Y j ∩ cube l c}
        exact ((hE.Ia j).1.inter (isClosed_cube l hc.le)).preimage (continuous_apply _)
      · show IsClosed {a : Player m n → Fin l → ℝ | a (Sum.inr (Sum.inr ())) ∈ priceSimplex l}
        exact (isClosed_priceSimplex l).preimage (continuous_apply _)
    exact hOthers.inter hown
  · -- convex constraint sets
    intro k a _
    rcases k with i | j | ⟨⟩
    · show Convex ℝ {x | x ∈ E.X i ∩ cube l c ∧ priceOf a ⬝ᵥ x ≤
        priceOf a ⬝ᵥ E.ζ i + max 0 (∑ j, E.α i j * (priceOf a ⬝ᵥ prodOf a j))}
      exact ((hE.II i).2.1.inter (convex_cube l hc.le)).inter
        (convex_halfSpace_le (isLinearMap_dot_right (priceOf a)) _)
    · exact (hE.Ia j).2.1.inter (convex_cube l hc.le)
    · exact convex_priceSimplex l
  · -- nonempty constraint sets
    intro k a ha
    rcases k with i | j | ⟨⟩
    · exact hne_cons i a ha
    · exact ⟨0, (hE.Ia j).2.2, h0C⟩
    · exact priceSimplex_nonempty hl

