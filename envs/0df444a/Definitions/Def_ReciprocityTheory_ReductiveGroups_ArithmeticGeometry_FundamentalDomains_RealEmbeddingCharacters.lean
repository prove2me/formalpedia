-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_RealEmbeddingCharacters
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_RealEmbeddingCharacters
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:34:48.491946+00:00
-- url     : https://prove2.me/theorems/8a2eef55-2541-4411-97d0-a2554f35535f
-- title:
--   Real Embedding Characters
-- statement:
--   Definitions and structural lemmas for Real Embedding Characters, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/RealEmbeddingCharacters.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_TransvectionPeriodicity
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.FD.RealEmbeddingCharacters
open NumberField Complex ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.EmbeddingHermitianPairs
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
lemma emb_real {τ : E →+* ℂ} {a : E} (ha : cc a = a) : τ a = ((τ a).re : ℂ) := by
  have h := NumberField.IsCMField.complexEmbedding_complexConj (K := E) τ a
  have h2 : (starRingEnd ℂ) (τ a) = τ a := by
    rw [← h]
    exact congrArg τ ha
  exact (Complex.conj_eq_iff_re.mp h2).symm
lemma cc_add' (a b : E) : cc (a + b) = cc a + cc b := by
  simp only [cc, map_add]
lemma cc_neg' (a : E) : cc (-a) = -cc a := by
  simp only [cc, map_neg]
lemma cc_zero' : cc (0 : E) = 0 := by
  simp only [cc, map_zero]
variable (X : Data E r) (la : Wt X.Ψ r)
lemma chiOrd_pos : 0 < X.chiOrd la := (X.χ_fin la).choose_spec.1
noncomputable def per (a : E) : X.Ψ → ℝ := fun τ => ((X.m * X.chiOrd la : ℕ) : ℝ) * (τ.1 a).re
lemma per_add (a b : E) : per X la (a + b) = per X la a + per X la b := by
  funext τ
  simp only [per, Pi.add_apply, map_add, Complex.add_re, mul_add]
lemma per_neg (a : E) : per X la (-a) = -per X la a := by
  funext τ
  simp only [per, Pi.neg_apply, map_neg, Complex.neg_re, mul_neg]
lemma mem_periods_iff (p : X.Ψ → ℝ) :
    p ∈ X.periods la ↔ ∃ a : E, cc a = a ∧ IsIntegral ℤ a ∧ p = per X la a := by
  constructor
  · intro hp
    unfold Data.periods at hp
    induction hp using AddSubgroup.closure_induction with
    | mem q hq =>
      obtain ⟨a, h1, h2, rfl⟩ := hq
      exact ⟨a, h1, h2, rfl⟩
    | zero =>
      refine ⟨0, cc_zero', isIntegral_zero, ?_⟩
      funext τ
      simp [per]
    | add q q' _ _ hq hq' =>
      obtain ⟨a, ha1, ha2, rfl⟩ := hq
      obtain ⟨b, hb1, hb2, rfl⟩ := hq'
      exact ⟨a + b, by rw [cc_add', ha1, hb1], ha2.add hb2, (per_add X la a b).symm⟩
    | neg q _ hq =>
      obtain ⟨a, ha1, ha2, rfl⟩ := hq
      exact ⟨-a, by rw [cc_neg', ha1], ha2.neg, (per_neg X la a).symm⟩
  · rintro ⟨a, h1, h2, rfl⟩
    exact AddSubgroup.subset_closure ⟨a, h1, h2, rfl⟩
lemma finite_small : {p : X.Ψ → ℝ | p ∈ X.periods la ∧ ‖p‖ < 1}.Finite := by
  have h3 : 1 ≤ X.m * X.chiOrd la := Nat.mul_pos X.m_pos (chiOrd_pos X la)
  have hc : (1 : ℝ) ≤ ((X.m * X.chiOrd la : ℕ) : ℝ) := by exact_mod_cast h3
  have hfin := NumberField.Embeddings.finite_of_norm_le E ℂ 1
  refine (hfin.image (per X la)).subset ?_
  rintro p ⟨hp, hn⟩
  obtain ⟨a, ha, hai, rfl⟩ := (mem_periods_iff X la p).mp hp
  have hΨ : ∀ τ : X.Ψ, ‖τ.1 a‖ ≤ 1 := by
    intro τ
    have h1 : ‖per X la a τ‖ < 1 := lt_of_le_of_lt (norm_le_pi_norm (per X la a) τ) hn
    rw [emb_real (τ := τ.1) ha, Complex.norm_real, Real.norm_eq_abs]
    simp only [per, Real.norm_eq_abs, abs_mul] at h1
    have hc0 : (0 : ℝ) ≤ ((X.m * X.chiOrd la : ℕ) : ℝ) := Nat.cast_nonneg _
    rw [abs_of_nonneg hc0] at h1
    nlinarith [abs_nonneg (τ.1 a).re]
  refine ⟨a, ⟨hai, fun φ => ?_⟩, rfl⟩
  by_cases hφ : φ ∈ X.Ψ
  · exact hΨ ⟨φ, hφ⟩
  · have hc' : NumberField.ComplexEmbedding.conjugate φ ∈ X.Ψ := by
      by_contra hc'
      exact hφ ((X.cmType φ).mpr hc')
    have h4 := hΨ ⟨_, hc'⟩
    change ‖starRingEnd ℂ (φ a)‖ ≤ 1 at h4
    rwa [Complex.norm_conj] at h4
instance periods_discrete : DiscreteTopology (X.periods la) := by
  rw [discreteTopology_iff_isOpen_singleton_zero]
  set T := {p : X.Ψ → ℝ | p ∈ X.periods la ∧ ‖p‖ < 1} \ {0}
  have hT : IsClosed T := ((finite_small X la).subset Set.sdiff_subset).isClosed
  have h0 : (0 : X.Ψ → ℝ) ∈ Tᶜ := by simp [T]
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hT.isOpen_compl 0 h0
  rw [Metric.isOpen_iff]
  intro q hq
  rw [Set.mem_singleton_iff] at hq
  subst hq
  refine ⟨min ε 1, lt_min hε one_pos, fun q hq => ?_⟩
  rw [Metric.mem_ball, dist_zero_right] at hq
  rw [Set.mem_singleton_iff]
  apply Subtype.ext
  have hq' : ‖(q : X.Ψ → ℝ)‖ < min ε 1 := by simpa using hq
  by_contra hne
  have hmem : (q : X.Ψ → ℝ) ∈ T :=
    ⟨⟨q.2, lt_of_lt_of_le hq' (min_le_right _ _)⟩, hne⟩
  have : (q : X.Ψ → ℝ) ∈ Metric.ball (0 : X.Ψ → ℝ) ε := by
    rw [Metric.mem_ball, dist_zero_right]; exact lt_of_lt_of_le hq' (min_le_left _ _)
  exact hball this hmem
def fixF : Subfield E where
  carrier := {a | cc a = a}
  mul_mem' {a b} ha hb := by
    show cc (a * b) = a * b
    rw [show cc (a * b) = cc a * cc b from map_mul _ a b, show cc a = a from ha, show cc b = b from hb]
  one_mem' := show cc (1 : E) = 1 from map_one _
  add_mem' {a b} ha hb := by
    show cc (a + b) = a + b
    rw [cc_add', show cc a = a from ha, show cc b = b from hb]
  zero_mem' := cc_zero'
  neg_mem' {a} ha := by
    show cc (-a) = -a
    rw [cc_neg', show cc a = a from ha]
  inv_mem' a ha := by
    show cc a⁻¹ = a⁻¹
    rw [show cc a⁻¹ = (cc a)⁻¹ from map_inv₀ _ a, show cc a = a from ha]
lemma cc_cc' (a : E) : cc (cc a) = a := by
  simp only [cc, NumberField.IsCMField.complexConj_apply_apply]
lemma restrict_inj {τ τ' : X.Ψ} (h : ∀ a : E, cc a = a → τ.1 a = τ'.1 a) : τ = τ' := by
  have hξ := X.ξ0_im
  have hξne := X.ξ0_ne
  have hf : ∀ a : E, cc (a + cc a) = a + cc a := fun a => by rw [cc_add', cc_cc', add_comm]
  have hh : ∀ a : E, cc ((a - cc a) * X.ξ0) = (a - cc a) * X.ξ0 := fun a => by
    rw [show cc ((a - cc a) * X.ξ0) = cc (a - cc a) * cc X.ξ0 from map_mul _ _ _, hξ,
      sub_eq_add_neg, cc_add', cc_neg', cc_cc']
    ring
  have hdec : ∀ a : E, (2 : E) * a = (a + cc a) + ((a - cc a) * X.ξ0) / X.ξ0 := fun a => by
    rw [mul_div_cancel_right₀ _ hξne]
    ring
  have hexp : ∀ σ : E →+* ℂ, ∀ a : E,
      2 * σ a = σ (a + cc a) + σ ((a - cc a) * X.ξ0) / σ X.ξ0 := by
    intro σ a
    have e := congrArg σ (hdec a)
    rw [map_mul, map_add, map_div₀, map_ofNat] at e
    exact e
  have hsq : τ.1 X.ξ0 ^ 2 = τ'.1 X.ξ0 ^ 2 := by
    rw [← map_pow, ← map_pow]
    apply h
    rw [pow_two, show cc (X.ξ0 * X.ξ0) = cc X.ξ0 * cc X.ξ0 from map_mul _ _ _, hξ]
    ring
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h1 | h1
  · apply Subtype.ext
    apply RingHom.ext
    intro a
    have e1 := hexp τ.1 a
    have e2 := hexp τ'.1 a
    rw [h (a + cc a) (hf a), h _ (hh a), h1] at e1
    have e3 : (2 : ℂ) * τ.1 a = 2 * τ'.1 a := e1.trans e2.symm
    exact mul_left_cancel₀ two_ne_zero e3
  · exfalso
    have hconj : ∀ a : E, τ'.1 a = starRingEnd ℂ (τ.1 a) := by
      intro a
      have e1 := hexp τ.1 (cc a)
      have e2 := hexp τ'.1 a
      rw [cc_cc'] at e1
      rw [← NumberField.IsCMField.complexEmbedding_complexConj (K := E) τ.1 a]
      show τ'.1 a = τ.1 (cc a)
      have k1 : τ.1 (cc a + a) = τ'.1 (a + cc a) := by
        rw [add_comm]
        exact h _ (hf a)
      have k2 : τ.1 ((cc a - a) * X.ξ0) = -τ'.1 ((a - cc a) * X.ξ0) := by
        rw [show (cc a - a) * X.ξ0 = -((a - cc a) * X.ξ0) by ring, map_neg, h _ (hh a)]
      rw [k1, k2, h1] at e1
      have e3 : (2 : ℂ) * τ.1 (cc a) = 2 * τ'.1 a := by
        rw [e1, e2, neg_div_neg_eq]
      exact (mul_left_cancel₀ two_ne_zero e3).symm
    have hτ : τ'.1 = NumberField.ComplexEmbedding.conjugate τ.1 := by
      apply RingHom.ext
      intro a
      rw [hconj a]
      rfl
    have hm := (X.cmType τ.1).mp τ.2
    rw [← hτ] at hm
    exact hm τ'.2
def resChar (τ : X.Ψ) : (fixF (E := E)) →* ℂ := (τ.1.comp (fixF (E := E)).subtype).toMonoidHom
open Classical in
lemma periods_span : Submodule.span ℝ (X.periods la : Set (X.Ψ → ℝ)) = ⊤ := by
  by_contra hne
  obtain ⟨f, hf0, hle⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.mpr hne)
  have hfv : ∀ v : X.Ψ → ℝ, f v = ∑ τ, v τ * f (fun j => if τ = j then 1 else 0) := fun v => by
    rw [LinearMap.pi_apply_eq_sum_univ f v]
    rfl
  have hM : ((X.m * X.chiOrd la : ℕ) : ℝ) ≠ 0 := by
    have h3 : 0 < X.m * X.chiOrd la := Nat.mul_pos X.m_pos (chiOrd_pos X la)
    exact_mod_cast h3.ne'

  have hvan : ∀ a : E, cc a = a → IsIntegral ℤ a →
      ∑ τ : X.Ψ, ((f (fun j => if τ = j then 1 else 0) : ℝ) : ℂ) * τ.1 a = 0 := by
    intro a ha hai
    have hmem : per X la a ∈ Submodule.span ℝ (X.periods la : Set (X.Ψ → ℝ)) :=
      Submodule.subset_span ((mem_periods_iff X la _).mpr ⟨a, ha, hai, rfl⟩)
    have h0 : f (per X la a) = 0 := LinearMap.mem_ker.mp (hle hmem)
    rw [hfv] at h0
    have h1 : ∑ τ : X.Ψ, (τ.1 a).re * f (fun j => if τ = j then 1 else 0) = 0 := by
      have h5 : ((X.m * X.chiOrd la : ℕ) : ℝ) *
          ∑ τ : X.Ψ, (τ.1 a).re * f (fun j => if τ = j then 1 else 0) = 0 := by
        rw [Finset.mul_sum]
        refine Eq.trans (Finset.sum_congr rfl fun τ _ => ?_) h0
        simp only [per]
        ring
      rcases mul_eq_zero.mp h5 with h | h
      · exact absurd h hM
      · exact h
    have h2 : ∀ τ : X.Ψ, ((f (fun j => if τ = j then 1 else 0) : ℝ) : ℂ) * τ.1 a =
        (((τ.1 a).re * f (fun j => if τ = j then 1 else 0) : ℝ) : ℂ) := by
      intro τ
      conv_lhs => rw [emb_real (τ := τ.1) ha]
      push_cast
      ring
    rw [Finset.sum_congr rfl fun τ _ => h2 τ, ← Complex.ofReal_sum, h1, Complex.ofReal_zero]

  let G : Submonoid (fixF (E := E)) :=
    { carrier := {a | IsIntegral ℤ (a : E)}
      mul_mem' := fun {a b} ha hb => IsIntegral.mul ha hb
      one_mem' := isIntegral_one }
  have hinj : Function.Injective (fun τ : X.Ψ => (resChar X τ).comp G.subtype) := by
    intro τ τ' h
    apply restrict_inj X
    intro a ha
    have hG : ∀ b : E, cc b = b → IsIntegral ℤ b → τ.1 b = τ'.1 b := by
      intro b hb hbi
      have h6 := DFunLike.congr_fun h (⟨⟨b, hb⟩, hbi⟩ : G)
      exact h6
    obtain ⟨x, y, hy, hxy⟩ := IsFractionRing.div_surjective (A := 𝓞 E) a
    set x' : E := algebraMap (𝓞 E) E x with hx'
    set y' : E := algebraMap (𝓞 E) E y with hy'
    have hy0 : y' ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hy
    have hxi : IsIntegral ℤ x' := (Algebra.IsIntegral.isIntegral (R := ℤ) x).algebraMap
    have hyi : IsIntegral ℤ y' := (Algebra.IsIntegral.isIntegral (R := ℤ) y).algebraMap
    have hcy : IsIntegral ℤ (cc y') :=
      hyi.map (RingHom.toIntAlgHom (IsCMField.complexConj E : E →+* E))
    have hcy0 : cc y' ≠ 0 := by
      intro h0
      apply hy0
      rw [← cc_cc' y', h0, cc_zero']
    have hd0 : y' * cc y' ≠ 0 := mul_ne_zero hy0 hcy0
    have hdfix : cc (y' * cc y') = y' * cc y' := by
      rw [show cc (y' * cc y') = cc y' * cc (cc y') from map_mul _ _ _, cc_cc', mul_comm]
    have hn : a * (y' * cc y') = x' * cc y' := by
      rw [← hxy, ← mul_assoc, div_mul_cancel₀ _ hy0]
    have hnfix : cc (x' * cc y') = x' * cc y' := by
      rw [← hn, show cc (a * (y' * cc y')) = cc a * cc (y' * cc y') from map_mul _ _ _, ha, hdfix]
    have e1 := hG _ hdfix (hyi.mul hcy)
    have e2 := hG _ hnfix (hxi.mul hcy)
    have ha' : a = (x' * cc y') / (y' * cc y') := by
      rw [← hn, mul_div_cancel_right₀ _ hd0]
    rw [ha', map_div₀, map_div₀, e1, e2]
  have hLI : LinearIndependent ℂ
      (fun τ : X.Ψ => (((resChar X τ).comp G.subtype : G →* ℂ) : G → ℂ)) :=
    (linearIndependent_monoidHom G ℂ).comp _ hinj
  have hsum : ∑ τ : X.Ψ, ((f (fun j => if τ = j then 1 else 0) : ℝ) : ℂ) •
      (((resChar X τ).comp G.subtype : G →* ℂ) : G → ℂ) = 0 := by
    funext g
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    exact hvan _ g.1.2 g.2
  have hzero := Fintype.linearIndependent_iff.mp hLI _ hsum
  apply hf0
  apply LinearMap.ext
  intro v
  rw [hfv v, LinearMap.zero_apply]
  refine Finset.sum_eq_zero fun τ _ => ?_
  rw [Complex.ofReal_eq_zero.mp (hzero τ), mul_zero]
def perL : Submodule ℤ (X.Ψ → ℝ) := (X.periods la).toIntSubmodule
instance perL_discrete : DiscreteTopology (perL X la) := periods_discrete X la
instance perL_isZLattice : IsZLattice ℝ (perL X la) := ⟨periods_span X la⟩
end ReciprocityTheory.ChartRestriction.G.FD.RealEmbeddingCharacters


