-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FourierCoefficientLattice
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FourierCoefficientLattice
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T14:32:47.166802+00:00
-- url     : https://prove2.me/theorems/2a3810a0-8808-4686-a110-2156fb51a2e4
-- title:
--   Fourier Coefficient Lattice
-- statement:
--   Definitions and structural lemmas for Fourier Coefficient Lattice, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FundamentalDomains/FourierCoefficientLattice.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FourierCoefficientMatrices
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.FD.FourierCoefficientLattice
open NumberField Complex ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FourierCoefficientMatrices ReciprocityTheory.ChartRestriction.G.FD.EmbeddingHermitianPairs
open scoped ComplexConjugate
noncomputable section
section Slot
variable {ι : Type} [Fintype ι]
def intersection_update_fsHerm_neg_one (i0 k0 : Fin 2) : (ι → ℝ) →ₗ[ℝ] (ι → Fin 2 → Fin 2 → ℝ) where
  toFun p := fun τ i k => if i = i0 ∧ k = k0 then p τ else 0
  map_add' p q := by funext τ i k; simp only [Pi.add_apply]; split_ifs <;> simp
  map_smul' s p := by
    funext τ i k; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; split_ifs <;> simp
end Slot
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) (g : ℕ)
def cE : E := ((g * dEnat E : ℕ) : E) / 2
def cr : ℝ := ((g * dEnat E : ℕ) : ℝ) / 2
lemma emb_cE (τ : E →+* ℂ) : τ (cE (E := E) g) = (cr (E := E) g : ℂ) := by
  simp only [cE, cr, map_div₀, map_natCast, map_ofNat]
  try push_cast
  try ring
lemma cr_pos (hg : 0 < g) : 0 < cr (E := E) g := by
  have hd : 0 < dEnat E := Int.natAbs_pos.mpr (NumberField.discr_ne_zero E)
  have h : (0:ℝ) < ((g * dEnat E : ℕ) : ℝ) := by exact_mod_cast Nat.mul_pos hg hd
  show (0:ℝ) < ((g * dEnat E : ℕ) : ℝ) / 2
  linarith
lemma cr_ge (hg : 0 < g) : (1 : ℝ) / 2 ≤ cr (E := E) g := by
  have hd : 0 < dEnat E := Int.natAbs_pos.mpr (NumberField.discr_ne_zero E)
  have h0 := Nat.mul_pos hg hd
  have h : (1:ℝ) ≤ ((g * dEnat E : ℕ) : ℝ) := by exact_mod_cast h0
  show (1:ℝ) / 2 ≤ ((g * dEnat E : ℕ) : ℝ) / 2
  linarith
lemma embH_herm {β : Matrix (Fin 2) (Fin 2) E} (hβ : ∀ i k, cc (β i k) = β k i) :
    IsHermFam (X.embH β) := by
  intro τ i k
  show τ.1 (β k i) = conj (τ.1 (β i k))
  rw [← hβ i k]
  exact NumberField.IsCMField.complexEmbedding_complexConj E τ.1 (β i k)
def LZsub : AddSubgroup (X.Ψ → Fin 2 → Fin 2 → ℂ) where
  carrier := X.LZ g
  add_mem' := by
    rintro _ _ ⟨β, hβ, hγ, rfl⟩ ⟨β', hβ', hγ', rfl⟩
    refine ⟨β + β', fun i k => ?_, fun i k => ?_, ?_⟩
    · show cc (β i k + β' i k) = β k i + β' k i
      rw [show cc (β i k + β' i k) = cc (β i k) + cc (β' i k) from map_add _ _ _, hβ, hβ']
    · obtain ⟨γ, hγi, e⟩ := hγ i k
      obtain ⟨γ', hγi', e'⟩ := hγ' i k
      exact ⟨γ + γ', hγi.add hγi', by simp only [Matrix.add_apply, e, e']; ring⟩
    · funext τ i k; simp [Data.embH]
  zero_mem' := ⟨0, fun i k => by simp [cc], fun i k => ⟨0, isIntegral_zero, by simp⟩,
    by funext τ i k; simp [Data.embH]⟩
  neg_mem' := by
    rintro _ ⟨β, hβ, hγ, rfl⟩
    refine ⟨-β, fun i k => ?_, fun i k => ?_, ?_⟩
    · show cc (-β i k) = -β k i
      rw [show cc (-β i k) = -cc (β i k) from map_neg _ _, hβ]
    · obtain ⟨γ, hγi, e⟩ := hγ i k
      exact ⟨-γ, hγi.neg, by simp only [Matrix.neg_apply, e]; ring⟩
    · funext τ i k; simp [Data.embH]
def Lc : Submodule ℤ (X.Ψ → Fin 2 → Fin 2 → ℝ) :=
  ((LZsub X g).map (kapL : (X.Ψ → Fin 2 → Fin 2 → ℂ) →ₗ[ℝ] _).toAddMonoidHom).toIntSubmodule
lemma mem_Lc {y : X.Ψ → Fin 2 → Fin 2 → ℝ} : y ∈ Lc X g ↔ ∃ b ∈ X.LZ g, kap b = y := by
  first
  | exact Iff.rfl
  | constructor
    · intro h
      obtain ⟨b, hb, e⟩ := AddSubgroup.mem_map.mp (AddSubgroup.mem_toIntSubmodule.mp h)
      exact ⟨b, hb, e⟩
    · rintro ⟨b, hb, e⟩
      exact AddSubgroup.mem_toIntSubmodule.mpr (AddSubgroup.mem_map.mpr ⟨b, hb, e⟩)
lemma finite_small (hg : 0 < g) : {y | y ∈ Lc X g ∧ ‖y‖ < 1}.Finite := by
  have hS := NumberField.Embeddings.finite_of_norm_le E ℂ 4
  have hpi : (Set.pi Set.univ fun _ : Fin 2 => Set.pi Set.univ fun _ : Fin 2 =>
      {x : E | IsIntegral ℤ x ∧ ∀ φ : E →+* ℂ, ‖φ x‖ ≤ 4}).Finite :=
    Set.Finite.pi fun _ => Set.Finite.pi fun _ => hS
  refine (hpi.image fun γ => kap (X.embH fun i k => cE g * γ i k)).subset ?_
  rintro y ⟨hy, hn⟩
  obtain ⟨b, ⟨β, hβ, hγ, rfl⟩, rfl⟩ := (mem_Lc X g).mp hy
  choose γ hγi hγe using hγ
  have hcr := cr_ge (E := E) g hg
  have hcr0 := cr_pos (E := E) g hg
  have hb : IsHermFam (X.embH β) := embH_herm X hβ
  have hk : ∀ (τ : X.Ψ) (i k : Fin 2), |kap (X.embH β) τ i k| < 1 := fun τ i k => by
    have h := (norm_le_pi_norm (kap (X.embH β) τ i) k).trans
      ((norm_le_pi_norm (kap (X.embH β) τ) i).trans (norm_le_pi_norm (kap (X.embH β)) τ))
    rw [Real.norm_eq_abs] at h
    linarith
  have hre : ∀ (τ : X.Ψ) (i k : Fin 2), |(τ.1 (β i k)).re| < 1 ∧ |(τ.1 (β i k)).im| < 1 := by
    intro τ
    have h00 : |(τ.1 (β 0 0)).re| < 1 := by
      first | exact hk τ 0 0 | simpa [kap, Data.embH] using hk τ 0 0
    have h01 : |(τ.1 (β 0 1)).re| < 1 := by
      first | exact hk τ 0 1 | simpa [kap, Data.embH] using hk τ 0 1
    have h10 : |(τ.1 (β 0 1)).im| < 1 := by
      first | exact hk τ 1 0 | simpa [kap, Data.embH] using hk τ 1 0
    have h11 : |(τ.1 (β 1 1)).re| < 1 := by
      first | exact hk τ 1 1 | simpa [kap, Data.embH] using hk τ 1 1
    have e0 : τ.1 (β 0 0) = conj (τ.1 (β 0 0)) := hb τ 0 0
    have e1 : τ.1 (β 1 1) = conj (τ.1 (β 1 1)) := hb τ 1 1
    have e2 : τ.1 (β 1 0) = conj (τ.1 (β 0 1)) := hb τ 0 1
    have i0 : |(τ.1 (β 0 0)).im| < 1 := by
      have h := congrArg Complex.im e0
      rw [Complex.conj_im] at h
      have h' : (τ.1 (β 0 0)).im = 0 := by linarith
      rw [h']
      norm_num
    have i1 : |(τ.1 (β 1 1)).im| < 1 := by
      have h := congrArg Complex.im e1
      rw [Complex.conj_im] at h
      have h' : (τ.1 (β 1 1)).im = 0 := by linarith
      rw [h']
      norm_num
    have r2 : |(τ.1 (β 1 0)).re| < 1 := by rw [e2, Complex.conj_re]; exact h01
    have m2 : |(τ.1 (β 1 0)).im| < 1 := by rw [e2, Complex.conj_im, abs_neg]; exact h10
    refine Fin.forall_fin_two.mpr ⟨Fin.forall_fin_two.mpr ⟨?_, ?_⟩, Fin.forall_fin_two.mpr ⟨?_, ?_⟩⟩
    · exact ⟨h00, i0⟩
    · exact ⟨h01, h10⟩
    · exact ⟨r2, m2⟩
    · exact ⟨h11, i1⟩
  have hΨ : ∀ (τ : X.Ψ) (i k : Fin 2), ‖τ.1 (γ i k)‖ ≤ 4 := by
    intro τ i k
    have h2 : ‖τ.1 (β i k)‖ < 2 := by
      have hn1 := Complex.norm_le_abs_re_add_abs_im (τ.1 (β i k))
      have hr := hre τ i k
      linarith [hr.1, hr.2]
    have e : τ.1 (β i k) = (cr (E := E) g : ℂ) * τ.1 (γ i k) := by
      rw [hγe i k, map_mul]
      congr 1
      exact emb_cE g τ.1
    have en : ‖τ.1 (β i k)‖ = cr (E := E) g * ‖τ.1 (γ i k)‖ := by
      rw [e, norm_mul]
      congr 1
      simp [abs_of_pos hcr0]
    rw [en] at h2
    nlinarith [norm_nonneg (τ.1 (γ i k))]
  refine ⟨γ, ?_, ?_⟩
  · simp only [Set.mem_pi, Set.mem_univ, true_implies, forall_const, Set.mem_setOf_eq]
    intro i k
    refine ⟨hγi i k, fun φ => ?_⟩
    by_cases hφ : φ ∈ X.Ψ
    · exact hΨ ⟨φ, hφ⟩ i k
    · have hc : ComplexEmbedding.conjugate φ ∈ X.Ψ := by
        by_contra h
        exact hφ ((X.cmType φ).mpr h)
      have := hΨ ⟨_, hc⟩ i k
      simpa [NumberField.ComplexEmbedding.conjugate_coe_eq] using this
  · have hfun : (fun i k => cE (E := E) g * γ i k) = β := by
      funext i k
      exact (hγe i k).symm
    exact congrArg (fun β' => kap (X.embH β')) hfun
instance Lc_discrete [Fact (0 < g)] : DiscreteTopology (Lc X g) := by
  have hg : 0 < g := Fact.out
  rw [discreteTopology_iff_isOpen_singleton_zero]
  set T := {y : X.Ψ → Fin 2 → Fin 2 → ℝ | y ∈ Lc X g ∧ ‖y‖ < 1} \ {0}
  have hT : IsClosed T := ((finite_small X g hg).subset Set.sdiff_subset).isClosed
  have h0 : (0 : X.Ψ → Fin 2 → Fin 2 → ℝ) ∈ Tᶜ := by simp [T]
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hT.isOpen_compl 0 h0
  rw [Metric.isOpen_iff]
  intro q hq
  rw [Set.mem_singleton_iff] at hq
  subst hq
  refine ⟨min ε 1, lt_min hε one_pos, fun q hq => ?_⟩
  rw [Metric.mem_ball, dist_zero_right] at hq
  rw [Set.mem_singleton_iff]
  apply Subtype.ext
  have hq' : ‖(q : X.Ψ → Fin 2 → Fin 2 → ℝ)‖ < min ε 1 := by simpa using hq
  by_contra hne
  have hmem : (q : X.Ψ → Fin 2 → Fin 2 → ℝ) ∈ T :=
    ⟨⟨q.2, lt_of_lt_of_le hq' (min_le_right _ _)⟩, hne⟩
  have : (q : X.Ψ → Fin 2 → Fin 2 → ℝ) ∈ Metric.ball (0 : X.Ψ → Fin 2 → Fin 2 → ℝ) ε := by
    rw [Metric.mem_ball, dist_zero_right]; exact lt_of_lt_of_le hq' (min_le_left _ _)
  exact hball this hmem
end
end ReciprocityTheory.ChartRestriction.G.FD.FourierCoefficientLattice


