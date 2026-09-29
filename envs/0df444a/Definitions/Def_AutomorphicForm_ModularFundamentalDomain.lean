-- Prove2me | Definitions.Def_AutomorphicForm_ModularFundamentalDomain
-- name    : AutomorphicForm_ModularFundamentalDomain
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.014713+00:00
-- url     : https://prove2.me/theorems/f4bad8ff-cd4e-5c0c-bba2-a2f3dcb850f0
-- title:
--   Two-to-one unfolding over the modular fundamental domain
-- statement:
--   The setting is the upper half-plane $\mathbb{H}$ with its hyperbolic volume (the $SL(2,\mathbb{Z})$-invariant measure of the project's measure module), Mathlib's closed fundamental domain $\mathcal{D} = \{z : 1 \le |z|,\ |\operatorname{Re} z| \le 1/2\}$ and its open counterpart $\mathcal{D}^{o}$. The single new definition is `goodSet`, the set of $z \in \mathbb{H}$ for which some $\gamma \in SL(2,\mathbb{Z})$ carries $z$ into $\mathcal{D}^{o}$; its complement is shown to be null, by covering it with the translates $\gamma \cdot (\mathcal{D} \setminus \mathcal{D}^{o})$ of the null boundary.
--
--   The remaining declarations record the arithmetic of $\pm 1$ in $SL(2,\mathbb{Z})$ and its measure-theoretic consequences: $-1$ acts trivially on $\mathbb{H}$ and on subsets of $\mathbb{H}$, $1 \ne -1$, $(-\gamma)^{-1} = -\gamma^{-1}$, $\gamma \ne -\gamma$; for $\gamma \ne \pm 1$ the overlap $\gamma \cdot \mathcal{D} \cap \mathcal{D}$ lies in $\mathcal{D} \setminus \mathcal{D}^{o}$ and is therefore null; and, because $1 \cdot \mathcal{D}$ and $(-1) \cdot \mathcal{D}$ coincide while $\mathcal{D}$ has positive volume, $\mathcal{D}$ is *not* a fundamental domain for the full group $SL(2,\mathbb{Z})$ in Mathlib's sense. In its place the module proves the exact two-fold count: for $z \in$ `goodSet` the sets $\{\gamma : \gamma \cdot z \in \mathcal{D}\}$ and $\{\gamma : z \in \gamma \cdot \mathcal{D}\}$ are pairs $\{\delta, -\delta\}$, so $\sum_{\gamma} \mathbf{1}_{\gamma \cdot \mathcal{D}}(z) = 2$ almost everywhere. Combining this with invariance of the measure under $\gamma$ gives the unfolding identities $\sum_{\gamma} \int_{\mathcal{D}} F(\gamma w) = \int_{\mathcal{D}} \sum_{\gamma} F(\gamma w) = 2 \int_{\mathbb{H}} F$ for measurable $F : \mathbb{H} \to [0,\infty]$. Specialising $F$ to the indicator of $\mathcal{D}^{o}$ yields the value $2 \cdot \pi/3$, together with the observations that this differs from $\pi/3$ and is neither zero nor infinite.
--
--   **Relation to Mathlib.** The domains $\mathcal{D}$, $\mathcal{D}^{o}$ and the rigidity statements about elements fixing points of $\mathcal{D}^{o}$ are Mathlib's; `goodSet` and the factor-two unfolding identities are the project's own, and are stated precisely because Mathlib's `MeasureTheory.IsFundamentalDomain` fails for $\mathcal{D}$ under the full $SL(2,\mathbb{Z})$-action (the failure being proved here).
--
--   **Where it is used.** These identities belong to the measure-theoretic foundations for automorphic forms: they relate integrals over $\mathcal{D}$ to integrals over $\mathbb{H}$ with an explicit factor $2$ coming from the centre $\pm 1$, and sit alongside the exact volume $\pi/3$ of $\mathcal{D}$ and the finite-volume fundamental sets for $\Gamma_0(N)$ that carry the $L^2$ spaces of automorphic forms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AutomorphicForm_ModularFundamentalDomain.lean

import Mathlib
import Definitions.Def_AutomorphicForm_Gamma0ExactVolume
import Definitions.Def_AutomorphicForm_L2ProductionInstance

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory Set ModularGroup UpperHalfPlane
open scoped MatrixGroups Pointwise ENNReal Modular

namespace FLT.ModularFundamentalDomain

open FLT.HyperbolicMeasure FLT.Gamma0ExactVolume FLT.FundamentalDomainExactVolume
open FLT.L2ProductionInstance

theorem neg_one_smul_eq (z : ℍ) : (-1 : SL(2, ℤ)) • z = z := by
  rw [show (-1 : SL(2, ℤ)) = -(1 : SL(2, ℤ)) from rfl, SL_neg_smul, one_smul]

theorem neg_one_smul_set_eq (s : Set ℍ) : (-1 : SL(2, ℤ)) • s = s := by
  ext z
  simp only [Set.mem_smul_set]
  constructor
  · rintro ⟨w, hw, rfl⟩; rwa [neg_one_smul_eq]
  · exact fun hz => ⟨z, hz, neg_one_smul_eq z⟩

theorem one_ne_neg_one : (1 : SL(2, ℤ)) ≠ -1 := by
  intro h
  have h00 := congrArg (fun A : SL(2, ℤ) => (A : Matrix (Fin 2) (Fin 2) ℤ) 0 0) h
  simp at h00

theorem inv_neg_eq (γ : SL(2, ℤ)) : (-γ)⁻¹ = -γ⁻¹ :=
  (eq_inv_of_mul_eq_one_left (by rw [neg_mul_neg, inv_mul_cancel])).symm

theorem inv_neg_one : (-1 : SL(2, ℤ))⁻¹ = -1 := by
  rw [inv_neg_eq, inv_one]

theorem ne_neg_self (γ : SL(2, ℤ)) : γ ≠ -γ := by
  intro h
  apply one_ne_neg_one
  calc (1 : SL(2, ℤ)) = γ⁻¹ * γ := (inv_mul_cancel γ).symm
    _ = γ⁻¹ * (-γ) := by rw [← h]
    _ = -(γ⁻¹ * γ) := by rw [mul_neg]
    _ = -1 := by rw [inv_mul_cancel]

theorem smul_fd_inter_fd_subset {γ : SL(2, ℤ)} (h1 : γ ≠ 1) (h2 : γ ≠ -1) :
    γ • (𝒟 : Set ℍ) ∩ 𝒟 ⊆ (𝒟 : Set ℍ) \ 𝒟ᵒ := by
  rintro z ⟨hzγ, hz⟩
  refine ⟨hz, fun hzo => ?_⟩
  rw [Set.mem_smul_set_iff_inv_smul_mem] at hzγ
  rcases ModularGroup.eq_one_or_neg_one_of_mem_fdo_mem_fd hzo hzγ with h | h
  · exact h1 (by rw [← inv_inv γ, h, inv_one])
  · exact h2 (by rw [← inv_inv γ, h, inv_neg_one])

theorem volume_smul_fd_inter_fd {γ : SL(2, ℤ)} (h1 : γ ≠ 1) (h2 : γ ≠ -1) :
    volume (γ • (𝒟 : Set ℍ) ∩ 𝒟) = 0 :=
  measure_mono_null (smul_fd_inter_fd_subset h1 h2) volume_fd_diff_fdo

theorem gate_not_isFundamentalDomain_sl2z :
    ¬ MeasureTheory.IsFundamentalDomain SL(2, ℤ) (𝒟 : Set ℍ) volume := by
  intro h
  have hae : MeasureTheory.AEDisjoint volume
      ((1 : SL(2, ℤ)) • (𝒟 : Set ℍ)) ((-1 : SL(2, ℤ)) • (𝒟 : Set ℍ)) :=
    h.aedisjoint one_ne_neg_one
  rw [MeasureTheory.AEDisjoint, one_smul, neg_one_smul_set_eq, Set.inter_self] at hae
  exact FLT.FundamentalDomainExactVolume.gate_volume_ne_zero hae

def goodSet : Set ℍ := {z | ∃ γ : SL(2, ℤ), γ • z ∈ (𝒟ᵒ : Set ℍ)}

theorem volume_compl_goodSet : volume (goodSetᶜ : Set ℍ) = 0 := by
  have hsub : (goodSetᶜ : Set ℍ) ⊆ ⋃ γ : SL(2, ℤ), γ • ((𝒟 : Set ℍ) \ 𝒟ᵒ) := by
    intro z hz
    simp only [Set.mem_compl_iff, goodSet, Set.mem_setOf_eq, not_exists] at hz
    obtain ⟨g, hg⟩ := ModularGroup.exists_smul_mem_fd z
    refine Set.mem_iUnion.mpr ⟨g⁻¹, ?_⟩
    rw [Set.mem_smul_set_iff_inv_smul_mem, inv_inv]
    exact ⟨hg, hz g⟩
  refine measure_mono_null hsub (measure_iUnion_null fun γ => ?_)
  rw [FLT.HyperbolicMeasure.volume_smul_sl2z]
  exact volume_fd_diff_fdo

theorem setOf_smul_mem_fd_eq_pair {z : ℍ} (hz : z ∈ goodSet) :
    ∃ δ : SL(2, ℤ), {γ : SL(2, ℤ) | γ • z ∈ (𝒟 : Set ℍ)} = {δ, -δ} := by
  obtain ⟨δ, hδ⟩ := hz
  refine ⟨δ, Set.Subset.antisymm ?_ ?_⟩
  · intro γ hγ
    have key : (γ * δ⁻¹) • (δ • z) ∈ (𝒟 : Set ℍ) := by
      rw [smul_smul, mul_assoc, inv_mul_cancel, mul_one]
      exact hγ
    rcases ModularGroup.eq_one_or_neg_one_of_mem_fdo_mem_fd hδ key with h | h
    · exact Or.inl (mul_inv_eq_one.mp h)
    · refine Or.inr ?_
      have hγδ : γ = -1 * δ := by
        rw [← h, mul_assoc, inv_mul_cancel, mul_one]
      rw [Set.mem_singleton_iff, hγδ, neg_one_mul]
  · rintro γ hγ
    rcases Set.mem_insert_iff.mp hγ with rfl | hγ
    · exact ModularGroup.fdo_subset_fd hδ
    · rw [Set.mem_singleton_iff] at hγ
      subst hγ
      show (-δ) • z ∈ (𝒟 : Set ℍ)
      rw [SL_neg_smul δ z]
      exact ModularGroup.fdo_subset_fd hδ

theorem setOf_mem_smul_fd_eq_pair {z : ℍ} (hz : z ∈ goodSet) :
    ∃ δ : SL(2, ℤ), {γ : SL(2, ℤ) | z ∈ γ • (𝒟 : Set ℍ)} = {δ, -δ} := by
  obtain ⟨ε, hε⟩ := setOf_smul_mem_fd_eq_pair hz
  refine ⟨ε⁻¹, ?_⟩
  ext γ
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  rw [Set.mem_smul_set_iff_inv_smul_mem]
  have hmem : γ⁻¹ • z ∈ (𝒟 : Set ℍ) ↔ γ⁻¹ ∈ ({ε, -ε} : Set SL(2, ℤ)) := by
    rw [← hε]; rfl
  rw [hmem]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro (h | h)
    · exact Or.inl (by rw [← inv_inv γ, h])
    · exact Or.inr (by rw [← inv_inv γ, h, inv_neg_eq])
  · rintro (rfl | rfl)
    · exact Or.inl (by rw [inv_inv])
    · exact Or.inr (by rw [inv_neg_eq, inv_inv])

theorem tsum_indicator_smul_fd {z : ℍ} (hz : z ∈ goodSet) :
    ∑' γ : SL(2, ℤ), (γ • (𝒟 : Set ℍ)).indicator (fun _ => (1 : ℝ≥0∞)) z = 2 := by
  obtain ⟨δ, hδ⟩ := setOf_mem_smul_fd_eq_pair hz
  have hpair : ∀ γ : SL(2, ℤ), z ∈ γ • (𝒟 : Set ℍ) ↔ (γ = δ ∨ γ = -δ) := by
    intro γ
    constructor
    · intro h
      have : γ ∈ ({δ, -δ} : Set SL(2, ℤ)) := hδ ▸ h
      simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using this
    · intro h
      have : γ ∈ ({δ, -δ} : Set SL(2, ℤ)) := by
        simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using h
      rw [← hδ] at this
      exact this
  have hsupp : ∀ γ : SL(2, ℤ), γ ∉ ({δ, -δ} : Finset SL(2, ℤ)) →
      (γ • (𝒟 : Set ℍ)).indicator (fun _ => (1 : ℝ≥0∞)) z = 0 := by
    intro γ hγ
    rw [Set.indicator_apply_eq_zero]
    intro hmem
    exact absurd (Finset.mem_insert.mpr (((hpair γ).mp hmem).imp id Finset.mem_singleton.mpr))
      hγ
  rw [tsum_eq_sum hsupp, Finset.sum_pair (ne_neg_self δ),
    Set.indicator_of_mem ((hpair δ).mpr (Or.inl rfl)),
    Set.indicator_of_mem ((hpair (-δ)).mpr (Or.inr rfl))]
  exact one_add_one_eq_two

theorem setLIntegral_smul_fd (γ : SL(2, ℤ)) (F : ℍ → ℝ≥0∞) :
    ∫⁻ w in (𝒟 : Set ℍ), F (γ • w) ∂volume = ∫⁻ u in γ • (𝒟 : Set ℍ), F u ∂volume := by
  have hemb : MeasurableEmbedding (fun w : ℍ => γ • w) :=
    (Homeomorph.smul γ (α := ℍ)).measurableEmbedding
  have hmp : MeasurePreserving (fun w : ℍ => γ • w) volume volume :=
    ⟨hemb.measurable, by
      ext s hs
      rw [Measure.map_apply hemb.measurable hs, Set.preimage_smul,
        FLT.HyperbolicMeasure.volume_smul_sl2z]⟩
  rw [hmp.setLIntegral_comp_emb hemb F (𝒟 : Set ℍ)]
  rfl

theorem tsum_setLIntegral_fd_smul (F : ℍ → ℝ≥0∞) (hF : Measurable F) :
    ∑' γ : SL(2, ℤ), ∫⁻ w in (𝒟 : Set ℍ), F (γ • w) ∂volume =
      2 * ∫⁻ z, F z ∂volume := by
  calc ∑' γ : SL(2, ℤ), ∫⁻ w in (𝒟 : Set ℍ), F (γ • w) ∂volume
      = ∑' γ : SL(2, ℤ), ∫⁻ u in γ • (𝒟 : Set ℍ), F u ∂volume := by
        exact tsum_congr fun γ => setLIntegral_smul_fd γ F
    _ = ∑' γ : SL(2, ℤ), ∫⁻ u, (γ • (𝒟 : Set ℍ)).indicator F u ∂volume := by
        exact tsum_congr fun γ => (lintegral_indicator (measurableSet_smul_fd γ) F).symm
    _ = ∫⁻ u, ∑' γ : SL(2, ℤ), (γ • (𝒟 : Set ℍ)).indicator F u ∂volume := by
        exact (lintegral_tsum fun γ =>
          (hF.indicator (measurableSet_smul_fd γ)).aemeasurable).symm
    _ = ∫⁻ u, 2 * F u ∂volume := by
        refine lintegral_congr_ae ?_
        filter_upwards [measure_eq_zero_iff_ae_notMem.mp volume_compl_goodSet] with z hzc
        have hz : z ∈ goodSet := by simpa using hzc
        calc ∑' γ : SL(2, ℤ), (γ • (𝒟 : Set ℍ)).indicator F z
            = ∑' γ : SL(2, ℤ), (γ • (𝒟 : Set ℍ)).indicator (fun _ => (1 : ℝ≥0∞)) z * F z := by
              refine tsum_congr fun γ => ?_
              by_cases h : z ∈ γ • (𝒟 : Set ℍ) <;>
                simp [Set.indicator_of_mem, Set.indicator_of_notMem, h]
          _ = (∑' γ : SL(2, ℤ), (γ • (𝒟 : Set ℍ)).indicator (fun _ => (1 : ℝ≥0∞)) z) * F z :=
              ENNReal.tsum_mul_right
          _ = 2 * F z := by rw [tsum_indicator_smul_fd hz]
    _ = 2 * ∫⁻ z, F z ∂volume := lintegral_const_mul 2 hF

theorem setLIntegral_fd_tsum_smul (F : ℍ → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ w in (𝒟 : Set ℍ), (∑' γ : SL(2, ℤ), F (γ • w)) ∂volume =
      2 * ∫⁻ z, F z ∂volume := by
  rw [← tsum_setLIntegral_fd_smul F hF]
  exact lintegral_tsum fun γ =>
    (hF.comp (Homeomorph.smul γ (α := ℍ)).measurable).aemeasurable.restrict

theorem gate_two_routes :
    ∑' γ : SL(2, ℤ), ∫⁻ w in (𝒟 : Set ℍ),
        (𝒟ᵒ : Set ℍ).indicator (fun _ => (1 : ℝ≥0∞)) (γ • w) ∂volume =
      2 * ENNReal.ofReal (Real.pi / 3) := by
  rw [tsum_setLIntegral_fd_smul _ (measurable_const.indicator ModularGroup.isOpen_fdo.measurableSet),
    lintegral_indicator ModularGroup.isOpen_fdo.measurableSet, setLIntegral_one,
    volume_fdo_eq_volume_fd, volume_fd_eq]

theorem gate_factor_two_load_bearing :
    (2 : ℝ≥0∞) * ENNReal.ofReal (Real.pi / 3) ≠ ENNReal.ofReal (Real.pi / 3) := by
  intro h
  have hne : ENNReal.ofReal (Real.pi / 3) ≠ 0 := by
    rw [← volume_fd_eq]
    exact FLT.FundamentalDomainExactVolume.gate_volume_ne_zero
  have hlt : ENNReal.ofReal (Real.pi / 3) ≠ ⊤ := ENNReal.ofReal_ne_top
  have := (ENNReal.mul_eq_right hne hlt).mp h
  norm_num at this

theorem gate_two_routes_ne_zero_ne_top :
    (2 : ℝ≥0∞) * ENNReal.ofReal (Real.pi / 3) ≠ 0 ∧
      (2 : ℝ≥0∞) * ENNReal.ofReal (Real.pi / 3) ≠ ⊤ := by
  constructor
  · refine mul_ne_zero (by norm_num) ?_
    rw [← volume_fd_eq]
    exact FLT.FundamentalDomainExactVolume.gate_volume_ne_zero
  · exact ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top

end FLT.ModularFundamentalDomain


