-- Prove2me | Definitions.Def_AutomorphicForm_Gamma0ExactVolume
-- name    : AutomorphicForm_Gamma0ExactVolume
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.014713+00:00
-- url     : https://prove2.me/theorems/4397e9be-4e49-511c-acba-92f90b8eed9b
-- title:
--   Exact hyperbolic volume of Gamma_0(N) fundamental sets
-- statement:
--   This module computes the hyperbolic volume of the sets `gammaFundamentalSet Γ = ⋃_{q ∈ SL(2,ℤ)/Γ} (Quotient.out q)⁻¹ • 𝒟`, unions of translates of Mathlib's closed fundamental domain $\mathcal{D} = \{|z| \ge 1,\ |\operatorname{Re} z| \le 1/2\}$ indexed by coset representatives chosen by `Quotient.out`, with respect to the measure $y^{-2}\,dx\,dy$ on $\mathbb{H}$. The preliminary lemmas record that a subset of $\mathbb{H}$ whose image in $\mathbb{C}$ is Lebesgue-null has volume zero, that a vertical line $\{\operatorname{Re} z = c\}$ and the unit circle $\{N(z) = 1\}$ are null in $\mathbb{C}$, hence that $\mathcal{D} \setminus \mathcal{D}^{\circ}$ is null and $\operatorname{vol}(\mathcal{D}^{\circ}) = \operatorname{vol}(\mathcal{D})$. Subadditivity together with $\mathrm{SL}_2(\mathbb{Z})$-invariance of the measure gives the inequality $\operatorname{vol}(\mathtt{gammaFundamentalSet}\ \Gamma) \le \#(\mathrm{SL}_2(\mathbb{Z})/\Gamma)\cdot\operatorname{vol}(\mathcal{D})$ for $\Gamma$ of finite index; conversely, if $-1 \in \Gamma$ the translates $(\mathtt{out}\,q)^{-1}\cdot\mathcal{D}^{\circ}$ are pairwise disjoint, giving the reverse inequality and hence the equality $\operatorname{vol} = \#(\mathrm{SL}_2(\mathbb{Z})/\Gamma)\cdot\operatorname{vol}(\mathcal{D})$, which combined with $\operatorname{vol}(\mathcal{D}) = \pi/3$ becomes $\#(\mathrm{SL}_2(\mathbb{Z})/\Gamma)\cdot\pi/3$ in $[0,\infty]$. Since $-1 \in \Gamma_0(N)$ for every $N$, this applies to $\Gamma_0(N)$ with $N \neq 0$, the index being finite. The remaining statements are consistency checks: the case $\Gamma = \top$ gives $\pi/3$ (proved twice, once through the index formula and once directly); $2\cdot\operatorname{vol}(\mathcal{D}) \neq 1\cdot\operatorname{vol}(\mathcal{D})$, so the index factor is not vacuous; the complement of $\mathcal{D}^{\circ}$ in $\mathbb{H}$ has infinite volume; and the volume for $\Gamma_0(N)$ is finite, non-zero and not $\infty$.
--
--   **Relation to Mathlib.** Mathlib provides the upper half-plane with its hyperbolic measure and the invariance of that measure under $\mathrm{GL}_2(\mathbb{R})$, the closed and open fundamental domains $\mathcal{D}$, $\mathcal{D}^{\circ}$ for $\mathrm{SL}_2(\mathbb{Z})$ and the criterion that two points of $\mathcal{D}^{\circ}$ in the same orbit differ by $\pm 1$; the exact value $\pi/3$ and the index formula for the volume of a union of coset translates are the project's own.
--
--   **Where it is used.** The exact covolume is the normalising constant on the spectral side of the automorphic theory for $\Gamma_0(N)$; the value $\pi/3$ matches the residue $3/\pi$ at $s=1$ of the Eisenstein scattering factor built from the completed Riemann zeta function in the imported module.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AutomorphicForm_Gamma0ExactVolume.lean

import Mathlib
import Definitions.Def_AutomorphicForm_FundamentalDomainExactVolume
import Definitions.Def_AutomorphicForm_Gamma0FundamentalSet

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory Set ModularGroup UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups Pointwise ENNReal Modular

namespace FLT.Gamma0ExactVolume

open FLT.Gamma0FundamentalSet FLT.HyperbolicMeasure FLT.FundamentalDomainExactVolume
  FLT.FundamentalDomainVolume

theorem volume_eq_zero_of_image_null {s : Set ℍ}
    (h : volume ((↑) '' s : Set ℂ) = 0) : volume s = 0 := by
  rw [UpperHalfPlane.volume_eq_lintegral]
  exact setLIntegral_measure_zero _ _ h

theorem volume_re_eq_zero (c : ℝ) : volume {z : ℂ | z.re = c} = 0 := by
  have hset : {z : ℂ | z.re = c} =
      Complex.measurableEquivRealProd ⁻¹' ({c} ×ˢ (Set.univ : Set ℝ)) := by
    ext z
    simp [Set.mem_prod]
  rw [hset, Complex.volume_preserving_equiv_real_prod.measure_preimage
    (((measurableSet_singleton c).prod MeasurableSet.univ).nullMeasurableSet)]
  rw [show (volume : Measure (ℝ × ℝ)) = (volume : Measure ℝ).prod volume from rfl,
    Measure.prod_prod, Real.volume_singleton, zero_mul]

theorem volume_normSq_eq_one : volume {z : ℂ | Complex.normSq z = 1} = 0 := by
  have hsub : {z : ℂ | Complex.normSq z = 1} ⊆ Metric.sphere (0 : ℂ) 1 := by
    intro z hz
    simp only [Set.mem_setOf_eq] at hz
    simp only [Metric.mem_sphere, dist_zero_right]
    nlinarith [Complex.normSq_eq_norm_sq z, norm_nonneg z]
  exact measure_mono_null hsub (Measure.addHaar_sphere volume 0 1)

theorem volume_fd_diff_fdo : volume (𝒟 \ 𝒟ᵒ) = 0 := by
  apply volume_eq_zero_of_image_null
  apply measure_mono_null (t := {z : ℂ | Complex.normSq z = 1} ∪
    ({z : ℂ | z.re = 1 / 2} ∪ {z : ℂ | z.re = -(1 / 2)}))
  · rintro w ⟨z, ⟨⟨hn, hr⟩, hz⟩, rfl⟩
    simp only [ModularGroup.fdo, Set.mem_setOf_eq, not_and_or, not_lt] at hz
    rcases hz with hz | hz
    · exact Or.inl (le_antisymm hz hn)
    · right
      have : |z.re| = 1 / 2 := le_antisymm hr hz
      rcases abs_eq (by norm_num : (0 : ℝ) ≤ 1 / 2) |>.mp this with h | h
      · exact Or.inl (by simp only [Set.mem_setOf_eq, UpperHalfPlane.coe_re]; exact h)
      · exact Or.inr (by simp only [Set.mem_setOf_eq, UpperHalfPlane.coe_re]; exact h)
  · refine measure_union_null volume_normSq_eq_one (measure_union_null ?_ ?_) <;>
      exact volume_re_eq_zero _

theorem volume_fdo_eq_volume_fd : volume 𝒟ᵒ = volume 𝒟 := by
  refine le_antisymm (measure_mono ModularGroup.fdo_subset_fd) ?_
  calc volume 𝒟 = volume (𝒟ᵒ ∪ 𝒟 \ 𝒟ᵒ) := by
        rw [Set.union_diff_cancel ModularGroup.fdo_subset_fd]
    _ ≤ volume 𝒟ᵒ + volume (𝒟 \ 𝒟ᵒ) := measure_union_le _ _
    _ = volume 𝒟ᵒ := by rw [volume_fd_diff_fdo, add_zero]

theorem volume_gammaFundamentalSet_le (Γ : Subgroup SL(2, ℤ)) [Finite (SL(2, ℤ) ⧸ Γ)] :
    volume (gammaFundamentalSet Γ) ≤ Nat.card (SL(2, ℤ) ⧸ Γ) • volume 𝒟 := by
  haveI : Fintype (SL(2, ℤ) ⧸ Γ) := Fintype.ofFinite _
  calc volume (gammaFundamentalSet Γ)
      = volume (⋃ q : SL(2, ℤ) ⧸ Γ, (Quotient.out q)⁻¹ • 𝒟) := rfl
    _ ≤ ∑' q : SL(2, ℤ) ⧸ Γ, volume ((Quotient.out q)⁻¹ • 𝒟) := measure_iUnion_le _
    _ = Nat.card (SL(2, ℤ) ⧸ Γ) • volume 𝒟 := by
        simp_rw [FLT.HyperbolicMeasure.volume_smul_sl2z]
        rw [tsum_eq_sum (s := Finset.univ) (fun i hi => absurd (Finset.mem_univ i) hi),
          Finset.sum_const, Finset.card_univ, Nat.card_eq_fintype_card]

theorem pairwise_disjoint_inv_smul_fdo (Γ : Subgroup SL(2, ℤ)) (hΓ : -1 ∈ Γ) :
    Pairwise (Function.onFun Disjoint
      fun q : SL(2, ℤ) ⧸ Γ => (Quotient.out q)⁻¹ • (𝒟ᵒ : Set ℍ)) := by
  intro q q' hqq'
  rw [Function.onFun, Set.disjoint_left]
  rintro z hz hz'
  rw [Set.mem_inv_smul_set_iff] at hz hz'
  have key : (Quotient.out q' * (Quotient.out q)⁻¹) • (Quotient.out q • z) ∈ 𝒟ᵒ := by
    rwa [mul_smul, inv_smul_smul]
  rcases ModularGroup.eq_one_or_neg_one_of_mem_fdo_mem_fdo hz key with h | h
  ·
    exact hqq' (by rw [← Quotient.out_eq q, ← Quotient.out_eq q', mul_inv_eq_one.mp h])
  ·
    apply hqq'
    rw [← Quotient.out_eq q, ← Quotient.out_eq q']
    refine Quotient.sound (QuotientGroup.leftRel_apply.mpr ?_)
    rw [mul_inv_eq_iff_eq_mul.mp h, neg_one_mul, mul_neg, inv_mul_cancel]
    exact hΓ

theorem nsmul_volume_fd_le (Γ : Subgroup SL(2, ℤ)) (hΓ : -1 ∈ Γ) [Finite (SL(2, ℤ) ⧸ Γ)] :
    Nat.card (SL(2, ℤ) ⧸ Γ) • volume 𝒟 ≤ volume (gammaFundamentalSet Γ) := by
  haveI : Fintype (SL(2, ℤ) ⧸ Γ) := Fintype.ofFinite _
  have hsub : (⋃ q : SL(2, ℤ) ⧸ Γ, (Quotient.out q)⁻¹ • (𝒟ᵒ : Set ℍ)) ⊆
      gammaFundamentalSet Γ :=
    Set.iUnion_mono fun q => Set.smul_set_mono ModularGroup.fdo_subset_fd
  calc Nat.card (SL(2, ℤ) ⧸ Γ) • volume 𝒟
      = ∑' q : SL(2, ℤ) ⧸ Γ, volume ((Quotient.out q)⁻¹ • (𝒟ᵒ : Set ℍ)) := by
        simp_rw [FLT.HyperbolicMeasure.volume_smul_sl2z, volume_fdo_eq_volume_fd]
        rw [tsum_eq_sum (s := Finset.univ) (fun i hi => absurd (Finset.mem_univ i) hi),
          Finset.sum_const, Finset.card_univ, Nat.card_eq_fintype_card]
    _ = volume (⋃ q : SL(2, ℤ) ⧸ Γ, (Quotient.out q)⁻¹ • (𝒟ᵒ : Set ℍ)) :=
        (measure_iUnion (pairwise_disjoint_inv_smul_fdo Γ hΓ)
          (fun _ => (ModularGroup.isOpen_fdo.smul _).measurableSet)).symm
    _ ≤ volume (gammaFundamentalSet Γ) := measure_mono hsub

theorem volume_gammaFundamentalSet_eq (Γ : Subgroup SL(2, ℤ)) (hΓ : -1 ∈ Γ)
    [Finite (SL(2, ℤ) ⧸ Γ)] :
    volume (gammaFundamentalSet Γ) = Nat.card (SL(2, ℤ) ⧸ Γ) • volume 𝒟 :=
  le_antisymm (volume_gammaFundamentalSet_le Γ) (nsmul_volume_fd_le Γ hΓ)

theorem volume_gammaFundamentalSet_eq_ofReal (Γ : Subgroup SL(2, ℤ)) (hΓ : -1 ∈ Γ)
    [Finite (SL(2, ℤ) ⧸ Γ)] :
    volume (gammaFundamentalSet Γ) =
      Nat.card (SL(2, ℤ) ⧸ Γ) • ENNReal.ofReal (Real.pi / 3) := by
  rw [volume_gammaFundamentalSet_eq Γ hΓ, FLT.FundamentalDomainExactVolume.volume_fd_eq]

theorem neg_one_mem_Gamma0_all (N : ℕ) : (-1 : SL(2, ℤ)) ∈ Gamma0 N := by
  rw [Gamma0_mem]
  simp

theorem volume_gamma0_eq (N : ℕ) [NeZero N] :
    haveI : Finite (SL(2, ℤ) ⧸ Gamma0 N) := FLT.SiegelSetCover.finite_quotient_gamma0 N
    volume (gammaFundamentalSet (Gamma0 N)) =
      Nat.card (SL(2, ℤ) ⧸ Gamma0 N) • ENNReal.ofReal (Real.pi / 3) := by
  haveI : Finite (SL(2, ℤ) ⧸ Gamma0 N) := FLT.SiegelSetCover.finite_quotient_gamma0 N
  exact volume_gammaFundamentalSet_eq_ofReal (Gamma0 N) (neg_one_mem_Gamma0_all N)

theorem gate_top_two_routes :
    volume (gammaFundamentalSet (⊤ : Subgroup SL(2, ℤ))) = ENNReal.ofReal (Real.pi / 3) := by
  haveI : Subsingleton (SL(2, ℤ) ⧸ (⊤ : Subgroup SL(2, ℤ))) :=
    QuotientGroup.subsingleton_quotient_top
  haveI : Finite (SL(2, ℤ) ⧸ (⊤ : Subgroup SL(2, ℤ))) := Finite.of_subsingleton
  rw [volume_gammaFundamentalSet_eq_ofReal ⊤ (Subgroup.mem_top _),
    Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, inferInstance⟩, one_smul]

theorem gate_top_committed_route :
    volume (gammaFundamentalSet (⊤ : Subgroup SL(2, ℤ))) = ENNReal.ofReal (Real.pi / 3) := by
  rw [FLT.Gamma0FundamentalSet.gate_volume_top_eq]
  exact FLT.FundamentalDomainExactVolume.volume_fd_eq

theorem gate_count_load_bearing : (2 : ℕ) • volume 𝒟 ≠ (1 : ℕ) • volume 𝒟 := by
  rw [one_smul, two_nsmul]
  intro h
  exact FLT.FundamentalDomainVolume.volume_fd_pos.ne'
    ((ENNReal.add_right_inj FLT.FundamentalDomainVolume.volume_fd_lt_top.ne).mp
      (h.trans (add_zero _).symm))

theorem gate_compl_fdo_volume_top : volume ((Set.univ : Set ℍ) \ 𝒟ᵒ) = ⊤ := by
  by_contra h
  have hlt : volume ((Set.univ : Set ℍ) \ 𝒟ᵒ) < ⊤ := lt_top_iff_ne_top.mpr h
  have : volume (Set.univ : Set ℍ) < ⊤ := by
    calc volume (Set.univ : Set ℍ) = volume ((Set.univ \ 𝒟ᵒ) ∪ (𝒟ᵒ : Set ℍ)) := by
          rw [Set.diff_union_of_subset (Set.subset_univ _)]
      _ ≤ volume ((Set.univ : Set ℍ) \ 𝒟ᵒ) + volume (𝒟ᵒ : Set ℍ) := measure_union_le _ _
      _ < ⊤ := ENNReal.add_lt_top.mpr ⟨hlt, lt_of_le_of_lt
          (measure_mono ModularGroup.fdo_subset_fd)
          FLT.FundamentalDomainVolume.volume_fd_lt_top⟩
  exact absurd FLT.HyperbolicMeasure.volume_univ_eq_top this.ne

theorem gate_no_regression_lt_top (N : ℕ) [NeZero N] :
    volume (gammaFundamentalSet (Gamma0 N)) < ⊤ := by
  haveI : Finite (SL(2, ℤ) ⧸ Gamma0 N) := FLT.SiegelSetCover.finite_quotient_gamma0 N
  rw [volume_gamma0_eq N, nsmul_eq_mul]
  exact ENNReal.mul_lt_top (ENNReal.natCast_lt_top _) ENNReal.ofReal_lt_top

theorem gate_rhs_ne_zero_ne_top (N : ℕ) [NeZero N] :
    haveI : Finite (SL(2, ℤ) ⧸ Gamma0 N) := FLT.SiegelSetCover.finite_quotient_gamma0 N
    (Nat.card (SL(2, ℤ) ⧸ Gamma0 N) • ENNReal.ofReal (Real.pi / 3) ≠ 0) ∧
      (Nat.card (SL(2, ℤ) ⧸ Gamma0 N) • ENNReal.ofReal (Real.pi / 3) ≠ ⊤) := by
  haveI : Finite (SL(2, ℤ) ⧸ Gamma0 N) := FLT.SiegelSetCover.finite_quotient_gamma0 N
  constructor
  · rw [← volume_gamma0_eq N]
    exact (FLT.Gamma0FundamentalSet.volume_gammaFundamentalSet_pos (Gamma0 N)).ne'
  · rw [← volume_gamma0_eq N]
    exact (gate_no_regression_lt_top N).ne

end FLT.Gamma0ExactVolume


