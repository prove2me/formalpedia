-- Prove2me | Definitions.Def_CuspForm_PeterssonCoset
-- name    : CuspForm_PeterssonCoset
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.503845+00:00
-- url     : https://prove2.me/theorems/c355f316-5626-571f-9491-aa94241d32bd
-- title:
--   Petersson pairing by coset sums over a fundamental domain
-- statement:
--   Throughout, $\mathcal D$ denotes Mathlib's closed fundamental domain $\mathcal D$ for the modular group acting on the upper half-plane $\mathfrak H$, equipped with the hyperbolic measure, and for a coset $q \in \mathrm{SL}_2(\mathbb Z)/\Lambda$ the chosen representative is $q$`.out`. The module introduces, for a subgroup $\Lambda \le \mathrm{SL}_2(\mathbb Z)$ of finite index, an integer $k$ and functions on $\mathfrak H$: the real density $\mathrm{dens}\,k\,H\,(x) = \|H(x)\|^2 (\operatorname{Im} x)^k$, which is exactly the diagonal value of Mathlib's `UpperHalfPlane.petersson`; the predicate `Nice Λ k H`, a structure with three fields asserting that $H$ is continuous, that $\mathrm{dens}\,k\,H$ is bounded on all of $\mathfrak H$, and that $H \mid_k h = H$ for every $h \in \Lambda$ (the slash action being taken through the image of $h$ in $\mathrm{GL}_2(\mathbb R)$); the twisted coset sum $\mathrm{cosum}\,\Lambda\,g\,\Phi\,(x) = \sum_{q} \Phi(g\,q.\mathrm{out}^{-1}x)$ for $g \in \mathrm{GL}_2(\mathbb R)$; and the pairing $\mathrm{pair}\,\Lambda\,k\,F\,G = \int_{\mathcal D} \mathrm{cosum}\,\Lambda\,1\,(\mathrm{petersson}\,k\,F\,G)$, i.e. the unfolded Petersson integral over $\Lambda\backslash\mathfrak H$ with no division by the index.
--
--   Auxiliary constructions support the unfolding: the bijection $\mathrm{SL}_2(\mathbb Z) \simeq (\mathrm{SL}_2(\mathbb Z)/\Lambda) \times \Lambda$ sending $\sigma$ to its coset together with $q.\mathrm{out}^{-1}\sigma$; the weight function $\mathrm{wt}\,\Lambda\,(x) = \sum_q \mathbf 1_{\mathcal D}(q.\mathrm{out}\cdot x)$, whose $\Lambda$-orbit sum equals $2$ almost everywhere (the factor $2$ reflecting $\pm 1$); and, for $\Lambda \le \Gamma''$ with a family of representatives $r$, the bijection $(q,i) \mapsto q.\mathrm{out}\,(r\,i)^{-1}\Lambda$ between $(\mathrm{SL}_2(\mathbb Z)/\Gamma'') \times \iota$ and $\mathrm{SL}_2(\mathbb Z)/\Lambda$. The results established are: integrability of the coset sum for bounded continuous data; conjugate symmetry, conjugate-linearity in the first and linearity in the second variable, additivity over finite sums of `Nice` functions; $\mathrm{pair}\,\Lambda_1\,k\,(F\mid_k\beta)\,(G\mid_k\beta) = (\det\beta)^{k-2}\,\mathrm{pair}\,\Lambda\,k\,F\,G$ when $\det\beta > 0$ and a bijection $c : \Lambda_1 \simeq \Lambda$ satisfies $\beta h = c(h)\beta$; $\mathrm{pair}\,\Lambda = [\Gamma'' : \Lambda]\,\mathrm{pair}\,\Gamma''$ for $\Lambda \le \Gamma''$; positive definiteness, in the form that a `Nice` function with vanishing self-pairing is identically zero; and equality of the indices of two subgroups conjugate in the above sense.
--
--   **Relation to Mathlib.** Builds on Mathlib's upper half-plane with its hyperbolic measure, the fundamental domain $\mathcal D$, the slash action and `UpperHalfPlane.petersson`; the coset sum `cosum`, the pairing `pair` and the predicate `Nice` are the project's own, Mathlib having no Petersson inner product for an arbitrary finite-index subgroup of $\mathrm{SL}_2(\mathbb Z)$.
--
--   **Where it is used.** The pairing defined here is the Petersson product used for cusp forms on finite-index subgroups of $\mathrm{SL}_2(\mathbb Z)$; its conjugate symmetry, positive definiteness and behaviour under the slash action by matrices of positive determinant and under change of level are what is needed to compare forms of different levels and to study Hecke operators on them.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_CuspForm_PeterssonCoset.lean

import Mathlib
import Definitions.Def_AutomorphicForm_ModularFundamentalDomain

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open MeasureTheory UpperHalfPlane ModularForm Filter CongruenceSubgroup
open scoped MatrixGroups ModularForm ComplexConjugate Modular ENNReal Pointwise

namespace CuspForm.PeterssonCoset

@[simp] theorem mapGL_apply (g : SL(2, ℤ)) (i j : Fin 2) :
    (Matrix.SpecialLinearGroup.mapGL ℝ g : GL (Fin 2) ℝ) i j = ((g i j : ℤ) : ℝ) := by
  simp

theorem val_mapGL_eq (g : SL(2, ℤ)) :
    ((Matrix.SpecialLinearGroup.mapGL ℝ g : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
      = !![((g 0 0 : ℤ) : ℝ), ((g 0 1 : ℤ) : ℝ); ((g 1 0 : ℤ) : ℝ), ((g 1 1 : ℤ) : ℝ)] := by
  ext i j
  rw [mapGL_apply]
  fin_cases i <;> fin_cases j <;> rfl

theorem mapGL_injective : Function.Injective
    (fun s : SL(2, ℤ) => (Matrix.SpecialLinearGroup.mapGL ℝ s : GL (Fin 2) ℝ)) := by
  intro s t h
  apply Subtype.ext
  ext i j
  have := congrArg (fun g : GL (Fin 2) ℝ => (g : Matrix (Fin 2) (Fin 2) ℝ) i j) h
  simpa using this

theorem det_entries (γ : SL(2, ℤ)) : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
  have h := γ.det_coe
  rwa [Matrix.det_fin_two] at h

theorem hact (γ : SL(2, ℤ)) (x : ℍ) :
    γ • x = (Matrix.SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ) • x :=
  MulAction.compHom_smul_def _ γ x

theorem mp_smul_SL (γ : SL(2, ℤ)) : MeasurePreserving (fun x : ℍ => γ • x) volume volume := by
  have hemb : MeasurableEmbedding (fun w : ℍ => γ • w) :=
    (Homeomorph.smul γ (α := ℍ)).measurableEmbedding
  exact ⟨hemb.measurable, by
    ext s hs
    rw [Measure.map_apply hemb.measurable hs, Set.preimage_smul,
      FLT.HyperbolicMeasure.volume_smul_sl2z]⟩

theorem mp_smul_GL (g : GL (Fin 2) ℝ) : MeasurePreserving (fun x : ℍ => g • x) volume volume := by
  have hemb : MeasurableEmbedding (fun w : ℍ => g • w) :=
    (Homeomorph.smul g (α := ℍ)).measurableEmbedding
  exact ⟨hemb.measurable, by
    ext s hs
    rw [Measure.map_apply hemb.measurable hs, Set.preimage_smul,
      FLT.HyperbolicMeasure.volume_smul_gl]⟩

theorem measurable_smul_SL (γ : SL(2, ℤ)) : Measurable (fun x : ℍ => γ • x) :=
  (continuous_const_smul γ).measurable

theorem measurable_smul_GL (g : GL (Fin 2) ℝ) : Measurable (fun x : ℍ => g • x) :=
  (continuous_const_smul g).measurable

section weight

variable (Λ : Subgroup SL(2, ℤ))

def splitEquiv : SL(2, ℤ) ≃ (SL(2, ℤ) ⧸ Λ) × Λ where
  toFun σ := (QuotientGroup.mk σ, ⟨(QuotientGroup.mk σ : SL(2, ℤ) ⧸ Λ).out⁻¹ * σ, by
    rw [← QuotientGroup.eq]; exact QuotientGroup.out_eq' _⟩)
  invFun x := x.1.out * x.2
  left_inv σ := by simp
  right_inv := by
    rintro ⟨q, h⟩
    have hq : (QuotientGroup.mk (q.out * (h : SL(2, ℤ))) : SL(2, ℤ) ⧸ Λ) = q := by
      rw [QuotientGroup.mk_mul_of_mem _ h.2, QuotientGroup.out_eq']
    refine Prod.ext hq (Subtype.ext ?_)
    simp only [hq]
    rw [inv_mul_cancel_left]

theorem tsum_SL_eq (F : SL(2, ℤ) → ℝ≥0∞) :
    ∑' σ : SL(2, ℤ), F σ = ∑' q : SL(2, ℤ) ⧸ Λ, ∑' h : Λ, F (q.out * (h : SL(2, ℤ))) := by
  rw [← (splitEquiv Λ).symm.tsum_eq, ENNReal.tsum_prod']
  rfl

theorem tsum_SL_inv (F : SL(2, ℤ) → ℝ≥0∞) : ∑' σ : SL(2, ℤ), F σ = ∑' σ : SL(2, ℤ), F σ⁻¹ :=
  ((Equiv.inv SL(2, ℤ)).tsum_eq F).symm

theorem tsum_Λ_inv (F : Λ → ℝ≥0∞) : ∑' h : Λ, F h = ∑' h : Λ, F h⁻¹ :=
  ((Equiv.inv Λ).tsum_eq F).symm

variable [Fintype (SL(2, ℤ) ⧸ Λ)]

def wt (x : ℍ) : ℝ≥0∞ :=
  ∑ q : SL(2, ℤ) ⧸ Λ, (𝒟 : Set ℍ).indicator (fun _ => (1 : ℝ≥0∞)) ((q.out : SL(2, ℤ)) • x)

theorem measurable_wt : Measurable (wt Λ) := by
  refine Finset.measurable_sum _ fun q _ => ?_
  exact (measurable_const.indicator ModularGroup.isClosed_fd.measurableSet).comp
    (measurable_smul_SL _)

theorem indicator_smul (σ : SL(2, ℤ)) (x : ℍ) :
    (𝒟 : Set ℍ).indicator (fun _ => (1 : ℝ≥0∞)) (σ • x)
      = (σ⁻¹ • (𝒟 : Set ℍ)).indicator (fun _ => (1 : ℝ≥0∞)) x := by
  by_cases h : σ • x ∈ (𝒟 : Set ℍ)
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem (Set.mem_inv_smul_set_iff.mpr h)]
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (fun h' => h (Set.mem_inv_smul_set_iff.mp h'))]

theorem tsum_wt_smul {x : ℍ} (hx : x ∈ FLT.ModularFundamentalDomain.goodSet) :
    ∑' h : Λ, wt Λ ((h : SL(2, ℤ)) • x) = 2 := by
  calc ∑' h : Λ, wt Λ ((h : SL(2, ℤ)) • x)
      = ∑' h : Λ, ∑' q : SL(2, ℤ) ⧸ Λ,
          (𝒟 : Set ℍ).indicator (fun _ => (1 : ℝ≥0∞)) ((q.out : SL(2, ℤ)) • (h : SL(2, ℤ)) • x) :=
        tsum_congr fun h => by rw [wt, tsum_fintype]
    _ = ∑' q : SL(2, ℤ) ⧸ Λ, ∑' h : Λ,
          (𝒟 : Set ℍ).indicator (fun _ => (1 : ℝ≥0∞)) ((q.out : SL(2, ℤ)) • (h : SL(2, ℤ)) • x) :=
        ENNReal.tsum_comm
    _ = ∑' q : SL(2, ℤ) ⧸ Λ, ∑' h : Λ,
          (𝒟 : Set ℍ).indicator (fun _ => (1 : ℝ≥0∞)) (((q.out : SL(2, ℤ)) * h) • x) :=
        tsum_congr fun q => tsum_congr fun h => by rw [mul_smul]
    _ = ∑' σ : SL(2, ℤ), (𝒟 : Set ℍ).indicator (fun _ => (1 : ℝ≥0∞)) (σ • x) :=
        (tsum_SL_eq Λ (fun σ => (𝒟 : Set ℍ).indicator (fun _ => (1 : ℝ≥0∞)) (σ • x))).symm
    _ = ∑' σ : SL(2, ℤ), (σ⁻¹ • (𝒟 : Set ℍ)).indicator (fun _ => (1 : ℝ≥0∞)) x :=
        tsum_congr fun σ => indicator_smul σ x
    _ = ∑' σ : SL(2, ℤ), (σ • (𝒟 : Set ℍ)).indicator (fun _ => (1 : ℝ≥0∞)) x := by
        rw [tsum_SL_inv (fun σ => (σ • (𝒟 : Set ℍ)).indicator (fun _ => (1 : ℝ≥0∞)) x)]
    _ = 2 := FLT.ModularFundamentalDomain.tsum_indicator_smul_fd hx

theorem ae_tsum_wt_smul : ∀ᵐ x : ℍ, ∑' h : Λ, wt Λ ((h : SL(2, ℤ)) • x) = 2 := by
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp FLT.ModularFundamentalDomain.volume_compl_goodSet]
    with x hx
  exact tsum_wt_smul Λ (by simpa using hx)

theorem tsum_G_eq (U w : ℍ → ℝ≥0∞) (hUinv : ∀ h ∈ Λ, ∀ x : ℍ, U (h • x) = U x) (x : ℍ)
    (hwt : ∀ q : SL(2, ℤ) ⧸ Λ, ∑' h : Λ, w ((h : SL(2, ℤ)) • (q.out⁻¹ : SL(2, ℤ)) • x) = 2) :
    ∑' σ : SL(2, ℤ), U (σ • x) * w (σ • x)
      = 2 * ∑ q : SL(2, ℤ) ⧸ Λ, U ((q.out⁻¹ : SL(2, ℤ)) • x) := by
  calc ∑' σ : SL(2, ℤ), U (σ • x) * w (σ • x)
      = ∑' σ : SL(2, ℤ), U (σ⁻¹ • x) * w (σ⁻¹ • x) :=
        tsum_SL_inv (fun σ => U (σ • x) * w (σ • x))
    _ = ∑' q : SL(2, ℤ) ⧸ Λ, ∑' h : Λ,
          U (((q.out : SL(2, ℤ)) * h)⁻¹ • x) * w (((q.out : SL(2, ℤ)) * h)⁻¹ • x) :=
        tsum_SL_eq Λ (fun σ => U (σ⁻¹ • x) * w (σ⁻¹ • x))
    _ = ∑' q : SL(2, ℤ) ⧸ Λ, ∑' h : Λ,
          U ((q.out⁻¹ : SL(2, ℤ)) • x) * w (((h⁻¹ : Λ) : SL(2, ℤ)) • (q.out⁻¹ : SL(2, ℤ)) • x) := by
        refine tsum_congr fun q => tsum_congr fun h => ?_
        have h1 : ((q.out : SL(2, ℤ)) * h)⁻¹ • x = ((h⁻¹ : Λ) : SL(2, ℤ)) • (q.out⁻¹ : SL(2, ℤ)) • x := by
          rw [mul_inv_rev, mul_smul, Subgroup.coe_inv]
        rw [h1, hUinv _ (h⁻¹).2]
    _ = ∑' q : SL(2, ℤ) ⧸ Λ, U ((q.out⁻¹ : SL(2, ℤ)) • x) *
          ∑' h : Λ, w (((h⁻¹ : Λ) : SL(2, ℤ)) • (q.out⁻¹ : SL(2, ℤ)) • x) :=
        tsum_congr fun q => ENNReal.tsum_mul_left
    _ = ∑' q : SL(2, ℤ) ⧸ Λ, U ((q.out⁻¹ : SL(2, ℤ)) • x) * 2 := by
        refine tsum_congr fun q => ?_
        rw [← tsum_Λ_inv Λ (fun h => w ((h : SL(2, ℤ)) • (q.out⁻¹ : SL(2, ℤ)) • x)), hwt q]
    _ = 2 * ∑ q : SL(2, ℤ) ⧸ Λ, U ((q.out⁻¹ : SL(2, ℤ)) • x) := by
        rw [ENNReal.tsum_mul_right, tsum_fintype, mul_comm]

theorem weight_lintegral (U w : ℍ → ℝ≥0∞) (hU : Measurable U) (hw : Measurable w)
    (hUinv : ∀ h ∈ Λ, ∀ x : ℍ, U (h • x) = U x)
    (hwt : ∀ᵐ x : ℍ, ∑' h : Λ, w ((h : SL(2, ℤ)) • x) = 2) :
    ∫⁻ x, U x * w x = ∫⁻ x in (𝒟 : Set ℍ), ∑ q : SL(2, ℤ) ⧸ Λ, U ((q.out⁻¹ : SL(2, ℤ)) • x) := by
  have hm : Measurable fun x => U x * w x := hU.mul hw
  have hae : ∀ᵐ x : ℍ, ∀ q : SL(2, ℤ) ⧸ Λ,
      ∑' h : Λ, w ((h : SL(2, ℤ)) • (q.out⁻¹ : SL(2, ℤ)) • x) = 2 := by
    haveI : Countable (SL(2, ℤ) ⧸ Λ) := inferInstance
    rw [ae_all_iff]
    intro q
    exact (mp_smul_SL (q.out⁻¹ : SL(2, ℤ))).quasiMeasurePreserving.ae
      (p := fun y : ℍ => ∑' h : Λ, w ((h : SL(2, ℤ)) • y) = 2) hwt
  have hA : ∑' γ : SL(2, ℤ), ∫⁻ x in (𝒟 : Set ℍ), U (γ • x) * w (γ • x) = 2 * ∫⁻ z, U z * w z :=
    FLT.ModularFundamentalDomain.tsum_setLIntegral_fd_smul (fun x => U x * w x) hm
  have hB : ∑' γ : SL(2, ℤ), ∫⁻ x in (𝒟 : Set ℍ), U (γ • x) * w (γ • x)
      = ∫⁻ x in (𝒟 : Set ℍ), ∑' γ : SL(2, ℤ), U (γ • x) * w (γ • x) :=
    (lintegral_tsum fun γ =>
      ((hm.comp (measurable_smul_SL γ) : Measurable fun x => U (γ • x) * w (γ • x))).aemeasurable).symm
  have hC : ∫⁻ x in (𝒟 : Set ℍ), ∑' γ : SL(2, ℤ), U (γ • x) * w (γ • x)
      = ∫⁻ x in (𝒟 : Set ℍ), 2 * ∑ q : SL(2, ℤ) ⧸ Λ, U ((q.out⁻¹ : SL(2, ℤ)) • x) := by
    refine lintegral_congr_ae (ae_restrict_of_ae ?_)
    filter_upwards [hae] with x hx
    exact tsum_G_eq Λ U w hUinv x hx
  have hmeasS : Measurable fun x : ℍ => ∑ q : SL(2, ℤ) ⧸ Λ, U ((q.out⁻¹ : SL(2, ℤ)) • x) :=
    Finset.measurable_sum _ fun q _ =>
      (hU.comp (measurable_smul_SL _) : Measurable fun x => U ((q.out⁻¹ : SL(2, ℤ)) • x))
  have hD : ∫⁻ x in (𝒟 : Set ℍ), 2 * ∑ q : SL(2, ℤ) ⧸ Λ, U ((q.out⁻¹ : SL(2, ℤ)) • x)
      = 2 * ∫⁻ x in (𝒟 : Set ℍ), ∑ q : SL(2, ℤ) ⧸ Λ, U ((q.out⁻¹ : SL(2, ℤ)) • x) :=
    lintegral_const_mul 2 hmeasS
  have key : (2 : ℝ≥0∞) * ∫⁻ x, U x * w x
      = 2 * ∫⁻ x in (𝒟 : Set ℍ), ∑ q : SL(2, ℤ) ⧸ Λ, U ((q.out⁻¹ : SL(2, ℤ)) • x) := by
    rw [← hA, hB, hC, hD]
  exact (ENNReal.mul_right_inj two_ne_zero ENNReal.ofNat_ne_top).mp key

end weight

section cvn

variable (Λ₁ Λ₂ : Subgroup SL(2, ℤ)) [Fintype (SL(2, ℤ) ⧸ Λ₁)] [Fintype (SL(2, ℤ) ⧸ Λ₂)]

theorem cvn_lintegral (β : GL (Fin 2) ℝ) (c : Λ₁ ≃ Λ₂)
    (hc : ∀ h : Λ₁, β * (Matrix.SpecialLinearGroup.mapGL ℝ (h : SL(2, ℤ)) : GL (Fin 2) ℝ)
      = (Matrix.SpecialLinearGroup.mapGL ℝ ((c h : Λ₂) : SL(2, ℤ)) : GL (Fin 2) ℝ) * β)
    (U : ℍ → ℝ≥0∞) (hU : Measurable U) (hUinv : ∀ h ∈ Λ₂, ∀ x : ℍ, U (h • x) = U x) :
    ∫⁻ x in (𝒟 : Set ℍ), ∑ q : SL(2, ℤ) ⧸ Λ₁, U (β • (q.out⁻¹ : SL(2, ℤ)) • x)
      = ∫⁻ x in (𝒟 : Set ℍ), ∑ q : SL(2, ℤ) ⧸ Λ₂, U ((q.out⁻¹ : SL(2, ℤ)) • x) := by
  have hUβinv : ∀ h ∈ Λ₁, ∀ x : ℍ, U (β • h • x) = U (β • x) := by
    intro h hh x
    rw [hact, ← mul_smul, hc ⟨h, hh⟩, mul_smul, ← hact, hUinv _ (c ⟨h, hh⟩).2]
  have h1 := weight_lintegral Λ₁ (fun x => U (β • x)) (wt Λ₁) (hU.comp (measurable_smul_GL β))
    (measurable_wt Λ₁) hUβinv (ae_tsum_wt_smul Λ₁)
  have h2 : ∫⁻ x, U (β • x) * wt Λ₁ x = ∫⁻ y, U y * wt Λ₁ (β⁻¹ • y) := by
    have hmeas : Measurable fun y : ℍ => U y * wt Λ₁ (β⁻¹ • y) :=
      hU.mul ((measurable_wt Λ₁).comp (measurable_smul_GL β⁻¹))
    have := (mp_smul_GL β).lintegral_comp hmeas
    simpa only [inv_smul_smul] using this
  have hwt' : ∀ᵐ y : ℍ, ∑' h : Λ₂, wt Λ₁ (β⁻¹ • (h : SL(2, ℤ)) • y) = 2 := by
    have hT : ∀ᵐ y : ℍ, ∑' h : Λ₁, wt Λ₁ ((h : SL(2, ℤ)) • β⁻¹ • y) = 2 :=
      (mp_smul_GL β⁻¹).quasiMeasurePreserving.ae
        (p := fun z : ℍ => ∑' h : Λ₁, wt Λ₁ ((h : SL(2, ℤ)) • z) = 2) (ae_tsum_wt_smul Λ₁)
    filter_upwards [hT] with y hy
    rw [← hy, ← c.tsum_eq (fun h : Λ₂ => wt Λ₁ (β⁻¹ • (h : SL(2, ℤ)) • y))]
    refine tsum_congr fun h => ?_
    show wt Λ₁ (β⁻¹ • ((c h : Λ₂) : SL(2, ℤ)) • y) = wt Λ₁ ((h : SL(2, ℤ)) • β⁻¹ • y)
    congr 1
    rw [hact, hact, ← mul_smul, ← mul_smul]
    congr 1
    rw [eq_mul_inv_iff_mul_eq, mul_assoc, ← hc h, ← mul_assoc, inv_mul_cancel, one_mul]
  have h3 := weight_lintegral Λ₂ U (fun y => wt Λ₁ (β⁻¹ • y)) hU
    ((measurable_wt Λ₁).comp (measurable_smul_GL β⁻¹)) hUinv hwt'
  rw [← h3, ← h2, h1]

end cvn

section pairing

def dens (k : ℤ) (H : ℍ → ℂ) (x : ℍ) : ℝ := ‖H x‖ ^ 2 * x.im ^ k

theorem dens_nonneg (k : ℤ) (H : ℍ → ℂ) (x : ℍ) : 0 ≤ dens k H x :=
  mul_nonneg (sq_nonneg _) (zpow_nonneg x.im_pos.le _)

theorem petersson_self_eq_dens (k : ℤ) (H : ℍ → ℂ) (x : ℍ) :
    UpperHalfPlane.petersson k H H x = ((dens k H x : ℝ) : ℂ) := by
  unfold UpperHalfPlane.petersson dens
  rw [Complex.conj_mul' (H x)]
  push_cast
  ring

structure Nice (Λ : Subgroup SL(2, ℤ)) (k : ℤ) (H : ℍ → ℂ) : Prop where
  cont : Continuous H
  bdd : ∃ C, ∀ x, dens k H x ≤ C
  inv : ∀ h ∈ Λ, H ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ h : GL (Fin 2) ℝ) = H

variable {Λ : Subgroup SL(2, ℤ)} {k : ℤ}

theorem Nice.add {F G : ℍ → ℂ} (hF : Nice Λ k F) (hG : Nice Λ k G) : Nice Λ k (F + G) := by
  obtain ⟨C₁, hC₁⟩ := hF.bdd
  obtain ⟨C₂, hC₂⟩ := hG.bdd
  refine ⟨hF.cont.add hG.cont, ⟨2 * C₁ + 2 * C₂, fun x => ?_⟩, fun h hh => ?_⟩
  · have h1 := hC₁ x
    have h2 := hC₂ x
    unfold dens at h1 h2 ⊢
    have hy : 0 ≤ x.im ^ k := zpow_nonneg x.im_pos.le _
    have hn : ‖(F + G) x‖ ^ 2 ≤ 2 * ‖F x‖ ^ 2 + 2 * ‖G x‖ ^ 2 := by
      rw [Pi.add_apply]
      have h3 : ‖F x + G x‖ ^ 2 ≤ (‖F x‖ + ‖G x‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (norm_add_le (F x) (G x)) 2
      nlinarith [h3, sq_nonneg (‖F x‖ - ‖G x‖)]
    nlinarith [mul_le_mul_of_nonneg_right hn hy]
  · rw [SlashAction.add_slash, hF.inv h hh, hG.inv h hh]

theorem Nice.smul {F : ℍ → ℂ} (hF : Nice Λ k F) (c : ℂ) : Nice Λ k (c • F) := by
  obtain ⟨C, hC⟩ := hF.bdd
  refine ⟨hF.cont.const_smul c, ⟨‖c‖ ^ 2 * C, fun x => ?_⟩, fun h hh => ?_⟩
  · have h1 := hC x
    unfold dens at h1 ⊢
    rw [Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow, mul_assoc]
    exact mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
  · have hσ : UpperHalfPlane.σ (Matrix.SpecialLinearGroup.mapGL ℝ h : GL (Fin 2) ℝ) = .refl ℝ ℂ := by
      rw [UpperHalfPlane.σ, if_pos (by simp)]
    rw [ModularForm.smul_slash, hF.inv h hh, hσ]
    rfl

theorem Nice.neg {F : ℍ → ℂ} (hF : Nice Λ k F) : Nice Λ k (-F) := by
  have := hF.smul (-1); rwa [neg_one_smul] at this

theorem Nice.sub {F G : ℍ → ℂ} (hF : Nice Λ k F) (hG : Nice Λ k G) : Nice Λ k (F - G) := by
  rw [sub_eq_add_neg]; exact hF.add hG.neg

theorem Nice.zero : Nice Λ k (0 : ℍ → ℂ) :=
  ⟨continuous_const, ⟨0, fun x => by simp [dens]⟩, fun _ _ => SlashAction.zero_slash k _⟩

theorem Nice.sum {ι : Type*} (s : Finset ι) {F : ι → ℍ → ℂ} (hF : ∀ i, Nice Λ k (F i)) :
    Nice Λ k (∑ i ∈ s, F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty]; exact Nice.zero
  | insert a s ha ih => rw [Finset.sum_insert ha]; exact (hF a).add ih

theorem Nice.mono {Λ' : Subgroup SL(2, ℤ)} {F : ℍ → ℂ} (hF : Nice Λ k F) (h : Λ' ≤ Λ) : Nice Λ' k F :=
  ⟨hF.cont, hF.bdd, fun g hg => hF.inv g (h hg)⟩

theorem Nice.dens_smul {F : ℍ → ℂ} (hF : Nice Λ k F) {h : SL(2, ℤ)} (hh : h ∈ Λ) (x : ℍ) :
    dens k F (h • x) = dens k F x := by
  have := UpperHalfPlane.petersson_slash_SL k F F h x
  rw [ModularForm.SL_slash, show ((h : GL (Fin 2) ℝ)) = (Matrix.SpecialLinearGroup.mapGL ℝ h : GL (Fin 2) ℝ)
    from rfl, hF.inv h hh, petersson_self_eq_dens, petersson_self_eq_dens] at this
  exact_mod_cast this.symm

theorem continuous_dens {F : ℍ → ℂ} (hF : Continuous F) : Continuous (dens k F) := by
  unfold dens
  refine ((continuous_norm.comp hF).pow 2).mul ?_
  exact (UpperHalfPlane.continuous_im.zpow₀ k fun x => Or.inl (x.im_pos.ne'))

theorem norm_petersson_le {F G : ℍ → ℂ} (x : ℍ) :
    ‖UpperHalfPlane.petersson k F G x‖ ≤ (dens k F x + dens k G x) / 2 := by
  unfold UpperHalfPlane.petersson dens
  rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_zpow, Complex.norm_real,
    Real.norm_of_nonneg x.im_pos.le]
  have hy : 0 ≤ x.im ^ k := zpow_nonneg x.im_pos.le _
  nlinarith [sq_nonneg (‖F x‖ - ‖G x‖), mul_nonneg (sq_nonneg (‖F x‖ - ‖G x‖)) hy]

variable (Λ) [Fintype (SL(2, ℤ) ⧸ Λ)]

def cosum (g : GL (Fin 2) ℝ) (Φ : ℍ → ℂ) (x : ℍ) : ℂ :=
  ∑ q : SL(2, ℤ) ⧸ Λ, Φ (g • (q.out⁻¹ : SL(2, ℤ)) • x)

def pair (k : ℤ) (F G : ℍ → ℂ) : ℂ :=
  ∫ x in (𝒟 : Set ℍ), cosum Λ 1 (UpperHalfPlane.petersson k F G) x

theorem integrable_cosum {F G : ℍ → ℂ} (hFc : Continuous F) (hGc : Continuous G)
    (hFb : ∃ C, ∀ x, dens k F x ≤ C) (hGb : ∃ C, ∀ x, dens k G x ≤ C) (g : GL (Fin 2) ℝ) :
    Integrable (cosum Λ g (UpperHalfPlane.petersson k F G)) (volume.restrict (𝒟 : Set ℍ)) := by
  obtain ⟨C₁, hC₁⟩ := hFb
  obtain ⟨C₂, hC₂⟩ := hGb
  have hmeas : Measurable (cosum Λ g (UpperHalfPlane.petersson k F G)) := by
    refine Finset.measurable_sum _ fun q _ => ?_
    exact (UpperHalfPlane.petersson_continuous k hFc hGc).measurable.comp
      ((measurable_smul_GL g).comp (measurable_smul_SL _))
  refine Measure.integrableOn_of_bounded (M := ∑ _q : SL(2, ℤ) ⧸ Λ, (C₁ + C₂) / 2)
    FLT.FundamentalDomainVolume.volume_fd_lt_top.ne hmeas.aestronglyMeasurable ?_
  refine Filter.Eventually.of_forall fun x => ?_
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun q _ => ?_)
  refine (norm_petersson_le _).trans ?_
  gcongr
  · exact hC₁ _
  · exact hC₂ _

theorem integral_cosum_self {Λ₁ : Subgroup SL(2, ℤ)} [Fintype (SL(2, ℤ) ⧸ Λ₁)] (β : GL (Fin 2) ℝ)
    (c : Λ₁ ≃ Λ)
    (hc : ∀ h : Λ₁,
      β * (Matrix.SpecialLinearGroup.mapGL ℝ (h : SL(2, ℤ)) : GL (Fin 2) ℝ)
        = (Matrix.SpecialLinearGroup.mapGL ℝ ((c h : Λ) : SL(2, ℤ)) : GL (Fin 2) ℝ) * β)
    {H : ℍ → ℂ} (hH : Nice Λ k H) :
    ∫ x in (𝒟 : Set ℍ), cosum Λ₁ β (UpperHalfPlane.petersson k H H) x
      = ∫ x in (𝒟 : Set ℍ), cosum Λ 1 (UpperHalfPlane.petersson k H H) x := by
  have hre : ∀ (Λ' : Subgroup SL(2, ℤ)) [Fintype (SL(2, ℤ) ⧸ Λ')] (g : GL (Fin 2) ℝ),
      (cosum Λ' g (UpperHalfPlane.petersson k H H))
      = fun x => ((∑ q : SL(2, ℤ) ⧸ Λ', dens k H (g • (q.out⁻¹ : SL(2, ℤ)) • x) : ℝ) : ℂ) := by
    intro Λ' _ g; funext x
    simp only [cosum, petersson_self_eq_dens, Complex.ofReal_sum]
  have hmeas : ∀ (Λ' : Subgroup SL(2, ℤ)) [Fintype (SL(2, ℤ) ⧸ Λ')] (g : GL (Fin 2) ℝ),
      Measurable fun x : ℍ => ∑ q : SL(2, ℤ) ⧸ Λ', dens k H (g • (q.out⁻¹ : SL(2, ℤ)) • x) := by
    intro Λ' _ g
    refine Finset.measurable_sum _ fun q _ => ?_
    exact (continuous_dens hH.cont).measurable.comp ((measurable_smul_GL g).comp (measurable_smul_SL _))
  have hnn : ∀ (Λ' : Subgroup SL(2, ℤ)) [Fintype (SL(2, ℤ) ⧸ Λ')] (g : GL (Fin 2) ℝ) (x : ℍ),
      0 ≤ ∑ q : SL(2, ℤ) ⧸ Λ', dens k H (g • (q.out⁻¹ : SL(2, ℤ)) • x) :=
    fun Λ' _ g x => Finset.sum_nonneg fun q _ => dens_nonneg k H _
  have hred : ∀ (Λ' : Subgroup SL(2, ℤ)) [Fintype (SL(2, ℤ) ⧸ Λ')] (g : GL (Fin 2) ℝ),
      ∫ x in (𝒟 : Set ℍ), cosum Λ' g (UpperHalfPlane.petersson k H H) x
        = ((∫⁻ x in (𝒟 : Set ℍ), ∑ q : SL(2, ℤ) ⧸ Λ',
            ENNReal.ofReal (dens k H (g • (q.out⁻¹ : SL(2, ℤ)) • x))).toReal : ℂ) := by
    intro Λ' _ g
    rw [hre Λ' g, integral_complex_ofReal, integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall (hnn Λ' g)) (hmeas Λ' g).aestronglyMeasurable]
    congr 2
    refine lintegral_congr fun x => ?_
    rw [ENNReal.ofReal_sum_of_nonneg fun q _ => dens_nonneg k H _]
  rw [hred Λ₁ β, hred Λ 1]
  congr 2
  have hU : Measurable fun x => ENNReal.ofReal (dens k H x) :=
    ENNReal.measurable_ofReal.comp (continuous_dens hH.cont).measurable
  have := cvn_lintegral Λ₁ Λ β c hc
    (fun x => ENNReal.ofReal (dens k H x)) hU (fun h hh x => by simp only [hH.dens_smul hh])
  simpa only [one_smul] using this

theorem petersson_polarization (F G : ℍ → ℂ) (x : ℍ) :
    UpperHalfPlane.petersson k F G x
      = (4 : ℂ)⁻¹ * (UpperHalfPlane.petersson k (G + F) (G + F) x
          + Complex.I * UpperHalfPlane.petersson k (G + Complex.I • F) (G + Complex.I • F) x
          - UpperHalfPlane.petersson k (G - F) (G - F) x
          - Complex.I * UpperHalfPlane.petersson k (G - Complex.I • F) (G - Complex.I • F) x) := by
  simp only [UpperHalfPlane.petersson, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    map_add, map_sub, map_mul, Complex.conj_I]
  linear_combination (-(1 / 2 : ℂ) * ((starRingEnd ℂ) (G x) * F x - (starRingEnd ℂ) (F x) * G x)
    * ((x.im : ℂ)) ^ k) * Complex.I_sq

omit [Fintype (SL(2, ℤ) ⧸ Λ)] in

theorem integral_cosum_polar (Λ' : Subgroup SL(2, ℤ)) [Fintype (SL(2, ℤ) ⧸ Λ')]
    (g : GL (Fin 2) ℝ) {F G : ℍ → ℂ} (hF : Nice Λ k F) (hG : Nice Λ k G) :
    ∫ x in (𝒟 : Set ℍ), cosum Λ' g (UpperHalfPlane.petersson k F G) x
      = (4 : ℂ)⁻¹ * ((∫ x in (𝒟 : Set ℍ), cosum Λ' g (UpperHalfPlane.petersson k (G + F) (G + F)) x)
        + Complex.I * (∫ x in (𝒟 : Set ℍ), cosum Λ' g
            (UpperHalfPlane.petersson k (G + Complex.I • F) (G + Complex.I • F)) x)
        - (∫ x in (𝒟 : Set ℍ), cosum Λ' g (UpperHalfPlane.petersson k (G - F) (G - F)) x)
        - Complex.I * (∫ x in (𝒟 : Set ℍ), cosum Λ' g
            (UpperHalfPlane.petersson k (G - Complex.I • F) (G - Complex.I • F)) x)) := by
  have hexp : cosum Λ' g (UpperHalfPlane.petersson k F G)
      = fun x => (4 : ℂ)⁻¹ * (cosum Λ' g (UpperHalfPlane.petersson k (G + F) (G + F)) x
          + Complex.I * cosum Λ' g (UpperHalfPlane.petersson k (G + Complex.I • F) (G + Complex.I • F)) x
          - cosum Λ' g (UpperHalfPlane.petersson k (G - F) (G - F)) x
          - Complex.I * cosum Λ' g (UpperHalfPlane.petersson k (G - Complex.I • F) (G - Complex.I • F)) x) := by
    funext x
    simp only [cosum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun q _ => by rw [petersson_polarization]
  have h0 := hG.add hF
  have h1 := hG.add (hF.smul Complex.I)
  have h2 := hG.sub hF
  have h3 := hG.sub (hF.smul Complex.I)
  have iA := integrable_cosum Λ' h0.cont h0.cont h0.bdd h0.bdd g
  have iB := (integrable_cosum Λ' h1.cont h1.cont h1.bdd h1.bdd g).const_mul Complex.I
  have iC := integrable_cosum Λ' h2.cont h2.cont h2.bdd h2.bdd g
  have iD := (integrable_cosum Λ' h3.cont h3.cont h3.bdd h3.bdd g).const_mul Complex.I
  have iAB : Integrable (fun x => cosum Λ' g (UpperHalfPlane.petersson k (G + F) (G + F)) x
      + Complex.I * cosum Λ' g (UpperHalfPlane.petersson k (G + Complex.I • F) (G + Complex.I • F)) x)
      (volume.restrict (𝒟 : Set ℍ)) := iA.add iB
  have iABC : Integrable (fun x => cosum Λ' g (UpperHalfPlane.petersson k (G + F) (G + F)) x
      + Complex.I * cosum Λ' g (UpperHalfPlane.petersson k (G + Complex.I • F) (G + Complex.I • F)) x
      - cosum Λ' g (UpperHalfPlane.petersson k (G - F) (G - F)) x)
      (volume.restrict (𝒟 : Set ℍ)) := iAB.sub iC
  rw [hexp, integral_const_mul]
  congr 1
  rw [integral_sub iABC iD, integral_sub iAB iC, integral_add iA iB, integral_const_mul,
    integral_const_mul]

theorem integral_cosum_pair {Λ₁ : Subgroup SL(2, ℤ)} [Fintype (SL(2, ℤ) ⧸ Λ₁)] (β : GL (Fin 2) ℝ)
    (c : Λ₁ ≃ Λ)
    (hc : ∀ h : Λ₁,
      β * (Matrix.SpecialLinearGroup.mapGL ℝ (h : SL(2, ℤ)) : GL (Fin 2) ℝ)
        = (Matrix.SpecialLinearGroup.mapGL ℝ ((c h : Λ) : SL(2, ℤ)) : GL (Fin 2) ℝ) * β)
    {F G : ℍ → ℂ} (hF : Nice Λ k F) (hG : Nice Λ k G) :
    ∫ x in (𝒟 : Set ℍ), cosum Λ₁ β (UpperHalfPlane.petersson k F G) x
      = ∫ x in (𝒟 : Set ℍ), cosum Λ 1 (UpperHalfPlane.petersson k F G) x := by
  rw [integral_cosum_polar Λ Λ₁ β hF hG, integral_cosum_polar Λ Λ 1 hF hG,
    integral_cosum_self Λ β c hc (hG.add hF), integral_cosum_self Λ β c hc (hG.add (hF.smul _)),
    integral_cosum_self Λ β c hc (hG.sub hF), integral_cosum_self Λ β c hc (hG.sub (hF.smul _))]

theorem pair_slash {Λ₁ : Subgroup SL(2, ℤ)} [Fintype (SL(2, ℤ) ⧸ Λ₁)] (β : GL (Fin 2) ℝ)
    (hβ : 0 < (β.det : ℝ)) (c : Λ₁ ≃ Λ)
    (hc : ∀ h : Λ₁,
      β * (Matrix.SpecialLinearGroup.mapGL ℝ (h : SL(2, ℤ)) : GL (Fin 2) ℝ)
        = (Matrix.SpecialLinearGroup.mapGL ℝ ((c h : Λ) : SL(2, ℤ)) : GL (Fin 2) ℝ) * β)
    {F G : ℍ → ℂ} (hF : Nice Λ k F) (hG : Nice Λ k G) :
    pair Λ₁ k (F ∣[k] β) (G ∣[k] β) = ((β.det : ℝ) : ℂ) ^ (k - 2) * pair Λ k F G := by
  unfold pair
  have hσ : UpperHalfPlane.σ β = .refl ℝ ℂ := by rw [UpperHalfPlane.σ, if_pos hβ]
  have hpt : cosum Λ₁ 1 (UpperHalfPlane.petersson k (F ∣[k] β) (G ∣[k] β))
      = fun x => ((β.det : ℝ) : ℂ) ^ (k - 2) * cosum Λ₁ β (UpperHalfPlane.petersson k F G) x := by
    funext x
    simp only [cosum, one_smul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [UpperHalfPlane.petersson_slash, hσ, abs_of_pos hβ]
    rfl
  rw [hpt, integral_const_mul, integral_cosum_pair Λ β c hc hF hG]

theorem pair_conj_symm (F G : ℍ → ℂ) : pair Λ k G F = conj (pair Λ k F G) := by
  unfold pair
  rw [← integral_conj]
  congr 1
  funext x
  simp only [cosum, map_sum]
  exact Finset.sum_congr rfl fun q _ => UpperHalfPlane.petersson_symm k F G _

theorem pair_smul_left (c : ℂ) (F G : ℍ → ℂ) : pair Λ k (c • F) G = conj c * pair Λ k F G := by
  unfold pair
  rw [← integral_const_mul]
  congr 1; funext x
  simp only [cosum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  simp only [UpperHalfPlane.petersson, Pi.smul_apply, smul_eq_mul, map_mul]; ring

theorem pair_smul_right (c : ℂ) (F G : ℍ → ℂ) : pair Λ k F (c • G) = c * pair Λ k F G := by
  unfold pair
  rw [← integral_const_mul]
  congr 1; funext x
  simp only [cosum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  simp only [UpperHalfPlane.petersson, Pi.smul_apply, smul_eq_mul]; ring

theorem pair_sum_left {ι : Type*} (s : Finset ι) (F : ι → ℍ → ℂ) (G : ℍ → ℂ)
    (hF : ∀ i, Nice Λ k (F i)) (hG : Nice Λ k G) :
    pair Λ k (∑ i ∈ s, F i) G = ∑ i ∈ s, pair Λ k (F i) G := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty, pair, cosum]
    simp [UpperHalfPlane.petersson]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih]
    unfold pair
    rw [← integral_add (integrable_cosum Λ (hF a).cont hG.cont (hF a).bdd hG.bdd 1)]
    · congr 1; funext x
      simp only [cosum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun q _ => ?_
      simp only [UpperHalfPlane.petersson, Pi.add_apply, Finset.sum_apply, map_add]; ring
    · have hs : Nice Λ k (∑ i ∈ s, F i) := Nice.sum s hF
      exact integrable_cosum Λ hs.cont hG.cont hs.bdd hG.bdd 1

theorem pair_sum_right {ι : Type*} (s : Finset ι) (F : ℍ → ℂ) (G : ι → ℍ → ℂ)
    (hF : Nice Λ k F) (hG : ∀ i, Nice Λ k (G i)) :
    pair Λ k F (∑ i ∈ s, G i) = ∑ i ∈ s, pair Λ k F (G i) := by
  rw [pair_conj_symm, pair_sum_left Λ s G F hG hF, map_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [pair_conj_symm Λ (k := k) F (G i), Complex.conj_conj]

end pairing

section definite

variable (Λ : Subgroup SL(2, ℤ)) [Fintype (SL(2, ℤ) ⧸ Λ)] {k : ℤ}

theorem pair_self_eq_lintegral {F : ℍ → ℂ} (hF : Continuous F) :
    pair Λ k F F = ((∫⁻ x in (𝒟 : Set ℍ), ∑ q : SL(2, ℤ) ⧸ Λ,
        ENNReal.ofReal (dens k F ((q.out⁻¹ : SL(2, ℤ)) • x))).toReal : ℂ) := by
  unfold pair
  have hre : cosum Λ 1 (UpperHalfPlane.petersson k F F)
      = fun x => ((∑ q : SL(2, ℤ) ⧸ Λ, dens k F ((q.out⁻¹ : SL(2, ℤ)) • x) : ℝ) : ℂ) := by
    funext x
    simp only [cosum, one_smul, petersson_self_eq_dens, Complex.ofReal_sum]
  have hmeas : Measurable fun x : ℍ => ∑ q : SL(2, ℤ) ⧸ Λ, dens k F ((q.out⁻¹ : SL(2, ℤ)) • x) := by
    refine Finset.measurable_sum _ fun q _ => ?_
    exact (continuous_dens hF).measurable.comp (measurable_smul_SL _)
  rw [hre, integral_complex_ofReal, integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall fun x => Finset.sum_nonneg fun q _ => dens_nonneg k F _)
    hmeas.aestronglyMeasurable]
  congr 2
  refine lintegral_congr fun x => ?_
  rw [ENNReal.ofReal_sum_of_nonneg fun q _ => dens_nonneg k F _]

theorem eq_zero_of_pair_self_eq_zero {F : ℍ → ℂ} (hF : Nice Λ k F) (h0 : pair Λ k F F = 0) :
    F = 0 := by
  obtain ⟨C, hC⟩ := hF.bdd
  set U : ℍ → ℝ≥0∞ := fun x => ENNReal.ofReal (dens k F x) with hUdef
  have hU : Measurable U := ENNReal.measurable_ofReal.comp (continuous_dens hF.cont).measurable
  have hUinv : ∀ h ∈ Λ, ∀ x, U (h • x) = U x := fun h hh x => by simp only [hUdef, hF.dens_smul hh]

  set I : ℝ≥0∞ := ∫⁻ x in (𝒟 : Set ℍ), ∑ q : SL(2, ℤ) ⧸ Λ, U ((q.out⁻¹ : SL(2, ℤ)) • x) with hI
  have hIfin : I ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (lintegral_mono (g := fun _ => ∑ _q : SL(2, ℤ) ⧸ Λ, ENNReal.ofReal C)
      fun x => Finset.sum_le_sum fun q _ => ENNReal.ofReal_le_ofReal (hC _))
    rw [lintegral_const]
    refine ENNReal.mul_ne_top ?_ (by
      rw [Measure.restrict_apply_univ]; exact FLT.FundamentalDomainVolume.volume_fd_lt_top.ne)
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) ENNReal.ofReal_ne_top
  have hI0 : I = 0 := by
    have h := pair_self_eq_lintegral Λ (k := k) hF.cont
    rw [h0] at h
    have h' : I.toReal = 0 := by exact_mod_cast h.symm
    rcases (ENNReal.toReal_eq_zero_iff _).mp h' with h'' | h''
    · exact h''
    · exact absurd h'' hIfin

  have hterm : ∀ q : SL(2, ℤ) ⧸ Λ, ∫⁻ x in (𝒟 : Set ℍ), U ((q.out⁻¹ : SL(2, ℤ)) • x) = 0 := by
    have hsum : ∑ q : SL(2, ℤ) ⧸ Λ, ∫⁻ x in (𝒟 : Set ℍ), U ((q.out⁻¹ : SL(2, ℤ)) • x) = 0 := by
      have h := lintegral_finsetSum (μ := volume.restrict (𝒟 : Set ℍ)) Finset.univ
        (f := fun (q : SL(2, ℤ) ⧸ Λ) (x : ℍ) => U ((q.out⁻¹ : SL(2, ℤ)) • x))
        (fun q _ => (hU.comp (measurable_smul_SL _)))
      rw [← h]
      exact hI0
    intro q
    exact Finset.sum_eq_zero_iff.mp hsum q (Finset.mem_univ q)

  have hall : ∀ σ : SL(2, ℤ), ∫⁻ x in (𝒟 : Set ℍ), U (σ • x) = 0 := by
    intro σ
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul Λ σ⁻¹
    set q : SL(2, ℤ) ⧸ Λ := QuotientGroup.mk σ⁻¹ with hq
    have hσ : σ = (h : SL(2, ℤ)) * (q.out)⁻¹ := by
      rw [hh, mul_inv_rev, inv_inv, ← mul_assoc, mul_inv_cancel, one_mul]
    have : (fun x => U (σ • x)) = fun x => U ((q.out)⁻¹ • x) := by
      funext x
      rw [hσ, mul_smul, hUinv _ h.2]
    rw [this]
    exact hterm q

  have htot : ∫⁻ x, U x = 0 := by
    have h := FLT.ModularFundamentalDomain.tsum_setLIntegral_fd_smul U hU
    simp only [hall, tsum_zero] at h
    have h2 : (2 : ℝ≥0∞) * ∫⁻ x, U x = 0 := h.symm
    simpa using h2
  have hae : U =ᵐ[volume] 0 := (lintegral_eq_zero_iff hU).mp htot
  have hdens : dens k F = fun _ => 0 := by
    have hae' : dens k F =ᵐ[volume] fun _ => (0 : ℝ) := by
      filter_upwards [hae] with x hx
      have hx' : ENNReal.ofReal (dens k F x) = 0 := hx
      exact le_antisymm (ENNReal.ofReal_eq_zero.mp hx') (dens_nonneg k F x)
    exact (Continuous.ae_eq_iff_eq volume (continuous_dens hF.cont) continuous_const).mp hae'
  funext x
  have hx := congrFun hdens x
  unfold dens at hx
  have hy : 0 < x.im ^ k := zpow_pos x.im_pos _
  have : ‖F x‖ ^ 2 = 0 := by
    rcases mul_eq_zero.mp hx with h | h
    · exact h
    · exact absurd h hy.ne'
  simpa using this

end definite

section level

variable {Γ'' Λ : Subgroup SL(2, ℤ)}

section unfold

variable (hΛΓ : Λ ≤ Γ'') {ι : Type*} (r : ι → SL(2, ℤ)) (hr : ∀ i, r i ∈ Γ'')
  (hex : ∀ γ ∈ Γ'', ∃ i, r i * γ ∈ Λ) (huniq : ∀ i i', r i * (r i')⁻¹ ∈ Λ → i = i')

def eMap (r : ι → SL(2, ℤ)) (x : (SL(2, ℤ) ⧸ Γ'') × ι) : SL(2, ℤ) ⧸ Λ :=
  QuotientGroup.mk (x.1.out * (r x.2)⁻¹)

include hΛΓ hr hex huniq in
theorem eMap_bijective : Function.Bijective (eMap (Γ'' := Γ'') (Λ := Λ) r) := by
  constructor
  · rintro ⟨q, i⟩ ⟨q', i'⟩ h
    have hmem : r i * q.out⁻¹ * q'.out * (r i')⁻¹ ∈ Λ := by
      have := QuotientGroup.eq.mp h
      simpa [mul_assoc, mul_inv_rev] using this
    have hqq : q = q' := by
      have hΓ : q.out⁻¹ * q'.out ∈ Γ'' := by
        have h1 : (r i)⁻¹ * (r i * q.out⁻¹ * q'.out * (r i')⁻¹) * r i' ∈ Γ'' :=
          mul_mem (mul_mem (inv_mem (hr i)) (hΛΓ hmem)) (hr i')
        simpa [mul_assoc] using h1
      rw [← QuotientGroup.out_eq' q, ← QuotientGroup.out_eq' q']
      exact QuotientGroup.eq.mpr hΓ
    subst hqq
    have : r i * (r i')⁻¹ ∈ Λ := by simpa using hmem
    rw [huniq i i' this]
  · intro y
    set σ := y.out
    set q : SL(2, ℤ) ⧸ Γ'' := QuotientGroup.mk σ
    have hγ : q.out⁻¹ * σ ∈ Γ'' := by
      rw [← QuotientGroup.eq]
      exact QuotientGroup.out_eq' q
    obtain ⟨i, hi⟩ := hex _ hγ
    refine ⟨(q, i), ?_⟩
    rw [← QuotientGroup.out_eq' y]
    show QuotientGroup.mk (q.out * (r i)⁻¹) = QuotientGroup.mk σ
    rw [QuotientGroup.eq]
    simpa [mul_assoc, mul_inv_rev] using hi

variable [Fintype (SL(2, ℤ) ⧸ Γ'')] [Fintype (SL(2, ℤ) ⧸ Λ)] [Fintype ι]

include hΛΓ hr hex huniq in

theorem unfold_sum {X : Type*} [AddCommMonoid X] (Φ : ℍ → X)
    (hΦ : ∀ h ∈ Λ, ∀ x : ℍ, Φ (h • x) = Φ x) (τ : ℍ) :
    ∑ q' : SL(2, ℤ) ⧸ Λ, Φ ((q'.out⁻¹ : SL(2, ℤ)) • τ)
      = ∑ q : SL(2, ℤ) ⧸ Γ'', ∑ i, Φ ((r i * q.out⁻¹ : SL(2, ℤ)) • τ) := by
  rw [← Fintype.sum_prod_type']
  symm
  refine Fintype.sum_bijective (eMap (Γ'' := Γ'') (Λ := Λ) r)
    (eMap_bijective hΛΓ r hr hex huniq) _ _ fun x => ?_
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul Λ (x.1.out * (r x.2)⁻¹)
  show Φ ((r x.2 * x.1.out⁻¹ : SL(2, ℤ)) • τ) = Φ (((eMap r x).out⁻¹ : SL(2, ℤ)) • τ)
  rw [eMap, hh, mul_inv_rev, mul_inv_rev, inv_inv, mul_smul ((h : SL(2, ℤ))⁻¹) (r x.2 * x.1.out⁻¹) τ,
    hΦ _ (inv_mem h.2)]

end unfold

variable [Fintype (SL(2, ℤ) ⧸ Γ'')] [Fintype (SL(2, ℤ) ⧸ Λ)]

theorem cosum_eq_relIndex_mul (hle : Λ ≤ Γ'') (Φ : ℍ → ℂ)
    (hΦ : ∀ h ∈ Γ'', ∀ x : ℍ, Φ (h • x) = Φ x) (τ : ℍ) :
    cosum Λ 1 Φ τ = (Λ.relIndex Γ'' : ℂ) * cosum Γ'' 1 Φ τ := by

  have hne : (Λ.subgroupOf Γ'').index ≠ 0 := by
    have h := Subgroup.relIndex_mul_index hle
    intro h0
    rw [Subgroup.relIndex, h0, zero_mul] at h
    have hΛ : Λ.index ≠ 0 := by
      rw [Subgroup.index_eq_card, Nat.card_eq_fintype_card]; exact Fintype.card_ne_zero
    exact hΛ h.symm
  haveI : (Λ.subgroupOf Γ'').FiniteIndex := ⟨hne⟩
  haveI : Finite (Γ'' ⧸ Λ.subgroupOf Γ'') := Subgroup.finite_quotient_of_finiteIndex
  letI : Fintype (Γ'' ⧸ Λ.subgroupOf Γ'') := Fintype.ofFinite _
  set r : (Γ'' ⧸ Λ.subgroupOf Γ'') → SL(2, ℤ) := fun i => ((i.out : Γ'') : SL(2, ℤ))⁻¹ with hr
  have hr' : ∀ i, r i ∈ Γ'' := fun i => inv_mem (i.out).2
  have hex : ∀ γ ∈ Γ'', ∃ i, r i * γ ∈ Λ := by
    intro γ hγ
    refine ⟨QuotientGroup.mk ⟨γ, hγ⟩, ?_⟩
    have h := QuotientGroup.out_eq' (QuotientGroup.mk (s := Λ.subgroupOf Γ'') ⟨γ, hγ⟩)
    have h2 := QuotientGroup.eq.mp h
    rw [Subgroup.mem_subgroupOf] at h2
    simpa [hr] using h2
  have huniq : ∀ i i', r i * (r i')⁻¹ ∈ Λ → i = i' := by
    intro i i' h
    have h2 : (i.out)⁻¹ * i'.out ∈ Λ.subgroupOf Γ'' := by
      rw [Subgroup.mem_subgroupOf]; simpa [hr] using h
    have := QuotientGroup.eq.mpr h2
    rwa [QuotientGroup.out_eq', QuotientGroup.out_eq'] at this
  unfold cosum
  simp only [one_smul]
  rw [unfold_sum hle r hr' hex huniq Φ (fun h hh x => hΦ h (hle hh) x) τ, Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  have : ∀ i, Φ ((r i * q.out⁻¹ : SL(2, ℤ)) • τ) = Φ ((q.out⁻¹ : SL(2, ℤ)) • τ) := fun i => by
    rw [mul_smul, hΦ _ (hr' i)]
  simp only [this, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  congr 1
  rw [Subgroup.relIndex, Subgroup.index_eq_card, Nat.card_eq_fintype_card]

theorem pair_eq_relIndex_mul (hle : Λ ≤ Γ'') {k : ℤ} {F G : ℍ → ℂ} (hF : Nice Γ'' k F) (hG : Nice Γ'' k G) :
    pair Λ k F G = (Λ.relIndex Γ'' : ℂ) * pair Γ'' k F G := by
  unfold pair
  rw [← integral_const_mul]
  congr 1
  funext τ
  refine cosum_eq_relIndex_mul hle _ (fun h hh x => ?_) τ
  have := UpperHalfPlane.petersson_slash_SL k F G h x
  rw [ModularForm.SL_slash, ModularForm.SL_slash,
    show ((h : GL (Fin 2) ℝ)) = (Matrix.SpecialLinearGroup.mapGL ℝ h : GL (Fin 2) ℝ) from rfl,
    hF.inv h hh, hG.inv h hh] at this
  exact this.symm

end level

section indexeq

variable (Λ₁ Λ₂ : Subgroup SL(2, ℤ)) [Fintype (SL(2, ℤ) ⧸ Λ₁)] [Fintype (SL(2, ℤ) ⧸ Λ₂)]

theorem card_quotient_eq_of_conj (β : GL (Fin 2) ℝ) (c : Λ₁ ≃ Λ₂)
    (hc : ∀ h : Λ₁, β * (Matrix.SpecialLinearGroup.mapGL ℝ (h : SL(2, ℤ)) : GL (Fin 2) ℝ)
      = (Matrix.SpecialLinearGroup.mapGL ℝ ((c h : Λ₂) : SL(2, ℤ)) : GL (Fin 2) ℝ) * β) :
    Fintype.card (SL(2, ℤ) ⧸ Λ₁) = Fintype.card (SL(2, ℤ) ⧸ Λ₂) := by
  have h := cvn_lintegral Λ₁ Λ₂ β c hc (fun _ => 1) measurable_const (fun _ _ _ => rfl)
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, lintegral_const,
    Measure.restrict_apply_univ] at h
  obtain ⟨h0, htop⟩ := FLT.FundamentalDomainVolume.volume_fd_ne_zero_ne_top
  have := (ENNReal.mul_left_inj h0 htop).mp h
  exact_mod_cast this

end indexeq

end CuspForm.PeterssonCoset

end


