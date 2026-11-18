-- Prove2me | solution 1 for ArtinKP.GK.kw_theta_of_diffInS
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T10:12:50.562596+00:00
-- url     : https://prove2.me/submissions/7a874e63-9893-4862-9bb7-fa7ec35f8d0c

import Mathlib
import Definitions.Def_ArtinHecke
import Definitions.Def_ArtinHeckeLocalCoeff
import Definitions.Def_ArtinHeckePoissonLocal
import Definitions.Def_ArtinHeckeProbe
import Definitions.Def_ArtinHeckeSModel
import Definitions.Def_ArtinHeckeTheta
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_ExtCitation_LocalLevelResidues
import Definitions.Def_IsDedekindDomain_FiniteUnitIdeles
import Definitions.Def_IsDedekindDomain_FiniteUnitIdelesOutside
import Definitions.Def_LanglandsTunnell_ArtinCoreCTM
import Definitions.Def_M4aHerbrand_GenuineDescent
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_NormIndex_AdmissibleExpOfDegree
import Definitions.Def_NumberField_ArchimedeanIdeleModule
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_ArtinKPB017
import Theorems.Thm_ArtinKP_C5_differentiableOn_functional_resPart
import Theorems.Thm_ArtinKP_C5_tendsto_ray_functional_resPart_theta
import Theorems.Thm_ArtinKP_C9_theta_eq_zero_of_forall_tau_eq_zero
import Theorems.Thm_ArtinKP_GK_tau_eq_rpow_mul_coefF_mul_kir
import Theorems.Thm_ArtinKP_GK_tau_eq_zero_of_theta
import Theorems.Thm_ArtinKP_GL_eisEigen_of_two_lt_re
import Theorems.Thm_ArtinKP_N_coeff_resPart_add_hInt
import Theorems.Thm_ArtinKP_N_differentiable_hInt
import Theorems.Thm_ArtinKP_N_integral_box_theta_eq_of_tendsto_ray
import Theorems.Thm_ArtinKP_N2_theta_eq_zero_iff_forall_zPsi_translate_eq_zero
import Theorems.Thm_ArtinKP_T_tau_smulFun
import Theorems.Thm_ArtinKP_X_X_isPOU_pou
import Theorems.Thm_ArtinKP_X_X_tsum_indicator_box_le_boxMult

section
-- module Solutions.Artin.KP.X_Discrete
attribute [-instance] _root_.ArtinKP.X.instContinuousConstSMulSubgroup _root_.ArtinKP.X.instIsFiniteMeasureOnCompactsXVol _root_.ArtinKP.X.instIsFiniteMeasureXRestrictVolBox _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-! # WP-X, file 6: discreteness of `SL(2, 𝓞_F)` on `X`, the quotient measure, `L²(Γ\X)`

* `entries_bounded`: if `Q` and `g • Q` lie in a box of `H3` the entries of `g` are bounded;
* `finite_return_box`: a box of `X` meets only finitely many of its `SL(2,𝓞_F)`-translates
  (`𝓞_F` is discrete in `ℂ^r`); the same for compact sets (`finite_return_of_isCompact`);
* a positive partition of unity for every subgroup `Γ ≤ SL(2,𝓞_F)`, the quotient measure
  `X.quotVol Γ` on `Γ \ X` (independent of the partition), `X.L2 Γ = L²(Γ\X)`;
* the cusp stabilizer `GammaInf Γ` and its action in coordinates.
-/

open scoped MatrixGroups ComplexConjugate ENNReal
open MeasureTheory Set NumberField

set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.X

noncomputable section

/-! ### One factor -/

/-! ### The integral group -/

variable {F : Type*} [Field F] [NumberField F]

lemma X.exists_mem_box (P : X F) : ∃ n : ℕ, P ∈ X.box n := by
  have h1 : ∃ n : ℕ, ∀ w, ‖P.x w‖ ≤ n ∧ P.v w ≤ n ∧ 1 / P.v w ≤ n := by
    obtain ⟨n, hn⟩ := exists_nat_ge
      (∑ w : InfinitePlace F, (‖P.x w‖ + P.v w + 1 / P.v w))
    refine ⟨n, fun w => ?_⟩
    have hnn : ∀ w' ∈ (Finset.univ : Finset (InfinitePlace F)),
        0 ≤ ‖P.x w'‖ + P.v w' + 1 / P.v w' := fun w' _ => by
      have := P.v_pos w'
      positivity
    have := (Finset.single_le_sum hnn (Finset.mem_univ w)).trans hn
    have hv := P.v_pos w
    have h3 : 0 < 1 / P.v w := by positivity
    have h4 := norm_nonneg (P.x w)
    exact ⟨by linarith, by linarith, by linarith⟩
  obtain ⟨n, hn⟩ := h1
  refine ⟨n, fun w => ⟨(hn w).1, ?_, ?_⟩⟩
  · have hv := P.v_pos w
    have h3 := (hn w).2.2
    change 1 / ((n : ℝ) + 1) ≤ P.v w
    rw [div_le_iff₀ (by positivity)]
    rw [div_le_iff₀ hv] at h3
    nlinarith
  · have := (hn w).2.1
    change P.v w ≤ (n : ℝ) + 1
    linarith

/-! ### Partition of unity, quotient measure, `L²(Γ\X)` -/

/-! ### The cusp stabilizer -/

end

end ArtinKP.X
end

section
-- module Solutions.Artin.KP.B1_L2
attribute [-instance] _root_.ArtinKP.X.instContinuousConstSMulSubgroup _root_.ArtinKP.X.instIsFiniteMeasureOnCompactsXVol _root_.ArtinKP.X.instIsFiniteMeasureXRestrictVolBox _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
attribute [-simp] _root_.ArtinKP.FB.v_gmap _root_.ArtinKP.FB.x_gmap _root_.ArtinKP.X.chart1_symm_fst _root_.ArtinKP.X.chart1_symm_snd _root_.ArtinKP.X.chart1_v _root_.ArtinKP.X.chart1_x _root_.ArtinKP.X.chart_apply _root_.ArtinKP.X.chart_symm_apply
/-! # WP-B1, file 9: `G ∈ L¹ ∩ L²(Γ\X)`, and compactness of the truncated space at the cusp `∞`

* `measurable_G`; `lintegral_G_pow_lt_top`: `∫_{Γ\X} G^k dμ < ∞` (in the partition-of-unity form of
  WP-X) for every `k`, from the boundedness of `G` and **finite volume of `Γ\X`** (hypothesis `hvol`).
* `H3.isCompact_box`, `X.isCompact_box`.
* `exists_reduced`: every point of `X` is `Γ_∞`-equivalent (`Γ_∞ ⊂ SL₂(𝓞_F)` upper triangular) to a point
  with `x` in the fundamental cell and balanced `v`; `siegel S' T` is compact; hence
  `subset_orbit_siegel`: the points whose top class is in the `SL₂(𝓞_F)`-orbit of `∞` and whose top
  height is in `[c, T]` lie in `SL₂(𝓞_F) · (compact)`.
-/

open scoped MatrixGroups ComplexConjugate ENNReal
open MeasureTheory Set NumberField Module

set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.B1

open ArtinKP.X

noncomputable section

variable {F : Type*} [Field F] [NumberField F] [IsTotallyComplex F] {S : Finset (FinitePlace F)}

/-! ### Compactness of the truncated space at the cusp `∞` (item 5) -/

omit [NumberField F] [IsTotallyComplex F] in
lemma H3.isCompact_box {m M B : ℝ} (hm : 0 < m) : IsCompact (H3.box m M B) := by
  have hind : Topology.IsInducing (Subtype.val : {p : ℂ × ℝ // 0 < p.2} → ℂ × ℝ) :=
    Topology.IsInducing.subtypeVal
  have himg : (Subtype.val : {p : ℂ × ℝ // 0 < p.2} → ℂ × ℝ) '' (H3.box m M B) =
      Metric.closedBall (0 : ℂ) B ×ˢ Set.Icc m M := by
    ext ⟨z, t⟩
    constructor
    · rintro ⟨Q, ⟨h1, h2, h3⟩, hQ⟩
      have hz : H3.x Q = z := congrArg Prod.fst hQ
      have ht : H3.v Q = t := congrArg Prod.snd hQ
      rw [hz] at h1
      rw [ht] at h2 h3
      exact ⟨by simpa using h1, h2, h3⟩
    · rintro ⟨h1, h2, h3⟩
      have h1' : ‖z‖ ≤ B := by simpa using h1
      exact ⟨⟨(z, t), lt_of_lt_of_le hm h2⟩, ⟨h1', h2, h3⟩, rfl⟩
  exact hind.isCompact_iff.mpr (himg ▸ (isCompact_closedBall 0 B).prod isCompact_Icc)

omit [IsTotallyComplex F] in
theorem isCompact_siegelBox {m M B : ℝ} (hm : 0 < m) : IsCompact (siegelBox F m M B) := by
  have : siegelBox F m M B = Set.pi Set.univ fun _ : InfinitePlace F => H3.box m M B := by
    ext P; simp [siegelBox]
  rw [this]
  exact isCompact_univ_pi fun _ => H3.isCompact_box hm

end

end ArtinKP.B1
end

section
-- module Solutions.Artin.KP.S_Twisted
attribute [-instance] _root_.ArtinKP.F.instAddCommMonoidTSection _root_.ArtinKP.N2.levelGroup_finiteIndex _root_.ArtinKP.S.GSection.instAdd _root_.ArtinKP.S.GSection.instAddCommMonoid _root_.ArtinKP.S.GSection.instCoeFunForallComplexForallForall _root_.ArtinKP.S.GSection.instSMulComplex _root_.ArtinKP.S.GSection.instZero _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
attribute [-simp] _root_.ArtinKP.G1.scal_apply _root_.ArtinKP.RO.rowClassEquiv_mk _root_.ArtinKP.RO.rowPair_c _root_.ArtinKP.RO.rowPair_d _root_.ArtinKP.S.GSection.add_apply _root_.ArtinKP.S.GSection.nT_apply _root_.ArtinKP.S.GSection.smulFun_apply _root_.ArtinKP.S.GSection.smul_apply _root_.ArtinKP.S.GSection.twist_apply _root_.ArtinKP.S.GSection.zero_apply _root_.ArtinKP.S2.cubicSymbol_sym
/-!
# WP-S, part 3: twisted sections on primitive rows

A *twisted section* (`TSection`) is MATH2's `Ψ_s = κ·Φ_s` restricted to primitive pairs of `R`:
a family `Ψ : ℂ → Row 𝔪 → ℂ`, entire in `s`, with

* `hom`: `Ψ_s(εp) = |ε|_{S_f}^{-s} Ψ_s(p)` for `ε ∈ U_S` (**no symbol**: the factor `⟨c, ε⟩` of the
  genuine section is cancelled by `κ(εp) = ⟨c, ε⟩⁻¹ κ(p)`, `kappaRow_smul`);
* `bound`: `|Ψ_s(p)| ≤ B ‖p‖^{-Re s}`, `B` uniform for `|s| ≤ M`;
* `level`: `Ψ_s(pγ) = κ(γ) Ψ_s(p)` for `γ ∈ Γ(𝔫)`, some `𝔫 ≠ 0`.

`SL₂(R)` acts by plain right translation (`TSection.translate`), with no cocycle; the
Eisenstein series `E_Ψ(P, s) = Σ_{p ∈ Row/U_S} Ψ_s(p) I_p(P)^s` then satisfies
`E_Ψ(γP) = E_{γ·Ψ}(P)` by reindexing `p ↦ pγ`.
-/

set_option autoImplicit false

open NumberField IsDedekindDomain ArtinPrimitiveRoots

noncomputable section

namespace ArtinKP.S

open ArtinKP.A

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}

/-! ### Comparison of norms -/

/-! ### Twisted sections -/

namespace TSection

variable {ι : F →+* ℂ}

section translate

variable (P : CubicPkg F) (hG : Good 𝔪) {z6 : 𝓞 F} (hz6 : IsPrimitiveRoot z6 6)

theorem translate_mul (σ₁ σ₂ : Matrix.SpecialLinearGroup (Fin 2) (SInt 𝔪)) (Ψ : TSection ι 𝔪) :
    translate P hG hz6 (σ₁ * σ₂) Ψ = translate P hG hz6 σ₁ (translate P hG hz6 σ₂ Ψ) := by
  ext s p; simp [Row.act_mul]

end translate

end TSection

/-! ### `Ψ ↦ Ψ · 1[P ∤ c]` for an exterior prime -/

end ArtinKP.S
end
end

section
-- module Solutions.Artin.KP.B_Def2
attribute [-instance] _root_.ArtinKP.F.instAddCommMonoidTSection _root_.ArtinKP.N2.levelGroup_finiteIndex _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-!
# WP-B0, part 2: regularity, automorphy, the term at `(0, 1)`

* `continuousOn_eis`: joint continuity of `(s, Q) ↦ E_Ψ(Q, s)` on `{Re s > 2} × X`;
  `continuous_eis`, `measurable_eis` (in `Q`); `differentiableOn_eis` (holomorphy in `s`).
* `eis_smul`: `E_Ψ(γ • Q) = E_{γ⁻¹·Ψ}(Q)` for `γ ∈ SL₂(R)` (the action on `X` through `toF 𝔪`),
  equivalently `eis_translate`: `E_{γ·Ψ}(Q) = E_Ψ(γ⁻¹ • Q)`.
* `TSection.stab Ψ`, `eis_smul_of_mem_stab`; `exists_level_eis`, `exists_level_eis_invariant`.
* `eis_eq_add`: `E_Ψ = Ψ_s(0,1) ht^s + ∑_{q ≠ ∞} Ψ̃_s(q) ht_q^s`.
-/

set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

open scoped MatrixGroups
open NumberField IsDedekindDomain ArtinPrimitiveRoots

noncomputable section

namespace ArtinKP.B

open ArtinKP.A ArtinKP.S ArtinKP.X ArtinKP.B1

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)} {ι : F →+* ℂ}

/-! ### Local compactness of `X` -/

/-! ### Regularity of the summands -/

/-! ### Automorphy by reindexing -/

theorem _root_.ArtinKP.S.TSection.mem_stab {Ψ : TSection ι 𝔪} {γ : SL(2, SInt 𝔪)} :
    γ ∈ Ψ.stab ↔ ∀ (s : ℂ) (p : Row 𝔪), Ψ s (p.act γ) = Ψ s p := Iff.rfl

/-! ### The term at the class of `(0, 1)` -/

end ArtinKP.B
end
end

section
-- module Solutions.Artin.KP.X_L2
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-! # WP-X, file 7: `L²` of the quotient and local restriction maps (abstract)

For a partition of unity `η` and a measurable set `B` meeting each orbit at most `m < ∞` times,
pulling back and restricting is a bounded operator
`restrictL2 : L²(G \ α) →L[ℂ] L²(B, μ)` of norm `≤ √m`.  Every functional
`u ↦ ∫_B conj ψ · u` with `ψ ∈ L²(B)` is therefore continuous on `L²(G \ α)`
(`pairingL2`).  This is the continuity of Fourier-coefficient functionals (MATH (C6)).
-/

open scoped ENNReal ComplexConjugate InnerProductSpace
open MeasureTheory Set

set_option linter.unusedSectionVars false

namespace ArtinKP.X

noncomputable section

variable {G α : Type*} [Group G] [Countable G] [MeasurableSpace α] [MulAction G α]
  [MeasurableConstSMul G α] {μ : Measure α} [SMulInvariantMeasure G α μ] {η : α → ℝ≥0∞}

lemma coeFn_restrictL2 (hη : IsPOU G η) {B : Set α} (hB : MeasurableSet B) {m : ℝ≥0∞}
    (hmtop : m ≠ ⊤) (hm : ∀ a, ∑' g : G, B.indicator (fun _ => (1 : ℝ≥0∞)) (g • a) ≤ m)
    (u : Lp ℂ 2 (quotMeasure G η μ)) :
    restrictL2 hη hB hmtop hm u =ᵐ[μ.restrict B] liftQ u :=
  MemLp.coeFn_toLp (memLp_liftQ_restrict hη hB hmtop hm u)

end

end ArtinKP.X
end

section
-- module Solutions.Artin.KP.X_Fourier
attribute [-instance] _root_.ArtinKP.B1.instCountableSubtypeForallInfinitePlaceComplexMemAddSubgroupLatSub _root_.ArtinKP.N.instCountableSubtypeForallInfinitePlaceComplexMemAddSubgroupLatN _root_.ArtinKP.T.instCountableSubtypeForallInfinitePlaceComplexMemAddSubgroupMinLatN _root_.ArtinKP.T.instCountableSubtypeForallInfinitePlaceComplexMemAddSubgroupMinLatNTransLat _root_.ArtinKP.X.instContinuousConstSMulSubgroup _root_.ArtinKP.X.instIsFiniteMeasureOnCompactsXVol _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
attribute [-simp] _root_.ArtinKP.FB.v_gmap _root_.ArtinKP.FB.x_gmap _root_.ArtinKP.X.chart1_symm_fst _root_.ArtinKP.X.chart1_symm_snd _root_.ArtinKP.X.chart1_v _root_.ArtinKP.X.chart1_x _root_.ArtinKP.X.chart_apply _root_.ArtinKP.X.chart_symm_apply
/-! # WP-X, file 9: local restriction and coefficient functionals on `L²(Γ\X)`

* `X.vol_box_lt_top`: boxes have finite measure;
* `X.restrictBox Γ n : L²(Γ\X) →L[ℂ] L²(box n)`, bounded;
* `X.coeffFunctional Γ n ψ … : L²(Γ\X) →L[ℂ] ℂ`, `u ↦ ∫_{box n} conj ψ · u`, for bounded measurable
  `ψ`.  The Fourier-coefficient functional `ℓ_{ν,φ}` of MATH (C6) is the case
  `ψ(P) = 1_D(x) · conj(e_∞(-ν x) φ(v))` with `D` a fundamental set of the translation lattice
  and `supp φ` compact (so that `D × supp φ` lies in a box).
-/

open scoped MatrixGroups ComplexConjugate ENNReal
open MeasureTheory Set NumberField

set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.X

noncomputable section

variable {F : Type*} [Field F] [NumberField F]

lemma X.stronglyMeasurable_lift (Γ : Subgroup (SL(2, 𝓞 F))) (u : X.L2 Γ) :
    StronglyMeasurable (X.lift Γ u) :=
  haveI _iCSL := ArtinKP.X.instCountableSLInt (F := F)
  stronglyMeasurable_liftQ u

lemma X.coeFn_restrictBox (Γ : Subgroup (SL(2, 𝓞 F))) (n : ℕ) (u : X.L2 Γ) :
    X.restrictBox Γ n u =ᵐ[(X.vol F).restrict (X.box n)] X.lift Γ u :=
  haveI _iCSL := ArtinKP.X.instCountableSLInt (F := F)
  coeFn_restrictL2 _ _ _ _ u

lemma X.coeFn_boxLp (n : ℕ) (ψ : X F → ℂ) (hψ : Measurable ψ) (C : ℝ) (hC : ∀ P, ‖ψ P‖ ≤ C) :
    X.boxLp n ψ hψ C hC =ᵐ[(X.vol F).restrict (X.box n)] ψ :=
  MemLp.coeFn_toLp _

theorem X.coeffFunctional_apply (Γ : Subgroup (SL(2, 𝓞 F))) (n : ℕ) (ψ : X F → ℂ)
    (hψ : Measurable ψ) (C : ℝ) (hC : ∀ P, ‖ψ P‖ ≤ C) (u : X.L2 Γ) :
    X.coeffFunctional Γ n ψ hψ C hC u = ∫ P in X.box n, conj (ψ P) * X.lift Γ u P ∂X.vol F := by
  unfold X.coeffFunctional
  rw [ContinuousLinearMap.comp_apply, innerSL_apply_apply, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [X.coeFn_restrictBox Γ n u, X.coeFn_boxLp n ψ hψ C hC] with P h1 h2
  rw [h1, h2]
  simp [mul_comm]

end

end ArtinKP.X
end

section
-- module Solutions.Artin.KP.X2_H1
attribute [-instance] _root_.ArtinKP.B1.instCountableSubtypeForallInfinitePlaceComplexMemAddSubgroupLatSub _root_.ArtinKP.N.instCountableSubtypeForallInfinitePlaceComplexMemAddSubgroupLatN _root_.ArtinKP.T.instCountableSubtypeForallInfinitePlaceComplexMemAddSubgroupMinLatN _root_.ArtinKP.T.instCountableSubtypeForallInfinitePlaceComplexMemAddSubgroupMinLatNTransLat _root_.ArtinKP.X.instContinuousConstSMulSubgroup _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-! # WP-X2, file 5: the geometric core and the energy space `H¹(Γ \ X)`

* `X.toL2 Γ f h : L²(Γ\X)` — the class of a measurable `Γ`-invariant function that is square
  integrable modulo `Γ` (`X.L2Rep Γ f`), with `X.inner_toL2`, `X.norm_sq_toL2`;
* `X.core Γ` — the functions `∑_{γ ∈ Γ} φ ∘ γ`, `φ ∈ C_c^∞(X)` (equivalently: smooth,
  `Γ`-invariant, support compact modulo `Γ`; see `X.mem_core_of_tsupport` in `X2_Weak`);
* `X.symmOp Γ : SymmOp (L²(Γ\X))` — the Laplacian on the core: dense domain, symmetric,
  nonnegative, with `⟪w, Δw⟫ = ∫_{Γ\X} ∑_w v_w² |∇_w w|²` (`X.inner_coreL2_coreLap_self`);
* `X.H1 Γ`, `X.energy Γ : CAbs.EnergySpace (X.H1 Γ) (X.L2 Γ)`.
-/

open scoped MatrixGroups ComplexConjugate ENNReal Topology InnerProductSpace
open MeasureTheory Set NumberField Filter

set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.X

noncomputable section

open Classical

variable {F : Type*} [Field F] [NumberField F] (Γ : Subgroup (SL(2, 𝓞 F)))

/-! ### Classes of invariant functions -/

variable {Γ}

variable (Γ)

variable {Γ}

variable (Γ)

variable {Γ}

/-- An element of `L²(Γ\X)` whose pull-back vanishes almost everywhere is zero. -/
lemma X.eq_zero_of_lift_ae_eq_zero (v : X.L2 Γ) (h : X.lift Γ v =ᵐ[X.vol F] 0) : v = 0 := by
  haveI _iCSL := ArtinKP.X.instCountableSLInt (F := F)
  rw [Lp.eq_zero_iff_ae_eq_zero]
  have hm : MeasurableSet {q : Quotient (MulAction.orbitRel Γ (X F)) | v q = (0 : ℂ)} :=
    (Lp.stronglyMeasurable v).measurable (measurableSet_singleton 0)
  have key : ∀ᵐ q ∂(Measure.map (Quotient.mk (MulAction.orbitRel Γ (X F)))
      ((X.vol F).withDensity (X.pou Γ))),
      q ∈ {q : Quotient (MulAction.orbitRel Γ (X F)) | v q = (0 : ℂ)} :=
    (ae_map_iff measurable_mk.aemeasurable hm).2
      ((withDensity_absolutelyContinuous _ _).ae_le h)
  exact key

/-! ### Local integrability of pull-backs -/

/-! ### The core -/

/-! ### Density of the core -/

/-! ### The symmetric operator and the energy space -/

end

end ArtinKP.X
end

section
-- module Solutions.Artin.KP.C5_Main
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-! # WP-C5, file 5: (C5), the continuation and the limit (C7)

`Γ ≤ SL₂(𝓞_F)` of finite index, `Ψ` a twisted section with `Inv Γ Ψ`, `hG : Good 𝔪`.

* `srcL2 Γ Ψ s = [F_s]`, `uL2 Γ Ψ s = [u_s]` in `X.L2 Γ` (total functions: `0` when the
  representative is not square integrable); `differentiable_srcL2`: `s ↦ [F_s]` is **entire**.
* `Omega = {s | λ(s) ∉ [0, ∞)} = {Re s ≠ 1} ∖ [0, 2]` (`lam_mem_resolventDomain_iff`),
  `slit_subset_Omega`.
* `resPart Γ Ψ s = −Res(λ(s)) [F_s]`; **(C5)** `uL2_eq_resPart : [u_s] = −Res(λ(s))[F_s]` for
  `Re s > 2` (given D1 = `EisEigen Ψ s`); `differentiableOn_resPart`: holomorphic on `Omega`.
* `Eext Γ Ψ s = h_s + lift (resPart Γ Ψ s)`: the continued series; `Eext_ae_eq`.
* **(C7)** `theta Γ Ψ = −c₀ • P_{λ₀}[F_{4/3}]`, `c₀ = 3/(2r)`, `λ₀ = 8r/9`;
  `tendsto_ray_resPart`: `(s_t − s₀) • resPart(s_t) → θ` along `s_t = 4/3 + t(1 + i)`;
  `exists_isWeakEigen_theta`, `inner_coreLap_theta`, `proj_theta`.
-/

open scoped MatrixGroups ComplexConjugate ENNReal Topology InnerProductSpace
open MeasureTheory Set NumberField Filter IsDedekindDomain

set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.C5

open ArtinKP.A ArtinKP.S ArtinKP.X ArtinKP.B1 ArtinKP.B ArtinKP.CAbs

noncomputable section

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)} {ι : F →+* ℂ}

/-! ### The eigenvalue function -/

/-- The slit half-plane of `E_Model` lies in the resolvent region. -/
theorem slit_subset_Omega : E.slit ⊆ Omega := fun _ hs =>
  ⟨ne_of_gt hs.1, fun h0 => Or.inr (hs.2 h0)⟩

/-! ### The classes in `L²(Γ\X)` -/

/-! ### (C5) -/

/-! ### Continuation -/

/-! ### The limit (C7) -/

/-! ### `θ` is a weak eigenfunction -/

end

end ArtinKP.C5
end

section
-- module Solutions.Artin.KP.S_Ops
attribute [-instance] _root_.ArtinKP.N2.levelGroup_finiteIndex _root_.ArtinKP.S.GSection.instAddCommMonoid _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
attribute [-simp] _root_.ArtinKP.G1.scal_apply _root_.ArtinKP.S2.cubicSymbol_sym
/-!
# WP-S, part 5: operations on genuine sections

* `GSection.nT t`: `(n(t)Φ)_s(c, d) = Φ_s(c, d + ct)`, `t ∈ F` (no symbol).
* `wFun`: `(wΦ)_s(c, d) = ⟨c, d⟩ Φ_s(d, -c)`; `twist_wFun`: its twist is the `w`-translate of the
  twist of `Φ` (MATH §5.2; the symbol is `σ_S((c,d), w)⁻¹·κ(w) = ⟨c, d⟩`).
* `GSection.torus β`: `(A(β)Φ)_s(c, d) = ⟨c, β⟩² Φ_s(β²c, βd)` for `c ≠ 0`, and
  `⟨d, β⟩ Φ_s(0, βd)` on the cell `c = 0` (MATH2 §6.1, with the `c = 0` factor decided by proof);
  `GSection.torusT β = |β|^{2s-1} A(β)` is `Ã(β)`.
  `torus_torus`: `A(β) A(β') = ⟨β, β'⟩ A(β β')`.
* `GSection.sharp π`: `Φ♯_s(c, d) = Φ_s(c, d/π³)`.
-/

set_option autoImplicit false

open NumberField IsDedekindDomain ArtinPrimitiveRoots

noncomputable section

namespace ArtinKP.S

open ArtinKP.A

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}

/-! ### The Weyl element -/

/-! ### The formal torus action `A(β)` -/

namespace GSection

variable {ι : F →+* ℂ} {P : CubicPkg F}

theorem torus_apply (hG : Good 𝔪) (β : F) (hβ : β ≠ 0) (Φ : GSection ι P 𝔪) (s : ℂ) (c d : F) :
    Φ.torus hG β hβ s c d = tf ι P 𝔪 β c d * Φ s (β ^ 2 * c) (β * d) := rfl

/-- `A(β) A(β') = ⟨β, β'⟩ A(β β')` (MATH2 Lemma 6.1 (ii)); in particular the `Ã(β)` commute up to
`⟨β, β'⟩²`. -/
theorem torus_torus (hG : Good 𝔪) (β β' : F) (hβ : β ≠ 0) (hβ' : β' ≠ 0) (Φ : GSection ι P 𝔪) :
    (Φ.torus hG β' hβ').torus hG β hβ
      = brk ι P 𝔪 β β' • Φ.torus hG (β * β') (mul_ne_zero hβ hβ') := by
  ext s c d
  rw [smul_apply, torus_apply, torus_apply, torus_apply]
  have e1 : β' ^ 2 * (β ^ 2 * c) = (β * β') ^ 2 * c := by ring
  have e2 : β' * (β * d) = β * β' * d := by ring
  rw [e1, e2]
  by_cases h0 : c = 0 ∧ d = 0
  · obtain ⟨rfl, rfl⟩ := h0
    simp [Φ.zero]
  have hcd : c ≠ 0 ∨ d ≠ 0 := by
    by_contra h; rw [not_or, not_not, not_not] at h; exact h0 h
  have key : tf ι P 𝔪 β c d * tf ι P 𝔪 β' (β ^ 2 * c) (β * d)
      = brk ι P 𝔪 β β' * tf ι P 𝔪 (β * β') c d := by
    by_cases hc : c = 0
    · have hd : d ≠ 0 := hcd.resolve_left (not_not.mpr hc)
      rw [hc, mul_zero, tf, if_pos rfl, tf, if_pos rfl, tf, if_pos rfl, brk_mul_left _ hβ hd,
        brk_mul_right _ hβ hβ']
      ring
    · have hW := brk_pow_three (ι := ι) (P := P) (𝔪 := 𝔪) β β'
      rw [tf, if_neg hc, tf, if_neg (mul_ne_zero (pow_ne_zero 2 hβ) hc), tf, if_neg hc,
        brk_mul_left _ (pow_ne_zero 2 hβ) hc, pow_two β, brk_mul_left _ hβ hβ,
        brk_mul_right _ hβ hβ']
      linear_combination (brk ι P 𝔪 β β' * brk ι P 𝔪 c β ^ 2 * brk ι P 𝔪 c β' ^ 2) * hW
  linear_combination (Φ s ((β * β') ^ 2 * c) (β * β' * d)) * key

end GSection

end ArtinKP.S
end
end

section
-- module Solutions.Artin.KP.RF_Fourier
attribute [-instance] _root_.ArtinKP.B1.instDiscreteTopologySubtypeE₂MemSubmoduleIntPairLattice _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-!
# WP-RF, part 4: Fourier series along `x` on `Γ\X` (stub S1 of WP-X)

Setting of WP-X "Remaining stubs": `F` totally complex, `Γ ≤ SL(2,𝓞_F)` containing the
translations `n(β)`, `β ∈ 𝔫`; `Λ = {GammaN.shift γ}` the translation lattice in `ι → ℂ`;

* `pair ν x = Σ_w Re(ν_w x_w)`, `eChar ν x = exp(2πi · pair ν x)`,
  `dualLat Γ = {ν | pair ν λ ∈ ℤ for all λ ∈ Λ}`;
* `stripFn D ν φ P = 1_D(P.x) · e_ν(P.x) · φ(P.v)`, the function `ψ` of
  `X.coeffFunctional Γ n ψ …` for the `(ν, φ)`-Fourier coefficient;
* `exists_latBasis`: a basis of `ι → ℂ` whose `ℤ`-span is `Λ`; the characters `chi bV m` of
  `RF_Torus` are the `eChar ν`, `ν ∈ dualLat Γ` (`exists_dual_of_chi`);
* **`eq_zero_of_coeff`** (S1 (b)): `u : X.L2 Γ` with all coefficient functionals zero is zero;
* `ae_eq_zero_of_strip`: the same for any measurable `GammaN Γ`-invariant function which is
  square integrable on boxes.
-/

open scoped MatrixGroups ComplexConjugate ENNReal
open MeasureTheory Set NumberField

set_option linter.dupNamespace false
set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace ArtinKP.RF

open ArtinKP.X

noncomputable section

variable {F : Type*} [Field F] [NumberField F]

/-! ### The pairing and the characters -/

/-! ### A basis of the translation lattice -/

lemma toMixed_shift [IsTotallyComplex F] {Γ : Subgroup (SL(2, 𝓞 F))} (γ : GammaN Γ) :
    toMixed F (GammaN.shift γ) = GammaN.mixed Γ (Additive.ofMul γ) := by
  have h := toMixed_add_shift (Γ := Γ) (0 : InfinitePlace F → ℂ) γ
  simp only [Pi.zero_apply, zero_add, map_zero, add_zero] at h
  exact h

open Classical in
theorem exists_latBasis [IsTotallyComplex F] (Γ : Subgroup (SL(2, 𝓞 F)))
    (h𝔫 : ∃ 𝔫 : Ideal (𝓞 F), 𝔫 ≠ ⊥ ∧
      ∀ β ∈ 𝔫, ∃ γ : GammaN Γ, ((γ : Γ) : SL(2, 𝓞 F)) 0 1 = β) :
    ∃ (d : ℕ) (bV : Module.Basis (Fin d) ℝ (InfinitePlace F → ℂ)), IsLatBasis Γ bV := by
  have := GammaN.isZLattice h𝔫
  set e : (InfinitePlace F → ℂ) ≃L[ℝ] mixedEmbedding.mixedSpace F :=
    (toMixed F).toContinuousLinearEquiv with he
  set L : Submodule ℤ (InfinitePlace F → ℂ) :=
    ZLattice.comap ℝ (E := mixedEmbedding.mixedSpace F) (GammaN.lattice Γ) e.toLinearMap with hL
  have hmem : ∀ x, x ∈ L ↔ ∃ γ : GammaN Γ, x = GammaN.shift γ := by
    intro x
    have h1 : x ∈ L ↔ toMixed F x ∈ GammaN.lattice Γ := Iff.rfl
    rw [h1, GammaN.mem_lattice]
    constructor
    · rintro ⟨γa, hγ⟩
      refine ⟨Additive.toMul γa, (toMixed F).injective ?_⟩
      rw [toMixed_shift, ofMul_toMul, hγ]
    · rintro ⟨γ, rfl⟩
      exact ⟨Additive.ofMul γ, (toMixed_shift γ).symm⟩
  have : Module.Free ℤ L := ZLattice.module_free ℝ L
  have : Module.Finite ℤ L := ZLattice.module_finite ℝ L
  let b0 := (Module.Free.chooseBasis ℤ L).reindex (Fintype.equivFin _)
  refine ⟨_, b0.ofZLatticeBasis ℝ L, fun x => ?_⟩
  rw [b0.ofZLatticeBasis_span ℝ, hmem]

end

end ArtinKP.RF
end

section
-- module Solutions.Artin.KP.N_Shape
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-! # WP-N, file 2: the shape of the constant term of `E_Ψ` at `∞` for `Re s > 2` (MATH2 §2.1(b))

* `Cell Γ D n₀`: `D` is a measurable fundamental domain of the translation lattice of `Γ`, contained
  in `{‖x_w‖ ≤ n₀}`.  `Cell.of_hfund` converts from the form used by WP-X/WP-RF (`hfund`);
  `exists_cell` gives one for every `Γ` of finite index.
* `cf D n φ f = ∫_{box n} conj (1_D(x) φ(v)) f`: the constant-term functional (it is
  `X.coeffFunctional Γ n (RF.stripFn D 0 φ) …` on `L²(Γ\X)`, `coeffFunctional_eq_cf`).
* `mD D Ψ s = vol(D)⁻¹ ∫_D tail Ψ s (x, 1) dx`: the coefficient of `ht^{2−s}`.
* **`cf_eis`**: for `Re s > 2`, `n ≥ n₀`,
  `cf D n φ (E_Ψ(·,s)) = Ψ_s(0,1) · cf D n φ (ht^s) + mD D Ψ s · cf D n φ (ht^{2−s})`.
-/

open scoped MatrixGroups ComplexConjugate ENNReal Topology
open MeasureTheory Set NumberField Filter IsDedekindDomain ArtinPrimitiveRoots

set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.N

open ArtinKP.A ArtinKP.S ArtinKP.X ArtinKP.B1 ArtinKP.B ArtinKP.C5 ArtinKP.K ArtinKP.RF

noncomputable section

variable {F : Type*} [Field F] [NumberField F] [IsTotallyComplex F] {𝔪 : Ideal (𝓞 F)}
  {ι : F →+* ℂ} {Γ : Subgroup (SL(2, 𝓞 F))}

/-! ### Cells -/

/-! ### The constant-term functional -/

/-! ### Fubini: a function with vanishing `x`-integrals over `D` is killed by `cf` -/

/-! ### The shape -/

lemma isCompact_box (n : ℕ) : IsCompact (X.box n : Set (X F)) :=
  isCompact_siegelBox (F := F) (m := 1 / ((n : ℝ) + 1)) (M := (n : ℝ) + 1) (B := n)
    (by positivity)

end

end ArtinKP.N
end

section
-- module Solutions.Artin.KP.N_Cont
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-! # WP-N, file 3: coefficients of `θ_Ψ` from continuations (MATH2 §2.1(c),(d); item 5)

* `differentiableAt_setIntegral`: a bounded holomorphic family integrates to a holomorphic function
  over a set of finite measure.
* `hInt Ψ n ψ s = ∫_{box n} conj ψ · h_s` is entire (`differentiable_hInt`).
* **`coeff_theta_of_continuation`** (all frequencies): if `a` is holomorphic on `E.slit`, equals
  `∫_{box n} conj ψ · E_Ψ(·, s)` for `Re s > 2`, and `(s_t − s₀) a(s_t) → r` along C5's ray, then
  `∫_{box n} conj ψ · θ_Ψ = r`.
* **`cf_theta_of_continuation`** (frequency `0`, MATH2 §2.1(d)): if `m'` is holomorphic on `E.slit`,
  equals `mD D Ψ` for `Re s > 2` and `(s_t − s₀) m'(s_t) → z`, then
  `cf D n φ (θ_Ψ) = z · cf D n φ (ht^{2/3})` for all `(n, φ)`.

`EisEigen Ψ s` (owner WP-RF) enters as the hypothesis `hE : ∀ s, 2 < s.re → EisEigen Ψ s`.
-/

open scoped MatrixGroups ComplexConjugate ENNReal Topology
open MeasureTheory Set NumberField Filter IsDedekindDomain ArtinPrimitiveRoots Metric

set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.N

open ArtinKP.A ArtinKP.S ArtinKP.X ArtinKP.B1 ArtinKP.B ArtinKP.C5 ArtinKP.K ArtinKP.RF

noncomputable section

/-! ### Holomorphic dependence of integrals on a parameter -/

/-! ### The ray and the slit -/

lemma continuous_ray : Continuous ray := by unfold ray; fun_prop

lemma tendsto_ray : Tendsto ray (𝓝[>] 0) (𝓝 (4 / 3)) := by
  have h := continuous_ray.tendsto 0
  have h0 : ray 0 = 4 / 3 := by simp [ray]
  rw [h0] at h
  exact h.mono_left nhdsWithin_le_nhds

lemma tendsto_ray_mul_zero {g : ℂ → ℂ} (hg : ContinuousAt g (4 / 3)) :
    Tendsto (fun t : ℝ => ((t : ℂ) * (1 + Complex.I)) * g (ray t)) (𝓝[>] 0) (𝓝 0) := by
  have h1 : Tendsto (fun t : ℝ => ((t : ℂ) * (1 + Complex.I))) (𝓝[>] 0) (𝓝 0) := by
    have hc : Continuous fun t : ℝ => ((t : ℂ) * (1 + Complex.I)) := by fun_prop
    have h := hc.tendsto 0
    simp only [Complex.ofReal_zero, zero_mul] at h
    exact h.mono_left nhdsWithin_le_nhds
  have h2 := hg.tendsto.comp tendsto_ray
  simpa using h1.mul h2

variable {F : Type*} [Field F] [NumberField F] [IsTotallyComplex F] {𝔪 : Ideal (𝓞 F)}
  {ι : F →+* ℂ} {Γ : Subgroup (SL(2, 𝓞 F))}

/-! ### The cut-off part against a bounded test function -/

lemma integrableOn_bdd_mul {n : ℕ} {ψ : X F → ℂ} (hψ : Measurable ψ) {C : ℝ}
    (hC : ∀ P, ‖ψ P‖ ≤ C) {f : X F → ℂ} (hf : IntegrableOn f (X.box n) (X.vol F)) :
    IntegrableOn (fun P => conj (ψ P) * f P) (X.box n) (X.vol F) := by
  refine Integrable.bdd_mul (c := C) hf
    (Complex.continuous_conj.measurable.comp hψ).aestronglyMeasurable ?_
  exact Eventually.of_forall fun P => by rw [RCLike.norm_conj]; exact hC P

/-! ### Coefficients of `θ_Ψ` from a continuation (all test functions) -/

/-! ### Frequency `0`: the residue of the `ht^{2−s}`-coefficient -/

end

end ArtinKP.N
end

section
-- module Solutions.Artin.KP.N_Level
attribute [-instance] _root_.ArtinKP.F.instAddCommMonoidTSection _root_.ArtinKP.N2.levelGroup_finiteIndex _root_.ArtinKP.T.instCountableSubtypeForallInfinitePlaceComplexMemAddSubgroupMinLatN _root_.ArtinKP.T.instCountableSubtypeForallInfinitePlaceComplexMemAddSubgroupMinLatNTransLat _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
attribute [-simp] _root_.ArtinKP.FB.v_gmap _root_.ArtinKP.FB.x_gmap
/-! # WP-N, file 5: `θ_Ψ` under change of `Γ` and under `SL₂(R)` (C5's open item 3; MATH2 §2.1 end)

* `ae_eq_zero_of_box_tests`: a locally integrable function killed by all bounded test functions on
  all boxes vanishes almost everywhere.
* **`lift_theta_of_eis_smul`**: if `E_{Ψ'}(Q, s) = E_Ψ(τQ, s)` for `Re s > 2` (`τ ∈ SL₂(F)`), then
  `θ_{Γ'}(Ψ') = θ_Γ(Ψ) ∘ τ` almost everywhere, for any finite-index `Γ`, `Γ'` fixing `Ψ`, `Ψ'`.
* `lift_theta_congr`: `θ_Γ(Ψ)` does not depend on `Γ` (as a function on `X`, a.e.).
* `lift_theta_translate`: `θ(σ·Ψ)(Q) = θ(Ψ)(σ⁻¹Q)` for `σ ∈ SL₂(R)`.
* `cf_theta_translate`: the constant term of `θ_Ψ` at the cusp `σ⁻¹∞`, i.e. of `Q ↦ θ_Ψ(σ⁻¹Q)` at
  `∞`, is `zRes(σ·Ψ)·ht^{2/3}`.
-/

open scoped MatrixGroups ComplexConjugate ENNReal Topology InnerProductSpace
open MeasureTheory Set NumberField Filter IsDedekindDomain ArtinPrimitiveRoots Metric

set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.N

open ArtinKP.A ArtinKP.S ArtinKP.X ArtinKP.B1 ArtinKP.B ArtinKP.C5 ArtinKP.K ArtinKP.RF

noncomputable section

variable {F : Type*} [Field F] [NumberField F] [IsTotallyComplex F] {𝔪 : Ideal (𝓞 F)}
  {ι : F →+* ℂ}

/-! ### Test functions on boxes -/

lemma integrableOn_lift (Γ : Subgroup (SL(2, 𝓞 F))) (n : ℕ) (u : X.L2 Γ) :
    IntegrableOn (X.lift Γ u) (X.box n) (X.vol F) :=
  haveI _iCSL := ArtinKP.X.instCountableSLInt (F := F)
  (memLp_liftQ_restrict (X.isPOU_pou Γ) (X.measurableSet_box n) (ENNReal.natCast_ne_top _)
    (X.tsum_indicator_box_le_boxMult Γ n) u).integrable one_le_two

lemma iUnion_box : (⋃ n : ℕ, (X.box n : Set (X F))) = univ :=
  eq_univ_of_forall fun P => mem_iUnion.mpr (X.exists_mem_box P)

theorem ae_eq_zero_of_box_tests {g : X F → ℂ} (hg : Measurable g)
    (hint : ∀ n : ℕ, IntegrableOn g (X.box n) (X.vol F))
    (h : ∀ (n : ℕ) (ψ : X F → ℂ), Measurable ψ → (∀ P, ‖ψ P‖ ≤ 1) →
      ∫ P in X.box n, conj (ψ P) * g P ∂X.vol F = 0) : g =ᵐ[X.vol F] 0 := by
  set ψ : X F → ℂ := fun P => g P / ((‖g P‖ : ℝ) : ℂ) with hψ
  have hψm : Measurable ψ := hg.div (Complex.measurable_ofReal.comp hg.norm)
  have hψ1 : ∀ P, ‖ψ P‖ ≤ 1 := fun P => by
    rw [hψ, norm_div, Complex.norm_real, norm_norm]
    exact div_self_le_one _
  have e : ∀ P, conj (ψ P) * g P = ((‖g P‖ : ℝ) : ℂ) := fun P => by
    by_cases h0 : g P = 0
    · simp [hψ, h0]
    · have h1 : ((‖g P‖ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr h0)
      rw [hψ, map_div₀, Complex.conj_ofReal, div_mul_eq_mul_div, Complex.conj_mul']
      field_simp
  have hbox : ∀ n : ℕ, ∀ᵐ P ∂(X.vol F).restrict (X.box n), g P = 0 := by
    intro n
    have h1 := h n ψ hψm hψ1
    simp only [e] at h1
    rw [integral_complex_ofReal, Complex.ofReal_eq_zero,
      integral_eq_zero_iff_of_nonneg (fun P => norm_nonneg _) (hint n).norm] at h1
    filter_upwards [h1] with P hP
    exact norm_eq_zero.mp hP
  have := (ae_restrict_iUnion_iff (fun n : ℕ => (X.box n : Set (X F))) (fun P => g P = 0)).mpr hbox
  rwa [iUnion_box, Measure.restrict_univ] at this

/-! ### Transport of a box integral by `τ ∈ SL₂(F)` -/

lemma measurable_psiT (τ : SL(2, F)) (n : ℕ) {ψ : X F → ℂ} (hψ : Measurable ψ) :
    Measurable (psiT τ n ψ) :=
  (hψ.indicator (X.measurableSet_box n)).comp (measurable_const_smul τ⁻¹)

lemma norm_psiT_le (τ : SL(2, F)) (n : ℕ) {ψ : X F → ℂ} (hψ1 : ∀ P, ‖ψ P‖ ≤ 1) (P : X F) :
    ‖psiT τ n ψ P‖ ≤ 1 := by
  unfold psiT
  by_cases h : τ⁻¹ • P ∈ (X.box n : Set (X F))
  · rw [indicator_of_mem h]; exact hψ1 _
  · rw [indicator_of_notMem h, norm_zero]; exact zero_le_one

theorem exists_setIntegral_box_smul (τ : SL(2, F)) (n : ℕ) (ψ : X F → ℂ) :
    ∃ n' : ℕ, ∀ f : X F → ℂ,
      ∫ Q in X.box n, conj (ψ Q) * f (τ • Q) ∂X.vol F
        = ∫ P in X.box n', conj (psiT τ n ψ P) * f P ∂X.vol F := by
  obtain ⟨n', hn'⟩ := X.exists_box_of_isCompact
    ((isCompact_box (F := F) n).image (continuous_const_smul τ))
  refine ⟨n', fun f => ?_⟩
  have h1 : ∀ Q : X F, (X.box n : Set (X F)).indicator (fun Q => conj (ψ Q) * f (τ • Q)) Q
      = (fun P => conj (psiT τ n ψ P) * f P) (τ • Q) := by
    intro Q
    simp only [psiT, inv_smul_smul]
    by_cases hQ : Q ∈ (X.box n : Set (X F))
    · rw [indicator_of_mem hQ, indicator_of_mem hQ]
    · rw [indicator_of_notMem hQ, indicator_of_notMem hQ]; simp
  rw [← integral_indicator (X.measurableSet_box n), integral_congr_ae (Eventually.of_forall h1)]
  refine ((measurePreserving_smul τ).integral_comp (MeasurableEquiv.smul τ).measurableEmbedding
    (fun P => conj (psiT τ n ψ P) * f P)).trans ?_
  refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun P hP => ?_).symm
  have h2 : τ⁻¹ • P ∉ (X.box n : Set (X F)) := fun hmem =>
    hP (hn' ⟨τ⁻¹ • P, hmem, smul_inv_smul τ P⟩)
  simp [psiT, indicator_of_notMem h2]

lemma integrableOn_comp_smul (τ : SL(2, F)) (n : ℕ) {u : X F → ℂ}
    (hu : ∀ n : ℕ, IntegrableOn u (X.box n) (X.vol F)) :
    IntegrableOn (fun Q => u (τ • Q)) (X.box n) (X.vol F) := by
  obtain ⟨n', hn'⟩ := X.exists_box_of_isCompact
    ((isCompact_box (F := F) n).image (continuous_const_smul τ))
  have hK : MeasurableSet ((fun Q : X F => τ • Q) '' (X.box n : Set (X F))) :=
    ((isCompact_box (F := F) n).image (continuous_const_smul τ)).measurableSet
  have h1 : Integrable (((fun Q : X F => τ • Q) '' (X.box n : Set (X F))).indicator u)
      (X.vol F) :=
    ((hu n').mono_set hn').integrable_indicator hK
  have h2 := ((measurePreserving_smul τ).integrable_comp_emb
    (MeasurableEquiv.smul τ).measurableEmbedding).mpr h1
  rw [← integrable_indicator_iff (X.measurableSet_box n)]
  refine h2.congr (Eventually.of_forall fun Q => ?_)
  simp only [Function.comp_apply]
  by_cases hQ : Q ∈ (X.box n : Set (X F))
  · rw [indicator_of_mem hQ, indicator_of_mem (mem_image_of_mem _ hQ)]
  · rw [indicator_of_notMem hQ, indicator_of_notMem]
    rintro ⟨Q', hQ', hQQ⟩
    exact hQ (by rwa [← smul_left_cancel τ hQQ])

/-! ### `θ` under a transformation of the series -/

/-- **Compatibility of `θ`**: if the series of `Ψ'` is the series of `Ψ` transported by
`τ ∈ SL₂(F)`, then so are the residues, whatever the groups used to define them. -/
theorem lift_theta_of_eis_smul (hG : Good 𝔪) {Γ Γ' : Subgroup (SL(2, 𝓞 F))} [Γ.FiniteIndex]
    [Γ'.FiniteIndex] {Ψ Ψ' : TSection ι 𝔪} (hΓ : Inv Γ Ψ) (hΓ' : Inv Γ' Ψ')
    (hE : ∀ s : ℂ, 2 < s.re → EisEigen Ψ s) (hE' : ∀ s : ℂ, 2 < s.re → EisEigen Ψ' s)
    (τ : SL(2, F)) (h : ∀ s : ℂ, 2 < s.re → ∀ Q : X F, eis Ψ' s Q = eis Ψ s (τ • Q)) :
    X.lift Γ' (theta Γ' Ψ') =ᵐ[X.vol F] fun Q => X.lift Γ (theta Γ Ψ) (τ • Q) := by
  have hm1 : Measurable (X.lift Γ' (theta Γ' Ψ')) := (X.stronglyMeasurable_lift Γ' _).measurable
  have hm2 : Measurable fun Q => X.lift Γ (theta Γ Ψ) (τ • Q) :=
    (X.stronglyMeasurable_lift Γ _).measurable.comp (measurable_const_smul τ)
  have hi1 := fun n => integrableOn_lift Γ' n (theta Γ' Ψ')
  have hi2 := fun n => integrableOn_comp_smul τ n fun n => integrableOn_lift Γ n (theta Γ Ψ)
  have key := ae_eq_zero_of_box_tests (g := fun Q => X.lift Γ' (theta Γ' Ψ') Q
    - X.lift Γ (theta Γ Ψ) (τ • Q)) (hm1.sub hm2) (fun n => (hi1 n).sub (hi2 n)) ?_
  · filter_upwards [key] with Q hQ
    exact sub_eq_zero.mp hQ
  intro n ψ hψ hψ1
  obtain ⟨n', hn'⟩ := exists_setIntegral_box_smul τ n ψ
  set ψ' := psiT τ n ψ with hψ'
  have hψ'm := measurable_psiT τ n hψ
  have hψ'1 := norm_psiT_le τ n hψ1
  set ℓ := X.coeffFunctional Γ n' ψ' hψ'm 1 hψ'1 with hℓ
  have hH := differentiable_hInt hG.ne_bot Ψ n' hψ'm hψ'1
  have ha : DifferentiableOn ℂ (fun s => ℓ (resPart Γ Ψ s) + hInt Ψ n' ψ' s) E.slit :=
    ((differentiableOn_functional_resPart hG Γ hΓ ℓ).mono slit_subset_Omega).add
      hH.differentiableOn
  have hr : Tendsto (fun t : ℝ => ((t : ℂ) * (1 + Complex.I))
      * (ℓ (resPart Γ Ψ (ray t)) + hInt Ψ n' ψ' (ray t))) (𝓝[>] 0) (𝓝 (ℓ (theta Γ Ψ))) := by
    have h1 := tendsto_ray_functional_resPart_theta hG Γ hΓ ℓ
    have h2 := tendsto_ray_mul_zero (g := hInt Ψ n' ψ') hH.continuous.continuousAt
    have h3 := h1.add h2
    rw [add_zero] at h3
    refine h3.congr fun t => ?_
    simp only [ray]
    ring
  have h1 := integral_box_theta_eq_of_tendsto_ray hG Γ' hΓ' hE' n ψ hψ 1 hψ1 ha (fun s hs => ?_) hr
  · have h2 : ℓ (theta Γ Ψ) = ∫ Q in X.box n, conj (ψ Q) * X.lift Γ (theta Γ Ψ) (τ • Q)
        ∂X.vol F := by
      rw [hℓ, X.coeffFunctional_apply, hn']
    have h3 : ∀ Q : X F, conj (ψ Q) * (X.lift Γ' (theta Γ' Ψ') Q - X.lift Γ (theta Γ Ψ) (τ • Q))
        = conj (ψ Q) * X.lift Γ' (theta Γ' Ψ') Q
          - conj (ψ Q) * X.lift Γ (theta Γ Ψ) (τ • Q) := fun Q => mul_sub _ _ _
    simp only [h3]
    rw [integral_sub (integrableOn_bdd_mul hψ hψ1 (hi1 n)) (integrableOn_bdd_mul hψ hψ1 (hi2 n)),
      h1, h2, sub_self]
  · rw [hℓ, coeff_resPart_add_hInt hG Γ hΓ hs (hE s hs) n' ψ' hψ'm 1 hψ'1, ← hn']
    simp only [h s hs]

/-- **`θ_Γ(Ψ)` does not depend on `Γ`** (C5's open item 3). -/
theorem lift_theta_congr (hG : Good 𝔪) {Γ Γ' : Subgroup (SL(2, 𝓞 F))} [Γ.FiniteIndex]
    [Γ'.FiniteIndex] {Ψ : TSection ι 𝔪} (hΓ : Inv Γ Ψ) (hΓ' : Inv Γ' Ψ)
    (hE : ∀ s : ℂ, 2 < s.re → EisEigen Ψ s) :
    X.lift Γ' (theta Γ' Ψ) =ᵐ[X.vol F] X.lift Γ (theta Γ Ψ) := by
  have := lift_theta_of_eis_smul hG hΓ hΓ' hE hE 1 (fun s _ Q => by rw [one_smul])
  simpa only [one_smul] using this

end

end ArtinKP.N
end

section
-- module Solutions.Artin.KP.S2_Kubota
attribute [-instance] _root_.ArtinKP.N2.levelGroup_finiteIndex _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-!
# WP-S2, part 8: the normalized finite Jacquet functional `Lam` and the laws of `E.Kubota`

`Lam ψ hG Φ c ν s := |c|_{S_f}^s · J_Φ(c; ν, s)`, the functional of WP-S (`S.lam`) taken at a
valid depth; by `jacD_eq_of_le` it does not depend on the valid depth (`Lam_eq_lamD`).

* `Lam_unit` (J1), `Lam_cube` (S1³), `Lam_act` (MATH2 Lemma 6.1 (iii), any frequency),
  `torusT_torusT_inv` and `Lam_act_surj`: the laws required by the interface `E.Kubota`.
* `kubota`: the instance `E.Kubota (cubicSymbol …) (B7.sAdd 𝔪 h𝔪) (GSection ι P 𝔪)` with
  `act β = Ã(β)`, **given** its field `summable` as a hypothesis.
-/

set_option autoImplicit false

open NumberField IsDedekindDomain ArtinPrimitiveRoots

noncomputable section

namespace ArtinKP.S2

open ArtinKP.A ArtinKP.S

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}
variable {ι : F →+* ℂ} {P : CubicPkg F}

theorem Lam_eq_lam (ψ : SfChar 𝔪) (hG : Good 𝔪) (Φ : GSection ι P 𝔪) {ν : F} {M : ℤ}
    (h : Valid ψ Φ ν (fun _ => M)) (c : F) (s : ℂ) :
    Lam ψ hG Φ c ν s = lam ψ M Φ c ν s :=
  Lam_eq_lamD ψ hG Φ h c s

/-! ### The interface `E.Kubota` -/

end ArtinKP.S2
end
end

section
-- module Solutions.Artin.KP.C9_Main
attribute [-instance] _root_.ArtinKP.F.instAddCommMonoidTSection _root_.ArtinKP.N2.levelGroup_finiteIndex _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-!
# WP-C9, part 3: (C10′) in terms of coefficient functionals; a single big cell with `θ ≠ 0`

* **`eq_zero_of_coeff_shape`**: `u ∈ L²(Γ\X)` whose frequency-`0` functionals are those of
  `z·ht^{s₁}` (`Re s₁ ≠ 0`) and whose functionals at all nonzero frequencies of `Λ_Γ^⊥` vanish
  is `0`.
* **`theta_eq_zero_of_coeff`** — (C10′), the core: if all nonzero-frequency coefficient
  functionals of `θ_Ψ` at `∞` vanish, then `θ_Ψ = 0` (and `zRes_eq_zero_of_coeff`: `z_Ψ = 0`).
  Stated for a twisted section `Ψ` and WP-RF's functionals; no dependence on WP-T.
* `lift_zero_ae`, `theta_eq_zero_congr`: `θ_Ψ = 0` does not depend on the group `Γ`.
* `twist_add`, `twist_zero`, `exists_inv_finset`, `theta_sum_eq_zero`: linearity bookkeeping.
* **`exists_theta_bigCell_ne_zero`**: some single big-cell section `Φ^big_η`, `η ∈ T`, has
  `θ ≠ 0` (for every finite-index `Γ` fixing its twist).
-/

open scoped MatrixGroups ComplexConjugate ENNReal Topology
open MeasureTheory Set NumberField Filter IsDedekindDomain ArtinPrimitiveRoots Metric

set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.C9

open ArtinKP.A ArtinKP.S ArtinKP.X ArtinKP.B1 ArtinKP.B ArtinKP.C5 ArtinKP.K ArtinKP.RF ArtinKP.N

noncomputable section

variable {F : Type*} [Field F] [NumberField F] [IsTotallyComplex F] {𝔪 : Ideal (𝓞 F)}
  {ι : F →+* ℂ} {P : CubicPkg F}

/-! ### (C10′), the core -/

/-! ### Independence of `Γ` -/

/-- The pull-back of the zero class vanishes almost everywhere. -/
theorem lift_zero_ae (Γ : Subgroup (SL(2, 𝓞 F))) [Γ.FiniteIndex] :
    X.lift Γ (0 : X.L2 Γ) =ᵐ[X.vol F] 0 := by
  refine ae_eq_zero_of_box_tests (X.stronglyMeasurable_lift Γ 0).measurable
    (fun n => integrableOn_lift Γ n 0) fun n ψ hψ hψ1 => ?_
  rw [← X.coeffFunctional_apply Γ n ψ hψ 1 hψ1 0, map_zero]

/-- `θ_Ψ = 0` for one admissible group implies it for every other. -/
theorem theta_eq_zero_congr (hG : Good 𝔪) {Γ Γ' : Subgroup (SL(2, 𝓞 F))} [Γ.FiniteIndex]
    [Γ'.FiniteIndex] {Ψ : TSection ι 𝔪} (hΓ : Inv Γ Ψ) (hΓ' : Inv Γ' Ψ)
    (h : theta Γ Ψ = 0) : theta Γ' Ψ = 0 := by
  apply X.eq_zero_of_lift_ae_eq_zero
  have h1 := lift_theta_congr hG hΓ hΓ' (fun s hs => GL.eisEigen_of_two_lt_re hG.ne_bot Ψ hs)
  rw [h] at h1
  exact h1.trans (lift_zero_ae Γ)

/-! ### Linearity bookkeeping -/

/-! ### A single big cell -/

end

end ArtinKP.C9
end

section
-- module Solutions.Artin.KP.C9_Tau
attribute [-instance] _root_.ArtinKP.F.instAddCommMonoidTSection _root_.ArtinKP.N2.levelGroup_finiteIndex _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
attribute [-simp] _root_.ArtinKP.G1.scal_apply
/-!
# WP-C9, part 4: (C10′) and (C9) in the vocabulary of WP-T (`T.tau`, `T.theta`)

WP-T's `T.coeff_theta` computes the coefficient functional of `θ_{Φ.twist}` at the frequency
`T.freq ν`, `ν ∈ R ∖ 0` (`R = SInt 𝔪`), as `kap · τ_Φ(ν) · Wc`.  The core lemma
`C9.theta_eq_zero_of_coeff` needs the vanishing at **every** nonzero frequency of WP-RF's dual
lattice `RF.dualLat Γ`.  The bridge is the one named hypothesis of this file:

* `DualCover 𝔪 Γ`: every nonzero `ν' ∈ RF.dualLat Γ` is `T.freq ν` for some `ν ∈ R`.
  (True when `Λ_Γ ⊇ emb(𝔪^N)` — `TransLevel 𝔪 Γ` — and the different of `F` is supported in the
  primes of `𝔪`: trace duality.  Proved in `C9_Dual.lean` / stated in `C9_Stubs.lean`, see
  WP-C9.md.)

Results:

* `stabGroup Ψ` (the full stabilizer of `Ψ` in `SL₂(𝓞)`), finite index, `TransLevel` for twists.
* **`theta_eq_zero_of_tau`** — (C10′) in WP-T's form: `τ_Φ(ν) = 0` for all `ν ∈ R ∖ 0` implies
  `θ_{Φ.twist} = 0`.
* **`exists_tau_sumBig_ne_zero`**, **`exists_tau_bigCell_ne_zero`** — the hypothesis of package
  G (MATH3 §1.2 (G1)): some `τ_{Φ^Σ}(ν₁) ≠ 0`, and some single class `η` with
  `τ_{Φ^big_η}(ν) ≠ 0`.
* `exists_kir_ne_zero_of_theoremE`: given Theorem E in any form `τ_Φ(ν) = c(ν)·𝒦_Φ(ν)`, the
  Kirillov function is not identically zero.
-/

open scoped MatrixGroups ComplexConjugate ENNReal Topology
open MeasureTheory Set NumberField Filter IsDedekindDomain ArtinPrimitiveRoots Metric

set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.C9

open ArtinKP.A ArtinKP.S ArtinKP.X ArtinKP.B1 ArtinKP.B ArtinKP.C5 ArtinKP.K ArtinKP.RF ArtinKP.N

noncomputable section

variable {F : Type*} [Field F] [NumberField F] [IsTotallyComplex F] {𝔪 : Ideal (𝓞 F)}
  {ι : F →+* ℂ} {P : CubicPkg F}

/-! ### The full stabilizer -/

theorem inv_stabGroup (Ψ : TSection ι 𝔪) : Inv (stabGroup Ψ) Ψ := fun _ hγ => hγ

theorem le_stabGroup {Γ : Subgroup (SL(2, 𝓞 F))} {Ψ : TSection ι 𝔪} (hΓ : Inv Γ Ψ) :
    Γ ≤ stabGroup Ψ := fun γ hγ => hΓ γ hγ

theorem stabGroup_finiteIndex (Pk : CubicPkg F) (hG : Good 𝔪) {z6 : 𝓞 F}
    (hz6 : IsPrimitiveRoot z6 6) (Ψ : TSection ι 𝔪) : (stabGroup Ψ).FiniteIndex := by
  obtain ⟨Γ, hfi, hΓ⟩ := exists_finiteIndex_inv Pk hG hz6 Ψ
  exact Subgroup.finiteIndex_of_le (le_stabGroup hΓ)

section twist

variable (hG : Good 𝔪) {z6 : 𝓞 F} (hz6 : IsPrimitiveRoot z6 6)

/-- The level of a twist is a power of `𝔪` (the `level` field of `GSection.twist`, with its
ideal made explicit). -/
theorem exists_twist_level (Φ : GSection ι P 𝔪) :
    ∃ N : ℕ, ∀ γ ∈ Gamma 𝔪 (𝔪 ^ N), ∀ (s : ℂ) (p : Row 𝔪),
      Φ.twist hG hz6 s (p.act γ) = kappa ι 𝔪 γ * Φ.twist hG hz6 s p := by
  obtain ⟨N, hN⟩ := Φ.level
  refine ⟨N, fun γ hγ s p => ?_⟩
  have hK := isK_of_mem_Gamma hγ
  have hc : (((p.act γ).c : SInt 𝔪) : F) = (p.c : F) * ((γ.1 0 0 : SInt 𝔪) : F)
      + (p.d : F) * ((γ.1 1 0 : SInt 𝔪) : F) := by
    rw [Row.act_c]; push_cast; rfl
  have hd : (((p.act γ).d : SInt 𝔪) : F) = (p.c : F) * ((γ.1 0 1 : SInt 𝔪) : F)
      + (p.d : F) * ((γ.1 1 1 : SInt 𝔪) : F) := by
    rw [Row.act_d]; push_cast; rfl
  rw [GSection.twist_apply, GSection.twist_apply, hc, hd, hN _ _ _ _ hK,
    kappaRow_act ι P hG hz6]
  have h0 : sig ι P 𝔪 (p.c : F) (p.d : F) ((γ.1 0 0 : SInt 𝔪) : F) ((γ.1 0 1 : SInt 𝔪) : F)
      ((γ.1 1 0 : SInt 𝔪) : F) ((γ.1 1 1 : SInt 𝔪) : F) ≠ 0 := brk_ne_zero _ _
  field_simp

/-- The stabilizer of a twist contains the translations by `𝔪^N`. -/
theorem transLevel_stabGroup (Φ : GSection ι P 𝔪) :
    TransLevel 𝔪 (stabGroup (Φ.twist hG hz6)) := by
  obtain ⟨N, hN⟩ := exists_twist_level hG hz6 Φ
  refine ⟨N, fun β hβ => ?_⟩
  change RO.intMat 𝔪 (nInt β) ∈ (Φ.twist hG hz6).stab
  rw [TSection.mem_stab]
  intro s p
  have hmem : RO.intMat 𝔪 (nInt β) ∈ Gamma 𝔪 (𝔪 ^ N) := by
    rw [mem_Gamma_iff]
    refine ⟨nInt β, fun i j => ?_, rfl⟩
    fin_cases i <;> fin_cases j <;> simp [nInt_coe, hβ]
  have hk : kappa ι 𝔪 (RO.intMat 𝔪 (nInt β)) = 1 := by
    have h10 : (RO.intMat 𝔪 (nInt β)).1 1 0 = 0 := by
      change algebraMap (𝓞 F) (SInt 𝔪) ((nInt β).1 1 0) = 0
      simp [nInt_coe]
    simp [kappa, h10]
  rw [hN _ hmem, hk, one_mul]

end twist

/-! ### The bridge between the two parametrizations of the frequencies -/

/-! ### (C10′) in WP-T's form -/

/-! ### The hypothesis of package G -/

end

end ArtinKP.C9
end

section
-- module Solutions.Artin.KP.RF_Parseval
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-!
# WP-RF, part 9: Parseval along `x` in the form of WP-X stub S1 (a)

For `g : (ι → ℂ) → ℂ` measurable, periodic under the translation lattice `Λ` of `Γ` and square
integrable on a strict fundamental set `D` of `Λ`:

`∑_{ν ∈ Λ^⊥} |∫_D conj(e_ν) g|² = vol(D) · ∫_D |g|²`   (`parseval_strip`).

The sum is over the subtype `dualLat Γ`; `dualEquiv` identifies it with `ℤ^J` for a lattice basis
(`nuOf bV m` is the frequency with `e_ν = chi bV m`).
-/

open scoped MatrixGroups ComplexConjugate ENNReal
open MeasureTheory Set NumberField

set_option linter.dupNamespace false
set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace ArtinKP.RF

open ArtinKP.X

noncomputable section

variable {F : Type*} [Field F] [NumberField F]

lemma pairLin_apply (ν x : InfinitePlace F → ℂ) : pairLin ν x = pair ν x := rfl

lemma pair_sub_left (ν ν' x : InfinitePlace F → ℂ) :
    pair (ν - ν') x = pair ν x - pair ν' x := by
  simp [pair, sub_mul, Finset.sum_sub_distrib]

lemma pair_single [DecidableEq (InfinitePlace F)] (μ : InfinitePlace F → ℂ)
    (w : InfinitePlace F) (z : ℂ) : pair μ (Pi.single w z) = (μ w * z).re := by
  rw [pair, Finset.sum_eq_single w]
  · rw [Pi.single_eq_same]
  · intro w' _ hne
    rw [Pi.single_eq_of_ne hne, mul_zero, Complex.zero_re]
  · intro h; exact absurd (Finset.mem_univ w) h

/-- The pairing is nondegenerate. -/
lemma eq_of_pair_eq {ν ν' : InfinitePlace F → ℂ} (h : ∀ x, pair ν x = pair ν' x) : ν = ν' := by
  classical
  funext w
  have h0 := pair_sub_left ν ν' (Pi.single w (conj ((ν - ν') w)))
  rw [h, sub_self, pair_single, Complex.mul_conj, Complex.ofReal_re] at h0
  have h1 : (ν - ν') w = 0 := Complex.normSq_eq_zero.mp h0
  exact sub_eq_zero.mp h1

end

end ArtinKP.RF
end

section
-- module Solutions.Artin.KP.C9_Dual
attribute [-instance] _root_.ArtinKP.N2.levelGroup_finiteIndex _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-!
# WP-C9, part 5: trace duality — the frequencies of `Λ_Γ^⊥` are `T.freq ν`, `ν ∈ R`

`DualCover 𝔪 Γ` (the named hypothesis of `C9_Tau`) is proved for every finite-index `Γ` whose
translations contain `emb(𝔪^N)` (`TransLevel 𝔪 Γ`), **under the hypothesis that the different of
`F` is supported in the primes of `𝔪`**:

  `hdiff : ∀ v, v ∉ placesOf 𝔪 → ¬ differentIdeal ℤ (𝓞 F) ≤ v.asIdeal`.

(Without it the statement is false: a prime `v ∤ 𝔪` dividing the different gives frequencies
`ν ∈ 𝔡⁻¹ ∖ R` in the dual lattice of `emb(𝓞)`.)

* `pair_freq_emb`: `pair (T.freq (-μ)) (emb x) = Tr_{F/ℚ}(μ x)`.
* **`dualCover_of_transLevel`**.
* `exists_tau_sumBig_ne_zero'`, `exists_tau_bigCell_ne_zero'`: the statements for package G with
  `hdiff` in place of `DualCover`.
-/

open scoped MatrixGroups ComplexConjugate ENNReal Topology nonZeroDivisors
open MeasureTheory Set NumberField Filter IsDedekindDomain ArtinPrimitiveRoots Metric

set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.C9

open ArtinKP.A ArtinKP.S ArtinKP.X ArtinKP.B1 ArtinKP.B ArtinKP.C5 ArtinKP.K ArtinKP.RF ArtinKP.N

noncomputable section

variable {F : Type*} [Field F] [NumberField F] [IsTotallyComplex F] {𝔪 : Ideal (𝓞 F)}
  {ι : F →+* ℂ} {P : CubicPkg F}

/-- The pairing with `T.freq (-μ)` on `emb(F)` is the trace form. -/
lemma pair_freq_emb (μ x : F) :
    pair (T.freq (-μ)) (emb x) = ((Algebra.trace ℚ F (μ * x) : ℚ) : ℝ) := by
  have h := congrArg Complex.re
    (K.trace_eq_sum_places (fun w => IsTotallyComplex.isComplex w) (μ * x))
  rw [Complex.ratCast_re, Complex.re_sum] at h
  rw [h]
  unfold pair
  refine Finset.sum_congr rfl fun w _ => ?_
  have e : T.freq (-μ) w * emb x w = ((2 : ℝ) : ℂ) * w.embedding (μ * x) := by
    change -2 * w.embedding (-μ) * w.embedding x = _
    rw [map_neg, map_mul]
    push_cast
    ring
  rw [e, Complex.re_ofReal_mul, Complex.add_re, Complex.conj_re]
  ring

/-- **Trace duality.**  If the translations of `Γ` contain `emb(𝔪^N)` and the different is
supported in the primes of `𝔪`, every frequency of `RF.dualLat Γ` is `T.freq ν` with
`ν ∈ R = SInt 𝔪`. -/
theorem dualCover_of_transLevel (h𝔪 : 𝔪 ≠ ⊥)
    (hdiff : ∀ v : HeightOneSpectrum (𝓞 F), v ∉ placesOf 𝔪 →
      ¬ differentIdeal ℤ (𝓞 F) ≤ v.asIdeal)
    (Γ : Subgroup (SL(2, 𝓞 F))) [Γ.FiniteIndex] (hΓ : TransLevel 𝔪 Γ) : DualCover 𝔪 Γ := by
  classical
  obtain ⟨N, hN⟩ := hΓ
  intro ν' hν' _
  have hint : ∀ β : 𝓞 F, β ∈ lamN Γ → ∃ m : ℤ, pair ν' (emb (β : F)) = m := by
    intro β hβ
    have h := hν' (ofLam ⟨β, hβ⟩)
    rw [shift_ofLam] at h
    exact h
  -- the `ℚ`-linear functional `x ↦ pair ν' (emb x)`
  let pA : (InfinitePlace F → ℂ) →+ ℝ := AddMonoidHom.mk' (pair ν') (RF.pair_add ν')
  let L : F →ₗ[ℚ] ℝ := (pA.comp (emb (F := F))).toRatLinearMap
  have hL : ∀ x : F, L x = pair ν' (emb x) := fun x => rfl
  -- an integer in `𝔪^N`
  set I : Ideal (𝓞 F) := 𝔪 ^ N with hIdef
  have hI : I ≠ ⊥ := pow_ne_zero N h𝔪
  set c : ℕ := Ideal.absNorm I with hcdef
  have hc0 : c ≠ 0 := by
    rw [hcdef, Ne, Ideal.absNorm_eq_zero_iff]
    exact hI
  have hcI : ((c : ℕ) : 𝓞 F) ∈ I := Ideal.absNorm_mem I
  -- a `ℚ`-basis of `F` inside `𝔪^N`
  have hu : ∀ _ : Module.Free.ChooseBasisIndex ℤ (𝓞 F), IsUnit ((c : ℚ)) := fun _ =>
    (Nat.cast_ne_zero.mpr hc0 : (c : ℚ) ≠ 0).isUnit
  let b := (integralBasis F).isUnitSMul hu
  have hb : ∀ i, b i = algebraMap (𝓞 F) F (((c : ℕ) : 𝓞 F) * RingOfIntegers.basis F i) := by
    intro i
    change (integralBasis F).isUnitSMul hu i = _
    rw [Module.Basis.isUnitSMul_apply, integralBasis_apply, map_mul, map_natCast]
    rw [Rat.smul_def]
    simp
  have hbm : ∀ i, ∃ m : ℤ, L (b i) = m := fun i => by
    rw [hL, hb]
    exact hint _ (hN _ (I.mul_mem_right _ hcI))
  choose m hm using hbm
  -- the element `μ` with `Tr(μ b_j) = m_j`
  let d := (Algebra.traceForm ℚ F).dualBasis (traceForm_nondegenerate ℚ F) b
  set μ : F := ∑ i, (m i : ℚ) • d i with hμ
  have hμb : ∀ j, Algebra.trace ℚ F (μ * b j) = m j := by
    intro j
    have h1 : ∀ i, Algebra.trace ℚ F (d i * b j) = if j = i then 1 else 0 := fun i =>
      (Algebra.traceForm ℚ F).apply_dualBasis_left (traceForm_nondegenerate ℚ F) b i j
    rw [hμ, Finset.sum_mul, map_sum]
    simp only [smul_mul_assoc, map_smul, h1, smul_eq_mul, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq, Finset.mem_univ, if_true]
  let L' : F →ₗ[ℚ] ℝ := (Algebra.linearMap ℚ ℝ).comp ((Algebra.traceForm ℚ F) μ)
  have hL' : ∀ x : F, L' x = ((Algebra.trace ℚ F (μ * x) : ℚ) : ℝ) := fun x => rfl
  have hLL : L = L' := b.ext fun j => by
    rw [hm, hL', hμb]
    push_cast
    rfl
  have hpair : ∀ x : F, pair ν' (emb x) = pair (T.freq (-μ)) (emb x) := fun x => by
    rw [pair_freq_emb, ← hL', ← hLL, hL]
  -- `emb(F)` spans
  obtain ⟨dd, bV, hbV⟩ := exists_latBasis Γ (exists_ideal_translations Γ)
  have heq : ν' = T.freq (-μ) := by
    apply eq_of_pair_eq
    have hlin : pairLin ν' = pairLin (T.freq (-μ)) := bV.ext fun j => by
      obtain ⟨γ, hγ⟩ := (hbV (bV j)).mp (Submodule.subset_span (Set.mem_range_self j))
      rw [pairLin_apply, pairLin_apply, hγ]
      exact hpair ((((γ : Γ) : SL(2, 𝓞 F)) 0 1 : 𝓞 F) : F)
    intro x
    exact LinearMap.congr_fun hlin x
  -- integrality of the trace on `𝔪^N`
  have htr : ∀ β ∈ I, ∃ k : ℤ, Algebra.trace ℚ F (μ * (β : F)) = k := by
    intro β hβ
    obtain ⟨k, hk⟩ := hint β (hN β hβ)
    refine ⟨k, ?_⟩
    have h1 : ((Algebra.trace ℚ F (μ * (β : F)) : ℚ) : ℝ) = (k : ℝ) := by
      rw [← hL', ← hLL, hL, hk]
    exact_mod_cast h1
  have hμS : -μ ∈ (placesOf 𝔪).integer F := by
    intro v hv
    rw [Valuation.map_neg]
    have hvI : ¬ I ≤ v.asIdeal := fun hle => hv (v.isPrime.le_of_pow_le hle)
    obtain ⟨c₁, hc₁, hc₁v⟩ := SetLike.not_le_iff_exists.mp hvI
    obtain ⟨p, hp, hpv⟩ := SetLike.not_le_iff_exists.mp (hdiff v hv)
    have hone : (1 : FractionalIdeal (𝓞 F)⁰ F) ≠ 0 := one_ne_zero
    have hdual : μ * algebraMap (𝓞 F) F c₁
        ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 F)⁰ F) := by
      rw [FractionalIdeal.mem_dual hone]
      intro a ha
      obtain ⟨a', rfl⟩ := (FractionalIdeal.mem_one_iff _).1 ha
      obtain ⟨k, hk⟩ := htr (c₁ * a') (I.mul_mem_right _ hc₁)
      refine ⟨k, ?_⟩
      rw [Algebra.traceForm_apply]
      have e : μ * algebraMap (𝓞 F) F c₁ * algebraMap (𝓞 F) F a'
          = μ * ((c₁ * a' : 𝓞 F) : F) := by
        rw [mul_assoc, ← map_mul]
      rw [e, hk]
      simp
    have hp' : algebraMap (𝓞 F) F p ∈
        ((differentIdeal ℤ (𝓞 F) : Ideal (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F) :=
      (FractionalIdeal.mem_coeIdeal _).2 ⟨p, hp, rfl⟩
    rw [coeIdeal_differentIdeal ℤ ℚ] at hp'
    have h1 := FractionalIdeal.mul_mem_mul hdual hp'
    rw [mul_inv_cancel₀ (FractionalIdeal.dual_ne_zero ℤ ℚ hone)] at h1
    obtain ⟨a, ha⟩ := (FractionalIdeal.mem_one_iff _).1 h1
    have hv1 : v.valuation F (algebraMap (𝓞 F) F c₁) = 1 :=
      (HeightOneSpectrum.valuation_eq_one_iff_notMem v).2 hc₁v
    have hv2 : v.valuation F (algebraMap (𝓞 F) F p) = 1 :=
      (HeightOneSpectrum.valuation_eq_one_iff_notMem v).2 hpv
    have h2 := v.valuation_le_one (K := F) a
    change v.valuation F (algebraMap (𝓞 F) F a) ≤ 1 at h2
    rw [ha, map_mul, map_mul, hv1, hv2, mul_one, mul_one] at h2
    exact h2
  exact ⟨⟨-μ, hμS⟩, heq.symm⟩

/-! ### The statements for package G, with `hdiff` -/

section G

variable (hG : Good 𝔪) {z6 : 𝓞 F} (hz6 : IsPrimitiveRoot z6 6)
  {N : ℕ} (hN1 : 1 ≤ N) (hN : P.IsDeepLevel 𝔪 N) (M : ℤ) (Tc : Finset {η : F // η ≠ 0})
  (hdisj : ∀ η ∈ Tc, ∀ η' ∈ Tc, η ≠ η' → ∀ c : F, InClass 𝔪 N η.1 c → ¬ InClass 𝔪 N η'.1 c)
  (hcov : ∀ c : F, c ≠ 0 → ∃ η ∈ Tc, InClass 𝔪 N η.1 c)
  (hdiff : ∀ v : HeightOneSpectrum (𝓞 F), v ∉ placesOf 𝔪 →
    ¬ differentIdeal ℤ (𝓞 F) ≤ v.asIdeal)

include hdiff in
/-- **(C10′) in WP-T's form, unconditional up to `hdiff`**: `τ_Φ(ν) = 0` for all `ν ∈ R ∖ 0`
implies `θ_{Φ.twist} = 0` for **every** finite-index `Γ` fixing the twist. -/
theorem theta_eq_zero_of_tau' (Φ : GSection ι P 𝔪) (Γ : Subgroup (SL(2, 𝓞 F)))
    [Γ.FiniteIndex] (hΓ : Inv Γ (Φ.twist hG hz6))
    (h : ∀ ν : SInt 𝔪, ν ≠ 0 → T.tau hG hz6 Φ ν = 0) :
    C5.theta Γ (Φ.twist hG hz6) = 0 := by
  have hfi := stabGroup_finiteIndex P hG hz6 (Φ.twist hG hz6)
  have h0 := theta_eq_zero_of_forall_tau_eq_zero hG hz6 Φ (stabGroup (Φ.twist hG hz6)) (inv_stabGroup _)
    (dualCover_of_transLevel hG.ne_bot hdiff _ (transLevel_stabGroup hG hz6 Φ)) h
  exact theta_eq_zero_congr hG (inv_stabGroup _) hΓ h0

end G

end

end ArtinKP.C9
end

section
-- module Solutions.Artin.KP.S2_Translate
attribute [-instance] _root_.ArtinKP.F.instAddCommMonoidTSection _root_.ArtinKP.N2.levelGroup_finiteIndex _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-!
# WP-S2, part 3: genuine sections are stable under `SL₂(F)`, in particular under `SL₂(R)`

* `GSection.translateF α β γ δ` (`αδ - βγ = 1`, entries in `F`):
  `(σ·Φ)_s(p) = σ_S(p, σ)⁻¹ Φ_s(pσ)`.  It is a genuine section: (S1), (S1³) by `sig_smul`, the
  level condition by Kubota's cocycle identity (`sig_cocycle`, twice) and `sig_conj`.
* `GSection.translate σ` for `σ ∈ SL₂(R)`: `κ(σ) · translateF σ`, and
  `twist_translate : twist (translate σ Φ) = TSection.translate σ (twist Φ)` — MATH2 §5.2's `Φ^σ`.
* `translate_mul`: `translate (σ₁ σ₂) Φ = translate σ₁ (translate σ₂ Φ)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open NumberField IsDedekindDomain ArtinPrimitiveRoots

noncomputable section

namespace ArtinKP.S2

open ArtinKP.A ArtinKP.S

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}
variable {ι : F →+* ℂ} {P : CubicPkg F}

namespace GSection

theorem translate_apply (hG : Good 𝔪) (σ : Matrix.SpecialLinearGroup (Fin 2) (SInt 𝔪))
    (Φ : GSection ι P 𝔪) (s : ℂ) (c d : F) :
    translate hG σ Φ s c d = kappa ι 𝔪 σ *
      ((sig ι P 𝔪 c d ((σ.1 0 0 : SInt 𝔪) : F) ((σ.1 0 1 : SInt 𝔪) : F)
        ((σ.1 1 0 : SInt 𝔪) : F) ((σ.1 1 1 : SInt 𝔪) : F))⁻¹ *
      Φ s (c * ((σ.1 0 0 : SInt 𝔪) : F) + d * ((σ.1 1 0 : SInt 𝔪) : F))
        (c * ((σ.1 0 1 : SInt 𝔪) : F) + d * ((σ.1 1 1 : SInt 𝔪) : F))) := rfl

/-- **Genuine sections are stable under `SL₂(R)`**: the twist of the genuine translate is the
right translate of the twist. -/
theorem twist_translate (hG : Good 𝔪) {z6 : 𝓞 F} (hz6 : IsPrimitiveRoot z6 6)
    (σ : Matrix.SpecialLinearGroup (Fin 2) (SInt 𝔪)) (Φ : GSection ι P 𝔪) :
    (translate hG σ Φ).twist hG hz6 = TSection.translate P hG hz6 σ (Φ.twist hG hz6) := by
  ext s p
  rw [GSection.twist_apply, TSection.translate_apply, GSection.twist_apply, translate_apply,
    kappaRow_act ι P hG hz6]
  have hc : (((p.act σ).c : SInt 𝔪) : F) = (p.c : F) * ((σ.1 0 0 : SInt 𝔪) : F)
      + (p.d : F) * ((σ.1 1 0 : SInt 𝔪) : F) := by
    rw [Row.act_c]; push_cast; rfl
  have hd : (((p.act σ).d : SInt 𝔪) : F) = (p.c : F) * ((σ.1 0 1 : SInt 𝔪) : F)
      + (p.d : F) * ((σ.1 1 1 : SInt 𝔪) : F) := by
    rw [Row.act_d]; push_cast; rfl
  rw [hc, hd]
  ring

end GSection

end ArtinKP.S2
end
end

section
-- module Solutions.Artin.KP.G1_Cusp
attribute [-instance] _root_.ArtinKP.N2.levelGroup_finiteIndex _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-!
# WP-G1, part 1: the cusp change at the section level (MATH3 §2.1)

Three identities of genuine sections, in the tree's conventions
(`wΦ := S2.GSection.translate hG (wMat 𝔪) Φ`, `(wΦ)_s(c,d) = ⟨c,d⟩Φ_s(d,-c)`):

* `torusT_nT` (N): `Ã(β) n(t) Φ = n(βt) Ã(β) Φ`;
* `w_torusT` (W): `w Ã(β) Φ = |β|^{s-2} Ã(β⁻¹) w Φ`;
* `translate_nT_cusp` (2.1): for `γ = [[a,b],[c,d]] ∈ SL₂(R)`, `c ≠ 0`,
  `translate γ (n(-d/c) Φ) = κ(γ) |c|^{s-2} n(a/c) Ã(c⁻²) (wΦ)` on all of `F²`
  (`translateF_nT_cusp` is the same for `γ ∈ SL₂(F)`, without `κ`).

All three are pure `brk`-algebra.  The symbol identities are proved by expanding into atoms
(`simp` with bimultiplicativity) and `grind` with the facts `⟨x,y⟩³ = 1`, `⟨y,x⟩⟨x,y⟩ = 1`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

open NumberField IsDedekindDomain ArtinPrimitiveRoots

noncomputable section

namespace ArtinKP.G1

open ArtinKP.A ArtinKP.S ArtinKP.S2

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}
variable {ι : F →+* ℂ} {P : CubicPkg F}

/-- The two facts about an atom `⟨x, y⟩` that `grind` needs. -/
theorem brk_facts (x y : F) :
    brk ι P 𝔪 x y ^ 3 = 1 ∧ brk ι P 𝔪 y x * brk ι P 𝔪 x y = 1 :=
  ⟨brk_pow_three _ _, brk_mul_skew _ _⟩

/-! ### Powers of `|x|_{S_f}` as multipliers -/

/-- `x^w` for a positive real `x`, as an exponential. -/
theorem ofReal_cpow_eq_exp {x : ℝ} (hx : 0 < x) (w : ℂ) :
    (x : ℂ) ^ w = Complex.exp (w * (Real.log x : ℂ)) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne'), ← Complex.ofReal_log hx.le,
    mul_comm]

theorem cpow_weyl {x : ℝ} (hx : 0 < x) (s : ℂ) :
    (x : ℂ) ^ (2 * s - 1) * (x : ℂ) ^ (-(3 * s))
      = (x : ℂ) ^ (1 * s + -2) * ((x⁻¹ : ℝ) : ℂ) ^ (2 * s - 1) := by
  have h1 : 0 < x⁻¹ := inv_pos.mpr hx
  rw [ofReal_cpow_eq_exp hx, ofReal_cpow_eq_exp hx, ofReal_cpow_eq_exp hx, ofReal_cpow_eq_exp h1,
    ← Complex.exp_add, ← Complex.exp_add, Real.log_inv]
  push_cast
  ring_nf

/-! ### The Weyl element -/

theorem kappa_wMat : kappa ι 𝔪 (wMat 𝔪) = 1 := by
  rw [kappa, wMat_10, if_neg one_ne_zero, cubicExt_of_unit_right ι _ _ (fun v _ => by simp),
    inv_one]

/-- `(wΦ)_s(c, d) = ⟨c, d⟩ Φ_s(d, -c)` on all of `F²`: the translate by `wMat` is `wFun`. -/
theorem wSec_apply (hG : Good 𝔪) (Φ : GSection ι P 𝔪) (s : ℂ) (c d : F) :
    wSec hG Φ s c d = brk ι P 𝔪 c d * Φ s d (-c) := by
  rw [wSec, S2.GSection.translate_apply, kappa_wMat, one_mul]
  simp only [wMat_00, wMat_01, wMat_10, wMat_11]
  push_cast
  rw [show c * (0 : F) + d * 1 = d by ring, show c * (-1 : F) + d * 0 = -c by ring]
  congr 1
  have h1 : Xs (1 : F) 0 = 1 := Xs_of_ne _ one_ne_zero
  rw [sig, show c * (0 : F) + d * 1 = d by ring, show c * (-1 : F) + d * 0 = -c by ring, h1,
    div_one]
  by_cases hc : c = 0
  · by_cases hd : d = 0
    · simp [hc, hd]
    · simp [hc, Xs_of_ne _ hd, div_self hd]
  by_cases hd : d = 0
  · simp [hd, Xs_of_ne _ hc, neg_div, div_self hc]
  · rw [Xs_of_ne _ hd, Xs_of_ne _ hc, brk_div_left _ hd hc, brk_self, one_mul, inv_inv]

/-! ### (N) and (W) -/

/-- **(W)** `w Ã(β) Φ = |β|^{s-2} Ã(β⁻¹) w Φ`. -/
theorem w_torusT (hG : Good 𝔪) (Φ : GSection ι P 𝔪) {β : F} (hβ : β ≠ 0) :
    wSec hG (Φ.torusT hG β hβ)
      = scal β hβ 1 (-2) ((wSec hG Φ).torusT hG β⁻¹ (inv_ne_zero hβ)) := by
  ext s c d
  rw [wSec_apply, GSection.torusT_apply, scal_apply, GSection.torusT_apply, wSec_apply]
  by_cases h0 : c = 0 ∧ d = 0
  · obtain ⟨rfl, rfl⟩ := h0
    simp [Φ.zero]
  have e1 : β ^ 2 * d = β ^ 3 * (β⁻¹ * d) := by field_simp
  have e2 : β * -c = β ^ 3 * -(β⁻¹ ^ 2 * c) := by field_simp
  rw [e1, e2, Φ.cube s β hβ, absS_inv]
  have hcp := cpow_weyl (absS_pos (𝔪 := 𝔪) hβ) s
  have hsym : brk ι P 𝔪 c d * tf ι P 𝔪 β d (-c)
      = tf ι P 𝔪 β⁻¹ c d * brk ι P 𝔪 (β⁻¹ ^ 2 * c) (β⁻¹ * d) := by
    have f1 := brk_facts (ι := ι) (P := P) (𝔪 := 𝔪) c d
    have f2 := brk_facts (ι := ι) (P := P) (𝔪 := 𝔪) c β
    have f3 := brk_facts (ι := ι) (P := P) (𝔪 := 𝔪) d β
    by_cases hc : c = 0
    · have hd : d ≠ 0 := fun hd => h0 ⟨hc, hd⟩
      subst hc
      simp [tf, hd, hβ, brk_inv_right]
      grind
    by_cases hd : d = 0
    · subst hd
      simp [tf, hc, hβ, brk_inv_right]
      grind
    · simp [tf, hc, hd, hβ, brk_mul_left, brk_mul_right, brk_inv_left, brk_inv_right, pow_succ]
      grind
  linear_combination (((absS 𝔪 β : ℝ) : ℂ) ^ (-(3 * s)) * ((absS 𝔪 β : ℝ) : ℂ) ^ (2 * s - 1)
      * Φ s (β⁻¹ * d) (-(β⁻¹ ^ 2 * c))) * hsym
    + (tf ι P 𝔪 β⁻¹ c d * brk ι P 𝔪 (β⁻¹ ^ 2 * c) (β⁻¹ * d)
      * Φ s (β⁻¹ * d) (-(β⁻¹ ^ 2 * c))) * hcp

/-! ### (2.1): the cusp change -/

end ArtinKP.G1
end
end

section
-- module Solutions.Artin.KP.G1_Lam
attribute [-instance] _root_.ArtinKP.N2.levelGroup_finiteIndex _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-!
# WP-G1, part 2: linearity of `Lam`, and the cusp change for `Lam` and for the Kirillov term

* `Lam_smulFun`, `Lam_smul`, `Lam_scal`, `Lam_nT` (all `s`); `Lam_add`, `Lam_sum`, `Lam_addProj`
  (`Re s > 1`, where the defining series converges: `summable_jacTerm`).
* `torusT_torusT`, `torusT_smulFun`, `torusT_smul`.
* `Kt ψ hG Φ β η s := Lam (Ã(β)Φ) η 1 s`, the `η`-term of the Kirillov function (`= S.kir` at a
  valid depth, `Kt_eq_kir`), with the rules (K4):
  `Kt_torusT`, `Kt_nT`, `Kt_smulFun`, `Kt_add`, `Kt_addProj`.
* `Lam_cusp`: `Lam Ψ c' μ s = κ(γ)|c|^{s-2} ψ(μa/c) ⟨c',c⟩⁻¹ Lam (wΦ) (c'/c) (μ/c²) s`,
  `Ψ = translate γ (n(-d/c)Φ)`;
  `cusp_torusT`: `Ã(μ)Ψ = κ(γ)⟨μ,c⟩ |c|^{s-2} n(μa/c) Ã(μ/c²)(wΦ)`;
  `Kt_cusp`, and `xiT_cusp` (MATH3 (2.2)): with `ξ^η_Φ(β) := |β|^{1/3} Kt Φ β η (4/3)`,
  `ξ^η_Ψ(μ) = κ(γ) ψ(μa/c) ⟨μ,c⟩ ξ^η_{wΦ}(μ/c²)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

open NumberField IsDedekindDomain ArtinPrimitiveRoots

noncomputable section

namespace ArtinKP.G1

open ArtinKP.A ArtinKP.S ArtinKP.S2

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}
variable {ι : F →+* ℂ} {P : CubicPkg F}

/-! ### Convergence of the defining series, linearity -/

theorem valid_smulFun {ψ : SfChar 𝔪} {Φ : GSection ι P 𝔪} {ν : F}
    {k : HeightOneSpectrum (𝓞 F) → ℤ} (h : Valid ψ Φ ν k) (f : ℂ → ℂ) (hf : Differentiable ℂ f) :
    Valid ψ (GSection.smulFun f hf Φ) ν k :=
  ⟨fun b hb s c d => by rw [GSection.smulFun_apply, GSection.smulFun_apply, h.1 b hb], h.2⟩

/-- `Lam` commutes with multiplication by a function of `s` (all `s`). -/
theorem Lam_smulFun (ψ : SfChar 𝔪) (hG : Good 𝔪) (Φ : GSection ι P 𝔪) (f : ℂ → ℂ)
    (hf : Differentiable ℂ f) (c ν : F) (s : ℂ) :
    Lam ψ hG (GSection.smulFun f hf Φ) c ν s = f s * Lam ψ hG Φ c ν s := by
  have h := valid_depth ψ hG Φ ν
  rw [Lam_eq_lam ψ hG _ (valid_smulFun h f hf), Lam_eq_lam ψ hG _ h, lam, lam]
  simp only [GSection.smulFun_apply]
  rw [jac_const_mul]
  ring

theorem Lam_smul (ψ : SfChar 𝔪) (hG : Good 𝔪) (Φ : GSection ι P 𝔪) (a : ℂ) (c ν : F) (s : ℂ) :
    Lam ψ hG (a • Φ) c ν s = a * Lam ψ hG Φ c ν s :=
  Lam_smulFun ψ hG Φ (fun _ => a) (differentiable_const a) c ν s

/-! ### `Ã(β)` against the other operations -/

/-- `Ã(β) Ã(β') = ⟨β, β'⟩ Ã(β β')` on genuine sections. -/
theorem torusT_torusT (hG : Good 𝔪) (Φ : GSection ι P 𝔪) {β β' : F} (hβ : β ≠ 0)
    (hβ' : β' ≠ 0) :
    (Φ.torusT hG β' hβ').torusT hG β hβ
      = brk ι P 𝔪 β β' • Φ.torusT hG (β * β') (mul_ne_zero hβ hβ') := by
  ext s c d
  have h := congrArg (fun Ψ : GSection ι P 𝔪 => Ψ s c d) (GSection.torus_torus hG β β' hβ hβ' Φ)
  simp only [GSection.torus_apply, GSection.smul_apply] at h
  rw [GSection.torusT_apply, GSection.torusT_apply, GSection.smul_apply, GSection.torusT_apply,
    absS_mul, ofReal_mul_cpow (absS_nonneg _) (absS_nonneg _)]
  linear_combination (((absS 𝔪 β : ℝ) : ℂ) ^ (2 * s - 1) * ((absS 𝔪 β' : ℝ) : ℂ) ^ (2 * s - 1)) * h

/-! ### The Kirillov term -/

theorem Kt_of_ne (ψ : SfChar 𝔪) (hG : Good 𝔪) (Φ : GSection ι P 𝔪) {β : F} (hβ : β ≠ 0)
    (η : F) (s : ℂ) : Kt ψ hG Φ β η s = Lam ψ hG (Φ.torusT hG β hβ) η 1 s := by
  rw [Kt, dif_neg hβ]

/-- (K4) `𝒦_{Ã(β₀)Φ}(β) = ⟨β, β₀⟩ 𝒦_Φ(β β₀)`. -/
theorem Kt_torusT (ψ : SfChar 𝔪) (hG : Good 𝔪) (Φ : GSection ι P 𝔪) {β β₀ : F} (hβ : β ≠ 0)
    (hβ₀ : β₀ ≠ 0) (η : F) (s : ℂ) :
    Kt ψ hG (Φ.torusT hG β₀ hβ₀) β η s = brk ι P 𝔪 β β₀ * Kt ψ hG Φ (β * β₀) η s := by
  rw [Kt_of_ne ψ hG _ hβ, Kt_of_ne ψ hG _ (mul_ne_zero hβ hβ₀), torusT_torusT hG Φ hβ hβ₀,
    Lam_smul]

/-! ### The cusp change for `Lam` and for the Kirillov term -/

/-! ### The normalized term `ξ^η = |β|^{1/3} Kt(·, 4/3)` -/

end ArtinKP.G1
end
end

section
-- module Solutions.Artin.KP.G1_Res
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-!
# WP-G1, part 6: interface repairs for WP-E's abstract residue layer (MATH3 findings 6, 7)

New lemmas beside `E.ResFun`, `E.HasResOn`, `E.Theta` (no file of WP-E is edited).

* `ResFun.SmulOn T U`: the scalar law of a residue functional for multipliers that are holomorphic
  on the open set `U` only (`E.ResFun.smul` asks for an entire multiplier).
* `hasResOn_smul`: for the model `HasResOn Ω s₀ γ`, a multiplier analytic on `Ω` with a limit `L`
  along the path `γ` multiplies the residue by `L`.
* `ofContinuation_smulOn`: `ResFun.ofContinuation Ω s₀ γ …` has `SmulOn U` for every open
  `U ⊇ Ω ∪ {s₀}`; `resFunSlit_smulOn`: the slit model has `SmulOn {Re s > 1}`.
  (What is true and sufficient: the multiplier must be analytic on the region `Ω` and continuous at
  `s₀` along the ray; holomorphy on a neighbourhood of `Ω ∪ {s₀}` gives both.)
* `Theta.tau_congr_at`: `τ` sees a section through `Lam` at the one frequency `ν` only, with a
  scalar that may depend on `ν` (`E.Theta.tau_congr` has one scalar for all `ν`).
* `Theta.tau_smul_at`: the same with an entire multiplier `h(s)`.
* `Theta.tau_sum_at`: `Lam Φ c ν s = Σ_i h_i(s) Lam Ψ_i c ν s` on `Re s > 2` gives
  `τ_Φ(ν) = Σ_i h_i(s₀) τ_{Ψ_i}(ν)`, for multipliers holomorphic on `U` (given `SmulOn U`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open Filter Topology

namespace ArtinKP.G1

open ArtinKP.B7 ArtinKP.E

section theta

variable {R K : Type*} [CommRing R] [IsDomain R] [Field K] [Algebra R K]
variable {S : CubicSymbol R} {A : AddData R K} {Sec : Type*} {D : Kubota S A Sec} {s₀ : ℂ}
  (T : Theta D s₀)

/-- **`tau_congr` per frequency**: if `Lam Φ c ν s = z · Lam Ψ c ν s` at the one frequency `ν`
(`c ≠ 0`, `Re s > 2`), then `τ_Φ(ν) = z τ_Ψ(ν)`. -/
theorem _root_.ArtinKP.E.Theta.tau_congr_at {Φ Ψ : Sec} {z : ℂ} {ν : R} (hν : ν ≠ 0)
    (h : ∀ (c : R) (s : ℂ), c ≠ 0 → 2 < s.re → D.Lam Φ c ν s = z * D.Lam Ψ c ν s) :
    T.tau Φ ν = z * T.tau Ψ ν := by
  have h1 := T.smul (fun _ => z) (differentiable_const z) (T.tau_spec Ψ ν hν)
  have h2 := T.congr h1 (fun s hs => by
    show z * D.aSer Ψ ν s = D.aSer Φ ν s
    unfold Kubota.aSer
    rw [← tsum_mul_left]
    refine tsum_congr fun a => ?_
    unfold Kubota.term
    rw [h _ s (rp_ne_zero a.2) hs]
    ring)
  exact T.unique (T.tau_spec Φ ν hν) h2

end theta

end ArtinKP.G1
end

section
-- module Solutions.Artin.KP.G1_Kir
attribute [-instance] _root_.ArtinKP.N2.levelGroup_finiteIndex _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-!
# WP-G1, part 7: the Kirillov function — (K1)–(K4), the class decomposition, the bound

Section level (any `S_f`-character `ψ` with bounded dual lattices, `HasDual ψ d₀`):

* `exists_Kt_support` (K3): `Kt Φ β η s = 0` unless `β ∈ 𝔩_D` (support in a fractional ideal,
  i.e. `|β|_v ≤ q_v^{-D}` at every `v ∈ S_f` separately); from `S.kir_eq_zero` and DUAL.
* `exists_Kt_bound` (K2): `|β|^{1/3} |Kt Φ β η (4/3)| ≤ C ∏_{v ∈ S_f} min(1, |β|_v^{1/3})` for all
  `β ∈ F^×`, all classes `η`; from `GL.xi_bound`, the support, and `S2.K_eq`.
* `exists_Kt_deep` (K1): `Kt Φ (βu) η s = Kt Φ β η s` for `u` deep.

`τ` level, for `D = B.kubota hG hz6` (`ψ = B.psiS`), any `T : E.Theta D (4/3)`:

* `tau_smul`, `tau_nT`, `tau_addProj`, `tau_sum`, `tau_smulFun`.
* `Kir T Φ β := τ_{Ã(β)Φ}(1)` (MATH3 §0), `xi T Φ β := |β|^{1/3} Kir T Φ β`; **(K4)**:
  `Kir_torusT` (`𝒦_{Ã(β₀)Φ}(β) = ⟨β,β₀⟩𝒦_Φ(ββ₀)`), `Kir_nT` (`𝒦_{n(t)Φ}(β) = ψ(βt)𝒦_Φ(β)`),
  `Kir_smulFun`, `Kir_addProj` (G2), `Kir_sum`, `xi_torusT`, `xi_nT`; `exists_Kir_deep` (K1);
  `Kir_cusp`/`xi_cusp` (MATH3 (2.2)).
* `tau_classDecomp` — **(CD)**: `τ_Ψ(ν) = Σ_η Lam Ψ η ν (4/3) · vol(𝔩_M)⁻¹ τ_{bigCell_η}(ν)`,
  given the scalar law `T.SmulOn {Re s > 1}` (true for `resFunSlit`: `resFunSlit_smulOn`).
* `exists_Kir_classDecomp`: one finite set of classes and weights `w_η` with
  `𝒦_Φ(β) = Σ_η Kt Φ β η (4/3) · w_η` for all `β ∈ F^×`.
* `exists_xi_le` — **the majorant for `ξ`** (MATH3 §4.3):
  `|ξ_Φ(β)| ≤ C ∏_v min(1, |β|_v^{1/3})` and `ξ_Φ(β) = 0` unless `β ∈ 𝔩_D`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

open scoped ComplexConjugate
open NumberField IsDedekindDomain ArtinPrimitiveRoots

noncomputable section

namespace ArtinKP.G1

open ArtinKP.A ArtinKP.S ArtinKP.S2 ArtinKP.E ArtinKP.B7

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}
variable {ι : F →+* ℂ} {P : CubicPkg F}

/-! ### Section level: support, bound, deep invariance -/

/-! ### `τ` level -/

section tau

variable [IsTotallyComplex F] (hG : Good 𝔪) {z6 : 𝓞 F} (hz6 : IsPrimitiveRoot z6 6)
  (T : Theta (B.kubota (ι := ι) (P := P) hG hz6) (4 / 3 : ℂ))

theorem coe_ne_zero' {c : SInt 𝔪} (hc : c ≠ 0) : (c : F) ≠ 0 := fun h => hc (Subtype.ext h)

/-- Transfer of a `Lam`-identity at one frequency (stated on `F`, `Re s > 1`) to `τ`. -/
theorem tau_congr_F {Φ Ψ : GSection ι P 𝔪} {z : ℂ} {ν : SInt 𝔪} (hν : ν ≠ 0)
    (h : ∀ (c : F) (s : ℂ), c ≠ 0 → 1 < s.re →
      Lam (B.psiS hG.ne_bot) hG Φ c (ν : F) s = z * Lam (B.psiS hG.ne_bot) hG Ψ c (ν : F) s) :
    T.tau Φ ν = z * T.tau Ψ ν :=
  T.tau_congr_at hν fun c s hc hs => h (c : F) s (coe_ne_zero' hc) (by linarith)

/-! ### The Kirillov function -/

theorem Kir_of_ne (Φ : GSection ι P 𝔪) {β : F} (hβ : β ≠ 0) :
    Kir hG hz6 T Φ β = T.tau (Φ.torusT hG β hβ) 1 := by
  rw [Kir, dif_neg hβ]

/-- Transfer of an identity of Kirillov terms (all classes, `Re s > 1`) to `𝒦`. -/
theorem Kir_congr {Φ Ψ : GSection ι P 𝔪} {β β' : F} (hβ : β ≠ 0) (hβ' : β' ≠ 0) {z : ℂ}
    (h : ∀ (η : F) (s : ℂ), η ≠ 0 → 1 < s.re →
      Kt (B.psiS hG.ne_bot) hG Φ β η s = z * Kt (B.psiS hG.ne_bot) hG Ψ β' η s) :
    Kir hG hz6 T Φ β = z * Kir hG hz6 T Ψ β' := by
  rw [Kir_of_ne hG hz6 T Φ hβ, Kir_of_ne hG hz6 T Ψ hβ']
  refine tau_congr_F hG hz6 T one_ne_zero fun c s hc hs => ?_
  have h1 : ((1 : SInt 𝔪) : F) = 1 := rfl
  rw [h1, ← Kt_of_ne _ hG Φ hβ, ← Kt_of_ne _ hG Ψ hβ']
  exact h c s hc hs

/-- **(K4)** `𝒦_{Ã(β₀)Φ}(β) = ⟨β, β₀⟩ 𝒦_Φ(β β₀)`. -/
theorem Kir_torusT (Φ : GSection ι P 𝔪) {β β₀ : F} (hβ : β ≠ 0) (hβ₀ : β₀ ≠ 0) :
    Kir hG hz6 T (Φ.torusT hG β₀ hβ₀) β = brk ι P 𝔪 β β₀ * Kir hG hz6 T Φ (β * β₀) :=
  Kir_congr hG hz6 T hβ (mul_ne_zero hβ hβ₀) fun η s _ _ => Kt_torusT _ hG Φ hβ hβ₀ η s

/-! ### The class decomposition and the majorant -/

end tau

end ArtinKP.G1
end
end

section
-- module Solutions.Artin.KP.GK_E
/-! # WP-GK, file 1: Theorem E without hypotheses, `hsm`, `hne`, Lemma KW

Setting of the cut: `hG : Good 𝔪`, `hz6`, `g : AllowedGen ι 𝔪`, `hgood` (every exterior prime is
`C3I.Good`), `hd : DD.DiffInS 𝔪`.  The theta functional is WP-T's `T.theta hG hz6`.

* `hsm`: the scalar law `SmulOn {Re s > 1}` of `T.theta` (G1's hypothesis `hsm`).
* `per_all`: cube periodicity at every exterior prime (from `F.per`).
* **`tau_eq_coefF'`** (Theorem E): `τ_Φ(ν) = N(νR)^{1/3} · coefF' g ⊤ (rowOf ν) · τ_{Ã(ν)Φ}(1)`;
  `tau_eq_Kir`: the same with G1's Kirillov function.
* **`hne`**: some Kirillov value is nonzero (G1's hypothesis `hne`).
* `tau_eq_zero_of_theta`: `θ_Φ = 0 ⇒ τ_Φ(ν) = 0` for every `ν ∈ R ∖ 0` (converse of (C10′)).
* `theta_wSec_eq_zero`: `θ_Φ = 0 ⇒ θ_{wΦ} = 0` (Corollary N, `N2.theta_eq_zero_iff`).
* **`KW`**: MATH3's Lemma KW in G1's form `G1.KW hG hz6 (T.theta hG hz6)`.
-/

open scoped MatrixGroups ComplexConjugate ENNReal Topology
open MeasureTheory Set NumberField Filter IsDedekindDomain ArtinPrimitiveRoots Metric

set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.GK

open ArtinKP.A ArtinKP.S ArtinKP.X ArtinKP.B1 ArtinKP.B ArtinKP.C5 ArtinKP.K ArtinKP.RF ArtinKP.N
  ArtinKP.B7

noncomputable section

variable {F : Type*} [Field F] [NumberField F] [IsTotallyComplex F] {𝔪 : Ideal (𝓞 F)}
  {ι : F →+* ℂ} {P : CubicPkg F}

variable (hG : Good 𝔪) {z6 : 𝓞 F} (hz6 : IsPrimitiveRoot z6 6)

/-! ### `θ = 0 ⇒ τ ≡ 0`, and `θ_Φ = 0 ⇒ θ_{wΦ} = 0` -/

/-- **`θ_Φ = 0 ⇒ θ_{σΦ} = 0`** for `σ ∈ SL₂(R)` (Corollary N in the form
`N2.theta_eq_zero_iff`: the residues at all cusps are permuted). -/
theorem theta_translate_eq_zero (Φ : GSection ι P 𝔪) (σ : SL(2, SInt 𝔪))
    (Γ Γ' : Subgroup (SL(2, 𝓞 F))) [Γ.FiniteIndex] [Γ'.FiniteIndex]
    (hΓ : Inv Γ (Φ.twist hG hz6))
    (hΓ' : Inv Γ' ((S2.GSection.translate hG σ Φ).twist hG hz6))
    (h : C5.theta Γ (Φ.twist hG hz6) = 0) :
    C5.theta Γ' ((S2.GSection.translate hG σ Φ).twist hG hz6) = 0 := by
  rw [S2.GSection.twist_translate] at hΓ' ⊢
  rw [N2.theta_eq_zero_iff_forall_zPsi_translate_eq_zero P hG hz6 hΓ']
  intro ρ
  rw [← TSection.translate_mul]
  exact (N2.theta_eq_zero_iff_forall_zPsi_translate_eq_zero P hG hz6 hΓ).mp h _

/-! ### Lemma KW -/

section KW

variable (g : AllowedGen ι 𝔪)
  (hgood : ∀ (Q : Ideal (𝓞 F)) (hQ : Q.IsPrime) (hext : IsExterior 𝔪 Q),
    C3I.Good 𝔪 (⟨Q, hQ, hext.1⟩ : HeightOneSpectrum (𝓞 F)))

include g hgood in
/-- **Lemma KW** (MATH3 §4.2) in G1's form: if `𝒦_Φ ≡ 0` on `F^×` then `𝒦_{wΦ} ≡ 0` on `F^×`.
At the level of `L²` classes: Theorem E, (C10′), Corollary N, the converse of (C10′), (W). -/
theorem kw_theta_of_diffInS_oai (hd : DD.DiffInS 𝔪) : G1.KW hG hz6 (T.theta (ι := ι) (P := P) hG hz6) := by
  intro Φ hΦ β hβ
  have hβi : β⁻¹ ≠ 0 := inv_ne_zero hβ
  set Φ' : GSection ι P 𝔪 := Φ.torusT hG β⁻¹ hβi with hΦ'
  -- `τ_{Φ'} ≡ 0` by Theorem E
  have h1 : ∀ ν : SInt 𝔪, ν ≠ 0 → T.tau hG hz6 Φ' ν = 0 := by
    intro ν hν
    have hνF : (ν : F) ≠ 0 := T.coe_ne_zero hν
    rw [tau_eq_rpow_mul_coefF_mul_kir hG hz6 g hgood ⟨ν, hν⟩ Φ', hΦ',
      G1.Kir_torusT hG hz6 _ Φ hνF hβi, hΦ _ (mul_ne_zero hνF hβi), mul_zero, mul_zero]
  -- `θ_{Φ'} = 0`
  have := C9.stabGroup_finiteIndex P hG hz6 (Φ'.twist hG hz6)
  have h2 := C9.theta_eq_zero_of_tau' hG hz6 hd Φ' (C9.stabGroup (Φ'.twist hG hz6))
    (C9.inv_stabGroup _) h1
  -- `θ_{wΦ'} = 0`
  have := C9.stabGroup_finiteIndex P hG hz6 ((G1.wSec hG Φ').twist hG hz6)
  have h3 : C5.theta (C9.stabGroup ((G1.wSec hG Φ').twist hG hz6))
      ((G1.wSec hG Φ').twist hG hz6) = 0 :=
    theta_translate_eq_zero hG hz6 Φ' (_root_.ArtinKP.S.wMat 𝔪) _ _ (C9.inv_stabGroup _) (C9.inv_stabGroup _) h2
  -- `τ_{wΦ'}(1) = 0`
  have h4 := tau_eq_zero_of_theta hG hz6 (G1.wSec hG Φ') _ (C9.inv_stabGroup _) h3
    (one_ne_zero (α := SInt 𝔪))
  -- (W)
  rw [hΦ', G1.w_torusT hG Φ hβi, G1.scal, T.tau_smulFun hG hz6 _ one_ne_zero] at h4
  have hne : ((absS 𝔪 β⁻¹ : ℝ) : ℂ) ^ ((1 : ℂ) * (4 / 3) + -2) ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff]
    exact fun h => (absS_pos hβi).ne' (Complex.ofReal_eq_zero.mp h.1)
  have h5 := (mul_eq_zero.mp h4).resolve_left hne
  have h6 := G1.Kir_of_ne hG hz6 (T.theta hG hz6) (G1.wSec hG Φ) (inv_ne_zero hβi)
  have h7 := h6.trans h5
  rwa [inv_inv] at h7

end KW

end

end ArtinKP.GK
end

theorem solution.{u_1} : type_of% @ArtinKP.GK.kw_theta_of_diffInS_oai.{u_1} := @ArtinKP.GK.kw_theta_of_diffInS_oai.{u_1}
