-- Prove2me | solution 1 for ArtinKP.G2a.thetaT_translate
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T10:10:39.272796+00:00
-- url     : https://prove2.me/submissions/79c57bc4-c97f-4b51-8937-69e851d12a9e

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
import Theorems.Thm_ArtinKP_C9_ae_eq_htC_of_coeff
import Theorems.Thm_ArtinKP_G2a_coeff_thetaS_freq
import Theorems.Thm_ArtinKP_G2a_coeff_thetaS_of_ne
import Theorems.Thm_ArtinKP_G2a_continuous_thetaS
import Theorems.Thm_ArtinKP_G2a_thetaS_smul_gammaN
import Theorems.Thm_ArtinKP_GL_eisEigen_of_two_lt_re
import Theorems.Thm_ArtinKP_N_cf_theta
import Theorems.Thm_ArtinKP_N_coeff_resPart_add_hInt
import Theorems.Thm_ArtinKP_N_differentiable_hInt
import Theorems.Thm_ArtinKP_N_integral_box_theta_eq_of_tendsto_ray
import Theorems.Thm_ArtinKP_N_lift_theta_translate
import Theorems.Thm_ArtinKP_T_coeffFunctional_theta_twist_eq
import Theorems.Thm_ArtinKP_X_X_isPOU_pou
import Theorems.Thm_ArtinKP_X_X_tsum_indicator_box_le_boxMult

section
-- module Solutions.Artin.KP.X_Space
attribute [-instance] _root_.ArtinKP.X.instContinuousConstSMulSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instContinuousConstSMulSubgroup _root_.ArtinKP.X.instIsFiniteMeasureOnCompactsXVol _root_.ArtinKP.X.instIsFiniteMeasureXRestrictVolBox _root_.ArtinKP.X.instMeasurableConstSMulSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instMulActionSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatRingOfIntegersXVol _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-! # WP-X, file 3: the space `X = (H³)^r`

`X F = InfinitePlace F → H3`, the action of `G∞ = InfinitePlace F → SL(2,ℂ)` and of `SL(2,F)`
(through the embeddings `w.embedding`), heights, pair heights, the invariant measure and the
torus `a(y)`.
-/

open scoped MatrixGroups ComplexConjugate ENNReal
open MeasureTheory Set NumberField

set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.X

noncomputable section

variable (F : Type*) [Field F] [NumberField F]

variable {F}

namespace X

lemma ht_pos (P : X F) : 0 < ht P := Finset.prod_pos fun w _ => P.v_pos w

end X

/-! ### Topology and measure -/

lemma X.continuous_ht : Continuous (X.ht : X F → ℝ) :=
  continuous_finsetProd _ fun w _ => X.continuous_v w

/-! ### Upper triangular elements, translations and the torus -/

end

end ArtinKP.X
end

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
-- module Solutions.Artin.KP.B1_Const
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-! # WP-B1, file 6: the constant term of `Tinf` (Lemma K) by unfolding and scaling

`constTerm S σ v = ∫_{ℂ^r/𝓞} ∑_{p ≠ ∞} ht_p(x, v)^σ dx` (integral over the fundamental cell `fundD`).
Unfolding over the free action of the translations `n(β)`, `β ∈ 𝓞_F`, on the classes `≠ ∞`
(`orbEquiv`) turns it into a sum of integrals over all of `ℂ^r`, each of which scales exactly like
`ht(v)^{2-σ}` (`lintegral_sHt_scale`).  Hence `constTerm S σ v = ht(v)^{2-σ} · constTerm S σ 1`
(`constTerm_scale`), and `constTerm S σ 1 < ∞` by the locally uniform convergence (`constTerm_one_lt_top`).
No zeta function and no strong approximation are needed.
-/

open scoped MatrixGroups ComplexConjugate ENNReal
open MeasureTheory Set NumberField Module

set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.B1

open ArtinKP.X

noncomputable section

variable {F : Type*} [Field F] [NumberField F]

theorem instCountableField : Countable F := by
  haveI _iCO := ArtinKP.X.instCountableRingOfIntegers (F := F)
  have : Function.Surjective (fun p : 𝓞 F × 𝓞 F => ((p.1 : F) / (p.2 : F))) := by
    intro z
    obtain ⟨x, y, -, h⟩ := IsFractionRing.div_surjective (A := 𝓞 F) z
    exact ⟨(x, y), h⟩
  exact this.countable

instance instCountableSPair {S : Finset (FinitePlace F)} : Countable (SPair S) := by
  haveI _iCF := ArtinKP.B1.instCountableField (F := F)
  have : Function.Injective (fun q : SPair S => (q.c, q.d)) := by
    intro q q' h
    exact SPair.ext (congrArg Prod.fst h) (congrArg Prod.snd h)
  exact this.countable

instance instCountablePairClass {S : Finset (FinitePlace F)} : Countable (PairClass S) :=
  Quotient.countable

variable [IsTotallyComplex F]

/-! ### The lattice `𝓞_F ⊂ ℂ^r` -/

lemma isFund : IsAddFundamentalDomain (latSub F) (fundD F) volume :=
  ZSpan.isAddFundamentalDomain' (latE (F := F)) volume

/-! ### Scaling -/

/-! ### Orbits of the translations on the classes `≠ ∞` -/

/-! ### The constant term -/

end

end ArtinKP.B1
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
-- module Solutions.Artin.KP.B_FourArch
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-!
# WP-B, part 2: the characters and the archimedean integral

* `eInf x = ∏_w archChar (-x_w)` on `ℂ^r`; `eInf (emb a) = exp(-2πi Tr a)` for `a ∈ F`.
* `psiS h𝔪 : SfChar 𝔪`, `ψ_{S_f}(x) = sAddChar 𝔪 x · conj (eInf (emb x))`; it is trivial on
  `𝔩_0`, and `eInf (emb x) = sAddChar 𝔪 x · conj ψ_{S_f}(x)` (`eInf_emb_eq`).
* `kerA v x = ∏_w v_w / (|x_w|² + v_w²)`; `I_{(c,d)}(x, v) = N_∞(c)⁻¹ · kerA v (x + d/c)`.
* `Winf s ν v = ∏_w jacquet s (-σ_w ν) v_w`; the integral of a shifted kernel against
  `conj eInf(ν x)` (`integral_shift_kernel`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped MatrixGroups ComplexConjugate
open NumberField IsDedekindDomain ArtinPrimitiveRoots MeasureTheory

noncomputable section

namespace ArtinKP.B

open ArtinKP.A ArtinKP.S ArtinKP.X ArtinKP.B1 ArtinKP.K

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}

/-! ### The archimedean character -/

theorem archChar_neg (z : ℂ) : archChar (-z) = conj (archChar z) := by
  rw [archChar_eq_re, archChar_eq_re, ← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, Complex.neg_re, map_ofNat]
  push_cast
  ring

/-! ### The `S_f`-character -/

/-! ### The archimedean kernel -/

theorem chiInf_eq_prod (ν : F) (x : InfinitePlace F → ℂ) :
    chiInf ν x = ∏ w, archChar (-(-(w.embedding ν)) * x w) := by
  rw [chiInf, eInf, map_prod]
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [← archChar_neg, Pi.mul_apply, emb_apply]
  congr 1
  ring

/-! ### Shifted kernels -/

end ArtinKP.B
end
end

section
-- module Solutions.Artin.KP.B_FourIndex
attribute [-instance] _root_.ArtinKP.N.instCountableSubtypeForallInfinitePlaceComplexMemAddSubgroupLatN _root_.ArtinKP.T.instCountableSubtypeForallInfinitePlaceComplexMemAddSubgroupMinLatN _root_.ArtinKP.T.instCountableSubtypeForallInfinitePlaceComplexMemAddSubgroupMinLatNTransLat _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-!
# WP-B, part 4: the index set of the unfolded sum

* `exists_sInt_sub_small`: strong approximation `F = R + 𝔩_M` (from `B7.hasWit_all`).
* `latR 𝔪 M = R ∩ 𝔩_M`, `transLat 𝔪 M = emb (R ∩ 𝔩_M) ⊂ ℂ^r` (the translation lattice `Λ_M`).
* `sec`: for `c ≠ 0` a section of `R → R/cR × F/𝔩_M`, `d ↦ (d mod c, d/c mod 𝔩_M)`.
* `thetaEquiv`: `((Σ a, R/c_a R) × F/𝔩_M) × Λ_M ≃ (R∖0)/Rˣ × R`,
  `(((a, α), u), b) ↦ (a, sec(α, u) + c_a b)` — MATH2's `R/cΛ ≅ R/cR × F_{S_f}/cΛ̂`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open NumberField IsDedekindDomain ArtinPrimitiveRoots

noncomputable section

namespace ArtinKP.B

open ArtinKP.A ArtinKP.S ArtinKP.X ArtinKP.B1 ArtinKP.E

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}

/-! ### Strong approximation -/

/-! ### The translation lattice -/

instance instCountableSInt : Countable (SInt 𝔪) :=
  haveI _iCF := ArtinKP.B1.instCountableField (F := F)
  (Subtype.val_injective : Function.Injective fun b : SInt 𝔪 => (b : F)).countable

instance instCountableSubtypeForallInfinitePlaceComplexMemAddSubgroupTransLat (M : ℤ) : Countable (transLat 𝔪 M) := (latREquiv 𝔪 M).symm.injective.countable

/-! ### The section -/

/-! ### The index equivalence -/

/-! ### Rows with `c ≠ 0` modulo units -/

end ArtinKP.B
end
end

section
-- module Solutions.Artin.KP.B_FourThm
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-!
# WP-B, part 8: the Fourier expansion at `∞` — statements

For a genuine section `Φ`, `Re s > 2`, `ν ∈ R`, a depth `M` valid for `(Φ, ν)`
(`ValidDepth hG Φ ν M`), and any fundamental cell `D` of finite volume of the translation
lattice `Λ_M = transLat 𝔪 M = emb (R ∩ 𝔩_M) ⊂ ℂ^r`:

* `fourier_coeff` (all `ν`), `fourier_coeff_ne_zero` (`ν ≠ 0`), `const_term` (`ν = 0`).

Normalizations: `chiInf ν x = conj e_∞(νx)`, `e_∞(x) = ∏_w archChar (-x_w)` (so
`e_∞ = exp(-2πi Tr)` on `F`); `dx` is Lebesgue measure on `ℂ^r = (ℝ²)^r`;
`Winf s ν v = ∏_w jacquet s (-σ_w ν) v_w`; `vol 𝔪 M = ∏_{v ∣ 𝔪} q_v^{-M}`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped MatrixGroups ComplexConjugate Pointwise
open NumberField IsDedekindDomain ArtinPrimitiveRoots MeasureTheory

noncomputable section

namespace ArtinKP.B

open ArtinKP.A ArtinKP.S ArtinKP.X ArtinKP.B1 ArtinKP.E ArtinKP.K

variable {F : Type*} [Field F] [NumberField F] [IsTotallyComplex F] {𝔪 : Ideal (𝓞 F)}
  {ι : F →+* ℂ} {P : CubicPkg F}

instance instCountableIdxI (M : ℤ) : Countable (IdxI 𝔪 M) := by
  haveI _iCF := ArtinKP.B1.instCountableField (F := F)
  have : Countable (Associates (SInt 𝔪)) := Associates.mk_surjective.countable
  have : ∀ c : SInt 𝔪, Countable (SInt 𝔪 ⧸ Ideal.span {c}) := fun c =>
    Ideal.Quotient.mk_surjective.countable
  have : Countable (F ⧸ lat 𝔪 M) := QuotientAddGroup.mk_surjective.countable
  infer_instance

/-! ### Characters on the cell -/

end ArtinKP.B
end
end

section
-- module Solutions.Artin.KP.B_Kub
attribute [-instance] _root_.ArtinKP.N2.levelGroup_finiteIndex _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-!
# WP-B, part 9: the Kubota series — convergence, holomorphy, the `E.Kubota` instance

* `kTerm`, `aCoeff`: `𝔞_Φ(ν, s) = ∑_{c ∈ (R∖0)/Rˣ} g(ν, c) · Lam Φ c ν s · N(c)^{-s}`, for every
  `ν ∈ R` (`ν = 0` gives the Dirichlet series of the constant term), with
  `Lam = S2.LamR ψ_{S_f}` (WP-S2's normalized finite Jacquet functional at a valid depth).
* `exists_majorant_kTerm`: locally uniform absolute convergence on `Re s > 2`
  (`|g(ν,c)| ≤ N(c)`, `S2.norm_Lam_le`, S-1, `∑ N(c)^{1-σ} < ∞`).
* `differentiableOn_aCoeff`: holomorphy on `Re s > 2`.
* `kubota hG hz6 : E.Kubota (S2.cubicSymbol …) (B7.sAdd 𝔪 _) (GSection ι P 𝔪)` — no hypothesis left.
* `fourier_coeff_aSer`, `const_term_aCoeff`: the Fourier coefficients in this normalization.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped MatrixGroups ComplexConjugate
open NumberField IsDedekindDomain ArtinPrimitiveRoots MeasureTheory

noncomputable section

namespace ArtinKP.B

open ArtinKP.A ArtinKP.S ArtinKP.X ArtinKP.B1 ArtinKP.E ArtinKP.K ArtinKP.B7

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}
  {ι : F →+* ℂ} {P : CubicPkg F}

variable [IsTotallyComplex F] (hG : Good 𝔪) {z6 : 𝓞 F} (hz6 : IsPrimitiveRoot z6 6)
  (Φ : GSection ι P 𝔪) (ν : SInt 𝔪)

/-- A valid depth exists for every section and frequency. -/
theorem exists_validDepth (ν : F) : ∃ M : ℤ, ValidDepth hG Φ ν M := by
  obtain ⟨M, h1, h2⟩ := S2.exists_valid hG (psiS hG.ne_bot) Φ ν
  exact ⟨M, h1, h2⟩

end ArtinKP.B
end
end

section
-- module Solutions.Artin.KP.BZ_Vol
attribute [-instance] _root_.ArtinKP.N.instCountableSubtypeForallInfinitePlaceComplexMemAddSubgroupLatN _root_.ArtinKP.T.instCountableSubtypeForallInfinitePlaceComplexMemAddSubgroupMinLatN _root_.ArtinKP.T.instCountableSubtypeForallInfinitePlaceComplexMemAddSubgroupMinLatNTransLat _root_.ArtinKP.X.instSigmaFiniteE1Mu1 _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-!
# WP-BZ, part 4: stub B-2 — the covolume of the translation lattice `Λ_M`

* `exists_fund_sublattice`, `measure_fund_sublattice` (Mathlib only): for countable subgroups
  `L' ≤ L` of finite index of a measurable additive group with an invariant measure, a
  fundamental domain of `L'` has measure `[L : L'] ·` that of a fundamental domain of `L`.
* `card_transLat_quot`: `[Λ_M : Λ_{M'}] = ∏_{v ∣ 𝔪} q_v^{M' - M}` for `M ≤ M'`
  (`S2.card_latD_quot` transported by strong approximation `F = R + 𝔩_{M'}`).
* `transLat_zero`: `Λ_0 = emb(𝓞_F)`.
* **`volume_cell`** (B-2): `vol(D) · vol(𝔩_M) = vol(B1.fundD F)` for every fundamental cell `D`
  of `Λ_M`, every `M : ℤ`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped Pointwise
open NumberField IsDedekindDomain ArtinPrimitiveRoots MeasureTheory

noncomputable section

namespace ArtinKP.BZ

/-! ### Fundamental domains of a sublattice -/

section abstract

variable {E : Type*} [AddCommGroup E] [MeasurableSpace E] [MeasurableAdd E]
  (μ : Measure E) [μ.IsAddLeftInvariant]

/-- From a fundamental domain of `L` to one of a subgroup `L' ≤ L` of finite index. -/
theorem exists_fund_sublattice {L' L : AddSubgroup E} [Countable L] (hle : L' ≤ L)
    [Finite (L ⧸ L'.addSubgroupOf L)] {D : Set E} (hD : IsAddFundamentalDomain L D μ) :
    ∃ D' : Set E, IsAddFundamentalDomain L' D' μ ∧
      μ D' = (Nat.card (L ⧸ L'.addSubgroupOf L) : ENNReal) * μ D := by
  classical
  set K := L'.addSubgroupOf L with hK
  let σ : L ⧸ K → L := fun q => Quotient.out q
  have hσ : ∀ q, (QuotientAddGroup.mk (σ q) : L ⧸ K) = q := fun q => Quotient.out_eq q
  have hσinj : ∀ q₁ q₂ : L ⧸ K, ((σ q₁ : L) : E) - ((σ q₂ : L) : E) ∈ L' → q₁ = q₂ := by
    intro q₁ q₂ h
    rw [← hσ q₁, ← hσ q₂, QuotientAddGroup.eq, hK, AddSubgroup.mem_addSubgroupOf]
    have : ((-(σ q₁) + σ q₂ : L) : E) = -(((σ q₁ : L) : E) - ((σ q₂ : L) : E)) := by
      push_cast
      abel
    rw [this]
    exact L'.neg_mem h
  let f : L ⧸ K → Set E := fun q => (σ q : L) +ᵥ D
  have hfm : ∀ q, NullMeasurableSet (f q) μ := fun q => hD.nullMeasurableSet_vadd (σ q)
  have hfd : Pairwise (Function.onFun (AEDisjoint μ) f) := by
    intro q₁ q₂ hq
    refine hD.aedisjoint fun h => hq (hσinj q₁ q₂ ?_)
    rw [h, sub_self]
    exact L'.zero_mem
  refine ⟨⋃ q, f q, ⟨NullMeasurableSet.iUnion hfm, ?_, ?_⟩, ?_⟩
  · -- covering
    filter_upwards [hD.ae_covers] with x hx
    obtain ⟨g, hg⟩ := hx
    set q : L ⧸ K := QuotientAddGroup.mk (-g) with hq
    have hmem : ((σ q : L) : E) + (g : E) ∈ L' := by
      have h1 : (QuotientAddGroup.mk (σ q) : L ⧸ K) = QuotientAddGroup.mk (-g) := hσ q
      rw [QuotientAddGroup.eq, hK, AddSubgroup.mem_addSubgroupOf] at h1
      have h2 : ((σ q : L) : E) + (g : E) = -((-(σ q) + -g : L) : E) := by
        push_cast
        abel
      rw [h2]
      exact L'.neg_mem h1
    refine ⟨⟨_, hmem⟩, Set.mem_iUnion.2 ⟨q, ?_⟩⟩
    refine ⟨g +ᵥ x, hg, ?_⟩
    change ((σ q : L) : E) + ((g : E) + x) = (((σ q : L) : E) + (g : E)) + x
    rw [add_assoc]
  · -- disjointness
    intro g₁ g₂ hg
    change AEDisjoint μ (g₁ +ᵥ ⋃ q, f q) (g₂ +ᵥ ⋃ q, f q)
    rw [Set.vadd_set_iUnion, Set.vadd_set_iUnion, AEDisjoint.iUnion_left_iff]
    intro q₁
    rw [AEDisjoint.iUnion_right_iff]
    intro q₂
    have e : ∀ (g : L') (q : L ⧸ K),
        g +ᵥ f q = ((⟨(g : E), hle g.2⟩ + σ q : L)) +ᵥ D := by
      intro g q
      ext y
      constructor
      · rintro ⟨z, ⟨w, hw, rfl⟩, rfl⟩
        exact ⟨w, hw, by
          change ((g : E) + ((σ q : L) : E)) + w = (g : E) + (((σ q : L) : E) + w)
          rw [add_assoc]⟩
      · rintro ⟨w, hw, rfl⟩
        exact ⟨(σ q : L) +ᵥ w, ⟨w, hw, rfl⟩, by
          change (g : E) + (((σ q : L) : E) + w) = ((g : E) + ((σ q : L) : E)) + w
          rw [add_assoc]⟩
    rw [e, e]
    refine hD.aedisjoint fun h => hg ?_
    have h' : (g₁ : E) + ((σ q₁ : L) : E) = (g₂ : E) + ((σ q₂ : L) : E) :=
      congrArg (fun z : L => (z : E)) h
    have hq : q₁ = q₂ := by
      refine hσinj q₁ q₂ ?_
      have : ((σ q₁ : L) : E) - ((σ q₂ : L) : E) = (g₂ : E) - (g₁ : E) := by
        rw [sub_eq_sub_iff_add_eq_add, add_comm, h', add_comm]
      rw [this]
      exact L'.sub_mem g₂.2 g₁.2
    rw [hq] at h'
    exact Subtype.ext (add_right_cancel h')
  · -- measure
    let _ := Fintype.ofFinite (L ⧸ K)
    rw [measure_iUnion₀ hfd hfm, tsum_fintype]
    have : ∀ q, μ (f q) = μ D := fun q => by
      change μ (((σ q : L) : E) +ᵥ D) = μ D
      exact measure_vadd μ _ D
    rw [Finset.sum_congr rfl fun q _ => this q, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, Nat.card_eq_fintype_card]

/-- A fundamental domain of a sublattice `L' ≤ L` of finite index has measure
`[L : L'] · μ(D)`. -/
theorem measure_fund_sublattice {L' L : AddSubgroup E} [Countable L] (hle : L' ≤ L)
    [Finite (L ⧸ L'.addSubgroupOf L)] {D D' : Set E} (hD : IsAddFundamentalDomain L D μ)
    (hD' : IsAddFundamentalDomain L' D' μ) :
    μ D' = (Nat.card (L ⧸ L'.addSubgroupOf L) : ENNReal) * μ D := by
  have : Countable L' := (AddSubgroup.inclusion_injective hle).countable
  obtain ⟨D'', h1, h2⟩ := exists_fund_sublattice μ hle hD
  rw [← h2]
  exact hD'.measure_eq h1

end abstract

/-- Two surjective homomorphisms with the same kernel have equinumerous targets. -/
theorem card_eq_of_ker_eq {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    (f : A →+ B) (g : A →+ C) (hf : Function.Surjective f) (hg : Function.Surjective g)
    (h : f.ker = g.ker) : Nat.card B = Nat.card C := by
  rw [← Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective f hf).toEquiv,
    ← Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective g hg).toEquiv, h]

open ArtinKP.A ArtinKP.S ArtinKP.X ArtinKP.B1 ArtinKP.B

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}

theorem transLat_mono {M M' : ℤ} (h : M ≤ M') : transLat 𝔪 M' ≤ transLat 𝔪 M := by
  rintro x ⟨b, hb, rfl⟩
  exact ⟨b, Small.mono (𝔪 := 𝔪) h hb, rfl⟩

theorem embR_mem_transLat {M : ℤ} {b : SInt 𝔪} :
    (embR b : InfinitePlace F → ℂ) ∈ transLat 𝔪 M ↔ b ∈ latR 𝔪 M := by
  constructor
  · rintro ⟨b', hb', h⟩
    rwa [← embR_injective h]
  · intro hb
    exact ⟨b, hb, rfl⟩

/-- `[Λ_M : Λ_{M'}] = ∏_{v ∣ 𝔪} q_v^{M' - M}` for `M ≤ M'`. -/
theorem card_transLat_quot (h𝔪 : 𝔪 ≠ ⊥) {M M' : ℤ} (h : M ≤ M') :
    Nat.card (transLat 𝔪 M ⧸ (transLat 𝔪 M').addSubgroupOf (transLat 𝔪 M))
      = ∏ v ∈ CubicPkg.sFin 𝔪, Ideal.absNorm v.asIdeal ^ (M' - M).toNat := by
  rw [← S2.card_latD_quot h𝔪 (k := fun _ => M) (k' := fun _ => M') fun _ _ => h]
  -- the two maps out of `R ∩ 𝔩_M`
  let f₀ : latR 𝔪 M →+ transLat 𝔪 M := (embR (𝔪 := 𝔪)).addSubgroupMap (latR 𝔪 M)
  have hf₀ : Function.Surjective f₀ := (embR (𝔪 := 𝔪)).addSubgroupMap_surjective (latR 𝔪 M)
  let g₀ : latR 𝔪 M →+ S2.latD 𝔪 (fun _ => M) :=
    { toFun := fun b => ⟨((b : SInt 𝔪) : F), b.2⟩
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  let f : latR 𝔪 M →+ transLat 𝔪 M ⧸ (transLat 𝔪 M').addSubgroupOf (transLat 𝔪 M) :=
    (QuotientAddGroup.mk' _).comp f₀
  let g : latR 𝔪 M →+
      S2.latD 𝔪 (fun _ => M) ⧸ (S2.latD 𝔪 (fun _ => M')).addSubgroupOf (S2.latD 𝔪 (fun _ => M)) :=
    (QuotientAddGroup.mk' _).comp g₀
  have hf : Function.Surjective f := (QuotientAddGroup.mk'_surjective _).comp hf₀
  have hg : Function.Surjective g := by
    intro y
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective y
    obtain ⟨r, hr⟩ := exists_sInt_sub_small h𝔪 M' (x : F)
    have hrM : Small 𝔪 M ((r : SInt 𝔪) : F) := by
      have h1 : Small 𝔪 M ((x : F) - (r : F)) := Small.mono (𝔪 := 𝔪) h hr
      have h2 : Small 𝔪 M (x : F) := x.2
      have := h2.sub h1
      rwa [sub_sub_cancel] at this
    refine ⟨⟨r, hrM⟩, ?_⟩
    change (QuotientAddGroup.mk (g₀ ⟨r, hrM⟩) : S2.latD 𝔪 (fun _ => M) ⧸ _) = QuotientAddGroup.mk x
    rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
    change Small 𝔪 M' (-((r : SInt 𝔪) : F) + (x : F))
    rwa [neg_add_eq_sub]
  refine card_eq_of_ker_eq f g hf hg ?_
  ext b
  rw [AddMonoidHom.mem_ker, AddMonoidHom.mem_ker]
  change (QuotientAddGroup.mk (f₀ b) : transLat 𝔪 M ⧸ _) = 0 ↔
    (QuotientAddGroup.mk (g₀ b) : S2.latD 𝔪 (fun _ => M) ⧸ _) = 0
  rw [QuotientAddGroup.eq_zero_iff, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf,
    AddSubgroup.mem_addSubgroupOf]
  change (embR (b : SInt 𝔪) : InfinitePlace F → ℂ) ∈ transLat 𝔪 M' ↔ _
  rw [embR_mem_transLat]
  rfl

variable [IsTotallyComplex F]

/-- `Λ_0 = emb(𝓞_F)`. -/
theorem transLat_zero (𝔪 : Ideal (𝓞 F)) : transLat 𝔪 0 = latSub F := by
  ext x
  rw [mem_latSub]
  constructor
  · rintro ⟨b, hb, rfl⟩
    have hall : ∀ v : HeightOneSpectrum (𝓞 F), v.valuation F ((b : SInt 𝔪) : F) ≤ 1 := by
      intro v
      by_cases hv : 𝔪 ≤ v.asIdeal
      · have := hb v hv
        rwa [neg_zero, WithZero.exp_zero] at this
      · exact sInt_val_le_one b v hv
    obtain ⟨β, hβ⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one F _ hall
    exact ⟨β, by rw [embR_apply, ← hβ]⟩
  · rintro ⟨β, rfl⟩
    refine ⟨algebraMap (𝓞 F) (SInt 𝔪) β, fun v _ => ?_, rfl⟩
    rw [neg_zero, WithZero.exp_zero]
    exact v.valuation_le_one β

/-- **Stub B-2, proved** (only `𝔪 ≠ ⊥` is used): `vol(D) · vol(𝔩_M) = covol(𝓞_F)`. -/
theorem volume_cell' (h𝔪 : 𝔪 ≠ ⊥) (M : ℤ) {D : Set (InfinitePlace F → ℂ)}
    (hD : IsAddFundamentalDomain (transLat 𝔪 M) D volume) :
    volume D * ENNReal.ofReal (vol 𝔪 M) = volume (B1.fundD F) := by
  classical
  set M' : ℤ := max M 0 with hM'
  have h1 : M ≤ M' := le_max_left _ _
  have h0 : (0 : ℤ) ≤ M' := le_max_right _ _
  have hq : ∀ v : HeightOneSpectrum (𝓞 F), 0 < Ideal.absNorm v.asIdeal := fun v => by
    have := NumberField.HeightOneSpectrum.one_lt_absNorm v
    omega
  set n₁ : ℕ := ∏ v ∈ CubicPkg.sFin 𝔪, Ideal.absNorm v.asIdeal ^ (M' - M).toNat with hn₁
  set n₀ : ℕ := ∏ v ∈ CubicPkg.sFin 𝔪, Ideal.absNorm v.asIdeal ^ (M' - 0).toNat with hn₀
  have hn₁0 : n₁ ≠ 0 := Finset.prod_ne_zero_iff.2 fun v _ => pow_ne_zero _ (hq v).ne'
  have hn₀0 : n₀ ≠ 0 := Finset.prod_ne_zero_iff.2 fun v _ => pow_ne_zero _ (hq v).ne'
  have hc₁ := card_transLat_quot h𝔪 h1
  have hc₀ := card_transLat_quot h𝔪 h0
  have hfin₁ : Finite (transLat 𝔪 M ⧸ (transLat 𝔪 M').addSubgroupOf (transLat 𝔪 M)) :=
    Nat.finite_of_card_ne_zero (by rw [hc₁]; exact hn₁0)
  have hfin₀ : Finite (transLat 𝔪 0 ⧸ (transLat 𝔪 M').addSubgroupOf (transLat 𝔪 0)) :=
    Nat.finite_of_card_ne_zero (by rw [hc₀]; exact hn₀0)
  have hF : IsAddFundamentalDomain (transLat 𝔪 0) (B1.fundD F) volume := by
    rw [transLat_zero]
    exact B1.isFund
  obtain ⟨D', hD', hvol₀⟩ := exists_fund_sublattice volume (transLat_mono h0) hF
  have hvol₁ := measure_fund_sublattice volume (transLat_mono h1) hD hD'
  rw [hc₀] at hvol₀
  rw [hc₁] at hvol₁
  -- `vol 𝔪 M = n₁ / n₀`
  have hvolM : vol 𝔪 M = (n₁ : ℝ) / (n₀ : ℝ) := by
    rw [vol, hn₁, hn₀, Nat.cast_prod, Nat.cast_prod, ← Finset.prod_div_distrib]
    refine Finset.prod_congr rfl fun v _ => ?_
    have hqv : (Ideal.absNorm v.asIdeal : ℝ) ≠ 0 := by exact_mod_cast (hq v).ne'
    push_cast
    rw [← zpow_natCast, ← zpow_natCast, Int.toNat_of_nonneg (by omega),
      Int.toNat_of_nonneg (by omega), ← zpow_sub₀ hqv]
    congr 1
    ring
  have hn₀pos : (0 : ℝ) < n₀ := by exact_mod_cast Nat.pos_of_ne_zero hn₀0
  rw [hvolM, ENNReal.ofReal_div_of_pos hn₀pos, ENNReal.ofReal_natCast, ENNReal.ofReal_natCast,
    ← mul_div_assoc, mul_comm (volume D), ← hvol₁, hvol₀, mul_comm,
    ENNReal.mul_div_cancel_right (by exact_mod_cast hn₀0) (ENNReal.natCast_ne_top n₀)]

end ArtinKP.BZ
end
end

section
-- module Solutions.Artin.KP.X2_Chart
attribute [-instance] _root_.ArtinKP.B.instCountableIdxI _root_.ArtinKP.B.instCountableSInt _root_.ArtinKP.B1.instCountablePairClass _root_.ArtinKP.X.instContinuousConstSMulSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instContinuousConstSMulSubgroup _root_.ArtinKP.X.instIsFiniteMeasureOnCompactsXVol _root_.ArtinKP.X.instIsFiniteMeasureXRestrictVolBox _root_.ArtinKP.X.instMeasurableConstSMulSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instMulActionSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatRingOfIntegersXVol _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
attribute [-simp] _root_.ArtinKP.X.e1_one _root_.ArtinKP.X.e1_two _root_.ArtinKP.X.e1_zero
/-! # WP-X2, file 1: the logarithmic chart of `X = (H³)^r`

`chart F : (InfinitePlace F → ℂ × ℝ) ≃ₜ X F`, `(x_w, t_w)_w ↦ (x_w, exp t_w)_w`.  In this chart
`X.vol F` is Lebesgue measure with the smooth density `rho y = exp (-2 ∑_w t_w)`
(`measurePreserving_chart`).  All calculus on `X` is done in this chart: a function on `X` is
smooth iff its pull-back to the vector space `Coord F` is.

Also: Tonelli for products of functions of one coordinate on a finite product
(`lintegral_fintype_prod_eq_prod`) and `pi_withDensity`.
-/

open scoped MatrixGroups ComplexConjugate ENNReal
open MeasureTheory Set NumberField

set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.X

noncomputable section

/-! ### Products of densities -/

section PiDensity

set_option backward.isDefEq.respectTransparency false in
theorem lintegral_fin_nat_prod_eq_prod {n : ℕ} {E : Fin n → Type*}
    {mE : ∀ i, MeasurableSpace (E i)} {μ : (i : Fin n) → Measure (E i)} [∀ i, SigmaFinite (μ i)]
    (f : (i : Fin n) → E i → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x : (i : Fin n) → E i, ∏ i, f i (x i) ∂(Measure.pi μ) = ∏ i, ∫⁻ x, f i x ∂(μ i) := by
  induction n with
  | zero => simp
  | succ n n_ih =>
      calc
        _ = ∫⁻ x : E 0 × ((i : Fin n) → E (Fin.succ i)),
            f 0 x.1 * ∏ i : Fin n, f (Fin.succ i) (x.2 i)
            ∂((μ 0).prod (Measure.pi (fun i ↦ μ i.succ))) := by
          rw [← ((measurePreserving_piFinSuccAbove μ 0).symm).lintegral_comp_emb
            (MeasurableEquiv.measurableEmbedding _)]
          simp_rw [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
            Fin.prod_univ_succ, Fin.insertNth_zero, Equiv.coe_fn_mk, Fin.cons_succ,
            Fin.zero_succAbove, cast_eq, Fin.cons_zero]
        _ = (∫⁻ x, f 0 x ∂μ 0)
            * ∏ i : Fin n, ∫⁻ (x : E (Fin.succ i)), f (Fin.succ i) x ∂(μ i.succ) := by
          rw [← n_ih (fun i => f i.succ) (fun i => hf i.succ),
            ← lintegral_prod_mul (hf 0).aemeasurable]
          exact (Finset.measurable_prod _ fun i _ =>
            (hf i.succ).comp (measurable_pi_apply i)).aemeasurable
        _ = ∏ i, ∫⁻ x, f i x ∂(μ i) := by rw [Fin.prod_univ_succ]

variable {ι : Type*} [Fintype ι]

/-- Tonelli on a finite product, for a product of functions of one coordinate each. -/
theorem lintegral_fintype_prod_eq_prod {E : ι → Type*} (f : (i : ι) → E i → ℝ≥0∞)
    {mE : ∀ i, MeasurableSpace (E i)} {μ : (i : ι) → Measure (E i)} [∀ i, SigmaFinite (μ i)]
    (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x : (i : ι) → E i, ∏ i, f i (x i) ∂(Measure.pi μ) = ∏ i, ∫⁻ x, f i x ∂(μ i) := by
  let e := (Fintype.equivFin ι).symm
  rw [← (measurePreserving_piCongrLeft _ e).lintegral_comp_emb
    (MeasurableEquiv.measurableEmbedding _)]
  simp_rw [← e.prod_comp, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_apply]
  rw [lintegral_fin_nat_prod_eq_prod (fun i => f (e i)) (fun i => hf (e i))]

/-- A product of measures with densities is the product measure with the product density. -/
theorem pi_withDensity {α : ι → Type*} [∀ i, MeasurableSpace (α i)] (μ : ∀ i, Measure (α i))
    [∀ i, SigmaFinite (μ i)] (f : ∀ i, α i → ℝ≥0∞) (hf : ∀ i, Measurable (f i))
    [∀ i, SigmaFinite ((μ i).withDensity (f i))] :
    Measure.pi (fun i => (μ i).withDensity (f i)) =
      (Measure.pi μ).withDensity (fun x => ∏ i, f i (x i)) := by
  refine Measure.pi_eq fun s hs => ?_
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs), ← lintegral_indicator (MeasurableSet.univ_pi hs)]
  have h : ∀ x : ∀ i, α i, (Set.pi univ s).indicator (fun x => ∏ i, f i (x i)) x =
      ∏ i, (s i).indicator (f i) (x i) := by
    intro x
    by_cases hx : x ∈ Set.pi univ s
    · rw [indicator_of_mem hx]
      exact Finset.prod_congr rfl fun i _ => (indicator_of_mem (hx i (mem_univ i)) _).symm
    · rw [indicator_of_notMem hx]
      simp only [mem_pi, mem_univ, forall_true_left, not_forall] at hx
      obtain ⟨i, hi⟩ := hx
      exact (Finset.prod_eq_zero (Finset.mem_univ i) (indicator_of_notMem hi _)).symm
  simp_rw [h]
  rw [lintegral_fintype_prod_eq_prod _ (fun i => (hf i).indicator (hs i))]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [withDensity_apply _ (hs i), lintegral_indicator (hs i)]

end PiDensity

/-! ### One factor -/

lemma map_exp_withDensity :
    Measure.map Real.exp
        ((volume : Measure ℝ).withDensity fun t => ENNReal.ofReal (Real.exp (-2 * t))) =
      ((volume : Measure ℝ).restrict (Ioi 0)).withDensity fun v => ENNReal.ofReal ((v ^ 3)⁻¹) := by
  ext s hs
  rw [Measure.map_apply Real.measurable_exp hs, withDensity_apply _ (Real.measurable_exp hs),
    withDensity_apply _ hs, Measure.restrict_restrict hs]
  have h := lintegral_image_eq_lintegral_abs_deriv_mul (s := Real.exp ⁻¹' s) (f := Real.exp)
    (f' := Real.exp) (Real.measurable_exp hs)
    (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt) Real.exp_injective.injOn
    (fun v => ENNReal.ofReal ((v ^ 3)⁻¹))
  rw [image_preimage_eq_inter_range, Real.range_exp] at h
  rw [h]
  refine setLIntegral_congr_fun (Real.measurable_exp hs) fun t _ => ?_
  rw [← ENNReal.ofReal_mul (abs_nonneg _), abs_of_pos (Real.exp_pos t), ← Real.exp_nat_mul,
    ← Real.exp_neg, ← Real.exp_add]
  congr 2
  push_cast
  ring

lemma map_coe_chart1 : Measure.map (fun p : E1 => (p.1, Real.exp p.2)) mu1 = amb := by
  have h0 : mu1 = (volume : Measure ℂ).prod
      ((volume : Measure ℝ).withDensity fun t => ENNReal.ofReal (Real.exp (-2 * t))) := by
    rw [prod_withDensity_right (by fun_prop)]
    rfl
  have h2 : (volume : Measure ℂ).prod ((volume : Measure ℝ).restrict (Ioi 0)) =
      (volume : Measure (ℂ × ℝ)).restrict upper := by
    have hu : upper = (univ : Set ℂ) ×ˢ Ioi (0 : ℝ) := by
      ext p; simp [upper]
    rw [hu, Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ]
  have h3 : (fun p : E1 => (p.1, Real.exp p.2)) = Prod.map id Real.exp := rfl
  rw [h0, h3, ← Measure.map_prod_map _ _ measurable_id Real.measurable_exp, Measure.map_id,
    map_exp_withDensity, prod_withDensity_right (by fun_prop), h2]
  rfl

/-- `H3.vol` is the image of `exp (-2t) dx dt` under the chart. -/
theorem map_chart1 : Measure.map chart1 mu1 = H3.vol := by
  have h := map_coe_chart1
  have hc : (fun p : E1 => (p.1, Real.exp p.2)) = H3.coe ∘ chart1 := rfl
  rw [hc, ← Measure.map_map H3.measurableEmbedding_coe.measurable chart1.continuous.measurable] at h
  unfold H3.vol
  rw [← h, H3.measurableEmbedding_coe.comap_map]

/-! ### The product -/

variable (F : Type*) [Field F] [NumberField F]

variable {F}

lemma rho_pos (y : Coord F) : 0 < rho y := Real.exp_pos _

lemma rho_eq_prod (y : Coord F) : rho y = ∏ w, rho1 (y w) := by
  unfold rho rho1
  rw [Finset.mul_sum, Real.exp_sum]

lemma continuous_rho : Continuous (rho : Coord F → ℝ) := by
  unfold rho; fun_prop

variable (F)

lemma muE_eq_pi : muE F = Measure.pi fun _ : InfinitePlace F => mu1 := by
  unfold mu1
  rw [pi_withDensity _ _ (fun _ => by unfold rho1; fun_prop)]
  unfold muE
  congr 1
  funext y
  rw [rho_eq_prod]
  exact ENNReal.ofReal_prod_of_nonneg fun w _ => (Real.exp_pos (-2 * (y w).2)).le

/-- **The chart carries `exp (-2 ∑ t_w) dy` to the invariant measure.** -/
theorem measurePreserving_chart : MeasurePreserving (chart F) (muE F) (X.vol F) := by
  rw [muE_eq_pi]
  exact measurePreserving_pi (fun _ => mu1) (fun _ => H3.vol)
    (fun _ => ⟨chart1.continuous.measurable, map_chart1⟩)

end

end ArtinKP.X
end

section
-- module Solutions.Artin.KP.X_L2
attribute [-instance] _root_.ArtinKP.B.instCountableSInt _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
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

lemma liftQ_smul (u : Lp ℂ 2 (quotMeasure G η μ)) (g : G) (a : α) :
    liftQ u (g • a) = liftQ u a := by
  unfold liftQ; rw [mk_smul]

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
attribute [-instance] _root_.ArtinKP.B.instCountableIdxI _root_.ArtinKP.B.instCountableSInt _root_.ArtinKP.B.instCountableSubtypeForallInfinitePlaceComplexMemAddSubgroupTransLat _root_.ArtinKP.B1.instCountablePairClass _root_.ArtinKP.B1.instCountableSubtypeForallInfinitePlaceComplexMemAddSubgroupLatSub _root_.ArtinKP.N.instCountableSubtypeForallInfinitePlaceComplexMemAddSubgroupLatN _root_.ArtinKP.T.instCountableSubtypeForallInfinitePlaceComplexMemAddSubgroupMinLatN _root_.ArtinKP.T.instCountableSubtypeForallInfinitePlaceComplexMemAddSubgroupMinLatNTransLat _root_.ArtinKP.X.instContinuousConstSMulSubgroup _root_.ArtinKP.X.instIsFiniteMeasureOnCompactsXVol _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
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

lemma X.lift_smul (Γ : Subgroup (SL(2, 𝓞 F))) (u : X.L2 Γ) (γ : Γ) (P : X F) :
    X.lift Γ u (γ • P) = X.lift Γ u P :=
  haveI _iCSL := ArtinKP.X.instCountableSLInt (F := F)
  liftQ_smul u γ P

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
-- module Solutions.Artin.KP.C5_Main
attribute [-instance] _root_.ArtinKP.B.instCountableSInt _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
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
-- module Solutions.Artin.KP.RF_Fourier
attribute [-instance] _root_.ArtinKP.B.instCountableSInt _root_.ArtinKP.B1.instDiscreteTopologySubtypeE₂MemSubmoduleIntPairLattice _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
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
attribute [-instance] _root_.ArtinKP.B.instCountableIdxI _root_.ArtinKP.B.instCountableSInt _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
attribute [-simp] _root_.ArtinKP.FB.v_gmap _root_.ArtinKP.FB.x_gmap
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

lemma continuous_htC (s : ℂ) : Continuous (htC s : X F → ℂ) := by
  unfold htC
  refine (Complex.continuous_ofReal.comp X.continuous_ht).cpow continuous_const fun P => ?_
  exact Or.inl (by simpa using X.ht_pos P)

lemma integrableOn_htC (s : ℂ) (n : ℕ) : IntegrableOn (htC s : X F → ℂ) (X.box n) (X.vol F) :=
  (continuous_htC s).continuousOn.integrableOn_compact (isCompact_box n)

end

end ArtinKP.N
end

section
-- module Solutions.Artin.KP.N_Cont
attribute [-instance] _root_.ArtinKP.B.instCountableSInt _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
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
attribute [-instance] _root_.ArtinKP.B.instCountableIdxI _root_.ArtinKP.B.instCountableSInt _root_.ArtinKP.B.instCountableSubtypeForallInfinitePlaceComplexMemAddSubgroupTransLat _root_.ArtinKP.F.instAddCommMonoidTSection _root_.ArtinKP.N2.levelGroup_finiteIndex _root_.ArtinKP.T.instCountableSubtypeForallInfinitePlaceComplexMemAddSubgroupMinLatN _root_.ArtinKP.T.instCountableSubtypeForallInfinitePlaceComplexMemAddSubgroupMinLatNTransLat _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
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
-- module Solutions.Artin.KP.T_Mean
attribute [-instance] _root_.ArtinKP.B.instCountableSInt _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-! # WP-T, file 1: strict cells of commensurable lattices (Mathlib only)

`PCell L D`: `D` is a measurable *strict* fundamental set of the subgroup `L` of `E` (every point
has exactly one translate in `D`) — the `hfund` form of WP-X2/WP-RF.

* `PCell.union`: if `L ≤ L₁` and `rep : κ → L₁` is a finite system of representatives of `L₁/L`,
  then `⋃_k (rep k + D)` is a strict cell of `L`.
* `exists_reps`: representatives from `L.relIndex L₁ ≠ 0`.
* **`mean_eq`**: let `D₁`, `D₂` be strict cells of `L₁`, `L₂`, `L ≤ L₁ ⊓ L₂` of finite index in
  both, `f` an `L₁`-periodic function, and suppose `∫_{t + D₂} f = I` for the representatives `t`
  of `L₂/L`.  Then `vol(D₂)·∫_{D₁} f = vol(D₁)·I`.
-/

open MeasureTheory Set

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace ArtinKP.T

noncomputable section

universe u

variable {E : Type u} [AddCommGroup E] [MeasurableSpace E] [MeasurableAdd₂ E] [MeasurableNeg E]

variable {L L₁ L₂ : AddSubgroup E} {D D₁ D₂ : Set E}

theorem PCell.isAddFundamentalDomain (h : PCell L D) (μ : Measure E) :
    IsAddFundamentalDomain L D μ :=
  IsAddFundamentalDomain.mk' h.meas.nullMeasurableSet fun x => h.fund x

end

end ArtinKP.T
end

section
-- module Solutions.Artin.KP.T_Lat
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-! # WP-T, file 3: the lattices `Λ_Γ` (translations of `Γ`) and `Λ_M` (`B.transLat 𝔪 M`)

Both sit in `latO F = emb(𝓞_F)` (for `M ≥ 0`) and contain the image of a nonzero ideal, hence are
commensurable: `relIndex_inf_left/right`.

* `pcell_of_hfund`: WP-X2/WP-RF's `hfund` is a strict cell `T.PCell (N.latN Γ) D`;
  `exists_pcell_latN`.
* `exists_pcell_transLat`: a bounded strict cell of `Λ_M` (`M ≥ 0`), as a union of translates of a
  cell of `emb(𝓞_F)`;  `cellM 𝔪 M` (a chosen one, bounded by `cellN 𝔪 M`).
* `kap 𝔪 M = (vol(cellM 𝔪 M) · vol(𝔩_M))⁻¹` — the constant of all coefficient formulas
  (`= covol(𝓞_F)⁻¹` by WP-B's stub B-2; independent of the chosen cell: `volume_eq_cellM`).
-/

open scoped MatrixGroups ComplexConjugate ENNReal Topology
open MeasureTheory Set NumberField Filter IsDedekindDomain ArtinPrimitiveRoots Metric

set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.T

open ArtinKP.A ArtinKP.S ArtinKP.X ArtinKP.B1 ArtinKP.B ArtinKP.C5 ArtinKP.K ArtinKP.RF ArtinKP.N

noncomputable section

variable {F : Type*} [Field F] [NumberField F] [IsTotallyComplex F] {𝔪 : Ideal (𝓞 F)}

/-! ### Ideal lattices -/

/-! ### The two families of lattices -/

/-! ### Cells -/


theorem pcell_cellM (h𝔪 : 𝔪 ≠ ⊥) {M : ℤ} (hM : 0 ≤ M) : PCell (transLat 𝔪 M) (cellM 𝔪 M) := by
  unfold cellM
  rw [dif_pos ⟨h𝔪, hM⟩]
  exact (exists_pcell_transLat h𝔪 hM).choose_spec.choose_spec.1

lemma vol_pos (𝔪 : Ideal (𝓞 F)) (M : ℤ) : 0 < vol 𝔪 M := by
  unfold vol
  refine Finset.prod_pos fun v _ => zpow_pos ?_ _
  have h : Ideal.absNorm v.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact v.ne_bot
  exact Nat.cast_pos.mpr (Nat.pos_of_ne_zero h)

end

end ArtinKP.T
end

section
-- module Solutions.Artin.KP.C9_Const
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
attribute [-simp] _root_.ArtinKP.FB.v_gmap _root_.ArtinKP.FB.x_gmap
/-!
# WP-C9, part 2: a `Γ`-invariant function with the constant-term shape is zero

Analytic core of (C10′) (MATH3 §5.1), independent of sections and of θ.

* `integral_conj_eChar_eq_zero`: orthogonality of a nonzero character of the dual lattice over a
  strict cell of `Λ_Γ`.
* **`ae_eq_htC_of_coeff`**: let `f` be measurable, `GammaN Γ`-invariant, `L²` on boxes.  If the
  frequency-`0` functionals of `f` are those of `z·ht^{s₁}` and all functionals at nonzero
  frequencies `ν ∈ Λ_Γ^⊥` vanish, then `f = z·ht^{s₁}` a.e.  (This contains WP-RF's optional
  lemma "nonzero frequencies vanish ⇒ independent of `x`", and its Fubini step, in one
  application of `RF.ae_eq_zero_of_strip` to `f − z·ht^{s₁}`.)
* `isOpenPosMeasure_vol`: `X.vol` is positive on nonempty open sets (chart + positive density).
* `lowInt`, `exists_lower_mem`: a finite-index `Γ` contains `[[1,0],[k,1]]`, `k ≠ 0`.
* `not_ae_ht_smul`: `ht(γP) = ht(P)` a.e. is impossible when the lower left entry of `γ` is
  nonzero (`X.pairHt_mul_pairHt_le`: then `ht² ≤ 1/|N(c)|²` everywhere).
* **`eq_zero_of_lift_ae_eq_htC`**: `u ∈ L²(Γ\X)` with `lift u = z·ht^{s₁}` a.e., `Re s₁ ≠ 0`, is `0`.
-/

open scoped MatrixGroups ComplexConjugate ENNReal Topology
open MeasureTheory Set NumberField Filter IsDedekindDomain ArtinPrimitiveRoots Metric

set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.C9

open ArtinKP.A ArtinKP.S ArtinKP.X ArtinKP.B1 ArtinKP.B ArtinKP.C5 ArtinKP.K ArtinKP.RF ArtinKP.N

noncomputable section

variable {F : Type*} [Field F] [NumberField F] [IsTotallyComplex F]
  {Γ : Subgroup (SL(2, 𝓞 F))}

/-! ### Characters -/

/-! ### Strip integrals as box integrals -/

/-! ### The constant-term shape forces the function -/

/-! ### `X.vol` is positive on open sets -/

theorem isOpenPosMeasure_vol : (X.vol F).IsOpenPosMeasure := by
  refine ⟨fun U hU hne h0 => ?_⟩
  have h1 : muE F (chart F ⁻¹' U) = 0 := by
    rw [(measurePreserving_chart F).measure_preimage hU.nullMeasurableSet]
    exact h0
  have hac : (volume : Measure (Coord F)) ≪ muE F := by
    unfold muE
    refine withDensity_absolutelyContinuous' ?_ ?_
    · exact (ENNReal.measurable_ofReal.comp continuous_rho.measurable).aemeasurable
    · exact Eventually.of_forall fun y => by
        simpa using rho_pos y
  have h2 : (volume : Measure (Coord F)) (chart F ⁻¹' U) = 0 := hac h1
  have hopen : IsOpen (chart F ⁻¹' U) := hU.preimage (chart F).continuous
  have hne' : (chart F ⁻¹' U).Nonempty := by
    obtain ⟨P, hP⟩ := hne
    exact ⟨(chart F).symm P, by simpa using hP⟩
  exact (hopen.measure_pos volume hne').ne' h2

/-! ### Lower unipotent elements -/

/-! ### Step (iii) -/

end

end ArtinKP.C9
end

section
-- module Solutions.Artin.KP.C9_Nonvanish
attribute [-instance] _root_.ArtinKP.T.instCountableSubtypeForallInfinitePlaceComplexMemAddSubgroupMinLatN _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-!
# WP-C9, part 1: `θ_{Φ^Σ} ≠ 0` (MATH2 §3)

`Φ^Σ = B.sumBig ι hG hN1 hN M T` (`T` a complete disjoint system of classes, `M ≥ 0`),
`Ψ^Σ = twist Φ^Σ`.

* `mD_eq_of_mean`: reconciliation of the two normalizations.  WP-N's coefficient `mD D Ψ s` is a
  mean over a cell `D` of `Λ_Γ = N.latN Γ`; WP-BZ computes means over cells of
  `Λ_M = B.transLat 𝔪 M`.  The two lattices are commensurable (`T.relIndex_inf_left/right`) and
  the means agree (`T.mean_eq`).
* `mD_sumBig`: `mD D Ψ^Σ s = C·(π/(s-1))^r·G(s)/(s-4/3)` for `Re s > 2`, `G` as in
  `BZ.exists_mean_const_term_pole`.
* **`zRes_sumBig`**: `zRes Γ Ψ^Σ D n = C·(3π)^r·G(4/3)`, and **`zRes_sumBig_ne_zero`**.
* **`theta_sumBig_ne_zero`**: `θ_{Ψ^Σ} ≠ 0`, for every finite-index `Γ` fixing `Ψ^Σ`.
* **`exists_theta_bigCell_ne_zero`**: some single big-cell section has `θ ≠ 0`.
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

/-- A bounded strict cell is a cell in WP-N's sense. -/
theorem cell_of_pcell {Γ : Subgroup (SL(2, 𝓞 F))} {D : Set (InfinitePlace F → ℂ)} {n : ℕ}
    (hD : T.PCell (latN Γ) D) (hb : ∀ x ∈ D, ∀ w, ‖x w‖ ≤ n) : Cell Γ D n :=
  ⟨hD.meas, hD.isAddFundamentalDomain volume, hb⟩

/-! ### The class-sum section -/

end

end ArtinKP.C9
end

section
-- module Solutions.Artin.KP.T_Coef
attribute [-instance] _root_.ArtinKP.N2.levelGroup_finiteIndex _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-! # WP-T, file 4: the `ν`-th coefficient of `E_Φ` over a cell, for `Re s > 2`

* `freq ν = (−2σ_w ν)_w`: `conj (RF.eChar (freq ν) x) = B.chiInf ν x`, so that
  `X.coeffFunctional Γ n (RF.stripFn D (freq ν) φ) …` is the `ν`-th coefficient against `conj φ`.
* `HasCoefT Ψ ν' a₀ D κ` (twisted section, any coefficient series `a₀`): for `Re s > 2` and all
  `v`, `∫_D E_Ψ(x, v) conj e_∞(ν'x) dx = vol(D)·κ·W_s(ν'; v)·a₀(s)`;
  `HasCoef hG hz6 Φ ν D κ` is the case `Ψ = Φ.twist`, `a₀ = 𝔞_Φ(ν, ·)`.
  - `hasCoef_transLat`: a strict cell of `Λ_M` (`M ≥ 0` valid) has it with `κ = kap 𝔪 M` (WP-B);
  - **`hasCoef_latN`**: so has every bounded strict cell of the translation lattice of any `Γ`
    fixing `Φ.twist`, provided `conj e_∞(ν·)` is `Λ_Γ`-periodic (`T.mean_eq`).
* `Afun Γ Ψ n ψ s = ∫_{box n} conj ψ · lift (resPart Γ Ψ s) + ∫_{box n} conj ψ · h_s`: holomorphic
  on `E.slit`, `= ∫_{box n} conj ψ · E_Ψ` for `Re s > 2`, ray limit `∫ conj ψ · θ`.
* `Wc D n φ ν s = N.cf D n φ (WX s ν)`: holomorphic on `Re s > 1`; `exists_Wc_ne_zero`.
* **`Afun_eq_of_hasCoefT`**: `Afun … (stripFn D (freq ν') φ) s = κ·a₀(s)·Wc D n φ ν' s`, `Re s > 2`.
-/

open scoped MatrixGroups ComplexConjugate ENNReal Topology
open MeasureTheory Set NumberField Filter IsDedekindDomain ArtinPrimitiveRoots Metric

set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.T

open ArtinKP.A ArtinKP.S ArtinKP.X ArtinKP.B1 ArtinKP.B ArtinKP.C5 ArtinKP.K ArtinKP.RF ArtinKP.N

noncomputable section

variable {F : Type*} [Field F] [NumberField F] [IsTotallyComplex F] {𝔪 : Ideal (𝓞 F)}
  {ι : F →+* ℂ} {P : CubicPkg F}

/-! ### The frequency of `ν` in WP-RF's parametrization -/

theorem conj_eChar_freq (ν : F) (x : InfinitePlace F → ℂ) :
    conj (eChar (freq ν) x) = chiInf ν x := by
  have h1 : chiInf ν x = Complex.exp (2 * Real.pi * Complex.I *
      ((∑ w : InfinitePlace F, 2 * (w.embedding ν * x w).re : ℝ) : ℂ)) := by
    rw [chiInf_eq_prod]
    simp only [archChar_eq_re, neg_neg]
    rw [← Complex.exp_sum]
    congr 1
    push_cast
    rw [Finset.mul_sum]
  have h2 : pair (freq ν) x = -∑ w : InfinitePlace F, 2 * (w.embedding ν * x w).re := by
    unfold pair freq
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun w _ => ?_
    have e : -2 * w.embedding ν * x w = ((-2 : ℝ) : ℂ) * (w.embedding ν * x w) := by
      push_cast; ring
    rw [e, Complex.re_ofReal_mul]
    ring
  rw [h1, eChar, h2, ← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat]
  push_cast
  ring

/-! ### Cells that compute the coefficient -/

variable (hG : Good 𝔪) {z6 : 𝓞 F} (hz6 : IsPrimitiveRoot z6 6) (Φ : GSection ι P 𝔪)
  (ν : SInt 𝔪)

theorem validDepth_mono {ν' : F} {M M' : ℤ} (h : ValidDepth hG Φ ν' M) (hMM : M ≤ M') :
    ValidDepth hG Φ ν' M' :=
  ⟨fun b hb => h.unip b (hb.mono hMM), fun x hx => h.char x (hx.mono hMM)⟩

theorem exists_validDepth_nonneg (ν' : F) : ∃ M : ℤ, 0 ≤ M ∧ ValidDepth hG Φ ν' M := by
  obtain ⟨M, hM⟩ := exists_validDepth hG Φ ν'
  exact ⟨max M 0, le_max_right _ _, validDepth_mono hG Φ hM (le_max_left _ _)⟩

/-! ### The coefficient function of the continuation -/

/-! ### The archimedean factor -/

/-! ### The coefficient of the series over an admissible cell -/

end

end ArtinKP.T
end

section
-- module Solutions.Artin.KP.T_Theta
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-! # WP-T, file 6: genuine sections — `aCont`, `tau`, the instance `E.Theta`, coefficients of `θ`

For `ν ∈ R ∖ 0` and a genuine section `Φ` (`Ψ = Φ.twist hG hz6`, `a₀ = (B.kubota hG hz6).aSer Φ ν`):

* `aCont hG hz6 Φ ν = contSlit a₀` — holomorphic on `E.slit` (`differentiableOn_aCont`), equal to
  the series on `Re s > 2` (`aCont_eq`), unique (`aCont_unique`);
* `tau hG hz6 Φ ν = resSlit a₀ = lim_{t↓0} (s_t − 4/3)·aCont(s_t)` (`tendsto_tau`);
* **`theta hG hz6 : E.Theta (B.kubota hG hz6) (4/3)`** with `toResFun = E.resFunSlit`;
* **`coeff_theta`** (item 3): the Fourier coefficients of `C5.theta Γ (Φ.twist)` for the cells of
  any `Γ`; `coeff_cont`: the same for the continuation on `E.slit`.
-/

open scoped MatrixGroups ComplexConjugate ENNReal Topology
open MeasureTheory Set NumberField Filter IsDedekindDomain ArtinPrimitiveRoots Metric

set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.T

open ArtinKP.A ArtinKP.S ArtinKP.X ArtinKP.B1 ArtinKP.B ArtinKP.C5 ArtinKP.K ArtinKP.RF ArtinKP.N

noncomputable section

variable {F : Type*} [Field F] [NumberField F] [IsTotallyComplex F] {𝔪 : Ideal (𝓞 F)}
  {ι : F →+* ℂ} {P : CubicPkg F}

variable (hG : Good 𝔪) {z6 : 𝓞 F} (hz6 : IsPrimitiveRoot z6 6) (Φ : GSection ι P 𝔪)
  (ν : SInt 𝔪)

variable {ν}

/-! ### The archimedean factor as an integral over `v` -/


/-! ### Fourier coefficients of `θ` for the cells of `Γ` -/

/-- `freq ν` in WP-RF's dual lattice gives the periodicity hypothesis. -/
lemma chiInf_of_mem_dualLat {Γ : Subgroup (SL(2, 𝓞 F))} {ν' : F} (h : freq ν' ∈ dualLat Γ)
    (β : 𝓞 F) (hβ : β ∈ lamN Γ) : chiInf ν' (emb (β : F)) = 1 := by
  obtain ⟨m, hm⟩ := h (ofLam ⟨β, hβ⟩)
  rw [shift_ofLam] at hm
  rw [← conj_eChar_freq, eChar]
  have e : (emb (β : F) : InfinitePlace F → ℂ) = embO β := rfl
  rw [e, hm]
  have : Complex.exp (2 * Real.pi * Complex.I * ((m : ℝ) : ℂ)) = 1 := by
    have := Complex.exp_int_mul_two_pi_mul_I m
    rw [← this]; congr 1; push_cast; ring
  rw [this, map_one]

end

end ArtinKP.T
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

lemma freq_zero : T.freq (0 : F) = 0 := by
  funext w
  simp [T.freq]

/-! ### (C10′) in WP-T's form -/

/-! ### The hypothesis of package G -/

end

end ArtinKP.C9
end

section
-- module Solutions.Artin.KP.RF_Parseval
attribute [-instance] _root_.ArtinKP.B.instCountableSInt _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
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
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
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

end

end ArtinKP.C9
end

section
-- module Solutions.Artin.KP.S2_Translate
attribute [-instance] _root_.ArtinKP.B.instCountableSInt _root_.ArtinKP.F.instAddCommMonoidTSection _root_.ArtinKP.N2.levelGroup_finiteIndex _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
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
-- module Solutions.Artin.KP.G2a_Per
/-! # WP-G2a, file 4: only frequencies of the dual lattice occur; periodicity of `thetaS`

* `eChar_freq`: `RF.eChar (T.freq ν) x = e_∞(νx)`.
* **`freq_mem_dualLat`**: if `τ_Φ(ν) ≠ 0` then `T.freq ν ∈ RF.dualLat Γ` for *every* finite-index
  `Γ` fixing `Φ.twist` (pass to `Γ ⊓ Γ(a)`, `aν ∈ 𝓞`, where `T.coeff_theta` applies, and use
  `T.coeff_theta_eq_zero`).
* `term_smul`, `thetaS_smul_GammaN`: invariance of every term, hence of `thetaS Φ`, under the
  translations of `Γ`.
-/

open scoped ComplexConjugate Topology MatrixGroups
open MeasureTheory Set NumberField Filter IsDedekindDomain ArtinPrimitiveRoots

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace ArtinKP.G2a

open ArtinKP.A ArtinKP.S ArtinKP.B ArtinKP.RF ArtinKP.X ArtinKP.B1 ArtinKP.C5 ArtinKP.N

noncomputable section

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}
variable {ι : F →+* ℂ} {P : CubicPkg F}
variable [IsTotallyComplex F]

lemma freq_injective : Function.Injective (T.freq : F → InfinitePlace F → ℂ) := by
  intro a b h
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace F))
  have := congrFun h w
  simp only [T.freq] at this
  exact w.embedding.injective (mul_left_cancel₀ (by norm_num) this)

end

end ArtinKP.G2a
end

section
-- module Solutions.Artin.KP.G2a_Coef
attribute [-simp] _root_.ArtinKP.FB.v_gmap _root_.ArtinKP.FB.x_gmap
/-! # WP-G2a, file 5: the Fourier coefficients of `thetaS` along a strip

For a finite-index `Γ` fixing `Φ.twist`, a bounded strict cell `D` of its translation lattice,
a box `n ⊇ D`, a frequency `ν' ∈ RF.dualLat Γ` and a test function `φ`:

* `integral_strip_term`: the strip integral of one term is `τ_Φ(ν)·Wc D n φ ν (4/3)` if
  `T.freq ν = ν'` and `0` otherwise (orthogonality of characters over the cell; a term with
  `τ_Φ(ν) ≠ 0` has `T.freq ν ∈ dualLat Γ` by `freq_mem_dualLat`);
* `integral_strip_thetaS`: termwise integration (dominated by the majorant on the box);
* `coeff_thetaS_freq`, `coeff_thetaS_of_ne`: the two cases.
-/

open scoped ComplexConjugate Topology MatrixGroups
open MeasureTheory Set NumberField Filter IsDedekindDomain ArtinPrimitiveRoots

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace ArtinKP.G2a

open ArtinKP.A ArtinKP.S ArtinKP.B ArtinKP.RF ArtinKP.X ArtinKP.B1 ArtinKP.C5 ArtinKP.N

noncomputable section

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}
variable {ι : F →+* ℂ} {P : CubicPkg F}

/-! ### Characters -/

variable [IsTotallyComplex F]

lemma isFiniteMeasure_box (n : ℕ) : IsFiniteMeasure ((X.vol F).restrict (X.box n)) := by
  have h := (integrableOn_htC (F := F) 0 n)
  have h1 : (htC (0 : ℂ) : X F → ℂ) = fun _ => 1 := by
    funext Q; simp [htC]
  rw [h1] at h
  exact ⟨by
    rw [Measure.restrict_apply_univ]
    have := (integrableOn_const_iff (C := (1 : ℂ)) (μ := X.vol F) (s := X.box n)).mp h
    simpa using this⟩

end

end ArtinKP.G2a
end

section
-- module Solutions.Artin.KP.T_Kap
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-! # WP-T, file 9: the constant `kap 𝔪 M` is `covol(𝓞_F)⁻¹`

By WP-BZ's `volume_cell'` (WP-B's stub B-2): `kap 𝔪 M = (volume (B1.fundD F)).toReal⁻¹` for every
`M ≥ 0`; in particular it does not depend on `M`.
-/

open scoped MatrixGroups ComplexConjugate ENNReal Topology
open MeasureTheory Set NumberField IsDedekindDomain ArtinPrimitiveRoots

set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.T

open ArtinKP.A ArtinKP.S ArtinKP.X ArtinKP.B1 ArtinKP.B

noncomputable section

variable {F : Type*} [Field F] [NumberField F] [IsTotallyComplex F] {𝔪 : Ideal (𝓞 F)}

theorem kap_eq (h𝔪 : 𝔪 ≠ ⊥) {M : ℤ} (hM : 0 ≤ M) :
    kap 𝔪 M = ((((volume (B1.fundD F)).toReal : ℝ)) : ℂ)⁻¹ := by
  have h := BZ.volume_cell' h𝔪 M ((pcell_cellM h𝔪 hM).isAddFundamentalDomain volume)
  have h' := congrArg ENNReal.toReal h
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (vol_pos 𝔪 M).le] at h'
  rw [kap, h']

end

end ArtinKP.T
end

section
-- module Solutions.Artin.KP.G2a_Exp
attribute [-instance] _root_.ArtinKP.F.instAddCommMonoidTSection _root_.ArtinKP.N2.levelGroup_finiteIndex
attribute [-simp] _root_.ArtinKP.FB.v_gmap _root_.ArtinKP.FB.x_gmap
/-! # WP-G2a, file 6: the pointwise theta function and **(Exp)**

* `kapC F = covol(𝓞_F)⁻¹` (`= T.kap 𝔪 M` for every `M ≥ 0`).
* `IsExp Φ z`: for every finite-index `Γ` fixing `Φ.twist`,
  `X.lift Γ (C5.theta Γ Φ.twist) = z·ht^{2/3} + kapC·thetaS Φ` almost everywhere.
* **`exists_isExp`** (Theorem E + `hdiff`): such a `z` exists.  (Fourier uniqueness on the full
  stabilizer, `C9.ae_eq_htC_of_coeff`; other groups by `N.lift_theta_congr`.)
* `zc Φ` := that `z` (unique: `isExp_unique`); **`thetaT Φ Q := zc Φ·ht(Q)^{2/3} + kapC·thetaS Φ Q`**,
  continuous, and `thetaT_ae`: it represents `θ_{Φ.twist}` for every admissible `Γ`.
-/

open scoped MatrixGroups ComplexConjugate ENNReal Topology
open MeasureTheory Set NumberField Filter IsDedekindDomain ArtinPrimitiveRoots Metric

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace ArtinKP.G2a

open ArtinKP.A ArtinKP.S ArtinKP.B ArtinKP.RF ArtinKP.X ArtinKP.B1 ArtinKP.C5 ArtinKP.N

noncomputable section

variable {F : Type*} [Field F] [NumberField F] [IsTotallyComplex F] {𝔪 : Ideal (𝓞 F)}
variable {ι : F →+* ℂ} {P : CubicPkg F}

lemma kap_eq_kapC (h𝔪 : 𝔪 ≠ ⊥) {M : ℤ} (hM : 0 ≤ M) : T.kap 𝔪 M = kapC F := T.kap_eq h𝔪 hM

/-- Linearity of the strip integral. -/
lemma integral_strip_sub {D : Set (InfinitePlace F → ℂ)} (hD : MeasurableSet D) (n : ℕ)
    (ν' : InfinitePlace F → ℂ) {φ : (InfinitePlace F → ℝ) → ℂ} (hφ : Measurable φ)
    (hφ1 : ∀ v, ‖φ v‖ ≤ 1) {a b : X F → ℂ} (ha : IntegrableOn a (X.box n) (X.vol F))
    (hb : IntegrableOn b (X.box n) (X.vol F)) (k : ℂ) :
    ∫ Q in X.box n, conj (stripFn D ν' φ Q) * (a Q - k * b Q) ∂X.vol F =
      (∫ Q in X.box n, conj (stripFn D ν' φ Q) * a Q ∂X.vol F) -
        k * ∫ Q in X.box n, conj (stripFn D ν' φ Q) * b Q ∂X.vol F := by
  have hsm : Measurable fun Q : X F => conj (stripFn D ν' φ Q) :=
    Complex.continuous_conj.measurable.comp (measurable_stripFn hD ν' hφ)
  have hs1 : ∀ Q : X F, ‖conj (stripFn D ν' φ Q)‖ ≤ 1 := fun Q => by
    rw [RCLike.norm_conj]; exact norm_stripFn_le D ν' hφ1 Q
  have ia := Integrable.bdd_mul (c := 1) ha hsm.aestronglyMeasurable (Eventually.of_forall hs1)
  have ib := Integrable.bdd_mul (c := 1) hb hsm.aestronglyMeasurable (Eventually.of_forall hs1)
  rw [← integral_const_mul, ← integral_sub ia (ib.const_mul k)]
  refine integral_congr_ae (Eventually.of_forall fun Q => ?_)
  simp only
  ring

variable (hG : Good 𝔪) {z6 : 𝓞 F} (hz6 : IsPrimitiveRoot z6 6)

variable {hG hz6} {g : AllowedGen ι 𝔪}

/-- **(Exp), existence of the constant term.** -/
theorem exists_isExp (hE : ThmE hG hz6 g P)
    (hdiff : ∀ v : HeightOneSpectrum (𝓞 F), v ∉ placesOf 𝔪 →
      ¬ differentIdeal ℤ (𝓞 F) ≤ v.asIdeal)
    (Φ : GSection ι P 𝔪) : ∃ z : ℂ, IsExp hG hz6 Φ z := by
  haveI _iCSL := ArtinKP.X.instCountableSLInt (F := F)
  have h𝔪 := hG.ne_bot
  set Ψ := Φ.twist hG hz6 with hΨ
  have hEis : ∀ s : ℂ, 2 < s.re → EisEigen Ψ s := fun s hs => GL.eisEigen_of_two_lt_re h𝔪 Ψ hs
  set Γ₀ := C9.stabGroup Ψ with hΓ₀def
  have hfi : Γ₀.FiniteIndex := C9.stabGroup_finiteIndex P hG hz6 Ψ
  have hΓ₀ : Inv Γ₀ Ψ := C9.inv_stabGroup Ψ
  have hdual : C9.DualCover 𝔪 Γ₀ :=
    C9.dualCover_of_transLevel h𝔪 hdiff Γ₀ (C9.transLevel_stabGroup hG hz6 Φ)
  obtain ⟨D, hD, hbdd, hfund⟩ :=
    exists_fundamental_translations Γ₀ (exists_ideal_translations Γ₀)
  obtain ⟨R, hR⟩ := hbdd.exists_norm_le
  obtain ⟨n₁, hn₁⟩ := exists_nat_ge (max R 1)
  have hn1 : 1 ≤ n₁ := by exact_mod_cast (le_max_right R 1).trans hn₁
  have hb : ∀ x ∈ D, ∀ w, ‖x w‖ ≤ (n₁ : ℝ) := fun x hx w =>
    (norm_le_pi_norm x w).trans ((hR x hx).trans ((le_max_left R 1).trans hn₁))
  have hbn : ∀ n : ℕ, n₁ ≤ n → ∀ x ∈ D, ∀ w, ‖x w‖ ≤ (n : ℝ) := fun n hn x hx w =>
    (hb x hx w).trans (by exact_mod_cast hn)
  have hpc := T.pcell_of_hfund hD hfund
  set z : ℂ := zRes Γ₀ Ψ D n₁ with hz
  have hSc := continuous_thetaS hE Φ
  have hSint : ∀ n : ℕ, IntegrableOn (thetaS hG hz6 Φ) (X.box n) (X.vol F) := fun n =>
    hSc.continuousOn.integrableOn_compact (isCompact_box n)
  have hLint : ∀ n : ℕ, IntegrableOn (X.lift Γ₀ (C5.theta Γ₀ Ψ)) (X.box n) (X.vol F) := fun n =>
    integrableOn_lift Γ₀ n _
  set f : X F → ℂ := fun Q => X.lift Γ₀ (C5.theta Γ₀ Ψ) Q - kapC F * thetaS hG hz6 Φ Q with hf
  have key : f =ᵐ[X.vol F] fun Q => z * htC (2 / 3) Q := by
    refine C9.ae_eq_htC_of_coeff Γ₀ (exists_ideal_translations Γ₀) hD hfund n₁ hb f
      ((X.stronglyMeasurable_lift Γ₀ _).measurable.sub (measurable_const.mul hSc.measurable))
      (fun γ Q => ?_) (fun n => ?_) (fun n => (hLint n).sub ((hSint n).const_mul _)) z (2 / 3)
      (fun n hn φ hφ hφ1 => ?_) (fun ν' hν' hν'0 n hn φ hφ hφ1 => ?_)
    · simp only [hf]
      have h1 : X.lift Γ₀ (C5.theta Γ₀ Ψ) (γ • Q) = X.lift Γ₀ (C5.theta Γ₀ Ψ) Q :=
        X.lift_smul Γ₀ _ (γ : Γ₀) Q
      rw [h1, thetaS_smul_gammaN hG hz6 Φ Γ₀ hΓ₀ γ Q]
    · have hfin := isFiniteMeasure_box (F := F) n
      refine (memLp_liftQ_restrict (X.isPOU_pou Γ₀) (X.measurableSet_box n)
        (ENNReal.natCast_ne_top _) (X.tsum_indicator_box_le_boxMult Γ₀ n) _).sub ?_
      obtain ⟨C, hC⟩ := (isCompact_box (F := F) n).exists_bound_of_continuousOn
        (continuous_const.mul hSc : Continuous fun Q => kapC F * thetaS hG hz6 Φ Q).continuousOn
      exact MemLp.of_bound (measurable_const.mul hSc.measurable).aestronglyMeasurable C
        (ae_restrict_of_forall_mem (X.measurableSet_box n) hC)
    · -- frequency 0
      have h1 := cf_theta hG hΓ₀ hEis (C9.cell_of_pcell hpc hb) hn1
        (C9.cell_of_pcell hpc (hbn n hn)) hφ hφ1
      have h2 := coeff_thetaS_of_ne Φ Γ₀ hΓ₀ hD hfund (hbn n hn) (ν' := 0)
        (fun γ => ⟨0, by simp [pair]⟩) hφ hφ1 hE (fun ν h0 => ν.2 (by
          have := freq_injective (h0.trans C9.freq_zero.symm)
          exact Subtype.ext this))
      unfold cf at h1 ⊢
      rw [integral_strip_sub hD n 0 hφ hφ1 (hLint n) (hSint n), h1, h2, mul_zero, sub_zero]
    · -- nonzero frequencies
      obtain ⟨ν, rfl⟩ := hdual ν' hν' hν'0
      have hν : ν ≠ 0 := by
        rintro rfl
        exact hν'0 C9.freq_zero
      obtain ⟨M, hM, hV⟩ := T.exists_validDepth_nonneg hG Φ ((ν : SInt 𝔪) : F)
      have h1 := T.coeffFunctional_theta_twist_eq hG hz6 Φ hν hM hV Γ₀ hΓ₀ hD hfund (hbn n hn)
        (T.chiInf_of_mem_dualLat hν') hφ hφ1
      rw [X.coeffFunctional_apply, kap_eq_kapC h𝔪 hM] at h1
      have h2 := coeff_thetaS_freq Φ Γ₀ hΓ₀ hD hfund (hbn n hn) hφ hφ1 hE ⟨ν, hν⟩ hν'
      rw [integral_strip_sub hD n _ hφ hφ1 (hLint n) (hSint n), h1, h2]
      ring
  refine ⟨z, fun Γ _ hΓ => ?_⟩
  have hcong := lift_theta_congr hG hΓ₀ hΓ hEis
  filter_upwards [hcong, key] with Q h1 h2
  rw [h1]
  simp only [hf] at h2
  linear_combination h2

variable (hG hz6)

variable {hG hz6}

theorem isExp_zc (hE : ThmE hG hz6 g P)
    (hdiff : ∀ v : HeightOneSpectrum (𝓞 F), v ∉ placesOf 𝔪 →
      ¬ differentIdeal ℤ (𝓞 F) ≤ v.asIdeal)
    (Φ : GSection ι P 𝔪) : IsExp hG hz6 Φ (zc hG hz6 Φ) := by
  have h := exists_isExp hE hdiff Φ
  rw [zc, dif_pos h]
  exact h.choose_spec

/-- **(Exp)**: `thetaT Φ` represents `θ_{Φ.twist}` for every admissible `Γ`. -/
theorem thetaT_ae (hE : ThmE hG hz6 g P)
    (hdiff : ∀ v : HeightOneSpectrum (𝓞 F), v ∉ placesOf 𝔪 →
      ¬ differentIdeal ℤ (𝓞 F) ≤ v.asIdeal)
    (Φ : GSection ι P 𝔪) (Γ : Subgroup (SL(2, 𝓞 F))) [Γ.FiniteIndex]
    (hΓ : Inv Γ (Φ.twist hG hz6)) :
    X.lift Γ (C5.theta Γ (Φ.twist hG hz6)) =ᵐ[X.vol F] thetaT hG hz6 Φ :=
  isExp_zc hE hdiff Φ Γ hΓ

/-- `thetaT Φ` is continuous. -/
theorem continuous_thetaT (hE : ThmE hG hz6 g P) (Φ : GSection ι P 𝔪) :
    Continuous (thetaT hG hz6 Φ) :=
  (continuous_const.mul (continuous_htC _)).add (continuous_const.mul (continuous_thetaS hE Φ))

end

end ArtinKP.G2a
end

section
-- module Solutions.Artin.KP.G2a_Aut
attribute [-instance] _root_.ArtinKP.F.instAddCommMonoidTSection _root_.ArtinKP.N2.levelGroup_finiteIndex
/-! # WP-G2a, file 7: **(Aut)**, linearity, (C10′) pointwise

All identities are *pointwise* on `X F`: an a.e. identity between continuous functions holds
everywhere (`X.vol` is positive on open sets, `C9.isOpenPosMeasure_vol`).

* `thetaT_add`, `thetaT_smul`, `thetaT_smulFun`: linearity in the section; `zc_add`, `zc_smulFun`.
* `thetaT_eq_zero_of_tau`: **(C10′)** for the pointwise function (and `zc_eq_zero_of_tau`).
* **`thetaT_translate`**: `θ̃_{translate σ Φ}(Q) = θ̃_Φ(σ⁻¹Q)` for `σ ∈ SL₂(R)` and all `Q`.
* `thetaT_congr_twist`: `θ̃_Φ` depends on the twist only.
-/

open scoped MatrixGroups ComplexConjugate ENNReal Topology
open MeasureTheory Set NumberField Filter IsDedekindDomain ArtinPrimitiveRoots Metric

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace ArtinKP.G2a

open ArtinKP.A ArtinKP.S ArtinKP.B ArtinKP.RF ArtinKP.X ArtinKP.B1 ArtinKP.C5 ArtinKP.N

noncomputable section

variable {F : Type*} [Field F] [NumberField F] [IsTotallyComplex F] {𝔪 : Ideal (𝓞 F)}
variable {ι : F →+* ℂ} {P : CubicPkg F}
variable {hG : Good 𝔪} {z6 : 𝓞 F} {hz6 : IsPrimitiveRoot z6 6} {g : AllowedGen ι 𝔪}

/-- An a.e. identity with a continuous function is an identity. -/
theorem thetaT_eq_of_ae (hE : ThmE hG hz6 g P) {Φ : GSection ι P 𝔪} {f : X F → ℂ}
    (hf : Continuous f) (h : thetaT hG hz6 Φ =ᵐ[X.vol F] f) : thetaT hG hz6 Φ = f := by
  have := C9.isOpenPosMeasure_vol (F := F)
  exact ((continuous_thetaT hE Φ).ae_eq_iff_eq (X.vol F) hf).mp h

section

variable (hE : ThmE hG hz6 g P)
  (hdiff : ∀ v : HeightOneSpectrum (𝓞 F), v ∉ placesOf 𝔪 →
    ¬ differentIdeal ℤ (𝓞 F) ≤ v.asIdeal)

include hE hdiff

/-- **(Aut)**: `θ̃_{translate σ Φ}(Q) = θ̃_Φ(σ⁻¹ Q)` for every `σ ∈ SL₂(R)` and every `Q`. -/
theorem thetaT_translate_oai (σ : SL(2, SInt 𝔪)) (Φ : GSection ι P 𝔪) (Q : X F) :
    thetaT hG hz6 (S2.GSection.translate hG σ Φ) Q = thetaT hG hz6 Φ (toF 𝔪 σ⁻¹ • Q) := by
  have h𝔪 := hG.ne_bot
  set Ψ := Φ.twist hG hz6 with hΨ
  have hfi := C9.stabGroup_finiteIndex P hG hz6 Ψ
  have hfi' := C9.stabGroup_finiteIndex P hG hz6 (TSection.translate P hG hz6 σ Ψ)
  set Γ := C9.stabGroup Ψ with hΓdef
  set Γ' := C9.stabGroup (TSection.translate P hG hz6 σ Ψ) with hΓ'def
  have hΓ : Inv Γ Ψ := C9.inv_stabGroup _
  have hΓ' : Inv Γ' (TSection.translate P hG hz6 σ Ψ) := C9.inv_stabGroup _
  have h1 := thetaT_ae hE hdiff (S2.GSection.translate hG σ Φ) Γ'
    (by rw [S2.GSection.twist_translate]; exact hΓ')
  rw [S2.GSection.twist_translate] at h1
  have h2 := lift_theta_translate P hG hz6 σ hΓ hΓ' (fun s hs => GL.eisEigen_of_two_lt_re h𝔪 Ψ hs)
    (fun s hs => GL.eisEigen_of_two_lt_re h𝔪 _ hs)
  have h3 := thetaT_ae hE hdiff Φ Γ hΓ
  have h4 : (fun Q => X.lift Γ (theta Γ Ψ) (toF 𝔪 σ⁻¹ • Q)) =ᵐ[X.vol F]
      fun Q => thetaT hG hz6 Φ (toF 𝔪 σ⁻¹ • Q) :=
    (X.measurePreserving_smul (toF 𝔪 σ⁻¹)).quasiMeasurePreserving.ae_eq_comp h3
  have key : thetaT hG hz6 (S2.GSection.translate hG σ Φ) =ᵐ[X.vol F]
      fun Q => thetaT hG hz6 Φ (toF 𝔪 σ⁻¹ • Q) := h1.symm.trans (h2.trans h4)
  exact congrFun (thetaT_eq_of_ae hE
    ((continuous_thetaT hE Φ).comp (continuous_const_smul (toF 𝔪 σ⁻¹))) key) Q

end

end

end ArtinKP.G2a
end

theorem solution.{u_1} : type_of% @ArtinKP.G2a.thetaT_translate_oai.{u_1} := @ArtinKP.G2a.thetaT_translate_oai.{u_1}
