-- Prove2me | Definitions.Def_ArtinKPB010
-- name    : ArtinKPB010
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-17T09:27:54.681816+00:00
-- url     : https://prove2.me/theorems/61db2081-8ec4-4314-95fc-e8b985da9426
-- title:
--   Definitions bundle ArtinKPB010 of the split of the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function)
-- statement:
--   A definitions bundle of the split of the formal proof of `ArtinPrimitiveRoots.exists_cutoff_exists_tsum_thetaWhittaker_sub_tsum_weylWhittaker_rotInvariant`, carved for this platform from the Lean development *the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function)* by the submitter, written with Claude. The declarations and their proofs are that development's. It formalizes part of the proof of Theorem 1.2 of OpenAI's paper *Primitive roots for every admissible integer base* (2026; github.com/openai/math, family 029), the step that rests on the cubic theta function of D. A. Kazhdan and S. J. Patterson, *Metaplectic forms*, Publ. Math. IHÉS 59 (1984), 35–142. It compiles with Lean 4.33.1 and Mathlib 0df444a.
--
--   **Contents.** It holds 28 declarations of that development: 4 definitions, 1 inductive type or structure, 2 instances and 21 theorems. The definitions and types are `ArtinKP.X.X.IsInv`, `ArtinKP.X.X.L2Rep`, `ArtinKP.X.X.desc`, `ArtinKP.X.X.quotVol`, `ArtinKP.X.quotMeasure`.
--
--   **Sources.** They come from these modules of the development, in whole or in part: `KP.X2_Core`, `KP.X2_H1`, `KP.X2_Isom`, `KP.X_Discrete`, `KP.X_Fourier`, `KP.X_Quot`, `KP.X_Space`.
--
--   **Imports.** It imports the bundles `ArtinKPB007` and `ArtinKPB009` of this split; the published statement `ArtinKP.X.X.isPOU_pou`.
--
--   **Imported by** (directly, in this split): the bundle `ArtinKPB011`; the statements `ArtinKP.C5.quotVol_lt_top`, `ArtinKP.X.X.IsInv.lap`, `ArtinKP.X.X.ims`, `ArtinKP.X.X.integrable_pou_mul`, `ArtinKP.X.X.l2Rep_of_mem_core`, `ArtinKP.X.X.mem_core_of_support` and `ArtinKP.X.X.qgreen`; the proofs of `ArtinKP.X.X.IsInv.lap`, `ArtinKP.X.X.l2Rep_of_mem_core` and `ArtinKP.X.X.qgreen`.
-- source:
--   the submitter, written with Claude, the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function); after part of the proof of Theorem 1.2 of OpenAI's paper *Primitive roots for every admissible integer base* (2026; github.com/openai/math, family 029), the step that rests on the cubic theta function of D. A. Kazhdan and S. J. Patterson, *Metaplectic forms*, Publ. Math. IHÉS 59 (1984), 35–142; definitions carved from that development

import Mathlib
import Definitions.Def_ArtinKPB007
import Definitions.Def_ArtinKPB009
import Theorems.Thm_ArtinKP_X_X_isPOU_pou

section
-- module Solutions.Artin.KP.X_Space
attribute [-instance] _root_.ArtinKP.X.instMeasurableConstSMulSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instMulActionSpecialLinearGroupFinOfNatNatRingOfIntegersX
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

/-! ### Topology and measure -/

/-- `SL(2,F)` preserves the measure. -/
theorem measurePreserving_smul (γ : SL(2, F)) :
    MeasurePreserving (fun P : X F => γ • P) (X.vol F) (X.vol F) :=
  measurePreserving_Ginf_smul (sigma F γ)

/-! ### Upper triangular elements, translations and the torus -/

end

end ArtinKP.X
end

section
-- module Solutions.Artin.KP.X2_Isom
attribute [-instance] _root_.ArtinKP.X.instMeasurableConstSMulSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instMulActionSpecialLinearGroupFinOfNatNatRingOfIntegersX
/-! # WP-X2, file 3: the group acts by isometries; the Laplacian commutes with it

* `Iso1 φ`: a smooth self-map of one factor (in the chart) whose derivative is conformal for the
  hyperbolic metric; translations and the inversion `Jmap` (the chart form of the Weyl element)
  are such, hence every element of `SL(2,ℂ)` acts by one (`mem_iso1`).
* `IsoHalf Φ`: a smooth self-map of `Coord F` preserving the carré du champ.
* `lapE_comp_of_iso`: a measure-preserving `IsoHalf` bijection with `IsoHalf` inverse commutes
  with the Laplacian.  The proof is weak: test against `C_c^∞`, use Green twice — no second
  derivative of the Möbius action is ever computed.
* On `X`: `X.Smooth`, `X.lap`, `X.gam`, and their invariance under `G∞ = SL(2,ℂ)^r`.
-/

open scoped MatrixGroups ComplexConjugate ENNReal
open MeasureTheory Set NumberField

set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.X

noncomputable section

open Classical

/-! ### One factor -/

/-! ### Every element of `SL(2,ℂ)` acts by an `Iso1` -/

/-! ### Isometries of the chart -/

variable {F : Type*} [Field F] [NumberField F]

/-! ### The action of `G∞` in the chart -/

/-! ### Calculus on `X` -/

lemma X.Smooth.continuous {u : X F → ℂ} (hu : X.Smooth u) : Continuous u := by
  have h : u = (fun y => u (chart F y)) ∘ (chart F).symm := by
    funext P; simp
  rw [h]
  have hu' : ContDiff ℝ (⊤ : ℕ∞) fun y => u (chart F y) := hu
  exact hu'.continuous.comp (chart F).symm.continuous

end

end ArtinKP.X
end

section
-- module Solutions.Artin.KP.X_Quot
/-! # WP-X, file 5: quotient measures and unfolding without fundamental domains

Abstract setting: a countable group `G` acting measurably on `(α, μ)` and preserving `μ`.
A *partition of unity* for the action is a measurable `η : α → ℝ≥0∞` with
`∑_g η (g • a) = 1` for all `a` (the indicator of a strict fundamental domain is one; in a
properly discontinuous situation an everywhere positive one always exists, `exists_isPOU`).
The quotient measure on `G \ α` is the push-forward of `η μ`; it does not depend on `η`
(`quotMeasure_eq`).  Everything is Tonelli:

* `lintegral_tsum_swap` : `∫ φ · Σ_g ψ∘g = ∫ ψ · Σ_g φ∘g`;
* `lintegral_mul_pou_eq` : independence of `η`;
* `lintegral_autom_mul_eq` : unfolding `∫_{G\α} (Σ_{H\G} f∘γ) u = ∫_{H\α} f u`;
* `setLIntegral_le_mul_lintegral_pou` : a set meeting each orbit at most `m` times has
  `∫_B f ≤ m ∫_{G\α} f`.
-/

open scoped ENNReal
open MeasureTheory Set

set_option linter.unusedSectionVars false

namespace ArtinKP.X

noncomputable section

variable {G α : Type*} [Group G] [Countable G] [MeasurableSpace α] [MulAction G α]
  [MeasurableConstSMul G α] {μ : Measure α} [SMulInvariantMeasure G α μ]

lemma lintegral_comp_smul (g : G) {f : α → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ a, f (g • a) ∂μ = ∫⁻ a, f a ∂μ :=
  (_root_.MeasureTheory.measurePreserving_smul g μ).lintegral_comp hf

/-- **The basic Tonelli swap**: `∫ φ · Σ_g ψ(g a) = ∫ ψ · Σ_g φ(g a)`. -/
theorem lintegral_tsum_swap {φ ψ : α → ℝ≥0∞} (hφ : Measurable φ) (hψ : Measurable ψ) :
    ∫⁻ a, φ a * ∑' g : G, ψ (g • a) ∂μ = ∫⁻ a, ψ a * ∑' g : G, φ (g • a) ∂μ := by
  have hm : ∀ g : G, Measurable fun a : α => g • a := fun g => measurable_const_smul g
  calc ∫⁻ a, φ a * ∑' g : G, ψ (g • a) ∂μ
      = ∑' g : G, ∫⁻ a, φ a * ψ (g • a) ∂μ := by
        simp_rw [← ENNReal.tsum_mul_left]
        exact lintegral_tsum fun g => (hφ.mul (hψ.comp (hm g))).aemeasurable
    _ = ∑' g : G, ∫⁻ a, ψ a * φ (g⁻¹ • a) ∂μ := by
        refine tsum_congr fun g => ?_
        have hF : Measurable fun a => ψ a * φ (g⁻¹ • a) := hψ.mul (hφ.comp (hm g⁻¹))
        rw [← lintegral_comp_smul (μ := μ) g hF]
        refine lintegral_congr fun a => ?_
        simp [mul_comm]
    _ = ∫⁻ a, ψ a * ∑' g : G, φ (g⁻¹ • a) ∂μ := by
        simp_rw [← ENNReal.tsum_mul_left]
        exact (lintegral_tsum fun g => (hψ.mul (hφ.comp (hm g⁻¹))).aemeasurable).symm
    _ = ∫⁻ a, ψ a * ∑' g : G, φ (g • a) ∂μ := by
        refine lintegral_congr fun a => ?_
        congr 1
        exact (Equiv.inv G).tsum_eq (fun g : G => φ (g • a))

/-- **Independence of the partition of unity.** -/
theorem lintegral_mul_pou_eq {η η' : α → ℝ≥0∞} (hη : IsPOU G η) (hη' : IsPOU G η')
    {f : α → ℝ≥0∞} (hf : Measurable f) (hinv : ∀ (g : G) (a : α), f (g • a) = f a) :
    ∫⁻ a, f a * η a ∂μ = ∫⁻ a, f a * η' a ∂μ := by
  have hfη : Measurable fun a => f a * η a := hf.mul hη.measurable
  have h := lintegral_tsum_swap (G := G) (μ := μ) hfη hη'.measurable
  simp only [hη'.tsum_eq, mul_one, hinv, ENNReal.tsum_mul_left, hη.tsum_eq] at h
  rw [h]
  exact lintegral_congr fun a => mul_comm _ _

/-! ### The quotient measure -/

variable (G) in
/-- The quotient measure on `G \ α` attached to a partition of unity. -/
def quotMeasure (η : α → ℝ≥0∞) (μ : Measure α) : Measure (Quotient (MulAction.orbitRel G α)) :=
  Measure.map (Quotient.mk (MulAction.orbitRel G α)) (μ.withDensity η)

lemma measurable_mk : Measurable (Quotient.mk (MulAction.orbitRel G α)) :=
  measurable_quotient_mk''

lemma mk_smul (g : G) (a : α) :
    Quotient.mk (MulAction.orbitRel G α) (g • a) = Quotient.mk (MulAction.orbitRel G α) a :=
  Quotient.sound (MulAction.mem_orbit a g)

/-- Integrals over the quotient are integrals against `η` upstairs. -/
theorem lintegral_quotMeasure {η : α → ℝ≥0∞} (hη : Measurable η)
    {f : Quotient (MulAction.orbitRel G α) → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ q, f q ∂quotMeasure G η μ =
      ∫⁻ a, f (Quotient.mk (MulAction.orbitRel G α) a) * η a ∂μ := by
  unfold quotMeasure
  rw [lintegral_map hf measurable_mk]
  exact (lintegral_withDensity_eq_lintegral_mul μ hη (hf.comp measurable_mk)).trans
    (lintegral_congr fun a => mul_comm _ _)

/-- **The quotient measure does not depend on the partition of unity.** -/
theorem quotMeasure_eq {η η' : α → ℝ≥0∞} (hη : IsPOU G η) (hη' : IsPOU G η') :
    quotMeasure G η μ = quotMeasure G η' μ := by
  ext A hA
  have h1 := lintegral_quotMeasure (G := G) (μ := μ) hη.measurable
    (measurable_const.indicator hA : Measurable (A.indicator fun _ => (1 : ℝ≥0∞)))
  have h2 := lintegral_quotMeasure (G := G) (μ := μ) hη'.measurable
    (measurable_const.indicator hA : Measurable (A.indicator fun _ => (1 : ℝ≥0∞)))
  rw [lintegral_indicator hA, setLIntegral_const, one_mul] at h1 h2
  rw [h1, h2]
  refine lintegral_mul_pou_eq hη hη' ((measurable_const.indicator hA).comp measurable_mk) ?_
  intro g a
  rw [mk_smul]

/-! ### Unfolding -/

/-! ### Multiplicity and existence of partitions of unity -/

end

end ArtinKP.X
end

section
-- module Solutions.Artin.KP.X_Discrete
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

instance instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatRingOfIntegersXVol : SMulInvariantMeasure (SL(2, 𝓞 F)) (X F) (X.vol F) :=
  ⟨fun γ s hs => (measurePreserving_smul (intSL F γ)).measure_preimage hs.nullMeasurableSet⟩

/-! ### Partition of unity, quotient measure, `L²(Γ\X)` -/

/-- The measure on `Γ \ X` induced by `X.vol`. -/
def X.quotVol (Γ : Subgroup (SL(2, 𝓞 F))) : Measure (Quotient (MulAction.orbitRel Γ (X F))) :=
  quotMeasure Γ (X.pou Γ) (X.vol F)

/-- The quotient measure can be computed with any partition of unity. -/
theorem X.quotVol_eq (Γ : Subgroup (SL(2, 𝓞 F))) {η : X F → ℝ≥0∞} (hη : IsPOU Γ η) :
    X.quotVol Γ = quotMeasure Γ η (X.vol F) :=
  haveI _iCSL := ArtinKP.X.instCountableSLInt (F := F)
  quotMeasure_eq (X.isPOU_pou Γ) hη

/-- Integration over `Γ \ X`. -/
theorem X.lintegral_quotVol (Γ : Subgroup (SL(2, 𝓞 F))) {η : X F → ℝ≥0∞} (hη : IsPOU Γ η)
    {f : Quotient (MulAction.orbitRel Γ (X F)) → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ q, f q ∂X.quotVol Γ =
      ∫⁻ P, f (Quotient.mk (MulAction.orbitRel Γ (X F)) P) * η P ∂X.vol F := by
  haveI _iCSL := ArtinKP.X.instCountableSLInt (F := F)
  rw [X.quotVol_eq Γ hη]
  exact lintegral_quotMeasure hη.measurable hf

/-! ### The cusp stabilizer -/

end

end ArtinKP.X
end

section
-- module Solutions.Artin.KP.X_Fourier
attribute [-simp] _root_.ArtinKP.X.chart1_symm_fst _root_.ArtinKP.X.chart1_symm_snd _root_.ArtinKP.X.chart1_v _root_.ArtinKP.X.chart1_x _root_.ArtinKP.X.chart_apply _root_.ArtinKP.X.chart_symm_apply
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

lemma H3.vol_box_lt_top (m M B : ℝ) (hm : 0 < m) : H3.vol (H3.box m M B) < ⊤ := by
  unfold H3.vol
  rw [H3.measurableEmbedding_coe.comap_apply]
  set T : Set (ℂ × ℝ) := Metric.closedBall (0 : ℂ) B ×ˢ Icc m M with hT
  have hTm : MeasurableSet T := Metric.isClosed_closedBall.measurableSet.prod measurableSet_Icc
  have hsub : H3.coe '' H3.box m M B ⊆ T := by
    rintro _ ⟨Q, ⟨hx, hv1, hv2⟩, rfl⟩
    exact ⟨mem_closedBall_zero_iff.mpr hx, hv1, hv2⟩
  refine (measure_mono hsub).trans_lt ?_
  rw [amb_apply hTm]
  calc ∫⁻ p in upper, T.indicator dens p
      ≤ ∫⁻ p, T.indicator (fun _ => ENNReal.ofReal ((m ^ 3)⁻¹)) p := by
        refine (setLIntegral_le_lintegral _ _).trans (lintegral_mono fun p => ?_)
        by_cases hp : p ∈ T
        · rw [indicator_of_mem hp, indicator_of_mem hp]
          refine ENNReal.ofReal_le_ofReal ?_
          have h1 : m ≤ p.2 := hp.2.1
          have h2 : m ^ 3 ≤ p.2 ^ 3 := pow_le_pow_left₀ hm.le h1 3
          exact inv_anti₀ (by positivity) h2
        · rw [indicator_of_notMem hp, indicator_of_notMem hp]
    _ = ENNReal.ofReal ((m ^ 3)⁻¹) * volume T := by
        rw [lintegral_indicator hTm, setLIntegral_const]
    _ < ⊤ := by
        refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
        rw [hT, Measure.volume_eq_prod, Measure.prod_prod]
        exact ENNReal.mul_lt_top measure_closedBall_lt_top (by simp)

variable {F : Type*} [Field F] [NumberField F]

/-- Boxes have finite measure. -/
theorem X.vol_box_lt_top (n : ℕ) : X.vol F (X.box n) < ⊤ := by
  have : (X.box n : Set (X F)) =
      Set.pi univ fun _ : InfinitePlace F => H3.box (1 / ((n : ℝ) + 1)) ((n : ℝ) + 1) n := by
    ext P; simp [X.box]
  rw [this, X.vol, Measure.pi_pi]
  exact ENNReal.prod_lt_top fun w _ => H3.vol_box_lt_top _ _ _ (by positivity)

end

end ArtinKP.X
end

section
-- module Solutions.Artin.KP.X2_Core
/-! # WP-X2, file 4: Green's identity on `X` and averaging over `Γ`

* `X.green`: `∫_X φ Δu = ∫_X Γ(φ, u)` when `φ` or `u` has compact support;
* `X.avg Γ φ = ∑_{γ ∈ Γ} φ ∘ γ` for compactly supported `φ`: locally finite, smooth,
  `Δ (avg φ) = avg (Δ φ)`, `Γ(avg φ, u) = avg Γ(φ, u)` for `Γ`-invariant `u`;
* unfolding `∫ η · avg φ · g = ∫_X φ g` for invariant `g` (`integral_avg_mul`);
* **Green's identity on `Γ \ X`** for `w = avg φ` and any smooth invariant `u`
  (`X.qgreen`, `X.qgreen'`): `∫ η w Δu = ∫ η Γ(w, u) = ∫ η u Δw`.
-/

open scoped MatrixGroups ComplexConjugate ENNReal Topology
open MeasureTheory Set NumberField Filter

set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.X

noncomputable section

open Classical

variable {F : Type*} [Field F] [NumberField F]

/-! ### Measure-theoretic instances -/

instance instIsFiniteMeasureOnCompactsXVol : IsFiniteMeasureOnCompacts (X.vol F) :=
  ⟨fun K hK => by
    obtain ⟨n, hn⟩ := X.exists_box_of_isCompact hK
    exact (measure_mono hn).trans_lt (X.vol_box_lt_top n)⟩

/-! ### Calculus on `X`: basic rules -/

/-! ### Invariance -/

/-- `Γ`-invariance of a function on `X`. -/
def X.IsInv (Γ : Subgroup (SL(2, 𝓞 F))) {β : Type*} (u : X F → β) : Prop :=
  ∀ (γ : Γ) (P : X F), u (γ • P) = u P

variable {Γ : Subgroup (SL(2, 𝓞 F))}

/-! ### Local finiteness and averaging -/

lemma X.avg_inv (Γ : Subgroup (SL(2, 𝓞 F))) (φ : X F → ℂ) : X.IsInv Γ (X.avg Γ φ) := by
  intro γ₀ P
  unfold X.avg
  rw [← (Equiv.mulRight γ₀).tsum_eq fun γ : Γ => φ (γ • P)]
  refine tsum_congr fun γ => ?_
  simp [mul_smul]

/-! ### Unfolding -/

lemma lintegral_avg_le {η : X F → ℝ≥0∞} (hη : IsPOU Γ η) {φ : X F → ℂ} (hφ : Measurable φ) :
    ∫⁻ P, ‖X.avg Γ φ P‖ₑ * η P ∂X.vol F ≤ ∫⁻ P, ‖φ P‖ₑ ∂X.vol F := by
  haveI _iCSL := ArtinKP.X.instCountableSLInt (F := F)
  have h := lintegral_tsum_swap (G := Γ) (μ := X.vol F) (φ := fun P => ‖φ P‖ₑ) (ψ := η)
    hφ.enorm hη.measurable
  simp only [hη.tsum_eq, mul_one] at h
  rw [h]
  refine lintegral_mono fun P => ?_
  rw [mul_comm]
  exact mul_le_mul_right (enorm_tsum_le_tsum_enorm) _

lemma lintegral_ne_top_of_continuous {f : X F → ℂ} (hf : Continuous f)
    (hc : HasCompactSupport f) : ∫⁻ P, ‖f P‖ₑ ∂X.vol F ≠ ⊤ :=
  (hf.integrable_of_hasCompactSupport hc).2.ne

/-! ### Green's identity on the quotient -/

end

end ArtinKP.X
end

section
-- module Solutions.Artin.KP.X2_H1
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

/-- The function on `Γ \ X` induced by a function on `X` (through representatives). -/
def X.desc (f : X F → ℂ) (q : Quotient (MulAction.orbitRel Γ (X F))) : ℂ := f q.out

variable {Γ}

lemma X.desc_mk {f : X F → ℂ} (hinv : X.IsInv Γ f) (P : X F) :
    X.desc Γ f (Quotient.mk (MulAction.orbitRel Γ (X F)) P) = f P := by
  have h := Quotient.mk_out (s := MulAction.orbitRel Γ (X F)) P
  obtain ⟨γ, hγ⟩ := h
  have hγ' : γ • P = (Quotient.mk (MulAction.orbitRel Γ (X F)) P).out := hγ
  unfold X.desc
  rw [← hγ']
  exact hinv γ P

lemma X.measurable_desc {f : X F → ℂ} (hf : Measurable f) (hinv : X.IsInv Γ f) :
    Measurable (X.desc Γ f) := by
  refine measurable_from_quotient.2 ?_
  have : X.desc Γ f ∘ Quotient.mk'' = f := funext fun P => X.desc_mk hinv P
  rw [this]
  exact hf

variable (Γ)

/-- `f` is measurable, `Γ`-invariant and square integrable modulo `Γ`. -/
structure X.L2Rep (f : X F → ℂ) : Prop where
  meas : Measurable f
  inv : X.IsInv Γ f
  memLp : MemLp (X.desc Γ f) 2 (X.quotVol Γ)

variable {Γ}

lemma X.L2Rep.of_lintegral {f : X F → ℂ} (hf : Measurable f) (hinv : X.IsInv Γ f)
    (hfin : ∫⁻ P, ‖f P‖ₑ ^ (2 : ℝ) * X.pou Γ P ∂X.vol F ≠ ⊤) : X.L2Rep Γ f := by
  refine ⟨hf, hinv, (X.measurable_desc hf hinv).aestronglyMeasurable, ?_⟩
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  simp only [ENNReal.toReal_ofNat]
  rw [X.lintegral_quotVol Γ (X.isPOU_pou Γ) ((X.measurable_desc hf hinv).enorm.pow_const _)]
  simp_rw [X.desc_mk hinv]
  exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) hfin

variable (Γ)

variable {Γ}

/-! ### Local integrability of pull-backs -/

/-! ### The core -/

variable (Γ)

variable {Γ}

lemma X.isInv_of_mem_core {w : X F → ℂ} (hw : w ∈ X.core Γ) : X.IsInv Γ w := by
  obtain ⟨φ, hφ, hc, rfl⟩ := hw
  exact X.avg_inv Γ φ

lemma X.avg_mul_inv {φ g : X F → ℂ} (hinv : X.IsInv Γ g) (P : X F) :
    X.avg Γ (fun P => φ P * g P) P = X.avg Γ φ P * g P := by
  simp only [X.avg, hinv _ P]
  rw [tsum_mul_right]

/-! ### Density of the core -/

/-! ### The symmetric operator and the energy space -/

end

end ArtinKP.X
end


