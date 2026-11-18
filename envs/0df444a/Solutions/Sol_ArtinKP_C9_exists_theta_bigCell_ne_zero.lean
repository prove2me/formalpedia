-- Prove2me | solution 1 for ArtinKP.C9.exists_theta_bigCell_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T10:04:28.526197+00:00
-- url     : https://prove2.me/submissions/1e5a2aad-92ec-4021-8240-a502902c499e

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
import Theorems.Thm_ArtinKP_C5_exists_single
import Theorems.Thm_ArtinKP_C5_l2Rep_src
import Theorems.Thm_ArtinKP_C5_tendsto_ray_functional_resPart_theta
import Theorems.Thm_ArtinKP_C9_theta_psiSum_ne_zero
import Theorems.Thm_ArtinKP_GL_eisEigen_of_two_lt_re
import Theorems.Thm_ArtinKP_N_coeff_resPart_add_hInt
import Theorems.Thm_ArtinKP_N_differentiable_hInt
import Theorems.Thm_ArtinKP_N_integral_box_theta_eq_of_tendsto_ray
import Theorems.Thm_ArtinKP_X_X_isPOU_pou
import Theorems.Thm_ArtinKP_X_X_tsum_indicator_box_le_boxMult

section
-- module Solutions.Artin.KP.X_Space
attribute [-instance] _root_.ArtinKP.X.instContinuousConstSMulSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instContinuousConstSMulSubgroup _root_.ArtinKP.X.instIsFiniteMeasureOnCompactsXVol _root_.ArtinKP.X.instIsFiniteMeasureXRestrictVolBox _root_.ArtinKP.X.instMeasurableConstSMulSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instMulActionSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatRingOfIntegersXVol _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
attribute [-simp] _root_.ArtinKP.FB.v_gmap _root_.ArtinKP.FB.x_gmap _root_.ArtinKP.X.chart_apply _root_.ArtinKP.X.chart_symm_apply
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

lemma pairDen_pos {c d : F} (h : c ≠ 0 ∨ d ≠ 0) (P : X F) : 0 < pairDen c d P :=
  Finset.prod_pos fun w _ => H3.rowDen_pos (by simpa using h) (P w)

lemma pairHt_pos {c d : F} (h : c ≠ 0 ∨ d ≠ 0) (P : X F) : 0 < pairHt c d P :=
  div_pos (ht_pos P) (pairDen_pos h P)

end X

/-! ### Topology and measure -/

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
-- module Solutions.Artin.KP.X_Disjoint
attribute [-instance] _root_.ArtinKP.X.instContinuousConstSMulSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instContinuousConstSMulSubgroup _root_.ArtinKP.X.instIsFiniteMeasureOnCompactsXVol _root_.ArtinKP.X.instIsFiniteMeasureXRestrictVolBox _root_.ArtinKP.X.instMeasurableConstSMulSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instMulActionSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatRingOfIntegersXVol _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-! # WP-X, file 4: disjointness of cusp neighbourhoods

For two pairs `(c,d)`, `(c',d')` with `Δ = c d' - c' d ≠ 0`:
`I_{(c,d)}(P) · I_{(c',d')}(P) ≤ 1 / ∏_w |Δ_w|²`.  With the `S`-normalized heights
`ht^S_{(c,d)} = I_{(c,d)} / ∏_{v ∈ S} max(|c|_v, |d|_v)` and `Δ` an `S`-integer the product formula
gives `ht^S_{(c,d)} · ht^S_{(c',d')} ≤ 1`: the regions `{ht^S_{(c,d)} > 1}` of non-proportional
pairs are disjoint.  No reduction theory is used.
-/

open scoped MatrixGroups ComplexConjugate
open NumberField

set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.X

noncomputable section

variable {F : Type*} [Field F] [NumberField F]

namespace X

lemma sNorm_pos (S : Finset (FinitePlace F)) {c d : F} (h : c ≠ 0 ∨ d ≠ 0) : 0 < sNorm S c d :=
  Finset.prod_pos fun v _ => by
    rcases h with h | h
    · exact lt_max_of_lt_left (FinitePlace.pos_iff.mpr h)
    · exact lt_max_of_lt_right (FinitePlace.pos_iff.mpr h)

lemma sHt_pos (S : Finset (FinitePlace F)) {c d : F} (h : c ≠ 0 ∨ d ≠ 0) (P : X F) :
    0 < sHt S c d P := div_pos (pairHt_pos h P) (sNorm_pos S h)

end X

end

end ArtinKP.X
end

section
-- module Solutions.Artin.KP.B1_Pairs
attribute [-instance] _root_.ArtinKP.X.instContinuousConstSMulSubgroup _root_.ArtinKP.X.instIsFiniteMeasureOnCompactsXVol _root_.ArtinKP.X.instIsFiniteMeasureXRestrictVolBox _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
attribute [-simp] _root_.ArtinKP.RO.rowPair_c _root_.ArtinKP.RO.rowPair_d
/-! # WP-B1, file 4: primitive pairs of `S`-integers modulo `S`-units; convergence and top height

`S` is any finite set of finite places of the totally complex field `F`; `IsSInt S`, `IsSUnit S`
describe the ring `R = 𝓞_S` and its units inside `F`.  `SPair S` = primitive pairs of `R²`
(`a c + b d = 1` solvable in `R`), `PairClass S = SPair S / U_S`, `PairClass.ht p P = ht_p(P)` the
`S`-normalized height, `PairClass.act` the right action of `SL₂(𝓞_F)`:
`(p.act γ).ht P = p.ht (γ • P)`.

* `summable_sHt_rpow`, `exists_summable_majorant_sHt`: (B1) for any family of pairwise
  `U_S`-inequivalent nonzero pairs of `S`-integers (primitive or not), `σ > 2`.
* `PairClass.summable_ht_rpow`, `PairClass.exists_summable_majorant`, `PairClass.exists_max_ht`.
* `PairClass.exists_ht_ge` (Lemma M): `sup_p ht_p(P) ≥ c₀ > 0`, under `SBezout S` (true when `R` is a PID).
-/

open scoped MatrixGroups ComplexConjugate ENNReal
open MeasureTheory Set NumberField Module

set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.B1

open ArtinKP.X

noncomputable section

variable {F : Type*} [Field F] [NumberField F]

variable {S : Finset (FinitePlace F)}

/-! ### The raw right action of `SL₂(𝓞_F)` on pairs -/

/-! ### Primitive pairs and pair classes -/

namespace SPair

lemma ne_zero (p : SPair S) : p.c ≠ 0 ∨ p.d ≠ 0 := by
  by_contra h
  push Not at h
  obtain ⟨a, b, -, -, hab⟩ := p.prim
  rw [h.1, h.2] at hab
  simp at hab

end SPair

namespace PairClass

variable [IsTotallyComplex F]

lemma ht_eq_out (p : PairClass S) (P : X F) : p.ht P = X.sHt S p.out.c p.out.d P := by
  conv_lhs => rw [← Quotient.out_eq p]
  rfl

lemma ht_pos (p : PairClass S) (P : X F) : 0 < p.ht P := by
  rw [ht_eq_out]; exact X.sHt_pos S p.out.ne_zero P

end PairClass

/-! ### (B1) for families of `S`-integer pairs -/

/-! ### Lemma M for pair classes -/

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
-- module Solutions.Artin.KP.B_RO
attribute [-instance] _root_.ArtinKP.X.instContinuousConstSMulSubgroup _root_.ArtinKP.X.instIsFiniteMeasureOnCompactsXVol _root_.ArtinKP.X.instIsFiniteMeasureXRestrictVolBox _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-!
# WP-B0, part 3: compatibility with WP-RO's bridge `Row 𝔪 / U_S ≃ B1.PairClass (SOf 𝔪)`

`B.sPl 𝔪` and `RO.SOf 𝔪` are the same finset, `B.RowClass 𝔪` is the source of `RO.rowClassEquiv`,
and the bridge preserves heights and the class of `(0, 1)`.  Hence B1's statements about
`PairClass (SOf 𝔪)` (`Tinf_le`, `G_le`, `PairClass.exists_top`, …) transfer to `RowClass 𝔪`.
(Leaf file: nothing in `B_Def`, `B_Def2` depends on WP-RO.)
-/

set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

open scoped MatrixGroups
open NumberField IsDedekindDomain ArtinPrimitiveRoots

noncomputable section

namespace ArtinKP.B

open ArtinKP.A ArtinKP.S ArtinKP.X ArtinKP.B1

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}

variable [IsTotallyComplex F]

/-- WP-RO's bridge preserves heights. -/
theorem ht_rowClassEquiv (h𝔪 : 𝔪 ≠ ⊥) (q : RowClass 𝔪) (Q : X F) :
    (RO.rowClassEquiv h𝔪 q).ht Q = q.ht Q := by
  conv_lhs => rw [← RowClass.mk_out q]
  rfl

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

lemma X.toL2_congr {f g : X F → ℂ} (hf : X.L2Rep Γ f) (hg : X.L2Rep Γ g) (h : f = g) :
    X.toL2 Γ f hf = X.toL2 Γ g hg := by
  subst h; rfl

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
-- module Solutions.Artin.KP.C5_PE
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-! # WP-C5, file 1: pseudo-Eisenstein series with a profile vanishing below height 2

For weights `a : PairClass S → ℂ` and a profile `g : ℝ → ℂ` (a function of `τ = log ht`),
`pe S a g P = ∑_p a(p) · g(log ht_p(P))`.  If `g` vanishes for `τ < log 2` (`VanishLow g`) the sum
is **locally a single term**, uniformly in `a` and `g` (`pe_eventually`; (H1) of MATH2 §0.1):
no convergence question arises.  Hence, for smooth `g`:

* `smooth_pe`, `lap_pe : Δ (pe a g) = pe a (Lg g)`, `Lg g = r(−g'' + 2g')`;
* `pe_smul`: invariance under `γ` when `a(pγ) = a(p)`;
* `norm_pe_le`, linearity in `a` and in `g`;
* if moreover `g` vanishes for `τ > log 3` (`VanishHigh g`), the support of `pe a g` lies in
  `Γ · K`, `K` compact (`exists_compact_pe`), so `pe a g ∈ X.core Γ` (`pe_mem_core`).
-/

open scoped MatrixGroups ComplexConjugate ENNReal Topology
open MeasureTheory Set NumberField Filter

set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace ArtinKP.C5

open ArtinKP.X ArtinKP.B1

noncomputable section

/-! ### Profiles -/

lemma VanishLow.deriv {g : ℝ → ℂ} (hg : VanishLow g) : VanishLow (deriv g) := by
  intro τ hτ
  have h : g =ᶠ[𝓝 τ] fun _ => (0 : ℂ) := by
    filter_upwards [Iio_mem_nhds hτ] with t ht using hg t ht
  rw [h.deriv_eq]
  simp

variable {F : Type*} [Field F] [NumberField F]

variable [IsTotallyComplex F] {S : Finset (FinitePlace F)}

/-! ### Locally a single term -/

lemma log_ht_lt {p : PairClass S} {P : X F} (h : p.ht P < 3 / 2) :
    Real.log (p.ht P) < Real.log 2 :=
  Real.log_lt_log (p.ht_pos P) (by linarith)

lemma pe_term_eq_zero {a : PairClass S → ℂ} {g : ℝ → ℂ} (hg : VanishLow g) {P : X F}
    {p : PairClass S} (h : p.ht P < 3 / 2) : a p * g (Real.log (p.ht P)) = 0 := by
  rw [hg _ (log_ht_lt h), mul_zero]

lemma pe_eq_single {a : PairClass S → ℂ} {g : ℝ → ℂ} (hg : VanishLow g) {P : X F}
    {p₁ : PairClass S} (h : ∀ p : PairClass S, p ≠ p₁ → p.ht P < 3 / 2) :
    pe S a g P = a p₁ * g (Real.log (p₁.ht P)) := by
  unfold pe
  exact tsum_eq_single p₁ fun p hp => pe_term_eq_zero hg (h p hp)

/-- **Locally a single term**, uniformly in the weights and the profile. -/
lemma pe_eventually (S : Finset (FinitePlace F)) (P₀ : X F) :
    ∃ p₁ : PairClass S, ∀ᶠ P in 𝓝 P₀, ∀ (a : PairClass S → ℂ) (g : ℝ → ℂ), VanishLow g →
      pe S a g P = a p₁ * g (Real.log (p₁.ht P)) := by
  obtain ⟨p₁, h⟩ := exists_single S P₀
  exact ⟨p₁, h.mono fun P hP a g hg => pe_eq_single hg hP⟩

lemma pe_single (S : Finset (FinitePlace F)) (P : X F) :
    ∃ p₁ : PairClass S, ∀ (a : PairClass S → ℂ) (g : ℝ → ℂ), VanishLow g →
      pe S a g P = a p₁ * g (Real.log (p₁.ht P)) := by
  obtain ⟨p₁, h⟩ := pe_eventually S P
  exact ⟨p₁, h.self_of_nhds⟩

/-! ### Algebra -/

lemma pe_lin_weight (a₁ a₂ : PairClass S → ℂ) {g : ℝ → ℂ} (hg : VanishLow g) (c : ℂ) (P : X F) :
    pe S (fun p => c * a₁ p + a₂ p) g P = c * pe S a₁ g P + pe S a₂ g P := by
  obtain ⟨p₁, h⟩ := pe_single S P
  rw [h _ g hg, h a₁ g hg, h a₂ g hg]
  ring

/-! ### Smoothness and the Laplacian -/

/-! ### Support -/

end

end ArtinKP.C5
end

section
-- module Solutions.Artin.KP.C5_Profile
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-! # WP-C5, file 3: the profiles of MATH2 §1

* `rho`: smooth, `0` on `(−∞, 2]`, `1` on `[3, ∞)`; `rt τ = ρ(e^τ)` and its derivatives `rt1`, `rt2`.
* `gS s τ = ρ(e^τ) e^{sτ}`: the profile of the cut-off part `h_s` (`gS_log : gS s (log h) = ρ(h) h^s`).
* `lam F s = r · s(2 − s)`.
* `phiS F s τ = r e^{sτ} (−ρ̃''(τ) + (2 − 2s) ρ̃'(τ))`: the profile of the source `F_s`
  (`Lg_gS : (L − λ(s)) gS s = phiS F s`); smooth, supported in `[log 2, log 3]`, entire in `s`,
  bounded on `{‖s‖ ≤ M} × ℝ` (`exists_norm_phiS_le`).
-/

open scoped MatrixGroups ComplexConjugate ENNReal Topology
open MeasureTheory Set NumberField Filter

set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.C5

noncomputable section

/-! ### The cut-off `ρ` -/

lemma rho_zero {h : ℝ} (hh : h ≤ 2) : rho h = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

lemma rt_low {τ : ℝ} (h : τ < Real.log 2) : rt τ = 0 := by
  unfold rt
  rw [rho_zero ((Real.lt_log_iff_exp_lt (by norm_num)).mp h).le]
  simp

lemma vanishLow_rt : VanishLow rt := fun _ h => rt_low h

lemma vanishLow_rt1 : VanishLow rt1 := vanishLow_rt.deriv

lemma vanishLow_rt2 : VanishLow rt2 := vanishLow_rt1.deriv

/-! ### The profile of `h_s` -/

variable {F : Type*} [Field F] [NumberField F]

/-! ### The eigenvalue and the profile of the source -/

lemma vanishLow_phiS (s : ℂ) : VanishLow (phiS F s) := fun τ h => by
  unfold phiS
  rw [vanishLow_rt1 τ h, vanishLow_rt2 τ h]
  simp

end

end ArtinKP.C5
end

section
-- module Solutions.Artin.KP.C5_Series
attribute [-instance] _root_.ArtinKP.F.instAddCommMonoidTSection _root_.ArtinKP.N2.levelGroup_finiteIndex _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-! # WP-C5, file 4: the cut-off part `h_s`, the source `F_s` and `u_s = E_Ψ − h_s`

For a twisted section `Ψ : TSection ι 𝔪` (weights `B.tildeC Ψ s` on `B.RowClass 𝔪`):

* `hpart Ψ s Q = ∑_q Ψ̃_s(q) ρ(ht_q(Q)) ht_q(Q)^s`, `src Ψ s Q = ∑_q Ψ̃_s(q) φ_s(log ht_q(Q))`,
  `upart Ψ s = eis Ψ s − hpart Ψ s`.  All three are defined without hypotheses; `hpart` and `src`
  are locally single terms for every `s ∈ ℂ` (`hpart_eq_pe`, `src_eq_pe`: they are WP-C5's `pe`
  with the weights `wt h𝔪 Ψ s` on `B1.PairClass (SOf 𝔪)`).
* `Inv Γ Ψ`: `Ψ` is fixed by (the image in `SL₂(R)` of) `Γ ≤ SL₂(𝓞_F)`.
* `norm_upart_le`: `|u_s| ≤ B · G` (WP-B1's `G`), `Re s > 2`; `l2Rep_upart`.
* `lap_hpart : Δ h_s = λ(s) h_s + F_s`; with the named hypothesis `EisEigen Ψ s` (WP-RF, D1:
  `E_Ψ(·, s)` is smooth and `Δ E = λ(s) E`): `lap_upart : Δ u_s = λ(s) u_s + (−F_s)`.
* `src`: smooth, invariant, in the core (`src_mem_core`), bounded (`exists_norm_src_le`), entire in
  `s` pointwise (`differentiable_src`).
-/

open scoped MatrixGroups ComplexConjugate ENNReal Topology
open MeasureTheory Set NumberField Filter IsDedekindDomain ArtinPrimitiveRoots

set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.C5

open ArtinKP.A ArtinKP.S ArtinKP.X ArtinKP.B1 ArtinKP.B

noncomputable section

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)} {ι : F →+* ℂ}

/-! ### Definitions (no hypotheses) -/

variable [IsTotallyComplex F]

/-- Sums over row classes are WP-C5's `pe` on WP-B1's pair classes. -/
lemma tsum_eq_pe (h𝔪 : 𝔪 ≠ ⊥) (Ψ : TSection ι 𝔪) (s : ℂ) (g : ℝ → ℂ) (Q : X F) :
    ∑' q : B.RowClass 𝔪, tildeC Ψ s q * g (Real.log (q.ht Q)) =
      pe (RO.SOf 𝔪) (wt h𝔪 Ψ s) g Q := by
  unfold pe
  rw [← (RO.rowClassEquiv h𝔪).tsum_eq]
  refine tsum_congr fun q => ?_
  rw [ht_rowClassEquiv]
  unfold wt
  rw [Equiv.symm_apply_apply]

lemma src_eq_pe (h𝔪 : 𝔪 ≠ ⊥) (Ψ : TSection ι 𝔪) (s : ℂ) :
    src Ψ s = pe (RO.SOf 𝔪) (wt h𝔪 Ψ s) (phiS F s) :=
  funext fun Q => tsum_eq_pe h𝔪 Ψ s (phiS F s) Q

/-! ### The Eisenstein series on pair classes -/

/-! ### Invariance, regularity -/

/-! ### The source -/

end

end ArtinKP.C5
end

section
-- module Solutions.Artin.KP.C5_Main
attribute [-instance] _root_.ArtinKP.F.instAddCommMonoidTSection _root_.ArtinKP.N2.levelGroup_finiteIndex _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
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

lemma srcL2_eq {Γ : Subgroup (SL(2, 𝓞 F))} {Ψ : TSection ι 𝔪} {s : ℂ}
    (h : X.L2Rep Γ (src Ψ s)) : srcL2 Γ Ψ s = X.toL2 Γ (src Ψ s) h := dif_pos h

/-! ### (C5) -/

/-! ### Continuation -/

/-! ### The limit (C7) -/

/-! ### `θ` is a weak eigenfunction -/

end

end ArtinKP.C5
end

section
-- module Solutions.Artin.KP.C5_Linear
attribute [-instance] _root_.ArtinKP.F.instAddCommMonoidTSection _root_.ArtinKP.N2.levelGroup_finiteIndex _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
attribute [-simp] _root_.ArtinKP.FB.v_gmap _root_.ArtinKP.FB.x_gmap _root_.ArtinKP.S.GSection.twist_apply
/-! # WP-C5, file 6: functionals and linearity in `Ψ`

* `differentiableOn_functional_resPart`, `tendsto_ray_functional`: for a bounded functional `ℓ`
  on `L²(Γ\X)` (e.g. `X.coeffFunctional Γ n ψ …`), `s ↦ ℓ(−Res(λ(s))[F_s])` is holomorphic on
  `Omega` and `(s_t − s₀) ℓ(…) → ℓ(θ_Ψ)` along the ray.
* `coeffFunctional_resPart`: for `Re s > 2` the local pairing of the resolvent expression is the
  integral of `u_s = E_Ψ − h_s` over the box.
* linearity: `src_add`, `src_smul`, `hpart_add`, `hpart_smul`, `Inv.add`, `Inv.smul`,
  `srcL2_add`, `srcL2_smul`, `resPart_add`, `resPart_smul`, `theta_add`, `theta_smul`.
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

/-! ### Linearity of the weights -/

lemma wt_add (h𝔪 : 𝔪 ≠ ⊥) (Ψ Ψ' : TSection ι 𝔪) (s : ℂ) (p : PairClass (RO.SOf 𝔪)) :
    wt h𝔪 (Ψ + Ψ') s p = wt h𝔪 Ψ s p + wt h𝔪 Ψ' s p := by
  unfold wt tildeC TSection.tilde
  rw [TSection.add_apply]
  ring

lemma wt_smul (h𝔪 : 𝔪 ≠ ⊥) (c : ℂ) (Ψ : TSection ι 𝔪) (s : ℂ) (p : PairClass (RO.SOf 𝔪)) :
    wt h𝔪 (c • Ψ) s p = c * wt h𝔪 Ψ s p := by
  unfold wt tildeC TSection.tilde
  rw [TSection.smul_apply]
  ring

lemma Inv.add {Γ : Subgroup (SL(2, 𝓞 F))} {Ψ Ψ' : TSection ι 𝔪} (h : Inv Γ Ψ) (h' : Inv Γ Ψ') :
    Inv Γ (Ψ + Ψ') := fun γ hγ => TSection.mem_stab.mpr fun s p => by
  rw [TSection.add_apply, TSection.add_apply, TSection.mem_stab.mp (h γ hγ) s p,
    TSection.mem_stab.mp (h' γ hγ) s p]

lemma Inv.smul {Γ : Subgroup (SL(2, 𝓞 F))} {Ψ : TSection ι 𝔪} (h : Inv Γ Ψ) (c : ℂ) :
    Inv Γ (c • Ψ) := fun γ hγ => TSection.mem_stab.mpr fun s p => by
  rw [TSection.smul_apply, TSection.smul_apply, TSection.mem_stab.mp (h γ hγ) s p]

variable [IsTotallyComplex F]

lemma pe_wt_add (h𝔪 : 𝔪 ≠ ⊥) (Ψ Ψ' : TSection ι 𝔪) (s : ℂ) {g : ℝ → ℂ} (hg : VanishLow g)
    (Q : X F) :
    pe (RO.SOf 𝔪) (wt h𝔪 (Ψ + Ψ') s) g Q =
      pe (RO.SOf 𝔪) (wt h𝔪 Ψ s) g Q + pe (RO.SOf 𝔪) (wt h𝔪 Ψ' s) g Q := by
  have e : wt h𝔪 (Ψ + Ψ') s = fun p => 1 * wt h𝔪 Ψ s p + wt h𝔪 Ψ' s p :=
    funext fun p => by rw [wt_add, one_mul]
  rw [e, pe_lin_weight _ _ hg, one_mul]

lemma pe_wt_smul (h𝔪 : 𝔪 ≠ ⊥) (c : ℂ) (Ψ : TSection ι 𝔪) (s : ℂ) {g : ℝ → ℂ} (hg : VanishLow g)
    (Q : X F) :
    pe (RO.SOf 𝔪) (wt h𝔪 (c • Ψ) s) g Q = c * pe (RO.SOf 𝔪) (wt h𝔪 Ψ s) g Q := by
  have e : wt h𝔪 (c • Ψ) s = fun p => c * wt h𝔪 Ψ s p + (fun _ => (0 : ℂ)) p :=
    funext fun p => by rw [wt_smul, add_zero]
  have h0 : pe (RO.SOf 𝔪) (fun _ => (0 : ℂ)) g Q = 0 := by
    unfold pe
    simp
  rw [e, pe_lin_weight _ _ hg, h0, add_zero]

theorem src_add (h𝔪 : 𝔪 ≠ ⊥) (Ψ Ψ' : TSection ι 𝔪) (s : ℂ) (Q : X F) :
    src (Ψ + Ψ') s Q = src Ψ s Q + src Ψ' s Q := by
  rw [src_eq_pe h𝔪, src_eq_pe h𝔪, src_eq_pe h𝔪]
  exact pe_wt_add h𝔪 Ψ Ψ' s (vanishLow_phiS s) Q

theorem src_smul (h𝔪 : 𝔪 ≠ ⊥) (c : ℂ) (Ψ : TSection ι 𝔪) (s : ℂ) (Q : X F) :
    src (c • Ψ) s Q = c * src Ψ s Q := by
  rw [src_eq_pe h𝔪, src_eq_pe h𝔪]
  exact pe_wt_smul h𝔪 c Ψ s (vanishLow_phiS s) Q

/-! ### Linearity of the classes, of the resolvent part and of `θ` -/

theorem srcL2_add (hG : Good 𝔪) (Γ : Subgroup (SL(2, 𝓞 F))) [Γ.FiniteIndex]
    {Ψ Ψ' : TSection ι 𝔪} (hΓ : Inv Γ Ψ) (hΓ' : Inv Γ Ψ') (s : ℂ) :
    srcL2 Γ (Ψ + Ψ') s = srcL2 Γ Ψ s + srcL2 Γ Ψ' s := by
  rw [srcL2_eq (l2Rep_src hG Γ (hΓ.add hΓ') s), srcL2_eq (l2Rep_src hG Γ hΓ s),
    srcL2_eq (l2Rep_src hG Γ hΓ' s), ← X.toL2_add]
  exact X.toL2_congr _ _ (funext fun Q => src_add hG.ne_bot Ψ Ψ' s Q)

theorem srcL2_smul (hG : Good 𝔪) (Γ : Subgroup (SL(2, 𝓞 F))) [Γ.FiniteIndex]
    {Ψ : TSection ι 𝔪} (hΓ : Inv Γ Ψ) (c : ℂ) (s : ℂ) :
    srcL2 Γ (c • Ψ) s = c • srcL2 Γ Ψ s := by
  rw [srcL2_eq (l2Rep_src hG Γ (hΓ.smul c) s), srcL2_eq (l2Rep_src hG Γ hΓ s),
    ← X.toL2_const_mul]
  exact X.toL2_congr _ _ (funext fun Q => src_smul hG.ne_bot c Ψ s Q)

/-- **`Ψ ↦ θ_Ψ` is additive.** -/
theorem theta_add (hG : Good 𝔪) (Γ : Subgroup (SL(2, 𝓞 F))) [Γ.FiniteIndex]
    {Ψ Ψ' : TSection ι 𝔪} (hΓ : Inv Γ Ψ) (hΓ' : Inv Γ Ψ') :
    theta Γ (Ψ + Ψ') = theta Γ Ψ + theta Γ Ψ' := by
  unfold theta
  rw [srcL2_add hG Γ hΓ hΓ', map_add, smul_add, neg_add]

/-- **`Ψ ↦ θ_Ψ` is homogeneous.** -/
theorem theta_smul (hG : Good 𝔪) (Γ : Subgroup (SL(2, 𝓞 F))) [Γ.FiniteIndex]
    {Ψ : TSection ι 𝔪} (hΓ : Inv Γ Ψ) (c : ℂ) : theta Γ (c • Ψ) = c • theta Γ Ψ := by
  unfold theta
  rw [srcL2_smul hG Γ hΓ, map_smul, smul_neg, smul_comm]

/-! ### Functionals -/

/-! ### A bound for the cut-off part on compact sets -/

end

end ArtinKP.C5
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
-- module Solutions.Artin.KP.C9_Main
attribute [-instance] _root_.ArtinKP.F.instAddCommMonoidTSection _root_.ArtinKP.N2.levelGroup_finiteIndex _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
attribute [-simp] _root_.ArtinKP.FB.v_gmap _root_.ArtinKP.FB.x_gmap
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

section lin

variable (hG : Good 𝔪) {z6 : 𝓞 F} (hz6 : IsPrimitiveRoot z6 6)

theorem twist_add (Φ Φ' : GSection ι P 𝔪) :
    (Φ + Φ').twist hG hz6 = Φ.twist hG hz6 + Φ'.twist hG hz6 := by
  ext s p
  simp only [GSection.twist_apply, GSection.add_apply, TSection.add_apply]
  ring

theorem twist_zero : (0 : GSection ι P 𝔪).twist hG hz6 = 0 := by
  ext s p
  simp only [GSection.twist_apply, GSection.zero_apply, TSection.zero_apply, mul_zero]

theorem inv_zero (Γ : Subgroup (SL(2, 𝓞 F))) : Inv Γ (0 : TSection ι 𝔪) :=
  fun _ _ => TSection.mem_stab.mpr fun _ _ => rfl

include hG in
theorem theta_zero (Γ : Subgroup (SL(2, 𝓞 F))) [Γ.FiniteIndex] :
    theta Γ (0 : TSection ι 𝔪) = 0 := by
  have h := theta_smul hG Γ (inv_zero (ι := ι) (𝔪 := 𝔪) Γ) 0
  have e : (0 : ℂ) • (0 : TSection ι 𝔪) = 0 := by
    ext s p
    simp
  rw [e, zero_smul] at h
  exact h

include hG hz6 in
/-- A finite family of twisted sections has a common finite-index invariance group. -/
theorem exists_inv_finset (Pk : CubicPkg F) {α : Type*} (I : Finset α)
    (Ψ : α → TSection ι 𝔪) :
    ∃ Γ : Subgroup (SL(2, 𝓞 F)), Γ.FiniteIndex ∧ ∀ i ∈ I, Inv Γ (Ψ i) := by
  classical
  induction I using Finset.induction_on with
  | empty => exact ⟨⊤, inferInstance, fun i hi => absurd hi (Finset.notMem_empty i)⟩
  | insert a I _ ih =>
    obtain ⟨Γ₁, h₁, hI⟩ := ih
    obtain ⟨Γ₂, h₂, ha⟩ := exists_finiteIndex_inv Pk hG hz6 (Ψ a)
    refine ⟨Γ₁ ⊓ Γ₂, inferInstance, fun i hi => ?_⟩
    rcases Finset.mem_insert.mp hi with rfl | hi'
    · exact fun γ hγ => ha γ hγ.2
    · exact fun γ hγ => hI i hi' γ hγ.1

/-- If every `θ_{Φ_i}` vanishes, so does `θ` of the sum. -/
theorem theta_sum_eq_zero (Γ : Subgroup (SL(2, 𝓞 F))) [Γ.FiniteIndex] {α : Type*}
    (I : Finset α) (f : α → GSection ι P 𝔪)
    (hinv : ∀ i ∈ I, Inv Γ ((f i).twist hG hz6))
    (h : ∀ i ∈ I, theta Γ ((f i).twist hG hz6) = 0) :
    Inv Γ ((∑ i ∈ I, f i).twist hG hz6) ∧ theta Γ ((∑ i ∈ I, f i).twist hG hz6) = 0 := by
  classical
  induction I using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, twist_zero]
    exact ⟨inv_zero Γ, theta_zero hG Γ⟩
  | insert a I ha ih =>
    obtain ⟨hI1, hI2⟩ := ih (fun i hi => hinv i (Finset.mem_insert_of_mem hi))
      (fun i hi => h i (Finset.mem_insert_of_mem hi))
    have ha1 := hinv a (Finset.mem_insert_self a I)
    rw [Finset.sum_insert ha, twist_add]
    refine ⟨ha1.add hI1, ?_⟩
    rw [theta_add hG Γ ha1 hI1, h a (Finset.mem_insert_self a I), hI2, add_zero]

end lin

/-! ### A single big cell -/

section bigCell

variable (hG : Good 𝔪) {z6 : 𝓞 F} (hz6 : IsPrimitiveRoot z6 6)
  {N : ℕ} (hN1 : 1 ≤ N) (hN : P.IsDeepLevel 𝔪 N) (M : ℤ) (Tc : Finset {η : F // η ≠ 0})
  (hdisj : ∀ η ∈ Tc, ∀ η' ∈ Tc, η ≠ η' → ∀ c : F, InClass 𝔪 N η.1 c → ¬ InClass 𝔪 N η'.1 c)
  (hcov : ∀ c : F, c ≠ 0 → ∃ η ∈ Tc, InClass 𝔪 N η.1 c)

include hdisj hcov in
/-- **(C9), single class**: some big-cell section `Φ^big_η`, `η ∈ T`, has `θ ≠ 0`; the statement
holds for every finite-index `Γ` fixing its twist. -/
theorem exists_theta_bigCell_ne_zero_oai (hM : 0 ≤ M) :
    ∃ η ∈ Tc, ∀ (Γ : Subgroup (SL(2, 𝓞 F))) [Γ.FiniteIndex],
      Inv Γ ((bigCell ι P hG hN1 hN η.1 η.2 M 0).twist hG hz6) →
      theta Γ ((bigCell ι P hG hN1 hN η.1 η.2 M 0).twist hG hz6) ≠ 0 := by
  classical
  obtain ⟨Γ₀, hfi, hΓ₀⟩ := exists_inv_finset hG hz6 P Tc
    fun η : {η : F // η ≠ 0} => (bigCell ι P hG hN1 hN η.1 η.2 M 0).twist hG hz6
  by_contra hcon
  push Not at hcon
  have hzero : ∀ η ∈ Tc, theta Γ₀ ((bigCell ι P hG hN1 hN η.1 η.2 M 0).twist hG hz6) = 0 := by
    intro η hη
    obtain ⟨Γ, hΓfi, hΓ, h0⟩ := hcon η hη
    exact theta_eq_zero_congr hG hΓ (hΓ₀ η hη) h0
  obtain ⟨hinv, h0⟩ := theta_sum_eq_zero hG hz6 Γ₀ Tc
    (fun η : {η : F // η ≠ 0} => bigCell ι P hG hN1 hN η.1 η.2 M 0) hΓ₀ hzero
  exact theta_psiSum_ne_zero hG hz6 hN1 hN M Tc hdisj hcov hM Γ₀ hinv h0

end bigCell

end

end ArtinKP.C9
end

theorem solution.{u_1} : type_of% @ArtinKP.C9.exists_theta_bigCell_ne_zero_oai.{u_1} := @ArtinKP.C9.exists_theta_bigCell_ne_zero_oai.{u_1}
