-- Prove2me | solution 1 for ArtinKP.G2a.coeff_thetaS_freq
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T10:07:51.572964+00:00
-- url     : https://prove2.me/submissions/75cf29fe-7cfa-43ac-bc89-87ec6ba305fb

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
import Theorems.Thm_ArtinKP_G2a_exists_major
import Theorems.Thm_ArtinKP_G2a_integral_strip_term

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

/-! ### The lattice `𝓞_F ⊂ ℂ^r` -/

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
-- module Solutions.Artin.KP.K_Jacquet
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-! # WP-K, file 2: the Jacquet integral at a complex place

Additive character: `archChar z = exp(2πi (z + z̄)) = exp(2πi · 2 Re z)` (the trace form `e(Tr z)`
of `ℂ/ℝ`; the goal's `sAddChar` is `exp(−2πi Tr_{F/ℚ}(·))` on fractional parts, whose factor at a
complex place `w` is `archChar (−σ_w ·)`; the Jacquet integral is even in `ν`, so the sign is
immaterial).

`jacquet s ν v = ∫_ℂ (v / (|x|² + v²))^s · archChar(−ν x) dx`. For `Re s > 1`, `v > 0`:

* `jacquet_zero`: `jacquet s 0 v = π/(s−1) · v^{2−s}`;
* `jacquet_eq`: for `ν ≠ 0`,
  `jacquet s ν v = (2π/Γ(s)) · (2π|ν|)^{s−1} · v · K_{s−1}(4π|ν|v)`
  `= (2π^s/Γ(s)) · (2|ν|)^{s−1} · v · K_{s−1}(4π|ν|v)` (`jacquet_eq'`).

The proof is OpenAI's (`OAI.CubicEisenstein.sourceFourierKernel_bessel`, openai/math family 003,
`Eisenstein/HyperbolicSpace.lean`, Apache 2.0; in our port `Definitions.Def_OAIHecke78B005`),
**copied** and restated for `besselK` (importing the bundle would drag B000–B004, ~45k lines).
-/

namespace ArtinKP.K

open MeasureTheory Set Filter
open scoped FourierTransform RealInnerProductSpace

noncomputable section

theorem continuous_archChar : Continuous archChar := by
  unfold archChar; fun_prop

/-! ## Radial integrals on `ℂ` (copied from OpenAI) -/

lemma integrable_radial_sq_iff (f : ℝ → ℂ) :
    Integrable (fun z : ℂ => f (‖z‖ ^ 2)) ↔ IntegrableOn f (Set.Ioi 0) := by
  rw [integrable_fun_norm_addHaar (volume : Measure ℂ) (f := fun r : ℝ => f (r^2))]
  have h := integrableOn_Ioi_comp_rpow_iff' (E := ℂ) f (p := 2) (by norm_num)
  simpa only [Complex.finrank_real_complex, Nat.reduceSub, pow_one,
    show (2:ℝ)-1=1 by norm_num, Real.rpow_one, Real.rpow_two] using h

lemma add_one_image_Ioi : (fun x : ℝ => x+1) '' Set.Ioi 0 = Set.Ioi 1 := by
  ext y
  constructor
  · rintro ⟨x,hx,rfl⟩
    simp only [Set.mem_Ioi] at *
    linarith
  · intro hy
    refine ⟨y-1, ?_, by ring⟩
    simp only [Set.mem_Ioi] at *
    linarith

lemma integrable_add_one_Ioi_iff (f : ℝ → ℂ) :
    IntegrableOn (fun x : ℝ => f (x+1)) (Set.Ioi 0) ↔ IntegrableOn f (Set.Ioi 1) := by
  have h := integrableOn_image_iff_integrableOn_abs_deriv_smul
    measurableSet_Ioi
    (fun x (hx : x ∈ Set.Ioi (0:ℝ)) => (hasDerivAt_id x |>.add_const 1).hasDerivWithinAt)
    (fun x hx y hy hxy => by dsimp at hxy; linarith : InjOn (fun x : ℝ => x+1) (Set.Ioi 0)) f
  simp only [id_eq] at h
  rw [add_one_image_Ioi] at h
  simpa only [abs_one, one_smul] using h.symm

lemma hyperbolicKernel_integrable (s : ℂ) (hs : 1 < s.re) :
    Integrable (hyperbolicKernel s) := by
  unfold hyperbolicKernel
  rw [integrable_radial_sq_iff (fun t : ℝ => ((1+t : ℝ) : ℂ)^(-s))]
  have h := (integrable_add_one_Ioi_iff (fun x : ℝ => (x : ℂ)^(-s))).mpr
    (integrableOn_Ioi_cpow_of_lt (by simpa using neg_lt_neg hs) (by norm_num : (0:ℝ)<1))
  simpa only [add_comm] using h

lemma continuous_hyperbolicKernel (s : ℂ) : Continuous (hyperbolicKernel s) := by
  unfold hyperbolicKernel
  apply Continuous.cpow
  · fun_prop
  · exact continuous_const
  · intro z
    exact Complex.ofReal_mem_slitPlane.mpr (by positivity)

/-! ## The Bessel form (ours, for `besselK`) -/

lemma traceIntegral_scale (v : ℝ) (hv : 0 < v) (s freq : ℂ) :
    (∫ z : ℂ,hyperbolicKernel s (z/(v:ℂ))*archChar (-freq*z))=
      (v:ℂ)^2*sourceFourierKernel s (freq*v) := by
  have heq (z : ℂ) : hyperbolicKernel s (z/(v:ℂ))*archChar (-freq*z)=
      (fun w : ℂ => hyperbolicKernel s w*archChar (-(freq*v)*w)) (v⁻¹ • z) := by
    simp only [Complex.real_smul,Complex.ofReal_inv]
    congr 2
    · ring
    · field_simp [Complex.ofReal_ne_zero.mpr hv.ne']
  simp_rw [heq]
  have h := Measure.integral_comp_inv_smul_of_nonneg (volume : Measure ℂ)
    (fun w : ℂ => hyperbolicKernel s w*archChar (-(freq*v)*w)) hv.le
  simpa only [Complex.finrank_real_complex,Complex.real_smul,Complex.ofReal_pow,sourceFourierKernel] using h

/-! ## The Jacquet integral -/

lemma height_cpow (s : ℂ) {v : ℝ} (hv : 0 < v) (x : ℂ) :
    ((v / (‖x‖ ^ 2 + v ^ 2) : ℝ) : ℂ) ^ s = (v : ℂ) ^ (-s) * hyperbolicKernel s (x / (v : ℂ)) := by
  unfold hyperbolicKernel
  have h1 : (v / (‖x‖ ^ 2 + v ^ 2) : ℝ) = v⁻¹ * (1 + ‖x / (v : ℂ)‖ ^ 2)⁻¹ := by
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hv.le]
    field_simp
    ring
  have hpos : (0 : ℝ) < 1 + ‖x / (v : ℂ)‖ ^ 2 := by positivity
  rw [h1, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (inv_nonneg.2 hv.le)
    (inv_nonneg.2 hpos.le), Complex.ofReal_inv, Complex.ofReal_inv,
    Complex.inv_cpow_ofReal_nonneg hv.le, Complex.inv_cpow_ofReal_nonneg hpos.le,
    Complex.cpow_neg, Complex.cpow_neg]

theorem jacquet_eq_sourceFourierKernel (s ν : ℂ) {v : ℝ} (hv : 0 < v) :
    jacquet s ν v = (v : ℂ) ^ (2 - s) * sourceFourierKernel s (ν * v) := by
  unfold jacquet
  simp_rw [height_cpow s hv, mul_assoc]
  rw [integral_const_mul, traceIntegral_scale v hv s ν, ← mul_assoc]
  congr 1
  rw [← Complex.cpow_natCast, ← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hv.ne')]
  congr 1
  push_cast; ring

/-! ## Holomorphy in `s` -/

end

end ArtinKP.K
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

theorem continuous_archChar : Continuous archChar := by
  unfold archChar
  fun_prop

theorem continuous_eInf : Continuous (eInf : (InfinitePlace F → ℂ) → ℂ) :=
  continuous_finsetProd _ fun w _ =>
    continuous_archChar.comp (continuous_apply w).neg

/-! ### The `S_f`-character -/

/-! ### The archimedean kernel -/

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
-- module Solutions.Artin.KP.RF_Fourier
attribute [-instance] _root_.ArtinKP.B.instCountableSInt _root_.ArtinKP.X.instContinuousConstSMulSubgroup _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
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

lemma mem_box_iff (n : ℕ) (P : X F) :
    P ∈ (X.box n : Set (X F)) ↔ (∀ w, ‖P.x w‖ ≤ n) ∧ P.v ∈ vBox F n := by
  simp only [X.box, H3.box, vBox, mem_ofPred_eq, X.x, X.v]
  exact forall_and

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
-- module Solutions.Artin.KP.T_Arch
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
attribute [-simp] _root_.ArtinKP.FB.v_gmap _root_.ArtinKP.FB.x_gmap
/-! # WP-T, file 2: the archimedean Whittaker function as a function on `X`

`WX s ν P = Winf s ν P.v = ∏_w jacquet s (−σ_w ν) v_w`.  For `Re s > 1`:

* `continuous_WX`, `differentiableOn_WX` (in `s`, `ν ≠ 0`), `exists_norm_WX_le` (bounded on
  `ball × box`);
* **`exists_WX_ne_zero`**: for every `s₁` (complex!) there is `δ > 0` with `WX s₁ ν P ≠ 0` whenever
  all `v_w < δ`.  (The Jacquet integral is `v^{2−s}·ĝ_s(νv)` with `ĝ_s` continuous and
  `ĝ_s(0) = π/(s−1) ≠ 0`; no information on zeros of `K_μ` of complex order is needed.)
* `phaseW s₁ ν`, a measurable test function of `v` of modulus `≤ 1` with
  `conj (phaseW s₁ ν P.v) * WX s₁ ν P = ‖WX s₁ ν P‖`.
-/

open scoped MatrixGroups ComplexConjugate ENNReal Topology
open MeasureTheory Set NumberField Filter IsDedekindDomain ArtinPrimitiveRoots Metric

set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.T

open ArtinKP.A ArtinKP.S ArtinKP.X ArtinKP.B1 ArtinKP.B ArtinKP.C5 ArtinKP.K ArtinKP.RF ArtinKP.N

noncomputable section

/-! ### One place -/

theorem continuous_sFK {s : ℂ} (hs : 1 < s.re) : Continuous (sourceFourierKernel s) := by
  unfold sourceFourierKernel
  refine continuous_of_dominated (bound := fun z => ‖hyperbolicKernel s z‖) (fun ξ => ?_)
    (fun ξ => ?_) (hyperbolicKernel_integrable s hs).norm ?_
  · have hchar : Continuous (fun z : ℂ => archChar (-ξ * z)) :=
      K.continuous_archChar.comp (by fun_prop)
    exact ((continuous_hyperbolicKernel s).mul hchar).aestronglyMeasurable
  · exact Eventually.of_forall fun z => by rw [norm_mul, archChar_norm, mul_one]
  · exact Eventually.of_forall fun z =>
      continuous_const.mul (K.continuous_archChar.comp (by fun_prop))

/-! ### The function on `X` -/

variable {F : Type*} [Field F] [NumberField F]

lemma WX_eq (s : ℂ) (ν : F) (P : X F) :
    WX s ν P = ∏ w : InfinitePlace F, ((P.v w : ℝ) : ℂ) ^ (2 - s) *
      sourceFourierKernel s (-(w.embedding ν) * P.v w) := by
  unfold WX Winf
  exact Finset.prod_congr rfl fun w _ => jacquet_eq_sourceFourierKernel s _ (P.v_pos w)

theorem continuous_WX {s : ℂ} (hs : 1 < s.re) (ν : F) : Continuous (WX s ν : X F → ℂ) := by
  have e : (WX s ν : X F → ℂ) = fun P => ∏ w : InfinitePlace F, ((P.v w : ℝ) : ℂ) ^ (2 - s) *
      sourceFourierKernel s (-(w.embedding ν) * P.v w) := funext fun P => WX_eq s ν P
  rw [e]
  refine continuous_finsetProd _ fun w _ => ?_
  have hv : Continuous fun P : X F => ((P.v w : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (X.continuous_v w)
  refine (hv.cpow continuous_const fun P => Or.inl ?_).mul
    ((continuous_sFK hs).comp (continuous_const.mul hv))
  simpa using P.v_pos w

/-! ### The phase test function -/

end

end ArtinKP.T
end

section
-- module Solutions.Artin.KP.G2a_Def
attribute [-instance] _root_.ArtinKP.N2.levelGroup_finiteIndex
attribute [-simp] _root_.ArtinKP.FB.v_gmap _root_.ArtinKP.FB.x_gmap
/-! # WP-G2a, file 3: the series `thetaS` (definition, convergence, continuity, linearity)

`term Φ ν Q = τ_Φ(ν)·W_{4/3}(ν; v)·e_∞(νx)` (`Q = (x, v)`), `thetaS Φ Q = Σ_{ν ∈ R∖0} term Φ ν Q`.
Under Theorem E (`ThmE`) the series converges absolutely, uniformly on every set `vOpen n`
(`v ∈ (1/(n+1), n+1)^r`, any `x`), together with every polynomial weight `∏_w (1+|ν|_w)^p`;
`thetaS Φ` is continuous on `X F`, additive in `Φ` and homogeneous for `smulFun`.
-/

open scoped ComplexConjugate Topology
open MeasureTheory Set NumberField Filter IsDedekindDomain ArtinPrimitiveRoots

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace ArtinKP.G2a

open ArtinKP.A ArtinKP.S ArtinKP.B ArtinKP.RF ArtinKP.X ArtinKP.B1

noncomputable section

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}
variable {ι : F →+* ℂ} {P : CubicPkg F}
variable [IsTotallyComplex F]
variable (hG : Good 𝔪) {z6 : 𝓞 F} (hz6 : IsPrimitiveRoot z6 6)

omit [IsTotallyComplex F] in
lemma continuous_x_pi : Continuous (X.x : X F → InfinitePlace F → ℂ) :=
  continuous_pi fun w => H3.continuous_x.comp (continuous_apply w)

lemma continuous_term (Φ : GSection ι P 𝔪) (ν : {ν : SInt 𝔪 // ν ≠ 0}) :
    Continuous (term hG hz6 Φ ν) := by
  unfold term
  exact (continuous_const.mul (T.continuous_WX (by norm_num) _)).mul
    (continuous_eInf.comp (continuous_const.mul continuous_x_pi))

lemma norm_term (Φ : GSection ι P 𝔪) (ν : {ν : SInt 𝔪 // ν ≠ 0}) (Q : X F) :
    ‖term hG hz6 Φ ν Q‖ =
      ‖T.tau hG hz6 Φ (ν : SInt 𝔪) * Winf (4 / 3) ((ν : SInt 𝔪) : F) Q.v‖ := by
  rw [term, norm_mul, norm_eInf, mul_one]
  rfl

variable {hG hz6} {g : AllowedGen ι 𝔪}

/-- **Uniform majorant on `vOpen n`, with polynomial weights.** -/
theorem exists_major_term (hE : ThmE hG hz6 g P) (Φ : GSection ι P 𝔪) (p n₀ : ℕ) :
    ∃ u : {ν : SInt 𝔪 // ν ≠ 0} → ℝ, Summable u ∧ (∀ ν, 0 ≤ u ν) ∧
      ∀ ν : {ν : SInt 𝔪 // ν ≠ 0}, ∀ Q : X F, Q.v ∈ vBox F n₀ →
        (∏ w : InfinitePlace F, (1 + w ((ν : SInt 𝔪) : F)) ^ p) * ‖term hG hz6 Φ ν Q‖ ≤ u ν := by
  obtain ⟨u, hu, hu0, h⟩ := exists_major hE Φ p n₀
  exact ⟨u, hu, hu0, fun ν Q hQ => by rw [norm_term]; exact h ν Q.v hQ⟩

theorem norm_term_le (hE : ThmE hG hz6 g P) (Φ : GSection ι P 𝔪) (n₀ : ℕ) :
    ∃ u : {ν : SInt 𝔪 // ν ≠ 0} → ℝ, Summable u ∧
      ∀ ν : {ν : SInt 𝔪 // ν ≠ 0}, ∀ Q : X F, Q.v ∈ vBox F n₀ → ‖term hG hz6 Φ ν Q‖ ≤ u ν := by
  obtain ⟨u, hu, -, h⟩ := exists_major_term hE Φ 0 n₀
  exact ⟨u, hu, fun ν Q hQ => by simpa using h ν Q hQ⟩

end

end ArtinKP.G2a
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
attribute [-instance] _root_.ArtinKP.N2.levelGroup_finiteIndex
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

variable (hG : Good 𝔪) {z6 : 𝓞 F} (hz6 : IsPrimitiveRoot z6 6)

section strip

variable (Φ : GSection ι P 𝔪) (Γ : Subgroup (SL(2, 𝓞 F))) [Γ.FiniteIndex]
  (hΓ : Inv Γ (Φ.twist hG hz6)) {D : Set (InfinitePlace F → ℂ)} (hD : MeasurableSet D)
  (hfund : ∀ x : InfinitePlace F → ℂ, ∃! γ : GammaN Γ, (fun w => x w + GammaN.shift γ w) ∈ D)
  {n : ℕ} (hb : ∀ x ∈ D, ∀ w, ‖x w‖ ≤ n) {ν' : InfinitePlace F → ℂ} (hν' : ν' ∈ dualLat Γ)
  {φ : (InfinitePlace F → ℝ) → ℂ} (hφ : Measurable φ) (hφ1 : ∀ v, ‖φ v‖ ≤ 1)

variable {hG hz6} {g : AllowedGen ι 𝔪}

include hΓ hD hfund hb hν' hφ hφ1 in
/-- **Termwise integration over the strip.** -/
theorem integral_strip_thetaS (hE : ThmE hG hz6 g P) :
    ∫ Q in X.box n, conj (stripFn D ν' φ Q) * thetaS hG hz6 Φ Q ∂X.vol F =
      ∑' ν : {ν : SInt 𝔪 // ν ≠ 0}, if T.freq ((ν : SInt 𝔪) : F) = ν' then
        T.tau hG hz6 Φ (ν : SInt 𝔪) * T.Wc D n φ ((ν : SInt 𝔪) : F) (4 / 3) else 0 := by
  have hfin := isFiniteMeasure_box (F := F) n
  obtain ⟨u, hu, hle⟩ := norm_term_le hE Φ n
  have hsm : Measurable fun Q : X F => conj (stripFn D ν' φ Q) :=
    Complex.continuous_conj.measurable.comp (measurable_stripFn hD ν' hφ)
  have hs1 : ∀ Q : X F, ‖conj (stripFn D ν' φ Q)‖ ≤ 1 := fun Q => by
    rw [RCLike.norm_conj]; exact norm_stripFn_le D ν' hφ1 Q
  set G : {ν : SInt 𝔪 // ν ≠ 0} → X F → ℂ := fun ν Q =>
    conj (stripFn D ν' φ Q) * term hG hz6 Φ ν Q with hGdef
  have hGint : ∀ ν, Integrable (G ν) ((X.vol F).restrict (X.box n)) := fun ν =>
    Integrable.bdd_mul (c := 1)
      ((continuous_term hG hz6 Φ ν).continuousOn.integrableOn_compact (isCompact_box n))
      hsm.aestronglyMeasurable (Eventually.of_forall hs1)
  have hGle : ∀ ν, ∫ Q in X.box n, ‖G ν Q‖ ∂X.vol F
      ≤ u ν * ((X.vol F).restrict (X.box n)).real univ := by
    intro ν
    have h1 : ∫ Q in X.box n, ‖G ν Q‖ ∂X.vol F ≤ ∫ _Q in X.box n, u ν ∂X.vol F := by
      refine integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _)
        (integrable_const _) ?_
      refine ae_restrict_of_forall_mem (X.measurableSet_box n) fun Q hQ => ?_
      have hQv : Q.v ∈ vBox F n := ((mem_box_iff n Q).mp hQ).2
      calc ‖G ν Q‖ = ‖conj (stripFn D ν' φ Q)‖ * ‖term hG hz6 Φ ν Q‖ := norm_mul _ _
        _ ≤ 1 * u ν := mul_le_mul (hs1 Q) (hle ν Q hQv) (norm_nonneg _) zero_le_one
        _ = u ν := one_mul _
    rw [integral_const, smul_eq_mul, mul_comm] at h1
    exact h1
  have hGsum : Summable fun ν => ∫ Q in X.box n, ‖G ν Q‖ ∂X.vol F :=
    Summable.of_nonneg_of_le (fun ν => integral_nonneg fun _ => norm_nonneg _) hGle
      (hu.mul_right _)
  have hsw := integral_tsum_of_summable_integral_norm hGint hGsum
  have e1 : ∫ Q in X.box n, conj (stripFn D ν' φ Q) * thetaS hG hz6 Φ Q ∂X.vol F
      = ∫ Q in X.box n, ∑' ν, G ν Q ∂X.vol F := by
    refine integral_congr_ae (Eventually.of_forall fun Q => ?_)
    simp only [hGdef, thetaS]
    rw [tsum_mul_left]
  rw [e1, ← hsw]
  exact tsum_congr fun ν => integral_strip_term hG hz6 Φ Γ hΓ hD hfund hb hν' hφ hφ1 ν

include hΓ hD hfund hb hφ hφ1 in
/-- **The coefficient of `thetaS Φ` at `T.freq ν`, `ν ∈ R ∖ 0`.** -/
theorem coeff_thetaS_freq_oai (hE : ThmE hG hz6 g P) (ν : {ν : SInt 𝔪 // ν ≠ 0})
    (hν : T.freq ((ν : SInt 𝔪) : F) ∈ dualLat Γ) :
    ∫ Q in X.box n, conj (stripFn D (T.freq ((ν : SInt 𝔪) : F)) φ Q) * thetaS hG hz6 Φ Q
        ∂X.vol F = T.tau hG hz6 Φ (ν : SInt 𝔪) * T.Wc D n φ ((ν : SInt 𝔪) : F) (4 / 3) := by
  rw [integral_strip_thetaS Φ Γ hΓ hD hfund hb hν hφ hφ1 hE, tsum_eq_single ν, if_pos rfl]
  intro μ hμ
  rw [if_neg]
  intro h
  exact hμ (Subtype.ext (Subtype.ext (freq_injective h)))

end strip

end

end ArtinKP.G2a
end

theorem solution.{u_1} : type_of% @ArtinKP.G2a.coeff_thetaS_freq_oai.{u_1} := @ArtinKP.G2a.coeff_thetaS_freq_oai.{u_1}
