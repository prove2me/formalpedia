-- Prove2me | solution 1 for ArtinKP.X.X.exists_isWeakSol_of_lap_eq_of_cutoff
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T09:45:25.132198+00:00
-- url     : https://prove2.me/submissions/9ec0cfba-c539-41db-b9d4-e5aa38ebfb40

import Mathlib
import Definitions.Def_ArtinKPB015
import Theorems.Thm_ArtinKP_X_X_coreL2_injective
import Theorems.Thm_ArtinKP_X_X_ims
import Theorems.Thm_ArtinKP_X_X_inner_coreL2_coreLap_self
import Theorems.Thm_ArtinKP_X_X_inner_coreLap_eq
import Theorems.Thm_ArtinKP_X_X_isPOU_pou
import Theorems.Thm_ArtinKP_X_X_l2Rep_of_mem_core
import Theorems.Thm_ArtinKP_X_X_mem_core_of_support

section
-- module Solutions.Artin.KP.CAbs_Form
/-!
# WP-C-abs, part 2: the form operator and the variational resolvent

Abstract setting (MATH.md §3.1): `H` plays `L²`, `V` plays `H¹`.  The data is a bounded map
`j : V →L[ℂ] H`, injective, with dense range and `‖j u‖ ≤ ‖u‖`.  The Dirichlet form is *defined* by
`𝔇(u, u') := ⟪u, u'⟫_V - ⟪j u, j u'⟫_H`, so that `‖u‖_V² = ‖j u‖² + 𝔇(u, u)` holds by definition.
Mathlib convention: inner products are conjugate-linear in the first and linear in the second
argument, so the "unknown" sits in the second slot and the test vector `u'` in the first.

* `T = j ∘ j†` (Riesz: `⟪j† f, u'⟫_V = ⟪f, j u'⟫_H`); bounded, self-adjoint, `0 ≤ T ≤ 1`, injective.
* `Res lam = T * (1 - (lam + 1) T)⁻¹` for `lam ∈ ℂ ∖ [0, ∞)`; `ResV lam f ∈ V` is the unique weak
  solution of `𝔇(u', u) - lam ⟪j u', j u⟫ = ⟪j u', f⟫` and `j (ResV lam f) = Res lam f`.
* `lam ↦ Res lam` is analytic (operator norm) on `ℂ ∖ [0, ∞)`.
-/

namespace ArtinKP.CAbs

open Filter Topology ComplexConjugate
open scoped InnerProductSpace NNReal

set_option linter.unusedSectionVars false

noncomputable section

namespace EnergySpace

variable {V : Type*} {H : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (E : EnergySpace V H)

/-- It suffices to test the weak equation on a dense set of test vectors of `V` (for instance
smooth compactly supported ones). -/
theorem isWeakSol_of_dense {S : Set V} (hS : Dense S) {lam : ℂ} {f : H} {u : V}
    (h : ∀ u' ∈ S, E.form u' u - lam * ⟪E.j u', E.j u⟫_ℂ = ⟪E.j u', f⟫_ℂ) :
    E.IsWeakSol lam f u := by
  intro u'
  have hcl : IsClosed {u' : V | E.form u' u - lam * ⟪E.j u', E.j u⟫_ℂ = ⟪E.j u', f⟫_ℂ} := by
    refine isClosed_eq ?_ ?_
    · unfold form; fun_prop
    · fun_prop
  exact hcl.closure_subset_iff.mpr h (hS u')

end EnergySpace

end

end ArtinKP.CAbs
end

section
-- module Solutions.Artin.KP.X_QuotC
/-! # WP-X, file 8: unfolding for complex-valued functions (absolutely convergent case)

Complex versions of the Tonelli lemmas of `X_Quot`, under an absolute-integrability hypothesis
stated as finiteness of a lower integral.  Weights are the real numbers `(η a).toReal`.
-/

open scoped ENNReal
open MeasureTheory Set

set_option linter.unusedSectionVars false

namespace ArtinKP.X

noncomputable section

variable {G α : Type*} [Group G] [Countable G] [MeasurableSpace α] [MulAction G α]
  [MeasurableConstSMul G α] {μ : Measure α} [SMulInvariantMeasure G α μ]

lemma IsPOU.le_one {η : α → ℝ≥0∞} (hη : IsPOU G η) (a : α) : η a ≤ 1 := by
  have h := ENNReal.le_tsum (f := fun g : G => η (g • a)) 1
  rwa [one_smul, hη.tsum_eq] at h

lemma IsPOU.ne_top {η : α → ℝ≥0∞} (hη : IsPOU G η) (a : α) : η a ≠ ⊤ :=
  ((hη.le_one a).trans_lt ENNReal.one_lt_top).ne

end

end ArtinKP.X
end

section
-- module Solutions.Artin.KP.X2_Core
attribute [-instance] _root_.ArtinKP.X.instContinuousConstSMulSubgroup
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

/-! ### Calculus on `X`: basic rules -/

lemma X.Smooth.mul {u w : X F → ℂ} (hu : X.Smooth u) (hw : X.Smooth w) :
    X.Smooth fun P => u P * w P := ContDiff.mul hu.contDiff hw.contDiff

lemma X.Smooth.differentiable {u : X F → ℂ} (hu : X.Smooth u) :
    Differentiable ℝ fun y => u (chart F y) := hu.contDiff.differentiable (by simp)

/-! ### Invariance -/

/-! ### Local finiteness and averaging -/

/-! ### Unfolding -/

/-! ### Green's identity on the quotient -/

end

end ArtinKP.X
end

section
-- module Solutions.Artin.KP.X_Friedrichs
/-! # WP-X, file 11: closability — the Friedrichs energy space of a symmetric nonnegative operator

Abstract form of "the Dirichlet form is closable".  Let `A` be a symmetric nonnegative operator
defined on a dense subspace `D` of a Hilbert space `H` (`SymmOp H`; think `D` = smooth
`Γ`-invariant functions with compact support modulo `Γ`, `A = Δ`, symmetry and positivity = Green's
identity).  Complete `D` for the energy inner product `⟪u,w⟫₁ = ⟪u,w⟫ + ⟪u, A w⟫`; the inclusion
`D → H` extends to a contraction `j : V → H` which is **injective** (this is closability:
`⟪x, w⟫₁ = ⟪j x, w + A w⟫` for `w ∈ D`, and `D` is dense in `V`) with dense range.  The result is an
`EnergySpace V H` in the sense of `CAbs_Form`, with `form u w = ⟪u, A w⟫` on the core.
-/

open scoped InnerProductSpace ComplexConjugate
open UniformSpace

set_option linter.unusedSectionVars false

namespace ArtinKP.X

noncomputable section

namespace SymmOp

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (S : SymmOp H)

variable [CompleteSpace H]

/-- Weak solutions can be tested on the core. -/
theorem dense_range_kappa_set : Dense (Set.range S.kappa) := S.denseRange_kappa

end SymmOp

end

end ArtinKP.X
end

section
-- module Solutions.Artin.KP.X2_H1
attribute [-instance] _root_.ArtinKP.B1.instCountableSubtypeForallInfinitePlaceComplexMemAddSubgroupLatSub _root_.ArtinKP.X.instContinuousConstSMulSubgroup
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

lemma X.L2Rep.lintegral_ne_top {f : X F → ℂ} (h : X.L2Rep Γ f) :
    ∫⁻ P, ‖f P‖ₑ ^ (2 : ℝ) * X.pou Γ P ∂X.vol F ≠ ⊤ := by
  have h1 := h.memLp.2
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)] at h1
  simp only [ENNReal.toReal_ofNat] at h1
  rw [X.lintegral_quotVol Γ (X.isPOU_pou Γ)
    ((X.measurable_desc h.meas h.inv).enorm.pow_const _)] at h1
  simp_rw [X.desc_mk h.inv] at h1
  intro htop
  rw [htop] at h1
  simp at h1

variable (Γ)

variable {Γ}

lemma X.toL2_sub {f g : X F → ℂ} (hf : X.L2Rep Γ f) (hg : X.L2Rep Γ g) :
    X.toL2 Γ (fun P => f P - g P) (hf.sub hg) = X.toL2 Γ f hf - X.toL2 Γ g hg :=
  MemLp.toLp_sub hf.memLp hg.memLp

/-- The pull-back of the class of `f` is `f` almost everywhere. -/
lemma X.lift_toL2 {f : X F → ℂ} (h : X.L2Rep Γ f) : X.lift Γ (X.toL2 Γ f h) =ᵐ[X.vol F] f := by
  haveI _iCSL := ArtinKP.X.instCountableSLInt (F := F)
  have h1 := liftQ_ae_eq (X.isPOU_pou Γ) (MemLp.coeFn_toLp h.memLp)
  refine h1.trans (Filter.Eventually.of_forall fun P => ?_)
  exact X.desc_mk h.inv P

lemma X.integral_quotVol {h : Quotient (MulAction.orbitRel Γ (X F)) → ℂ} (hh : Measurable h) :
    ∫ q, h q ∂X.quotVol Γ =
      ∫ P, (((X.pou Γ P).toReal : ℝ) : ℂ) * h (Quotient.mk _ P) ∂X.vol F := by
  haveI _iCSL := ArtinKP.X.instCountableSLInt (F := F)
  unfold X.quotVol quotMeasure
  rw [integral_map measurable_mk.aemeasurable hh.aestronglyMeasurable,
    integral_withDensity_eq_integral_toReal_smul (X.isPOU_pou Γ).measurable
      (Filter.Eventually.of_forall fun P => ((X.isPOU_pou Γ).ne_top P).lt_top)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun P => ?_)
  simp only [Complex.real_smul]

/-- Inner products with a class are integrals against the partition of unity. -/
theorem X.inner_toL2 {f : X F → ℂ} (h : X.L2Rep Γ f) (v : X.L2 Γ) :
    ⟪X.toL2 Γ f h, v⟫_ℂ =
      ∫ P, (((X.pou Γ P).toReal : ℝ) : ℂ) * (conj (f P) * X.lift Γ v P) ∂X.vol F := by
  rw [MeasureTheory.L2.inner_def]
  have h1 : (fun q => ⟪(X.toL2 Γ f h : Quotient (MulAction.orbitRel Γ (X F)) → ℂ) q, v q⟫_ℂ)
      =ᵐ[X.quotVol Γ] fun q => conj (X.desc Γ f q) * v q := by
    filter_upwards [MemLp.coeFn_toLp h.memLp] with q hq
    rw [show (X.toL2 Γ f h : Quotient (MulAction.orbitRel Γ (X F)) → ℂ) q = X.desc Γ f q from hq]
    simp [mul_comm]
  have hm : Measurable fun q : Quotient (MulAction.orbitRel Γ (X F)) =>
      conj (X.desc Γ f q) * v q :=
    (Complex.continuous_conj.measurable.comp (X.measurable_desc h.meas h.inv)).mul
      (Lp.stronglyMeasurable v).measurable
  rw [integral_congr_ae h1, X.integral_quotVol hm]
  refine integral_congr_ae (Filter.Eventually.of_forall fun P => ?_)
  simp only [X.desc_mk h.inv]
  rfl

theorem X.inner_toL2_toL2 {f g : X F → ℂ} (hf : X.L2Rep Γ f) (hg : X.L2Rep Γ g) :
    ⟪X.toL2 Γ f hf, X.toL2 Γ g hg⟫_ℂ =
      ∫ P, (((X.pou Γ P).toReal : ℝ) : ℂ) * (conj (f P) * g P) ∂X.vol F := by
  rw [X.inner_toL2]
  refine integral_congr_ae ?_
  filter_upwards [X.lift_toL2 hg] with P hP
  rw [hP]

theorem X.norm_sq_toL2 {f : X F → ℂ} (h : X.L2Rep Γ f) :
    ‖X.toL2 Γ f h‖ ^ 2 = ∫ P, (X.pou Γ P).toReal * ‖f P‖ ^ 2 ∂X.vol F := by
  have h1 := X.inner_toL2_toL2 h h
  have h2 : ∀ P, (((X.pou Γ P).toReal : ℝ) : ℂ) * (conj (f P) * f P) =
      (((X.pou Γ P).toReal * ‖f P‖ ^ 2 : ℝ) : ℂ) := by
    intro P
    rw [Complex.conj_mul']
    push_cast
    ring
  simp_rw [h2] at h1
  rw [integral_complex_ofReal] at h1
  have h3 := inner_self_eq_norm_sq (𝕜 := ℂ) (X.toL2 Γ f h)
  rw [h1] at h3
  rw [← h3]
  simp

/-! ### Local integrability of pull-backs -/

/-! ### The core -/

variable (Γ)

variable {Γ}

variable (Γ)

variable {Γ}

lemma X.coreL2_apply (w : X.core Γ) :
    X.coreL2 Γ w = X.toL2 Γ w (X.l2Rep_of_mem_core w.2) := rfl

/-! ### Density of the core -/

/-! ### The symmetric operator and the energy space -/

variable (Γ)

variable {Γ}

lemma X.incl_coreD (a : X.core Γ) : (X.symmOp Γ).incl (X.coreD Γ a) = X.coreL2 Γ a := rfl

lemma X.op_coreD (a : X.core Γ) :
    (X.symmOp Γ).op (X.coreD Γ a) = X.coreL2 Γ (X.coreLap Γ a) := by
  change X.coreL2 Γ (X.coreLap Γ
    ((LinearEquiv.ofInjective (X.coreL2 Γ) X.coreL2_injective).symm
      (LinearEquiv.ofInjective (X.coreL2 Γ) X.coreL2_injective a))) = _
  rw [LinearEquiv.symm_apply_apply]

lemma X.coreD_surjective (c : (X.symmOp Γ).Core) : ∃ a : X.core Γ, X.coreD Γ a = c :=
  ⟨_, LinearEquiv.apply_symm_apply (LinearEquiv.ofInjective (X.coreL2 Γ) X.coreL2_injective) c⟩

end

end ArtinKP.X
end

section
-- module Solutions.Artin.KP.X2_Cutoff
/-! # WP-X2, file 7: the height cut-off lemma

`X.exists_weakSol`: a smooth `Γ`-invariant `u ∈ L²(Γ\X)` with `Δu = λu + f` pointwise,
`f ∈ L²(Γ\X)`, lies in `H¹(Γ\X)` and is a weak solution against all of `H¹`, given cut-offs
`χ_n` (smooth, invariant, `0 ≤ χ_n ≤ 1`, compact support modulo `Γ`, `χ_n → 1` pointwise,
`∑_w v_w²|∇_w χ_n|² ≤ ε_n → 0`).  This is MATH2 §1.6; the only completeness input is the
existence of the cut-offs (MATH2 §1.4(d)).

The energy of `χ u` is computed by the IMS localisation formula (`X.ims`)
`∫ |∇(χu)|² = ∫ χ² Re(ū Δu) + ∫ |u|² |∇χ|²`, so finiteness of the energy of `u` is not assumed.
-/

open scoped MatrixGroups ComplexConjugate ENNReal Topology InnerProductSpace
open MeasureTheory Set NumberField Filter

set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.X

noncomputable section

open Classical

variable {F : Type*} [Field F] [NumberField F] {Γ : Subgroup (SL(2, 𝓞 F))}

lemma X.Smooth.sub {u w : X F → ℂ} (hu : X.Smooth u) (hw : X.Smooth w) :
    X.Smooth fun P => u P - w P := ContDiff.sub hu.contDiff hw.contDiff

lemma X.Smooth.ofReal_continuous {c : X F → ℝ} (hc : X.Smooth fun P => (c P : ℂ)) :
    Continuous c := by
  have h : c = Complex.re ∘ fun P => (c P : ℂ) := by
    funext P; simp
  rw [h]
  exact Complex.continuous_re.comp hc.continuous

lemma X.L2Rep.integrable_sq {f : X F → ℂ} (h : X.L2Rep Γ f) :
    Integrable (fun P => (X.pou Γ P).toReal * ‖f P‖ ^ 2) (X.vol F) := by
  have h1 := integrable_toReal_of_lintegral_ne_top
    ((h.meas.enorm.pow_const (2 : ℝ)).mul (X.isPOU_pou Γ).measurable).aemeasurable
    h.lintegral_ne_top
  refine h1.congr (Filter.Eventually.of_forall fun P => ?_)
  simp only [Pi.mul_apply, ENNReal.toReal_mul, ← ENNReal.toReal_rpow, toReal_enorm]
  rw [Real.rpow_two, mul_comm]

/-- The energy norm of a core function. -/
lemma X.norm_sq_kappa (a : X.core Γ) :
    ‖(X.symmOp Γ).kappa (X.coreD Γ a)‖ ^ 2 =
      (∫ P, (X.pou Γ P).toReal * ‖(a : X F → ℂ) P‖ ^ 2 ∂X.vol F) +
        ∫ P, (X.pou Γ P).toReal * X.grad2 a P ∂X.vol F := by
  rw [SymmOp.kappa_apply, UniformSpace.Completion.norm_coe, @norm_sq_eq_re_inner ℂ,
    SymmOp.inner_core, X.incl_coreD, X.op_coreD, X.inner_coreL2_coreLap_self]
  have h2 : RCLike.re ⟪X.coreL2 Γ a, X.coreL2 Γ a⟫_ℂ =
      ∫ P, (X.pou Γ P).toReal * ‖(a : X F → ℂ) P‖ ^ 2 ∂X.vol F := by
    rw [← @norm_sq_eq_re_inner ℂ]
    exact X.norm_sq_toL2 (X.l2Rep_of_mem_core a.2)
  rw [map_add, h2]
  simp

/-- The squared gradient of a difference. -/
lemma X.grad2_sub_le {u w : X F → ℂ} (hu : X.Smooth u) (hw : X.Smooth w) (P : X F) :
    X.grad2 (fun P => u P - w P) P ≤ 2 * X.grad2 u P + 2 * X.grad2 w P := by
  unfold X.grad2
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun v _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun k _ => ?_
  have h1 : pd v k (fun y => u (chart F y) - w (chart F y)) ((chart F).symm P) =
      pd v k (fun y => u (chart F y)) ((chart F).symm P) -
        pd v k (fun y => w (chart F y)) ((chart F).symm P) := by
    unfold pd
    rw [fderiv_fun_sub (hu.differentiable _) (hw.differentiable _)]
    rfl
  rw [h1]
  set A := pd v k (fun y => u (chart F y)) ((chart F).symm P)
  set B := pd v k (fun y => w (chart F y)) ((chart F).symm P)
  have h2 : ‖A - B‖ ^ 2 ≤ 2 * ‖A‖ ^ 2 + 2 * ‖B‖ ^ 2 := by
    have := norm_sub_le A B
    nlinarith [sq_nonneg (‖A‖ - ‖B‖), norm_nonneg (A - B), norm_nonneg A, norm_nonneg B]
  have h3 := acoef_pos k ((chart F).symm P v)
  nlinarith

/-- **The height cut-off lemma** (MATH2 §1.6).  Let `u` be smooth, `Γ`-invariant, in `L²(Γ\X)`,
with `Δu = λu + f` pointwise and `f ∈ L²(Γ\X)`.  Given cut-offs `χ_n` (smooth, invariant,
`0 ≤ χ_n ≤ 1`, support compact modulo `Γ`, `χ_n → 1` pointwise, `|∇χ_n|² ≤ ε_n → 0`), `u` is in
`H¹(Γ\X)` and is the weak solution: `𝔇(u', u) − λ⟪u', u⟫ = ⟪u', f⟫` for all `u' ∈ H¹`. -/
theorem X.exists_isWeakSol_of_lap_eq_of_cutoff_oai {u f : X F → ℂ} (hu : X.Smooth u) (hu2 : X.L2Rep Γ u)
    (hf2 : X.L2Rep Γ f) (lam : ℂ) (heq : ∀ P, X.lap u P = lam * u P + f P)
    (χ : ℕ → X F → ℝ) (hχs : ∀ n, X.Smooth fun P => (χ n P : ℂ))
    (hχinv : ∀ n, X.IsInv Γ (χ n))
    (hχK : ∀ n, ∃ K : Set (X F), IsCompact K ∧ ∀ P, χ n P ≠ 0 → ∃ γ : Γ, γ • P ∈ K)
    (hχ0 : ∀ n P, 0 ≤ χ n P) (hχ1 : ∀ n P, χ n P ≤ 1)
    (hχlim : ∀ P, Tendsto (fun n => χ n P) atTop (𝓝 1))
    (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝 0))
    (hgrad : ∀ n P, X.grad2 (fun P => (χ n P : ℂ)) P ≤ ε n) :
    ∃ x : X.H1 Γ, (X.energy Γ).j x = X.toL2 Γ u hu2 ∧
      (X.energy Γ).IsWeakSol lam (X.toL2 Γ f hf2) x := by
  have hinv := hu2.inv
  set η : X F → ℝ := fun P => (X.pou Γ P).toReal with hη
  have hη0 : ∀ P, 0 ≤ η P := fun P => ENNReal.toReal_nonneg
  set G₀ : X F → ℝ := fun P => (‖lam‖ + 2) * ‖u P‖ ^ 2 + ‖f P‖ ^ 2 with hG₀
  have hG₀0 : ∀ P, 0 ≤ G₀ P := fun P => by positivity
  have hIu : Integrable (fun P => η P * ‖u P‖ ^ 2) (X.vol F) := hu2.integrable_sq
  have hIf : Integrable (fun P => η P * ‖f P‖ ^ 2) (X.vol F) := hf2.integrable_sq
  have hB : Integrable (fun P => η P * G₀ P) (X.vol F) := by
    have := (hIu.const_mul (‖lam‖ + 2)).add hIf
    refine this.congr (Filter.Eventually.of_forall fun P => ?_)
    simp only [hG₀, Pi.add_apply]
    ring
  set U : ℝ := ∫ P, η P * ‖u P‖ ^ 2 ∂X.vol F with hU
  set σ : ℕ → ℝ := fun n => ∫ P, (1 - χ n P) * (η P * G₀ P) ∂X.vol F with hσdef
  set τ : ℕ → ℝ := fun n => σ n + 2 * ε n * U with hτdef
  have hχc : ∀ n, Continuous (χ n) := fun n => (hχs n).ofReal_continuous
  have hχabs : ∀ n P, |1 - χ n P| ≤ 1 := fun n P => by
    rw [abs_le]; constructor <;> linarith [hχ0 n P, hχ1 n P]
  have hσint : ∀ n, Integrable (fun P => (1 - χ n P) * (η P * G₀ P)) (X.vol F) := fun n =>
    Integrable.bdd_mul (c := 1) hB ((continuous_const.sub (hχc n)).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun P => by rw [Real.norm_eq_abs]; exact hχabs n P)
  have hσ : Tendsto σ atTop (𝓝 0) := by
    have := tendsto_integral_of_dominated_convergence (μ := X.vol F)
      (F := fun n P => (1 - χ n P) * (η P * G₀ P)) (f := fun _ => (0 : ℝ))
      (fun P => η P * G₀ P) (fun n => (hσint n).aestronglyMeasurable) hB
      (fun n => Filter.Eventually.of_forall fun P => ?_)
      (Filter.Eventually.of_forall fun P => ?_)
    · simpa using this
    · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (mul_nonneg (hη0 P) (hG₀0 P))]
      exact mul_le_of_le_one_left (mul_nonneg (hη0 P) (hG₀0 P)) (hχabs n P)
    · have := ((tendsto_const_nhds (x := (1 : ℝ))).sub (hχlim P)).mul_const (η P * G₀ P)
      simpa using this
  have hτ : Tendsto τ atTop (𝓝 0) := by
    have := hσ.add ((hε.const_mul 2).mul_const U)
    simpa using this
  -- the approximants
  have hmem : ∀ n, (fun P => (χ n P : ℂ) * u P) ∈ X.core Γ := fun n => by
    obtain ⟨K, hK, hKs⟩ := hχK n
    exact X.mem_core_of_support ((hχs n).mul hu)
      (fun γ P => by simp only [hχinv n γ P, hinv γ P]) hK
      (fun P hP => hKs P (by intro h0; apply hP; simp [h0]))
  set a : ℕ → X.core Γ := fun n => ⟨fun P => (χ n P : ℂ) * u P, hmem n⟩ with ha
  have ha_apply : ∀ n P, ((a n : X.core Γ) : X F → ℂ) P = (χ n P : ℂ) * u P := fun n P => rfl
  set x : ℕ → X.H1 Γ := fun n => (X.symmOp Γ).kappa (X.coreD Γ (a n)) with hx
  have hRe : ∀ P, (conj (u P) * X.lap u P).re ≤ (‖lam‖ + 1) * ‖u P‖ ^ 2 + ‖f P‖ ^ 2 := by
    intro P
    rw [heq]
    have h1 := Complex.re_le_norm (conj (u P) * (lam * u P + f P))
    rw [norm_mul, RCLike.norm_conj] at h1
    have h2 : ‖lam * u P + f P‖ ≤ ‖lam‖ * ‖u P‖ + ‖f P‖ := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul]
    have h3 := mul_le_mul_of_nonneg_left h2 (norm_nonneg (u P))
    nlinarith [sq_nonneg (‖u P‖ - ‖f P‖), norm_nonneg (u P), norm_nonneg (f P), norm_nonneg lam]
  have hbound : ∀ n m, ‖x n - x m‖ ^ 2 ≤ τ n + τ m := by
    intro n m
    have h1 : x n - x m = (X.symmOp Γ).kappa (X.coreD Γ (a n - a m)) := by
      have h0 : X.coreD Γ (a n - a m) = X.coreD Γ (a n) - X.coreD Γ (a m) :=
        map_sub (LinearEquiv.ofInjective (X.coreL2 Γ) X.coreL2_injective) _ _
      rw [h0, map_sub]
    set c : X F → ℝ := fun P => χ n P - χ m P with hc
    have hcfun : (fun P => ((c P : ℝ) : ℂ)) = fun P => (χ n P : ℂ) - (χ m P : ℂ) := by
      funext P; simp [hc]
    have hcs : X.Smooth fun P => (c P : ℂ) := by
      rw [hcfun]; exact (hχs n).sub (hχs m)
    obtain ⟨Kn, hKn, hKns⟩ := hχK n
    obtain ⟨Km, hKm, hKms⟩ := hχK m
    have hcK : ∀ P, c P ≠ 0 → ∃ γ : Γ, γ • P ∈ Kn ∪ Km := by
      intro P hP
      by_cases h0 : χ n P = 0
      · have h1 : χ m P ≠ 0 := by
          intro h1; apply hP; simp [hc, h0, h1]
        obtain ⟨γ, hγ⟩ := hKms P h1
        exact ⟨γ, Or.inr hγ⟩
      · obtain ⟨γ, hγ⟩ := hKns P h0
        exact ⟨γ, Or.inl hγ⟩
    have hda : ((a n - a m : X.core Γ) : X F → ℂ) = fun P => (c P : ℂ) * u P := by
      funext P
      simp only [Submodule.coe_sub, Pi.sub_apply, ha_apply, hc]
      push_cast
      ring
    obtain ⟨hint, hims⟩ := X.ims hcs
      (fun γ P => by simp only [hc, hχinv n γ P, hχinv m γ P]) (hKn.union hKm) hcK hu hinv
      (a n - a m) hda
    have hd2 : Integrable (fun P => η P * ‖((a n - a m : X.core Γ) : X F → ℂ) P‖ ^ 2)
        (X.vol F) := (X.l2Rep_of_mem_core (a n - a m).2).integrable_sq
    rw [h1, X.norm_sq_kappa, hims, ← integral_add hd2 hint]
    have i1 : Integrable (fun P => (1 - χ n P) * (η P * G₀ P) + (1 - χ m P) * (η P * G₀ P))
        (X.vol F) := (hσint n).add (hσint m)
    have i2 : Integrable (fun P => 2 * ε n * (η P * ‖u P‖ ^ 2) + 2 * ε m * (η P * ‖u P‖ ^ 2))
        (X.vol F) := (hIu.const_mul _).add (hIu.const_mul _)
    have hR : Integrable (fun P => (1 - χ n P) * (η P * G₀ P) + (1 - χ m P) * (η P * G₀ P) +
        (2 * ε n * (η P * ‖u P‖ ^ 2) + 2 * ε m * (η P * ‖u P‖ ^ 2))) (X.vol F) := i1.add i2
    have hRval : ∫ P, ((1 - χ n P) * (η P * G₀ P) + (1 - χ m P) * (η P * G₀ P) +
        (2 * ε n * (η P * ‖u P‖ ^ 2) + 2 * ε m * (η P * ‖u P‖ ^ 2))) ∂X.vol F = τ n + τ m := by
      rw [integral_add i1 i2,
        integral_add (hσint n) (hσint m), integral_add (hIu.const_mul _) (hIu.const_mul _),
        integral_const_mul, integral_const_mul]
      simp only [hτdef, hσdef, hU]
      ring
    rw [← hRval]
    refine integral_mono (hd2.add hint) hR fun P => ?_
    have hc2 : c P ^ 2 ≤ (1 - χ n P) + (1 - χ m P) := by
      simp only [hc]
      nlinarith [hχ0 n P, hχ1 n P, hχ0 m P, hχ1 m P,
        mul_nonneg (sub_nonneg.2 (hχ1 n P)) (sub_nonneg.2 (hχ1 m P)),
        mul_nonneg (hχ0 n P) (sub_nonneg.2 (hχ1 n P)),
        mul_nonneg (hχ0 m P) (sub_nonneg.2 (hχ1 m P))]
    have hg2 : X.grad2 (fun P => (c P : ℂ)) P ≤ 2 * ε n + 2 * ε m := by
      rw [hcfun]
      have := X.grad2_sub_le (hχs n) (hχs m) P
      linarith [hgrad n P, hgrad m P]
    have hg0 := X.grad2_nonneg (fun P => (c P : ℂ)) P
    have hnd : ‖((a n - a m : X.core Γ) : X F → ℂ) P‖ ^ 2 = c P ^ 2 * ‖u P‖ ^ 2 := by
      rw [hda, norm_mul, Complex.norm_real, mul_pow, Real.norm_eq_abs, sq_abs]
    have k1 : c P ^ 2 * ‖u P‖ ^ 2 + c P ^ 2 * (conj (u P) * X.lap u P).re ≤
        ((1 - χ n P) + (1 - χ m P)) * G₀ P := by
      have e1 : c P ^ 2 * (‖u P‖ ^ 2 + (conj (u P) * X.lap u P).re) ≤ c P ^ 2 * G₀ P :=
        mul_le_mul_of_nonneg_left (by simp only [hG₀]; linarith [hRe P]) (sq_nonneg _)
      have e2 : c P ^ 2 * G₀ P ≤ ((1 - χ n P) + (1 - χ m P)) * G₀ P :=
        mul_le_mul_of_nonneg_right hc2 (hG₀0 P)
      linarith
    have k2 : ‖u P‖ ^ 2 * X.grad2 (fun P => (c P : ℂ)) P ≤ ‖u P‖ ^ 2 * (2 * ε n + 2 * ε m) :=
      mul_le_mul_of_nonneg_left hg2 (sq_nonneg _)
    have k3 := mul_le_mul_of_nonneg_left (add_le_add k1 k2) (hη0 P)
    simp only [hnd]
    calc η P * (c P ^ 2 * ‖u P‖ ^ 2) + η P * (c P ^ 2 * (conj (u P) * X.lap u P).re +
          ‖u P‖ ^ 2 * X.grad2 (fun P => (c P : ℂ)) P)
        = η P * (c P ^ 2 * ‖u P‖ ^ 2 + c P ^ 2 * (conj (u P) * X.lap u P).re +
          ‖u P‖ ^ 2 * X.grad2 (fun P => (c P : ℂ)) P) := by ring
      _ ≤ η P * (((1 - χ n P) + (1 - χ m P)) * G₀ P + ‖u P‖ ^ 2 * (2 * ε n + 2 * ε m)) := k3
      _ = _ := by ring
  have hcauchy : CauchySeq x := by
    rw [Metric.cauchySeq_iff]
    intro δ hδ
    have h1 : ∀ᶠ n in atTop, τ n < δ ^ 2 / 2 := hτ.eventually (gt_mem_nhds (by positivity))
    obtain ⟨N, hN⟩ := eventually_atTop.1 h1
    refine ⟨N, fun m hm n hn => ?_⟩
    rw [dist_eq_norm]
    have h2 := hbound m n
    have h3 : ‖x m - x n‖ ^ 2 < δ ^ 2 := by linarith [hN m hm, hN n hn]
    exact lt_of_pow_lt_pow_left₀ 2 hδ.le h3
  obtain ⟨x', hx'⟩ := cauchySeq_tendsto_of_complete hcauchy
  have hj : (X.symmOp Γ).j x' = X.toL2 Γ u hu2 := by
    have h1 : Tendsto (fun n => (X.symmOp Γ).j (x n)) atTop (𝓝 ((X.symmOp Γ).j x')) :=
      ((X.symmOp Γ).j.continuous.tendsto _).comp hx'
    have h2 : Tendsto (fun n => (X.symmOp Γ).j (x n)) atTop (𝓝 (X.toL2 Γ u hu2)) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      have h3 : ∀ n, ‖(X.symmOp Γ).j (x n) - X.toL2 Γ u hu2‖ ^ 2 ≤ σ n := by
        intro n
        have e1 : (X.symmOp Γ).j (x n) = X.toL2 Γ (a n) (X.l2Rep_of_mem_core (a n).2) := by
          simp only [hx]
          rw [SymmOp.j_kappa, X.incl_coreD, X.coreL2_apply]
        rw [e1, ← X.toL2_sub, X.norm_sq_toL2]
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun P => by positivity)
          (hσint n) (Filter.Eventually.of_forall fun P => ?_)
        have e2 : ‖((a n : X.core Γ) : X F → ℂ) P - u P‖ ^ 2 = (1 - χ n P) ^ 2 * ‖u P‖ ^ 2 := by
          have : ((a n : X.core Γ) : X F → ℂ) P - u P = (((χ n P - 1 : ℝ)) : ℂ) * u P := by
            rw [ha_apply]; push_cast; ring
          rw [this, norm_mul, Complex.norm_real, mul_pow, Real.norm_eq_abs, sq_abs]
          ring
        have e3 : (1 - χ n P) ^ 2 ≤ 1 - χ n P := by nlinarith [hχ0 n P, hχ1 n P]
        have e4 : ‖u P‖ ^ 2 ≤ G₀ P := by
          simp only [hG₀]
          nlinarith [sq_nonneg ‖u P‖, sq_nonneg ‖f P‖, norm_nonneg lam,
            mul_nonneg (norm_nonneg lam) (sq_nonneg ‖u P‖)]
        show η P * ‖((a n : X.core Γ) : X F → ℂ) P - u P‖ ^ 2 ≤ (1 - χ n P) * (η P * G₀ P)
        rw [e2]
        have e5 : (1 - χ n P) ^ 2 * ‖u P‖ ^ 2 ≤ (1 - χ n P) * G₀ P :=
          mul_le_mul e3 e4 (sq_nonneg _) (sub_nonneg.2 (hχ1 n P))
        nlinarith [hη0 P]
      have h4 : Tendsto (fun n => Real.sqrt (σ n)) atTop (𝓝 0) := by
        have := (Real.continuous_sqrt.tendsto 0).comp hσ
        rw [Real.sqrt_zero] at this
        exact this
      refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) h4
      rw [← Real.sqrt_sq (norm_nonneg ((X.symmOp Γ).j (x n) - X.toL2 Γ u hu2))]
      exact Real.sqrt_le_sqrt (h3 n)
    exact tendsto_nhds_unique h1 h2
  refine ⟨x', hj, ?_⟩
  refine (X.energy Γ).isWeakSol_of_dense (X.symmOp Γ).dense_range_kappa_set ?_
  rintro _ ⟨c, rfl⟩
  obtain ⟨b, rfl⟩ := X.coreD_surjective c
  show (X.symmOp Γ).energySpace.form ((X.symmOp Γ).kappa (X.coreD Γ b)) x' -
      lam * ⟪(X.symmOp Γ).energySpace.j ((X.symmOp Γ).kappa (X.coreD Γ b)),
        (X.symmOp Γ).energySpace.j x'⟫_ℂ =
      ⟪(X.symmOp Γ).energySpace.j ((X.symmOp Γ).kappa (X.coreD Γ b)), X.toL2 Γ f hf2⟫_ℂ
  unfold ArtinKP.CAbs.EnergySpace.form
  rw [SymmOp.energySpace_j, SymmOp.j_kappa, X.incl_coreD, hj]
  have h1 : ⟪(X.symmOp Γ).kappa (X.coreD Γ b), x'⟫_ℂ =
      ⟪X.coreL2 Γ b + X.coreL2 Γ (X.coreLap Γ b), X.toL2 Γ u hu2⟫_ℂ := by
    rw [← inner_conj_symm, SymmOp.inner_kappa_right, hj, X.incl_coreD, X.op_coreD,
      inner_conj_symm]
  have h2 : ⟪X.coreL2 Γ (X.coreLap Γ b), X.toL2 Γ u hu2⟫_ℂ =
      lam * ⟪X.coreL2 Γ b, X.toL2 Γ u hu2⟫_ℂ + ⟪X.coreL2 Γ b, X.toL2 Γ f hf2⟫_ℂ := by
    rw [X.inner_coreLap_eq b hu hinv _ (X.lift_toL2 hu2), ← inner_smul_right,
      ← inner_add_right, ← X.toL2_const_mul hu2 lam, ← X.toL2_add (hu2.const_mul lam) hf2,
      X.coreL2_apply, X.inner_toL2_toL2]
    simp_rw [heq]
  rw [h1, inner_add_left, h2]
  ring

/-! ### Testing against the core -/

end

end ArtinKP.X
end

theorem solution.{u_1} : type_of% @ArtinKP.X.X.exists_isWeakSol_of_lap_eq_of_cutoff_oai.{u_1} := @ArtinKP.X.X.exists_isWeakSol_of_lap_eq_of_cutoff_oai.{u_1}
