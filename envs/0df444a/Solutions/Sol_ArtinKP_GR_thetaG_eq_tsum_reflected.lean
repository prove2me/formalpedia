-- Prove2me | solution 1 for ArtinKP.GR.thetaG_eq_tsum_reflected
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T10:08:45.658982+00:00
-- url     : https://prove2.me/submissions/ac122411-2ed4-49c2-a718-98e5871d85be

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
import Theorems.Thm_ArtinKP_G2a_ThetaM_tau
import Theorems.Thm_ArtinKP_GK_xi_wSec_phiB_eq_jdef
import Theorems.Thm_ArtinKP_GR_ThetaM_flip

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
-- module Solutions.Artin.KP.S_Basic
attribute [-instance] _root_.ArtinKP.N2.levelGroup_finiteIndex _root_.ArtinKP.S.GSection.instAdd _root_.ArtinKP.S.GSection.instAddCommMonoid _root_.ArtinKP.S.GSection.instCoeFunForallComplexForallForall _root_.ArtinKP.S.GSection.instSMulComplex _root_.ArtinKP.S.GSection.instZero _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-!
# WP-S, part 1: `S_f`-adic smallness, norms, the pairing `⟨·,·⟩` on `F`, rows of `SL₂(R)`

* `Small 𝔪 N x`: `v(x) ≤ exp(-N)` at every `v ∣ 𝔪` (`N : ℤ`; `N < 0` means "bounded").
* `absS 𝔪 x = |x|_{S_f}`, `normS 𝔪 c d = ‖(c,d)‖ = ∏_{v ∣ 𝔪} max(|c|_v, |d|_v)`.
* `brk ι P 𝔪 x y = ⟨x, y⟩ = ι (x, y)_S` for `x, y ≠ 0`, and `1` if `x = 0` or `y = 0`.
  With WP-A's orientation `⟨c, d⟩ = (d/c)(c/d)⁻¹` on coprime elements of `R` (`brk_reciprocity`).
* `sig`: Kubota's `σ_S` evaluated on a pair and a matrix, through `ι`.
* `Row 𝔪`: primitive pairs of `R = SInt 𝔪`; right action of `SL₂(R)`; scaling by `Rˣ`;
  `kappaRow` and its transformation laws (`kappaRow_act` is Lemma A5 on rows).
-/

set_option autoImplicit false

open NumberField IsDedekindDomain ArtinPrimitiveRoots

noncomputable section

namespace ArtinKP.S

open ArtinKP.A

variable {F : Type*} [Field F] [NumberField F]

/-! ### Smallness at the places of `S_f` -/

/-! ### Absolute values at `S_f` -/

/-! ### The pairing `⟨x, y⟩ = ι (x, y)_S` on `F` -/

section brk

variable {ι : F →+* ℂ} {P : CubicPkg F} {𝔪 : Ideal (𝓞 F)}

theorem brk_div_right (x : F) {y y' : F} (hy : y ≠ 0) (hy' : y' ≠ 0) :
    brk ι P 𝔪 x (y / y') = brk ι P 𝔪 x y * (brk ι P 𝔪 x y')⁻¹ := by
  rw [div_eq_mul_inv, brk_mul_right x hy (inv_ne_zero hy'), brk_inv_right]

end brk

/-! ### Kubota's `σ_S` on a pair and a matrix -/

/-! ### Primitive rows -/

/-! ### The Kubota symbol on rows -/

/-! ### The matrices `w` and `n(t)` -/

end ArtinKP.S
end
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
-- module Solutions.Artin.KP.S_Jacquet
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-!
# WP-S, part 7: finite Jacquet functionals

`F_{S_f}/𝔩` is the discrete countable group `F/𝔩_M`, `𝔩_M = {x : Small M x}` (strong
approximation is not needed to *define* the functional).  For `f : F → ℂ` invariant under `𝔩_M`:

`jac ψ M f ν = vol(𝔩_M) · Σ_{u ∈ F/𝔩_M} f(u) · conj ψ(ν u)`   (`= ∫_{F_{S_f}} f(u) conj ψ(νu) du`),

`J_Φ(c; ν, s) = jac ψ M (u ↦ Φ_s(c, cu)) ν`, `λ_η(Φ_s; ν) = |η|^s J_Φ(η; ν, s)` (`lam`).

* `lam_bigCell`: `λ_η(Φ^{big}_{η,L}; ν) = vol(𝔩) conj ψ(ν t₀)` for `ν ∈ 𝔩^⊥`.
* `jac_eq_zero`: the functional vanishes when `ψ(ν ·)` is non-trivial on a lattice of periods.
* `norm_lam_le`: the uniform bound `|c|^σ |J_Φ(c; ν, s)| ≤ B·K_σ` (MATH2 §0.2), `K_σ = vol·Σ_u
  ∏_v max(1,|u|_v)^{-σ}`.
* `kir`, `xi_bound`: the bound for the Kirillov function (MATH2 §6.3 (K2), (K3)).
-/

set_option autoImplicit false

open NumberField IsDedekindDomain ArtinPrimitiveRoots

noncomputable section

namespace ArtinKP.S

open ArtinKP.A

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}

theorem out_spec {M : ℤ} (x : F) :
    ∃ h : F, Small 𝔪 M h ∧ (QuotientAddGroup.mk x : F ⧸ lat 𝔪 M).out = x + h := by
  obtain ⟨h, hh⟩ := QuotientAddGroup.mk_out_eq_add (lat 𝔪 M) x
  exact ⟨h.1, h.2, hh⟩

section jac

variable (ψ : SfChar 𝔪) {M : ℤ} {f : F → ℂ} {ν : F}

/-- The summand of `jac` on the class of `x`, for periodic data. -/
theorem jac_term (hf : ∀ x h : F, Small 𝔪 M h → f (x + h) = f x)
    (hψ : ∀ h : F, Small 𝔪 M h → ψ (ν * h) = 1) (x : F) :
    f (QuotientAddGroup.mk x : F ⧸ lat 𝔪 M).out
        * (starRingEnd ℂ) (ψ (ν * (QuotientAddGroup.mk x : F ⧸ lat 𝔪 M).out))
      = f x * (starRingEnd ℂ) (ψ (ν * x)) := by
  obtain ⟨h, hh, he⟩ := out_spec (𝔪 := 𝔪) (M := M) x
  rw [he, hf x h hh, mul_add, ψ.map_add, hψ h hh, mul_one]

end jac

/-- Translation: `∫ f(u + t) conj ψ(νu) du = ψ(νt) ∫ f(u) conj ψ(νu) du`
(MATH2 (K4): `𝒦_{n(t)Φ}(β) = ψ(βt) 𝒦_Φ(β)`). -/
theorem jac_shift (ψ : SfChar 𝔪) {M : ℤ} {f : F → ℂ} {ν : F}
    (hf : ∀ x h : F, Small 𝔪 M h → f (x + h) = f x)
    (hψ : ∀ h : F, Small 𝔪 M h → ψ (ν * h) = 1) (t : F) :
    jac ψ M (fun u => f (u + t)) ν = ψ (ν * t) * jac ψ M f ν := by
  set g : F ⧸ lat 𝔪 M → ℂ := fun u => f u.out * (starRingEnd ℂ) (ψ (ν * u.out)) with hg
  have hft : ∀ x h : F, Small 𝔪 M h → f (x + h + t) = f (x + t) := fun x h hh => by
    rw [add_right_comm, hf _ h hh]
  have hunit : ψ (ν * t) * (starRingEnd ℂ) (ψ (ν * t)) = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, ψ.norm_one]
    simp
  have key : ∀ u : F ⧸ lat 𝔪 M, f (u.out + t) * (starRingEnd ℂ) (ψ (ν * u.out))
      = ψ (ν * t) * g (u + QuotientAddGroup.mk t) := by
    intro u
    induction u using QuotientAddGroup.induction_on with
    | H x =>
      rw [← QuotientAddGroup.mk_add, hg]
      simp only
      rw [jac_term ψ (f := fun u => f (u + t)) hft hψ, jac_term ψ hf hψ, mul_add, ψ.map_add,
        map_mul]
      linear_combination (-(f (x + t) * (starRingEnd ℂ) (ψ (ν * x)))) * hunit
  rw [jac, jac]
  simp only [key]
  have h1 : ∑' u : F ⧸ lat 𝔪 M, g (u + QuotientAddGroup.mk t) = ∑' u, g u :=
    (Equiv.addRight (QuotientAddGroup.mk t : F ⧸ lat 𝔪 M)).tsum_eq g
  rw [tsum_mul_left, h1]
  ring

/-! ### The Kirillov function -/

end ArtinKP.S
end
end

section
-- module Solutions.Artin.KP.B_FourArch
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
attribute [-simp] _root_.ArtinKP.B.coe_latREquiv _root_.ArtinKP.B.embR_apply
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

theorem emb_mul (a b : F) : emb (a * b) = emb a * emb b := by
  ext w
  simp

/-! ### The `S_f`-character -/

theorem psiS_apply [IsTotallyComplex F] (h𝔪 : 𝔪 ≠ ⊥) (x : F) :
    psiS h𝔪 x = sAddChar 𝔪 x * conj (eInf (emb x)) := rfl

/-- `e_∞(x) = sAddChar(x) · conj ψ_{S_f}(x)` for `x ∈ F` (MATH2 §0.2). -/
theorem eInf_emb_eq [IsTotallyComplex F] (h𝔪 : 𝔪 ≠ ⊥) (x : F) :
    eInf (emb x) = sAddChar 𝔪 x * conj (psiS h𝔪 x) := by
  have h1 : sAddChar 𝔪 x * conj (sAddChar 𝔪 x) = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_sAddChar h𝔪]
    simp
  rw [psiS_apply, map_mul, Complex.conj_conj, ← mul_assoc, h1, one_mul]

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
-- module Solutions.Artin.KP.S2_Kubota
attribute [-instance] _root_.ArtinKP.B.instCountableSInt _root_.ArtinKP.N2.levelGroup_finiteIndex _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
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
-- module Solutions.Artin.KP.S2_Translate
attribute [-instance] _root_.ArtinKP.B.instCountableSInt _root_.ArtinKP.N2.levelGroup_finiteIndex _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
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

theorem translateF_apply (hG : Good 𝔪) (α β γ δ : F) (det : α * δ - β * γ = 1)
    (Φ : GSection ι P 𝔪) (s : ℂ) (c d : F) :
    translateF hG α β γ δ det Φ s c d
      = (sig ι P 𝔪 c d α β γ δ)⁻¹ * Φ s (c * α + d * γ) (c * β + d * δ) := rfl

theorem translate_apply (hG : Good 𝔪) (σ : Matrix.SpecialLinearGroup (Fin 2) (SInt 𝔪))
    (Φ : GSection ι P 𝔪) (s : ℂ) (c d : F) :
    translate hG σ Φ s c d = kappa ι 𝔪 σ *
      ((sig ι P 𝔪 c d ((σ.1 0 0 : SInt 𝔪) : F) ((σ.1 0 1 : SInt 𝔪) : F)
        ((σ.1 1 0 : SInt 𝔪) : F) ((σ.1 1 1 : SInt 𝔪) : F))⁻¹ *
      Φ s (c * ((σ.1 0 0 : SInt 𝔪) : F) + d * ((σ.1 1 0 : SInt 𝔪) : F))
        (c * ((σ.1 0 1 : SInt 𝔪) : F) + d * ((σ.1 1 1 : SInt 𝔪) : F))) := rfl

end GSection

end ArtinKP.S2
end
end

section
-- module Solutions.Artin.KP.G1_Cusp
attribute [-instance] _root_.ArtinKP.B.instCountableSInt _root_.ArtinKP.N2.levelGroup_finiteIndex _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
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

theorem cpow_cusp {x : ℝ} (hx : 0 < x) (s : ℂ) :
    (x : ℂ) ^ (1 * s + -2) * (((x⁻¹ ^ 2 : ℝ) : ℂ) ^ (2 * s - 1) * ((x⁻¹ : ℝ) : ℂ) ^ (-(3 * s)))
      = 1 := by
  have h1 : 0 < x⁻¹ := inv_pos.mpr hx
  rw [ofReal_cpow_eq_exp hx, ofReal_cpow_eq_exp (pow_pos h1 2), ofReal_cpow_eq_exp h1,
    ← Complex.exp_add, ← Complex.exp_add, Real.log_pow, Real.log_inv]
  push_cast
  ring_nf
  exact Complex.exp_zero

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

/-- **(N)** `Ã(β) n(t) Φ = n(βt) Ã(β) Φ`. -/
theorem torusT_nT (hG : Good 𝔪) (Φ : GSection ι P 𝔪) {β : F} (hβ : β ≠ 0) (t : F) :
    (Φ.nT hG t).torusT hG β hβ = (Φ.torusT hG β hβ).nT hG (β * t) := by
  ext s c d
  rw [GSection.torusT_apply, GSection.nT_apply, GSection.nT_apply, GSection.torusT_apply]
  have htf : tf ι P 𝔪 β c (d + c * (β * t)) = tf ι P 𝔪 β c d := by
    by_cases hc : c = 0
    · rw [hc, zero_mul, add_zero]
    · rw [tf, if_neg hc, tf, if_neg hc]
  rw [htf, show β * d + β ^ 2 * c * t = β * (d + c * (β * t)) by ring]

/-! ### (2.1): the cusp change -/

/-- The symbol identity of (2.1). -/
theorem sig_cusp {a b c d : F} (det : a * d - b * c = 1) (hc : c ≠ 0) (x y : F)
    (hxy : x ≠ 0 ∨ y ≠ 0) :
    (sig ι P 𝔪 x y a b c d)⁻¹
      = tf ι P 𝔪 (c⁻¹ ^ 2) x (y + x * (a / c))
        * brk ι P 𝔪 ((c⁻¹ ^ 2) ^ 2 * x) (c⁻¹ ^ 2 * (y + x * (a / c))) := by
  set T : F := x * a + y * c with hT
  have eT : c⁻¹ ^ 2 * (y + x * (a / c)) = c⁻¹ ^ 3 * T := by rw [hT]; field_simp; ring
  have e2 : x * b + y * d = (T * d - x) / c := by
    rw [hT]; field_simp; linear_combination -x * det
  rw [eT, sig, ← hT, e2, Xs_of_ne _ hc]
  have f1 := brk_facts (ι := ι) (P := P) (𝔪 := 𝔪) x c
  have f2 := brk_facts (ι := ι) (P := P) (𝔪 := 𝔪) x T
  have f3 := brk_facts (ι := ι) (P := P) (𝔪 := 𝔪) c T
  have f4 := brk_facts (ι := ι) (P := P) (𝔪 := 𝔪) y c
  by_cases hx : x = 0
  · have hy : y ≠ 0 := hxy.resolve_left (not_not.mpr hx)
    have hT' : T = y * c := by rw [hT, hx]; ring
    have hT0 : T ≠ 0 := by rw [hT']; exact mul_ne_zero hy hc
    rw [Xs_of_ne _ hT0, hx, Xs_zero, hT']
    simp [tf, hy, hc, brk_mul_left, brk_mul_right, brk_inv_left, brk_inv_right, pow_succ]
    grind
  by_cases hT0 : T = 0
  · have hX : Xs T ((T * d - x) / c) = -(x / c) := by
      rw [hT0, Xs_zero]; ring
    rw [hX, Xs_of_ne _ hx, hT0]
    simp [tf, hx, hc, brk_mul_left, brk_mul_right, brk_div_left, brk_div_right, brk_inv_left,
      brk_inv_right, pow_succ, neg_div]
    grind
  · rw [Xs_of_ne _ hT0, Xs_of_ne _ hx]
    simp [tf, hx, hc, hT0, brk_mul_left, brk_mul_right, brk_div_left, brk_div_right, brk_inv_left,
      brk_inv_right, pow_succ]
    grind

/-- **(2.1) on `SL₂(F)`**: `[[a,b],[c,d]]·(n(-d/c)Φ) = |c|^{s-2} n(a/c) Ã(c⁻²) (wΦ)`, `c ≠ 0`. -/
theorem translateF_nT_cusp (hG : Good 𝔪) (Φ : GSection ι P 𝔪) {a b c d : F}
    (det : a * d - b * c = 1) (hc : c ≠ 0) :
    S2.GSection.translateF hG a b c d det (Φ.nT hG (-d / c))
      = scal c hc 1 (-2)
          (((wSec hG Φ).torusT hG (c⁻¹ ^ 2) (pow_ne_zero 2 (inv_ne_zero hc))).nT hG (a / c)) := by
  ext s x y
  rw [S2.GSection.translateF_apply, GSection.nT_apply, scal_apply, GSection.nT_apply,
    GSection.torusT_apply, wSec_apply]
  by_cases h0 : x = 0 ∧ y = 0
  · obtain ⟨rfl, rfl⟩ := h0
    simp [Φ.zero]
  have hxy : x ≠ 0 ∨ y ≠ 0 := by
    by_contra h; rw [not_or, not_not, not_not] at h; exact h0 h
  set T : F := x * a + y * c with hT
  have e1 : x * b + y * d + T * (-d / c) = -(x / c) := by
    rw [hT]; field_simp; linear_combination -x * det
  have e2 : c⁻¹ ^ 2 * (y + x * (a / c)) = c⁻¹ ^ 3 * T := by rw [hT]; field_simp; ring
  have e3 : -((c⁻¹ ^ 2) ^ 2 * x) = c⁻¹ ^ 3 * -(x / c) := by field_simp
  have hsym := sig_cusp (ι := ι) (P := P) (𝔪 := 𝔪) det hc x y hxy
  rw [e1, hsym, e3]
  rw [show Φ s (c⁻¹ ^ 2 * (y + x * (a / c))) (c⁻¹ ^ 3 * -(x / c))
    = Φ s (c⁻¹ ^ 3 * T) (c⁻¹ ^ 3 * -(x / c)) by rw [e2]]
  rw [Φ.cube s c⁻¹ (inv_ne_zero hc), absS_pow, absS_inv]
  have hcp := cpow_cusp (absS_pos (𝔪 := 𝔪) hc) s
  linear_combination (-(tf ι P 𝔪 (c⁻¹ ^ 2) x (y + x * (a / c))
    * brk ι P 𝔪 ((c⁻¹ ^ 2) ^ 2 * x) (c⁻¹ ^ 2 * (y + x * (a / c))) * Φ s T (-(x / c)))) * hcp

/-- **(2.1), the cusp change at the section level** (MATH3 §2a): for `γ = [[a,b],[c,d]] ∈ SL₂(R)`
with `c ≠ 0` and `ξ = -d/c`,
`translate γ (n(ξ)Φ) = κ(γ) · |c|^{s-2} · n(a/c) · Ã(c⁻²) · (wΦ)` on all of `F²`. -/
theorem translate_nT_cusp (hG : Good 𝔪) (Φ : GSection ι P 𝔪)
    (γ : Matrix.SpecialLinearGroup (Fin 2) (SInt 𝔪)) (hc : ((γ.1 1 0 : SInt 𝔪) : F) ≠ 0) :
    S2.GSection.translate hG γ
        (Φ.nT hG (-((γ.1 1 1 : SInt 𝔪) : F) / ((γ.1 1 0 : SInt 𝔪) : F)))
      = kappa ι 𝔪 γ • scal ((γ.1 1 0 : SInt 𝔪) : F) hc 1 (-2)
          (((wSec hG Φ).torusT hG (((γ.1 1 0 : SInt 𝔪) : F)⁻¹ ^ 2)
            (pow_ne_zero 2 (inv_ne_zero hc))).nT hG
              (((γ.1 0 0 : SInt 𝔪) : F) / ((γ.1 1 0 : SInt 𝔪) : F))) := by
  rw [S2.GSection.translate, translateF_nT_cusp hG Φ (det_coe γ) hc]

end ArtinKP.G1
end
end

section
-- module Solutions.Artin.KP.G1_Lam
attribute [-instance] _root_.ArtinKP.B.instCountableSInt _root_.ArtinKP.N2.levelGroup_finiteIndex _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
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

theorem valid_nT {ψ : SfChar 𝔪} {Φ : GSection ι P 𝔪} {ν : F}
    {k : HeightOneSpectrum (𝓞 F) → ℤ} (h : Valid ψ Φ ν k) (hG : Good 𝔪) (t : F) :
    Valid ψ (Φ.nT hG t) ν k :=
  ⟨fun b hb s c d => by
    rw [GSection.nT_apply, GSection.nT_apply, show d + c * b + c * t = d + c * t + c * b by ring,
      h.1 b hb], h.2⟩

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

/-- `Lam (n(t)Φ) c ν = ψ(νt) Lam Φ c ν` (all `s`, all `c`). -/
theorem Lam_nT (ψ : SfChar 𝔪) (hG : Good 𝔪) (Φ : GSection ι P 𝔪) (t : F) (c ν : F) (s : ℂ) :
    Lam ψ hG (Φ.nT hG t) c ν s = ψ (ν * t) * Lam ψ hG Φ c ν s := by
  have h := valid_depth ψ hG Φ ν
  rw [Lam_eq_lam ψ hG _ (valid_nT h hG t), Lam_eq_lam ψ hG _ h, lam, lam]
  have hfun : (fun u => (Φ.nT hG t) s c (c * u)) = fun u => (fun u => Φ s c (c * u)) (u + t) := by
    funext u
    simp only [GSection.nT_apply, mul_add]
  rw [hfun, jac_shift ψ (f := fun u => Φ s c (c * u))
    (fun x b hb => by
      have := h.1 b hb s c (c * x)
      simpa [mul_add] using this)
    (fun b hb => h.2 b hb) t]
  ring

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

theorem torusT_smulFun (hG : Good 𝔪) (Φ : GSection ι P 𝔪) {β : F} (hβ : β ≠ 0) (f : ℂ → ℂ)
    (hf : Differentiable ℂ f) :
    (GSection.smulFun f hf Φ).torusT hG β hβ = GSection.smulFun f hf (Φ.torusT hG β hβ) := by
  ext s c d
  simp only [GSection.torusT_apply, GSection.smulFun_apply]
  ring

theorem torusT_smul (hG : Good 𝔪) (Φ : GSection ι P 𝔪) {β : F} (hβ : β ≠ 0) (a : ℂ) :
    (a • Φ).torusT hG β hβ = a • Φ.torusT hG β hβ :=
  torusT_smulFun hG Φ hβ _ _

/-! ### The Kirillov term -/

/-! ### The cusp change for `Lam` and for the Kirillov term -/

section cusp

variable (ψ : SfChar 𝔪) (hG : Good 𝔪) (Φ : GSection ι P 𝔪)
  (γ : Matrix.SpecialLinearGroup (Fin 2) (SInt 𝔪)) (hc : ((γ.1 1 0 : SInt 𝔪) : F) ≠ 0)

include hc

/-- **(2.2) as an identity of sections**: `Ã(μ)Ψ = κ(γ)⟨μ,c⟩ · |c|^{s-2} · n(μa/c) Ã(μ/c²) (wΦ)`. -/
theorem cusp_torusT {μ : F} (hμ : μ ≠ 0) :
    (S2.GSection.translate hG γ
        (Φ.nT hG (-((γ.1 1 1 : SInt 𝔪) : F) / ((γ.1 1 0 : SInt 𝔪) : F)))).torusT hG μ hμ
      = (kappa ι 𝔪 γ * brk ι P 𝔪 μ ((γ.1 1 0 : SInt 𝔪) : F)) •
          scal ((γ.1 1 0 : SInt 𝔪) : F) hc 1 (-2)
            (((wSec hG Φ).torusT hG (μ / ((γ.1 1 0 : SInt 𝔪) : F) ^ 2)
              (div_ne_zero hμ (pow_ne_zero 2 hc))).nT hG
                (μ * (((γ.1 0 0 : SInt 𝔪) : F) / ((γ.1 1 0 : SInt 𝔪) : F)))) := by
  set c : F := ((γ.1 1 0 : SInt 𝔪) : F) with hcdef
  have hci : c⁻¹ ^ 2 ≠ 0 := pow_ne_zero 2 (inv_ne_zero hc)
  rw [translate_nT_cusp hG Φ γ hc, torusT_smul, scal, torusT_smulFun, torusT_nT,
    torusT_torusT hG (wSec hG Φ) hμ hci]
  have hsym : brk ι P 𝔪 μ (c⁻¹ ^ 2) = brk ι P 𝔪 μ c := by
    have f1 := brk_facts (ι := ι) (P := P) (𝔪 := 𝔪) μ c
    simp [hc, hμ, brk_mul_right, brk_inv_right, pow_succ]
    grind
  have e : μ * c⁻¹ ^ 2 = μ / c ^ 2 := by field_simp
  ext s x y
  simp only [GSection.smul_apply, GSection.smulFun_apply, scal_apply, GSection.nT_apply, hsym]
  simp only [e]
  ring

end cusp

/-! ### The normalized term `ξ^η = |β|^{1/3} Kt(·, 4/3)` -/

theorem absS_cusp {μ c : F} (hμ : μ ≠ 0) (hc : c ≠ 0) :
    ((absS 𝔪 μ ^ (1 / 3 : ℝ) : ℝ) : ℂ) * ((absS 𝔪 c : ℝ) : ℂ) ^ ((4 / 3 : ℂ) - 2)
      = ((absS 𝔪 (μ / c ^ 2) ^ (1 / 3 : ℝ) : ℝ) : ℂ) := by
  have hc0 := absS_pos (𝔪 := 𝔪) hc
  have hμ0 := absS_pos (𝔪 := 𝔪) hμ
  have e : ((absS 𝔪 c : ℝ) : ℂ) ^ ((4 / 3 : ℂ) - 2) = ((absS 𝔪 c ^ (-(2 / 3) : ℝ) : ℝ) : ℂ) := by
    rw [Complex.ofReal_cpow hc0.le]
    congr 1
    push_cast
    ring
  rw [e, ← Complex.ofReal_mul]
  congr 1
  rw [show μ / c ^ 2 = μ * (c ^ 2)⁻¹ from div_eq_mul_inv _ _, absS_mul, absS_inv, absS_pow, Real.mul_rpow hμ0.le (by positivity),
    Real.inv_rpow (by positivity), ← Real.rpow_natCast, ← Real.rpow_mul hc0.le,
    ← Real.rpow_neg hc0.le]
  norm_num

end ArtinKP.G1
end
end

section
-- module Solutions.Artin.KP.G1_FI
attribute [-instance] _root_.ArtinKP.B.instCountableSInt _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-!
# WP-G1, part 5: Lemma FI — finite Fourier inversion on the dual lattices

For an `S_f`-character `ψ` with bounded dual lattices (`HasDual ψ d₀`; for `ψ_{S_f}` this is
`psiS_dual`), `A_M = {β : ψ(β 𝔩_M) = 1}`:

* `sum_char`: orthogonality.  For `β ∈ A_M` and `J ≤ M`,
  `Σ_{t ∈ 𝔩_J/𝔩_M} ψ(βt) = [𝔩_J : 𝔩_M]·1[β ∈ A_J]`.
* `exists_fourier` — **Lemma FI** (MATH3 §4.4): every function on `A_M` invariant under
  translation by `A_J` (`J ≤ M`) is a finite trigonometric polynomial
  `β ↦ Σ_{t ∈ T} ϕ(t) ψ(βt)` with frequencies `T ⊂ 𝔩_J`.
* `exists_fourier_indicator`: the indicator of a coset `β₁ + 𝔩_k` (any depth function `k`),
  restricted to `A_M` — the form used for (G2).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

open scoped ComplexConjugate
open NumberField IsDedekindDomain ArtinPrimitiveRoots

noncomputable section

namespace ArtinKP.G1

open ArtinKP.A ArtinKP.S ArtinKP.S2

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}

theorem SfChar.mul_conj_self (ψ : SfChar 𝔪) (x : F) : ψ x * conj (ψ x) = 1 := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, ψ.norm_one]
  simp

end ArtinKP.G1
end
end

section
-- module Solutions.Artin.T12.L3X_Meas
attribute [-instance] _root_.ArtinKP.B.instCountableSInt
/-! # L3X_Meas: sheet measures on the model `SModel 𝔪 k` of `F_S^× / U`

* `lnorm y = Σ_w log|y_w|_w + log |y_f|_{S_f}` (the log of the `S`-norm).
* For a place `w₀`, the base space `SFin × (ℝ^{W∖w₀} × (ℝ/2πℤ)^W)` carries counting ⊗ Lebesgue ⊗
  Haar, and `slice w₀ a` sends it onto the sheet `{lnorm = a}`, solving for the `w₀` log-coordinate.
* `shMeasure w₀ a` is the push-forward: the sheet measure on `X_{e^a}`.
* Translation by `d` maps `shMeasure a` to `shMeasure (a + lnorm d)`; negation maps `shMeasure a` to
  `shMeasure (-a)`; moving the `w₀` coordinate by `t` moves the slice from `a` to `a + t`.
-/

namespace ArtinPrimitiveRoots.L3X

open NumberField MeasureTheory

set_option linter.unusedSectionVars false

open scoped Classical

noncomputable section

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)} {k : ℕ}

/-! ### The finite norm -/

theorem SFin.norm_mk (x : Fˣ) :
    (SFin.mk 𝔪 k x).norm = ∏ᶠ v ∈ placesOf 𝔪, NumberField.HeightOneSpectrum.adicAbv F v (x : F) :=
  rfl


theorem SFin.norm_mk_eq_prod (h𝔪 : 𝔪 ≠ ⊥) (x : Fˣ) :
    (SFin.mk 𝔪 k x).norm =
      ∏ v ∈ (finite_placesOf h𝔪).toFinset, NumberField.HeightOneSpectrum.adicAbv F v (x : F) := by
  rw [SFin.norm_mk, finprod_mem_eq_finite_toFinset_prod _ (finite_placesOf h𝔪)]

theorem SFin.norm_mk_pos (h𝔪 : 𝔪 ≠ ⊥) (x : Fˣ) : 0 < (SFin.mk 𝔪 k x).norm := by
  rw [SFin.norm_mk_eq_prod h𝔪]
  exact Finset.prod_pos fun v _ => (AbsoluteValue.pos_iff _).2 x.ne_zero

/-! ### `lnorm` -/

/-! ### Slices -/


/-! ### Measure preservation -/

end

end ArtinPrimitiveRoots.L3X
end

section
-- module Solutions.Artin.T12.L3P_Val
attribute [-instance] _root_.ArtinKP.B.instCountableSInt _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-!
# L3P_Val: valuations as counts of principal fractional ideals

For `x ≠ 0` in a number field, `v.valuation x = exp (−count_v (x))`, where
`count_v (x) = FractionalIdeal.count F v (spanSingleton x)`. Membership in a nonzero fractional
ideal is a comparison of counts.
-/

namespace ArtinPrimitiveRoots.L3P

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum FractionalIdeal
open scoped nonZeroDivisors Classical

set_option linter.unusedSectionVars false

variable {F : Type*} [Field F] [NumberField F]

/-! ### The places of `S` -/

variable {𝔪 : Ideal (𝓞 F)}

variable [Fintype (SP 𝔪)]

omit [Fintype (SP 𝔪)] in
theorem one_lt_qS (v : SP 𝔪) : 1 < qS v := by
  rw [qS]
  have h0 : Ideal.absNorm v.1.asIdeal ≠ 0 := by
    rw [ne_eq, Ideal.absNorm_eq_zero_iff]; exact v.1.ne_bot
  have h1 : Ideal.absNorm v.1.asIdeal ≠ 1 := by
    rw [ne_eq, Ideal.absNorm_eq_one_iff]; exact v.1.isPrime.ne_top
  have : 2 ≤ Ideal.absNorm v.1.asIdeal := by omega
  exact_mod_cast this

theorem NN_eq_prod {S : Type*} [Fintype S] (q : S → ℝ) (hq : ∀ v, 0 < q v) (k : S → ℤ) :
    NN q k = ∏ v, q v ^ k v := by
  rw [NN, Real.exp_sum]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [lq, mul_comm, ← Real.rpow_intCast, Real.rpow_def_of_pos (hq v)]

theorem absNorm_Pk (k : SP 𝔪 → ℤ) :
    ((FractionalIdeal.absNorm ((Pk k : (FractionalIdeal (𝓞 F)⁰ F)ˣ) :
      FractionalIdeal (𝓞 F)⁰ F) : ℚ) : ℝ) = NN (qS (𝔪 := 𝔪)) k := by
  rw [coe_Pk, map_prod, NN_eq_prod qS (fun v => (one_lt_qS v).trans' one_pos)]
  push_cast
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [map_zpow₀, coeIdeal_absNorm]
  push_cast; rfl

/-- `|N m| = N 𝔟 · N(P^{val_S m})`. -/
theorem abs_norm_eq {𝔟 : Ideal (𝓞 F)} (h𝔟 : IsExterior 𝔪 𝔟) {m : SInt 𝔪}
    (hm : Ideal.span {m} = 𝔟.map (algebraMap (𝓞 F) (SInt 𝔪))) :
    ((|Algebra.norm ℚ (m : F)| : ℚ) : ℝ) = (Ideal.absNorm 𝔟 : ℝ) * NN (qS (𝔪 := 𝔪)) (valS (m : F)) := by
  rw [← absNorm_span_singleton (R := 𝓞 F), spanSingleton_eq_mul_Pk h𝔟 hm, map_mul,
    coeIdeal_absNorm, Rat.cast_mul, absNorm_Pk]
  push_cast; rfl

/-! ### Units, the different, and the trace dual -/

end ArtinPrimitiveRoots.L3P
end

section
-- module Solutions.Artin.T12.L3X_Emb
attribute [-instance] _root_.ArtinKP.B.instCountableSInt
/-! # L3X_Emb: the embedding `F^× → SModel 𝔪 k`

* `sEmb` is a homomorphism on `F^×`.
* The `v`-adic absolute value is `q_v^{-ord_v}`; the finite norm of `[x]` is `∏_{v∈S_f} q_v^{-ord_v x}`.
* The product formula: `lnorm (sEmb m) = log N 𝔟` for an `S`-integer `m` generating the exterior
  ideal `𝔟 R`; in particular `lnorm (sEmb ε) = 0` for `S`-units.
* Valuations at `S_f` descend to `SFin`.
-/

namespace ArtinPrimitiveRoots.L3X

open NumberField MeasureTheory IsDedekindDomain

set_option linter.unusedSectionVars false

open scoped Classical

noncomputable section

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)} {k : ℕ}

theorem sEmb_of_ne {x : F} (hx : x ≠ 0) :
    sEmb 𝔪 k x = (fun w => (w.mult : ℝ) * Real.log (w x),
      fun w => ((Complex.arg (w.embedding x) : ℝ) : AddCircle (2 * Real.pi)),
      SFin.mk 𝔪 k (Units.mk0 x hx)) := by
  rw [sEmb, dif_neg hx]

theorem sEmb_fin {x : F} (hx : x ≠ 0) : (sEmb 𝔪 k x).2.2 = SFin.mk 𝔪 k (Units.mk0 x hx) := by
  rw [sEmb_of_ne hx]

theorem sEmb_fst {x : F} (hx : x ≠ 0) (w : InfinitePlace F) :
    (sEmb 𝔪 k x).1 w = (w.mult : ℝ) * Real.log (w x) := by
  rw [sEmb_of_ne hx]

/-! ### Absolute values and valuations -/

theorem adicAbv_eq (v : HeightOneSpectrum (𝓞 F)) {x : F} (hx : x ≠ 0) :
    NumberField.HeightOneSpectrum.adicAbv F v x =
      (Ideal.absNorm v.asIdeal : ℝ) ^ (-L3P.ordv v x) := by
  rw [NumberField.HeightOneSpectrum.adicAbv_def, L3P.valuation_eq_exp_neg_ordv v hx,
    WithZeroMulInt.toNNReal_neg_apply _ WithZero.exp_ne_zero, WithZero.toAdd_unzero_eq_log,
    WithZero.log_exp]
  simp [zpow_neg]

theorem log_SFin_norm_mk (h𝔪 : 𝔪 ≠ ⊥) {x : F} (hx : x ≠ 0) :
    letI : Fintype (L3P.SP 𝔪) := (finite_placesOf h𝔪).fintype
    Real.log (SFin.mk 𝔪 k (Units.mk0 x hx)).norm =
      -∑ v : L3P.SP 𝔪, (L3P.ordv v.1 x : ℝ) * Real.log (Ideal.absNorm v.1.asIdeal : ℝ) := by
  letI : Fintype (L3P.SP 𝔪) := (finite_placesOf h𝔪).fintype
  rw [SFin.norm_mk_eq_prod h𝔪]
  have hq : ∀ v : HeightOneSpectrum (𝓞 F), 0 < (Ideal.absNorm v.asIdeal : ℝ) := fun v => by
    have := NumberField.HeightOneSpectrum.one_lt_absNorm v
    exact_mod_cast (by omega : 0 < Ideal.absNorm v.asIdeal)
  rw [Real.log_prod (fun v _ => by
    rw [Units.val_mk0, adicAbv_eq v hx]; exact (zpow_pos (hq v) _).ne')]
  rw [← Finset.sum_neg_distrib]
  rw [Finset.sum_subtype (finite_placesOf h𝔪).toFinset (p := fun v => v ∈ placesOf 𝔪)
    (by simp)]
  convert Finset.sum_congr rfl fun (v : L3P.SP 𝔪) _ => (show
    Real.log ((NumberField.HeightOneSpectrum.adicAbv F v.1) ((Units.mk0 x hx : Fˣ) : F)) =
      -((L3P.ordv v.1 x : ℝ) * Real.log (Ideal.absNorm v.1.asIdeal : ℝ)) by
    rw [Units.val_mk0, adicAbv_eq v.1 hx, Real.log_zpow]; push_cast; ring)

/-- The product formula on the model. -/
theorem lnorm_sEmb_gen (h𝔪 : 𝔪 ≠ ⊥) {𝔟 : Ideal (𝓞 F)} (h𝔟 : IsExterior 𝔪 𝔟) {m : SInt 𝔪}
    (hm : Ideal.span {m} = 𝔟.map (algebraMap (𝓞 F) (SInt 𝔪))) :
    lnorm (sEmb 𝔪 k (m : F)) = Real.log (Ideal.absNorm 𝔟 : ℝ) := by
  letI : Fintype (L3P.SP 𝔪) := (finite_placesOf h𝔪).fintype
  have hm0 : (m : F) ≠ 0 := L3P.ne_zero_of_span_eq h𝔟 hm
  have hN := L3P.abs_norm_eq (𝔪 := 𝔪) h𝔟 hm
  have hinf : ∑ w : InfinitePlace F, (w.mult : ℝ) * Real.log (w (m : F)) =
      Real.log (((|Algebra.norm ℚ (m : F)| : ℚ) : ℝ)) := by
    rw [← InfinitePlace.prod_eq_abs_norm, Real.log_prod (fun w _ =>
      pow_ne_zero _ ((map_ne_zero w).2 hm0))]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [Real.log_pow]
  have h𝔟0 : (0 : ℝ) < Ideal.absNorm 𝔟 := by
    have : Ideal.absNorm 𝔟 ≠ 0 := by
      rw [ne_eq, Ideal.absNorm_eq_zero_iff]; exact h𝔟.1
    exact_mod_cast Nat.pos_of_ne_zero this
  rw [lnorm, sEmb_of_ne hm0]
  simp only
  rw [hinf, log_SFin_norm_mk h𝔪 hm0, hN, L3P.NN, Real.log_mul h𝔟0.ne' (Real.exp_pos _).ne',
    Real.log_exp]
  simp only [L3P.lq, L3P.qS, L3P.valS]
  ring

end

end ArtinPrimitiveRoots.L3X
end

section
-- module Solutions.Artin.T12.L3X_Phi
attribute [-instance] _root_.ArtinKP.B.instCountableSInt
/-! # L3X_Phi: the weight `Φ = ρ · 1_B([y]) · L(y)⁻¹` and the `S`-functions

* `Lmod` is a unitary character of `SModel`, radially trivial, rotating by `ω_{m_w}`.
* `psi y = 1_B([y]) L(y)⁻¹` is `Γ`-invariant; `Phi = ρ · psi`.
* `fpF` facts: its norm, and `L(y)⁻¹ fpF(y) = ∏_w κ(|y_w|)` on `y_f = 0`.
-/

namespace ArtinPrimitiveRoots.L3X

open NumberField MeasureTheory IsDedekindDomain UniqueFactorizationMonoid

set_option linter.unusedSectionVars false

open scoped Classical

noncomputable section

variable {F : Type*} [Field F] [NumberField F] {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)} {k : ℕ}

/-! ### Angular characters -/

theorem toCircle_zsmul_add (n : ℤ) (a b : AddCircle (2 * Real.pi)) :
    ((AddCircle.toCircle (n • (a + b)) : Circle) : ℂ) =
      ((AddCircle.toCircle (n • a) : Circle) : ℂ) * ((AddCircle.toCircle (n • b) : Circle) : ℂ) := by
  rw [smul_add, AddCircle.toCircle_add]; rfl

/-! ### The weight -/

/-! ### The forward `S`-function -/

end

end ArtinPrimitiveRoots.L3X
end

section
-- module Solutions.Artin.KP.H0_Row
attribute [-instance] _root_.ArtinKP.B.instCountableSInt
/-! # WP-H0, file 3: the coordinate dictionary, part 1 — rows and frequencies

`(z, γ) ↦ γ · rowElt g z` is a bijection `RowClass 𝔪 × U_S⁶ ≃ R ∖ {0}` (`rowEquiv`), so each of the
two `∑'` of the frozen goal is a sum over `ν ∈ R ∖ 0` (`tsum_forward`, `tsum_reflected`, with the
exact summands of the goal). `rowOf ν` is the row class of `ν`: its ideal is the unique exterior
ideal `𝔷` with `𝔷R = νR` (`span_eq_map_rowOf`, `rowOf_ideal_unique`), its multiplicities are the
valuations of `ν` (`count_rowOf`), and it only depends on `ν` modulo `U_S⁶` (`rowOf_gam_mul`). -/

namespace ArtinKP.H0

open NumberField IsDedekindDomain UniqueFactorizationMonoid ArtinPrimitiveRoots

set_option linter.unusedSectionVars false

open scoped Classical

noncomputable section

variable {F : Type*} [Field F] [NumberField F] {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)} {k : ℕ}

section

variable (h𝔪 : 𝔪 ≠ ⊥) (g : AllowedGen ι 𝔪)
include h𝔪

/-- The ideal of `rowOf ν` generates `νR`. -/
theorem span_eq_map_rowOf (ν : {ν : SInt 𝔪 // ν ≠ 0}) :
    Ideal.span {(ν : SInt 𝔪)} = (rowOf h𝔪 g ν).1.1.map (algebraMap (𝓞 F) (SInt 𝔪)) := by
  have : Fintype (L3P.SP 𝔪) := (L3X.finite_placesOf h𝔪).fintype
  have h : (ν : SInt 𝔪) = rowSInt g ((rowEquiv h𝔪 g).symm ν) :=
    (congrArg Subtype.val ((rowEquiv h𝔪 g).apply_symm_apply ν)).symm
  rw [h, rowSInt_eq_par]
  exact L3P.span_unit_mul_gen g _ _

/-! ### Reindexing the two sums of the frozen goal -/

end

end

end ArtinKP.H0
end

section
-- module Solutions.Artin.KP.H0_Coord
attribute [-instance] _root_.ArtinKP.B.instCountableSInt
/-! # WP-H0, file 4: the coordinate dictionary, part 2 — `SFin`, `sEmb`, `fp`, `Fm`

* `SFin`: `SFin.mk x = 0 ↔ x ∈ SLevel` (`= F^× ∩ U_k`), equality of classes, and weak approximation
  in the form needed: every class of `SFin 𝔪 k` is the class of a nonzero `S`-integer
  (`exists_sInt_rep`); `mem_SLevel_of_sub_one_mem`: `d ≡ 1 mod 𝔪^{k+1}` lies in `SLevel 𝔪 k`.
* `fpF_sEmb_add`: `fp (sEmb ν + y)` is the indicator of `[ν] + y_f = 0` (i.e. `ν·y_f ∈ U_k`)
  times `∏_w ω_{m_w}(ν_w) ω_{m_w}(y_w) κ(|ν|_w · e^{x_w})`.
* `FmOf_sEmb_sub`: the product-form `Fm` at `sEmb ν − y`.
* rotation covariance: `fpF_add_rot`, `FmOf_sub_rot`. -/

namespace ArtinKP.H0

open NumberField IsDedekindDomain UniqueFactorizationMonoid ArtinPrimitiveRoots FractionalIdeal

set_option linter.unusedSectionVars false

open scoped Classical nonZeroDivisors

noncomputable section

variable {F : Type*} [Field F] [NumberField F] {ι : F →+* ℂ} {𝔪 : Ideal (𝓞 F)} {k : ℕ}

/-! ### `SFin` -/

/-! ### `SFinCls` -/

/-! ### Angular characters and rotations -/

variable (κ : ℝ → ℝ) (m : InfinitePlace F → ℤ)

/-! ### The two functions at `sEmb ν ± y` -/

theorem exp_sEmb_fst_add {ν : F} (hν : ν ≠ 0) (w : InfinitePlace F) (t : ℝ) :
    Real.exp ((sEmb 𝔪 k ν).1 w + t) = w ν ^ w.mult * Real.exp t := by
  rw [L3X.sEmb_fst hν, Real.exp_add, Real.exp_nat_mul, Real.exp_log (w.pos_iff.2 hν)]

/-- **The product-form `Fm` at `sEmb ν − y`.** -/
theorem FmOf_sEmb_sub (J : SFinCls 𝔪 k → SFin 𝔪 k → ℂ) (cl : SFinCls 𝔪 k) {ν : F} (hν : ν ≠ 0)
    (y : SModel 𝔪 k) :
    FmOf κ m J cl (sEmb 𝔪 k ν - y) =
      J cl (SFin.mk 𝔪 k (Units.mk0 ν hν) - y.2.2) *
        ∏ w, ((AddCircle.toCircle ((-m w) • ((Complex.arg (w.embedding ν) : ℝ) :
            AddCircle (2 * Real.pi))) : Circle) : ℂ) *
          ((AddCircle.toCircle (m w • y.2.1 w) : Circle) : ℂ) *
          (κ (w ν ^ w.mult * Real.exp (-(y.1 w))) : ℂ) := by
  unfold FmOf
  have h2 : (sEmb 𝔪 k ν - y).2.2 = SFin.mk 𝔪 k (Units.mk0 ν hν) - y.2.2 := by
    rw [Prod.snd_sub, Prod.snd_sub, L3X.sEmb_fin hν]
  have h1 : ∀ w, Real.exp ((sEmb 𝔪 k ν - y).1 w) = w ν ^ w.mult * Real.exp (-(y.1 w)) := fun w => by
    rw [← exp_sEmb_fst_add (𝔪 := 𝔪) (k := k) hν w, ← sub_eq_add_neg]; rfl
  have h3 : ∀ w, (sEmb 𝔪 k ν - y).2.1 w =
      ((Complex.arg (w.embedding ν) : ℝ) : AddCircle (2 * Real.pi)) + -(y.2.1 w) := fun w => by
    rw [L3X.sEmb_of_ne hν, ← sub_eq_add_neg]; rfl
  simp only [h1, h2, h3, L3X.toCircle_zsmul_add, neg_smul_neg]

end

end ArtinKP.H0
end

section
-- module Solutions.Artin.KP.G1_BfS
attribute [-instance] _root_.ArtinKP.B.instCountableSInt
/-!
# WP-G1, part 10: the majorant `bf` on `SFin 𝔪 k` and its summability (MATH3 §4.5)

`bf([x]) = C · ∏_{v ∈ S_f} min(1, |x|_v^{1/3}) · 1[x ∈ 𝔩_D]` is well defined on
`SFin 𝔪 k = F^×/U_k`, and `Σ_{y ∈ SFin} bf(y) |y|^σ < ∞` for every `σ > -1/3`
(`exists_bf`; the cut `H0.KPCut` wants `σ ≥ -α`, any `α < 1/3`).

Proof: `[x] ↦ (ord_v x)_{v ∈ S_f}` has fibres that inject into the finite group `𝔩_0/𝔩_{k+1}`
(`x ↦ x / t_{ord x}`, `t_n` an element with valuations `n`), and the sum over valuation vectors is a
finite product of geometric series (`summable_pi_prod`, `summable_local_weight`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

open NumberField IsDedekindDomain ArtinPrimitiveRoots

noncomputable section

namespace ArtinKP.G1

open ArtinKP.A ArtinKP.S ArtinKP.S2
open NumberField.HeightOneSpectrum

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)} {k : ℕ}

theorem mk_repS (y : SFin 𝔪 k) : SFin.mk 𝔪 k (repS y) = y := by
  show Additive.ofMul (QuotientGroup.mk (Quotient.out (Additive.toMul y))) = y
  rw [QuotientGroup.out_eq']
  rfl

theorem sFin_eq_toFinset (h𝔪 : 𝔪 ≠ ⊥) :
    (L3X.finite_placesOf h𝔪).toFinset = CubicPkg.sFin 𝔪 := by
  ext v
  rw [Set.Finite.mem_toFinset, CubicPkg.mem_sFin h𝔪]
  rfl

end ArtinKP.G1
end
end

section
-- module Solutions.Artin.KP.G1_Res
attribute [-instance] _root_.ArtinKP.B.instCountableSInt _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
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

/-- Per frequency, with an entire multiplier. -/
theorem _root_.ArtinKP.E.Theta.tau_smul_at {Φ Ψ : Sec} (g : ℂ → ℂ) (hg : Differentiable ℂ g)
    {ν : R} (hν : ν ≠ 0)
    (h : ∀ (c : R) (s : ℂ), c ≠ 0 → 2 < s.re → D.Lam Φ c ν s = g s * D.Lam Ψ c ν s) :
    T.tau Φ ν = g s₀ * T.tau Ψ ν := by
  have h1 := T.smul g hg (T.tau_spec Ψ ν hν)
  have h2 := T.congr h1 (fun s hs => by
    show g s * D.aSer Ψ ν s = D.aSer Φ ν s
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

theorem tau_smul (Φ : GSection ι P 𝔪) (a : ℂ) {ν : SInt 𝔪} (hν : ν ≠ 0) :
    T.tau (a • Φ) ν = a * T.tau Φ ν :=
  tau_congr_F hG hz6 T hν fun c s _ _ => Lam_smul _ hG Φ a c _ s

theorem tau_nT (Φ : GSection ι P 𝔪) (t : F) {ν : SInt 𝔪} (hν : ν ≠ 0) :
    T.tau (Φ.nT hG t) ν = B.psiS hG.ne_bot ((ν : F) * t) * T.tau Φ ν :=
  tau_congr_F hG hz6 T hν fun c s _ _ => Lam_nT _ hG Φ t c _ s

theorem tau_smulFun (Φ : GSection ι P 𝔪) (f : ℂ → ℂ) (hf : Differentiable ℂ f) {ν : SInt 𝔪}
    (hν : ν ≠ 0) : T.tau (GSection.smulFun f hf Φ) ν = f (4 / 3) * T.tau Φ ν :=
  T.tau_smul_at f hf hν fun c s _ _ => Lam_smulFun _ hG Φ f hf (c : F) _ s

/-! ### The Kirillov function -/

theorem Kir_of_ne (Φ : GSection ι P 𝔪) {β : F} (hβ : β ≠ 0) :
    Kir hG hz6 T Φ β = T.tau (Φ.torusT hG β hβ) 1 := by
  rw [Kir, dif_neg hβ]

/-- **MATH3 (2.2) for `𝒦`**: with `γ = [[a,b],[c,d]]`, `c ≠ 0`, `Ψ = translate γ (n(-d/c)Φ)`:
`𝒦_Ψ(μ) = κ(γ) |c|^{-2/3} ψ(μa/c) ⟨μ,c⟩ 𝒦_{wΦ}(μ/c²)`. -/
theorem Kir_cusp (Φ : GSection ι P 𝔪) (γ : Matrix.SpecialLinearGroup (Fin 2) (SInt 𝔪))
    (hc : ((γ.1 1 0 : SInt 𝔪) : F) ≠ 0) {μ : F} (hμ : μ ≠ 0) :
    Kir hG hz6 T (S2.GSection.translate hG γ
        (Φ.nT hG (-((γ.1 1 1 : SInt 𝔪) : F) / ((γ.1 1 0 : SInt 𝔪) : F)))) μ
      = kappa ι 𝔪 γ * ((absS 𝔪 ((γ.1 1 0 : SInt 𝔪) : F) : ℝ) : ℂ) ^ ((4 / 3 : ℂ) - 2)
        * B.psiS hG.ne_bot (μ * (((γ.1 0 0 : SInt 𝔪) : F) / ((γ.1 1 0 : SInt 𝔪) : F)))
        * brk ι P 𝔪 μ ((γ.1 1 0 : SInt 𝔪) : F)
        * Kir hG hz6 T (wSec hG Φ) (μ / ((γ.1 1 0 : SInt 𝔪) : F) ^ 2) := by
  have hμ' : μ / ((γ.1 1 0 : SInt 𝔪) : F) ^ 2 ≠ 0 := div_ne_zero hμ (pow_ne_zero 2 hc)
  rw [Kir_of_ne hG hz6 T _ hμ, Kir_of_ne hG hz6 T _ hμ', cusp_torusT hG Φ γ hc hμ,
    tau_smul hG hz6 T _ _ one_ne_zero, scal, tau_smulFun hG hz6 T _ _ _ one_ne_zero,
    tau_nT hG hz6 T _ _ one_ne_zero]
  have h1 : ((1 : SInt 𝔪) : F) = 1 := rfl
  rw [h1, show (1 : ℂ) * (4 / 3) + -2 = 4 / 3 - 2 by ring, one_mul]
  ring

/-- **MATH3 (2.2)**: `ξ_Ψ(μ) = κ(γ) ψ(μa/c) ⟨μ,c⟩ ξ_{wΦ}(μ/c²)`. -/
theorem xi_cusp (Φ : GSection ι P 𝔪) (γ : Matrix.SpecialLinearGroup (Fin 2) (SInt 𝔪))
    (hc : ((γ.1 1 0 : SInt 𝔪) : F) ≠ 0) {μ : F} (hμ : μ ≠ 0) :
    xi hG hz6 T (S2.GSection.translate hG γ
        (Φ.nT hG (-((γ.1 1 1 : SInt 𝔪) : F) / ((γ.1 1 0 : SInt 𝔪) : F)))) μ
      = kappa ι 𝔪 γ
        * B.psiS hG.ne_bot (μ * (((γ.1 0 0 : SInt 𝔪) : F) / ((γ.1 1 0 : SInt 𝔪) : F)))
        * brk ι P 𝔪 μ ((γ.1 1 0 : SInt 𝔪) : F)
        * xi hG hz6 T (wSec hG Φ) (μ / ((γ.1 1 0 : SInt 𝔪) : F) ^ 2) := by
  rw [xi, xi, Kir_cusp hG hz6 T Φ γ hc hμ, ← absS_cusp hμ hc]
  ring

/-! ### The class decomposition and the majorant -/

end tau

end ArtinKP.G1
end
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
attribute [-instance] _root_.ArtinKP.T.instCountableSubtypeForallInfinitePlaceComplexMemAddSubgroupMinLatN _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
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

lemma volume_ne_top_of_bdd {D : Set (InfinitePlace F → ℂ)} {n : ℕ}
    (h : ∀ x ∈ D, ∀ w, ‖x w‖ ≤ n) : volume D ≠ ⊤ := by
  have hsub : D ⊆ Metric.closedBall (0 : InfinitePlace F → ℂ) n := fun x hx => by
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg (Nat.cast_nonneg _)]
    exact h x hx
  exact ((measure_mono hsub).trans_lt measure_closedBall_lt_top).ne


theorem pcell_cellM (h𝔪 : 𝔪 ≠ ⊥) {M : ℤ} (hM : 0 ≤ M) : PCell (transLat 𝔪 M) (cellM 𝔪 M) := by
  unfold cellM
  rw [dif_pos ⟨h𝔪, hM⟩]
  exact (exists_pcell_transLat h𝔪 hM).choose_spec.choose_spec.1

theorem cellM_bdd (h𝔪 : 𝔪 ≠ ⊥) {M : ℤ} (hM : 0 ≤ M) :
    ∀ x ∈ cellM 𝔪 M, ∀ w, ‖x w‖ ≤ cellN 𝔪 M := by
  unfold cellM cellN
  rw [dif_pos ⟨h𝔪, hM⟩, dif_pos ⟨h𝔪, hM⟩]
  exact (exists_pcell_transLat h𝔪 hM).choose_spec.choose_spec.2

lemma vol_pos (𝔪 : Ideal (𝓞 F)) (M : ℤ) : 0 < vol 𝔪 M := by
  unfold vol
  refine Finset.prod_pos fun v _ => zpow_pos ?_ _
  have h : Ideal.absNorm v.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact v.ne_bot
  exact Nat.cast_pos.mpr (Nat.pos_of_ne_zero h)

lemma volume_toReal_pos {L : AddSubgroup (InfinitePlace F → ℂ)} [Countable L]
    {D : Set (InfinitePlace F → ℂ)} (h : PCell L D) {n : ℕ} (hb : ∀ x ∈ D, ∀ w, ‖x w‖ ≤ n) :
    0 < (volume D).toReal :=
  ENNReal.toReal_pos ((h.isAddFundamentalDomain volume).measure_ne_zero (NeZero.ne _))
    (volume_ne_top_of_bdd hb)

theorem kap_ne_zero (h𝔪 : 𝔪 ≠ ⊥) {M : ℤ} (hM : 0 ≤ M) : kap 𝔪 M ≠ 0 := by
  unfold kap
  refine inv_ne_zero (Complex.ofReal_ne_zero.mpr (mul_pos ?_ (vol_pos 𝔪 M)).ne')
  exact volume_toReal_pos (pcell_cellM h𝔪 hM) (cellM_bdd h𝔪 hM)

end

end ArtinKP.T
end

section
-- module Solutions.Artin.KP.G2a_Major
attribute [-instance] _root_.ArtinKP.N2.levelGroup_finiteIndex
/-! # WP-G2a, file 2: the summable majorant of `τ_Φ(ν)·W_{4/3}(ν; v)`

* `ThmE hG hz6 g`: **named hypothesis**, Theorem E for the instance `T.theta hG hz6` in the form
  of `H.tau_eq_coefF'` (`thmE_of_PER` derives it from cube periodicity at every exterior prime
  plus the standing data of `H_Tau`).
* `absNorm_rowOf`: the product formula, exact: `N(νR) = ∏_w |ν|_w^{mult} · |ν|_{S_f}`.
* `norm_tau_le`: `|τ_Φ(ν)| ≤ ∏_w |ν|_w^{2/3} · bf([ν])` with `bf` summable against `|y|^σ`,
  `σ > −1/3` (G1's majorant of the Kirillov function).
* `exists_major`: for every box `vBox F n₀` and every `p` a summable `u` with
  `∏_w (1+|ν|_w)^p · |τ_Φ(ν) W_{4/3}(ν; v)| ≤ u ν` for all `v` in the box.
-/

open scoped ComplexConjugate Topology
open MeasureTheory Set NumberField Filter IsDedekindDomain ArtinPrimitiveRoots

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace ArtinKP.G2a

open ArtinKP.A ArtinKP.S ArtinKP.B ArtinKP.RF

noncomputable section

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}
variable {ι : F →+* ℂ} {P : CubicPkg F}

/-- The product formula on `R ∖ 0`, exact. -/
theorem absNorm_rowOf (h𝔪 : 𝔪 ≠ ⊥) (g : AllowedGen ι 𝔪) (k : ℕ) (d : {ν : SInt 𝔪 // ν ≠ 0}) :
    (Ideal.absNorm (H0.rowOf h𝔪 g d).1.1 : ℝ) =
      (∏ w : InfinitePlace F, w ((d : SInt 𝔪) : F) ^ w.mult) *
        (SFin.mk 𝔪 k (Units.mk0 ((d : SInt 𝔪) : F) (H0.coe_ne_zero d))).norm := by
  have hd := H0.coe_ne_zero d
  have h1 := L3X.lnorm_sEmb_gen (k := k) h𝔪 (H0.rowOf h𝔪 g d).1.2 (H0.span_eq_map_rowOf h𝔪 g d)
  have hN : (0 : ℝ) < Ideal.absNorm (H0.rowOf h𝔪 g d).1.1 := by
    have : Ideal.absNorm (H0.rowOf h𝔪 g d).1.1 ≠ 0 := by
      rw [ne_eq, Ideal.absNorm_eq_zero_iff]; exact (H0.rowOf h𝔪 g d).1.2.1
    exact_mod_cast Nat.pos_of_ne_zero this
  have hP : 0 < ∏ w : InfinitePlace F, w ((d : SInt 𝔪) : F) ^ w.mult :=
    Finset.prod_pos fun w _ => pow_pos (w.pos_iff.2 hd) _
  have hn := L3X.SFin.norm_mk_pos (k := k) h𝔪 (Units.mk0 _ hd)
  have h2 : L3X.lnorm (sEmb 𝔪 k ((d : SInt 𝔪) : F)) =
      ∑ w : InfinitePlace F, Real.log (w ((d : SInt 𝔪) : F) ^ w.mult) +
        Real.log (SFin.mk 𝔪 k (Units.mk0 ((d : SInt 𝔪) : F) hd)).norm := by
    rw [L3X.lnorm, L3X.sEmb_fin hd]
    congr 1
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [L3X.sEmb_fst hd, Real.log_pow]
  refine Real.log_injOn_pos (Set.mem_Ioi.mpr hN) (Set.mem_Ioi.mpr (mul_pos hP hn)) ?_
  rw [Real.log_mul hP.ne' hn.ne', Real.log_prod (fun w _ => (pow_pos (w.pos_iff.2 hd) _).ne'),
    ← h2, h1]

theorem norm_mk_eq_absS (h𝔪 : 𝔪 ≠ ⊥) (k : ℕ) (x : Fˣ) :
    (SFin.mk 𝔪 k x).norm = absS 𝔪 (x : F) := by
  rw [L3X.SFin.norm_mk_eq_prod h𝔪, G1.sFin_eq_toFinset h𝔪]
  rfl

variable [IsTotallyComplex F]

/-- `N(νR)^{1/3} = ∏_w |ν|_w^{2/3} · |ν|_{S_f}^{1/3}`. -/
theorem absNorm_rowOf_rpow (h𝔪 : 𝔪 ≠ ⊥) (g : AllowedGen ι 𝔪) (d : {ν : SInt 𝔪 // ν ≠ 0}) :
    (Ideal.absNorm (H0.rowOf h𝔪 g d).1.1 : ℝ) ^ (1 / 3 : ℝ) =
      (∏ w : InfinitePlace F, w ((d : SInt 𝔪) : F) ^ (2 / 3 : ℝ)) *
        absS 𝔪 ((d : SInt 𝔪) : F) ^ (1 / 3 : ℝ) := by
  rw [absNorm_rowOf h𝔪 g 0 d, norm_mk_eq_absS h𝔪, Units.val_mk0,
    Real.mul_rpow (Finset.prod_nonneg fun w _ => by positivity) (absS_nonneg _),
    ← Real.finsetProd_rpow _ _ (fun w _ => by positivity)]
  congr 1
  refine Finset.prod_congr rfl fun w _ => ?_
  have hm : w.mult = 2 := by
    rw [InfinitePlace.mult, if_neg]
    exact InfinitePlace.not_isReal_iff_isComplex.mpr (IsTotallyComplex.isComplex w)
  rw [hm, ← Real.rpow_natCast, ← Real.rpow_mul (apply_nonneg _ _)]
  norm_num

variable (hG : Good 𝔪) {z6 : 𝓞 F} (hz6 : IsPrimitiveRoot z6 6) (g : AllowedGen ι 𝔪)

variable {hG hz6 g}

/-- `τ_Φ(ν) = N(νR)^{1/3}·coef·𝒦_Φ(ν)` with G1's Kirillov function. -/
theorem tau_eq_Kir (hE : ThmE hG hz6 g P) (Φ : GSection ι P 𝔪) (ν : {ν : SInt 𝔪 // ν ≠ 0}) :
    T.tau hG hz6 Φ (ν : SInt 𝔪) =
      (((Ideal.absNorm (H0.rowOf hG.ne_bot g ν).1.1 : ℝ) ^ (1 / 3 : ℝ) : ℝ) : ℂ) *
        L3X.coefF' g ⊤ (H0.rowOf hG.ne_bot g ν) *
        G1.Kir hG hz6 (T.theta hG hz6) Φ ((ν : SInt 𝔪) : F) := by
  rw [hE Φ ν, G1.Kir_of_ne hG hz6 _ Φ (H0.coe_ne_zero ν)]
  congr 2
  show S2.actR hG (ν : SInt 𝔪) Φ = _
  rw [S2.actR, dif_neg (H0.coe_ne_zero ν)]

/-- `τ_Φ(ν) = ∏_w |ν|_w^{2/3} · coef^S(ν) · ξ_Φ(ν)`. -/
theorem tau_eq_xi (hE : ThmE hG hz6 g P) (Φ : GSection ι P 𝔪) (ν : {ν : SInt 𝔪 // ν ≠ 0}) :
    T.tau hG hz6 Φ (ν : SInt 𝔪) =
      ((∏ w : InfinitePlace F, w ((ν : SInt 𝔪) : F) ^ (2 / 3 : ℝ) : ℝ) : ℂ) *
        L3X.coefF' g ⊤ (H0.rowOf hG.ne_bot g ν) *
        G1.xi hG hz6 (T.theta hG hz6) Φ ((ν : SInt 𝔪) : F) := by
  rw [tau_eq_Kir hE, absNorm_rowOf_rpow, G1.xi]
  push_cast
  ring

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

lemma kapC_ne_zero (h𝔪 : 𝔪 ≠ ⊥) : kapC F ≠ 0 := by
  rw [← kap_eq_kapC h𝔪 le_rfl]
  exact T.kap_ne_zero h𝔪 le_rfl

end

end ArtinKP.G2a
end

section
-- module Solutions.Artin.KP.G2a_Fwd
attribute [-instance] _root_.ArtinKP.N2.levelGroup_finiteIndex
/-! # WP-G2a, file 9: `∂_m θ̃_Φ` termwise and the forward field (MATH3 §1.1)

* `thetaX Φ v hv x = θ̃_Φ(x, v)` as a function of `x` at fixed height `v`.
* **`Dm_thetaX`**: `∂_m θ̃_Φ(·, v)` is the termwise series; the constant term is killed and the
  `ν`-th term is multiplied by `∏_w (−2πi·ν_w^{(m_w)})`.
* `ThetaM m Φ X Y := ∏_w Y_w^{(m_w)} · (∂_m θ̃_Φ)(X, |Y|)` (MATH3's `Θ_m^Φ(X, Y)`).
* `place_kappaB`: `(νY)^{(m)}·jacquet (4/3) (−ν) |Y| = C0·|ν|^{−2/3}·ω_m(νY)·κ(|νY|²)`,
  `κ = K.kappaB (4π)`, `C0 = (2π)^{4/3}/Γ(4/3)`.
* **`ThetaM_tau`**: the expansion with coefficient `τ_Φ(ν)` (no Theorem E beyond convergence);
* **`ThetaM_forward`** = MATH3 (1.1):
  `Θ_m^Φ(X,Y) = kapC·C_a^r·Σ_ν coef^S(ν)·ξ_Φ(ν)·e_∞(νX)·∏_w ω_{m_w}(ν_wY_w)·κ(|ν_wY_w|²)`,
  `C_a = −2πi·C0`, with `summable_forward`.
-/

open scoped MatrixGroups ComplexConjugate ENNReal Topology Classical
open MeasureTheory Set NumberField Filter IsDedekindDomain ArtinPrimitiveRoots Metric

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace ArtinKP.G2a

open ArtinKP.A ArtinKP.S ArtinKP.B ArtinKP.RF ArtinKP.X ArtinKP.B1 ArtinKP.C5 ArtinKP.N ArtinKP.K

noncomputable section

/-! ### One place -/

lemma cj_mul (m : ℤ) (a b : ℂ) : cj m (a * b) = cj m a * cj m b := by
  unfold cj; split_ifs <;> simp

variable {F : Type*} [Field F] [NumberField F] [IsTotallyComplex F] {𝔪 : Ideal (𝓞 F)}
variable {ι : F →+* ℂ} {P : CubicPkg F}
variable (hG : Good 𝔪) {z6 : 𝓞 F} (hz6 : IsPrimitiveRoot z6 6)

variable {hG hz6} {g : AllowedGen ι 𝔪}

variable (hG hz6)

variable {hG hz6}

/-- `τ_Φ(ν)·∏_w |ν|_w^{−2/3} = coef^S(ν)·ξ_Φ(ν)` (Theorem E and the product formula). -/
lemma tau_mul_rpow (hE : ThmE hG hz6 g P) (Φ : GSection ι P 𝔪) (ν : {ν : SInt 𝔪 // ν ≠ 0}) :
    T.tau hG hz6 Φ (ν : SInt 𝔪) *
        ((∏ w : InfinitePlace F, (w ((ν : SInt 𝔪) : F)) ^ (-(2 / 3 : ℝ)) : ℝ) : ℂ) =
      L3X.coefF' g ⊤ (H0.rowOf hG.ne_bot g ν) *
        G1.xi hG hz6 (T.theta hG hz6) Φ ((ν : SInt 𝔪) : F) := by
  rw [tau_eq_xi hE]
  have h1 : (∏ w : InfinitePlace F, (w ((ν : SInt 𝔪) : F)) ^ (2 / 3 : ℝ)) *
      ∏ w : InfinitePlace F, (w ((ν : SInt 𝔪) : F)) ^ (-(2 / 3 : ℝ)) = 1 := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_eq_one fun w _ => ?_
    rw [← Real.rpow_add (w.pos_iff.2 (H0.coe_ne_zero ν))]
    norm_num
  have h2 := congrArg (fun t : ℝ => (t : ℂ)) h1
  simp only [Complex.ofReal_mul, Complex.ofReal_one] at h2
  linear_combination (L3X.coefF' g ⊤ (H0.rowOf hG.ne_bot g ν) *
    G1.xi hG hz6 (T.theta hG hz6) Φ ((ν : SInt 𝔪) : F)) * h2

/-- **MATH3 (1.1), the forward field of a general section.** -/
theorem ThetaM_forward (hE : ThmE hG hz6 g P) (m : InfinitePlace F → ℤ) (Φ : GSection ι P 𝔪)
    (X Y : InfinitePlace F → ℂ) (hY : ∀ w, Y w ≠ 0) :
    ThetaM hG hz6 m Φ X Y hY =
      kapC F * (-(2 * Real.pi * Complex.I) * C0) ^ Fintype.card (InfinitePlace F) *
        ∑' ν : {ν : SInt 𝔪 // ν ≠ 0}, L3X.coefF' g ⊤ (H0.rowOf hG.ne_bot g ν) *
          G1.xi hG hz6 (T.theta hG hz6) Φ ((ν : SInt 𝔪) : F) *
          eInf (emb ((ν : SInt 𝔪) : F) * X) *
          ∏ w : InfinitePlace F, (omg (m w) (w.embedding ((ν : SInt 𝔪) : F) * Y w) *
            (kappaB (4 * Real.pi) (‖w.embedding ((ν : SInt 𝔪) : F) * Y w‖ ^ 2) : ℂ)) := by
  rw [ThetaM_tau hE]
  congr 1
  refine tsum_congr fun ν => ?_
  rw [tau_mul_rpow hE]

lemma C0_ne_zero : C0 ≠ 0 := by
  unfold C0
  have h1 : Complex.Gamma (4 / 3) ≠ 0 := by
    have : (4 / 3 : ℂ) = ((4 / 3 : ℝ) : ℂ) := by push_cast; rfl
    rw [this, Complex.Gamma_ofReal]
    exact Complex.ofReal_ne_zero.mpr (Real.Gamma_pos_of_pos (by norm_num)).ne'
  have h2 : (2 * Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast (by positivity : (2 * Real.pi : ℝ) ≠ 0)
  exact mul_ne_zero (div_ne_zero h2 h1) (Complex.ofReal_ne_zero.mpr (by positivity))

end

end ArtinKP.G2a
end

section
-- module Solutions.Artin.KP.GR_Arch
/-! # WP-GR, file 1: the archimedean dictionary

G2a's profile `∏_w ω_{m_w}(ν_w Y_w)·κ(|ν_w Y_w|²)` (`G2a.omg`, `K.kappaB (4π)`) against the
frozen `L3X.fpF κ m (sEmb ν + y)` and `H0.FmOf κ m J cl (sEmb ν̃ − y)`.

* `Yof y w = exp(y.1 w / 2)·e^{iθ_w}` (MATH3 §0), `Yrt` a square root of it.
* `omg_polar`: for `m = ±1`, `ω_m(z·r·e^{iθ}) = e^{i m arg z}·e^{i m θ}`.
* `arch_forward`: the product at `ν_w·Y_w`;
* `arch_reflected`: the product of type `−m` at `ν̃_w / Y_w`.
-/

open scoped ComplexConjugate Topology Classical
open NumberField IsDedekindDomain ArtinPrimitiveRoots

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace ArtinKP.GR

open ArtinKP.G2a ArtinKP.K

noncomputable section

/-! ### One place -/

lemma toCircle_coe (x : ℝ) :
    ((AddCircle.toCircle ((x : ℝ) : AddCircle (2 * Real.pi)) : Circle) : ℂ)
      = Complex.exp (x * Complex.I) := by
  rw [AddCircle.toCircle_apply_mk, Circle.coe_exp]
  congr 2
  rw [div_self (by positivity), one_mul]

lemma toCircle_arg {z : ℂ} (hz : z ≠ 0) :
    ((AddCircle.toCircle ((Complex.arg z : ℝ) : AddCircle (2 * Real.pi)) : Circle) : ℂ)
      = z / (‖z‖ : ℂ) := by
  have hn : (‖z‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hz)
  rw [toCircle_coe, eq_div_iff hn, mul_comm]
  exact Complex.norm_mul_exp_arg_mul_I z

lemma toCircle_neg_one_zsmul (a : AddCircle (2 * Real.pi)) :
    ((AddCircle.toCircle ((-1 : ℤ) • a) : Circle) : ℂ)
      = conj ((AddCircle.toCircle a : Circle) : ℂ) := by
  rw [neg_one_zsmul, AddCircle.toCircle_neg, Circle.coe_inv_eq_conj]

lemma cj_toCircle {m : ℤ} (hm : m = 1 ∨ m = -1) (a : AddCircle (2 * Real.pi)) :
    cj m ((AddCircle.toCircle a : Circle) : ℂ) = ((AddCircle.toCircle (m • a) : Circle) : ℂ) := by
  rcases hm with rfl | rfl
  · simp [cj]
  · rw [toCircle_neg_one_zsmul]
    simp [cj]

lemma cj_ofReal (m : ℤ) (r : ℝ) : cj m (r : ℂ) = (r : ℂ) := by
  unfold cj; split_ifs <;> simp

lemma cj_div (m : ℤ) (a b : ℂ) : cj m (a / b) = cj m a / cj m b := by
  unfold cj; split_ifs <;> simp

/-- `ω_m(z) = e^{i m arg z}` for `m = ±1`. -/
lemma omg_eq_toCircle {m : ℤ} (hm : m = 1 ∨ m = -1) {z : ℂ} (hz : z ≠ 0) :
    omg m z = ((AddCircle.toCircle (m • ((Complex.arg z : ℝ) : AddCircle (2 * Real.pi))) :
      Circle) : ℂ) := by
  rw [← cj_toCircle hm, toCircle_arg hz, cj_div, cj_ofReal, omg]

/-- `ω_m(z·r·e^{iθ}) = e^{i m arg z}·e^{i m θ}` for `m = ±1`, `r > 0`. -/
lemma omg_polar {m : ℤ} (hm : m = 1 ∨ m = -1) {z : ℂ} (hz : z ≠ 0) {r : ℝ} (hr : 0 < r)
    (θ : AddCircle (2 * Real.pi)) :
    omg m (z * ((r : ℂ) * ((AddCircle.toCircle θ : Circle) : ℂ))) =
      ((AddCircle.toCircle (m • ((Complex.arg z : ℝ) : AddCircle (2 * Real.pi))) : Circle) : ℂ) *
        ((AddCircle.toCircle (m • θ) : Circle) : ℂ) := by
  rw [← omg_eq_toCircle hm hz, ← cj_toCircle hm, omg, omg, cj_mul, cj_mul, cj_ofReal, norm_mul,
    norm_mul, Complex.norm_real, Real.norm_of_nonneg hr.le, Circle.norm_coe, mul_one]
  have h1 : (‖z‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hz)
  have h2 : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
  push_cast
  field_simp

lemma norm_polar (z : ℂ) {r : ℝ} (hr : 0 < r) (θ : AddCircle (2 * Real.pi)) :
    ‖z * ((r : ℂ) * ((AddCircle.toCircle θ : Circle) : ℂ))‖ = ‖z‖ * r := by
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hr.le, Circle.norm_coe, mul_one]

/-! ### The archimedean coordinate `Y(y)` -/

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)} {k : ℕ}

lemma Yrt_ne_zero (y : SModel 𝔪 k) (w : InfinitePlace F) : Yrt y w ≠ 0 := Complex.exp_ne_zero _

lemma Yrt_sq (y : SModel 𝔪 k) (w : InfinitePlace F) : Yrt y w ^ 2 = Yof y w := by
  rw [Yrt, ← Complex.exp_nat_mul]
  push_cast
  rw [mul_div_cancel₀ _ (two_ne_zero), Complex.exp_log (Yof_ne_zero y w)]

lemma Yof_inv (y : SModel 𝔪 k) (w : InfinitePlace F) :
    (Yof y w)⁻¹ = ((Real.exp (-(y.1 w) / 2) : ℝ) : ℂ) *
      ((AddCircle.toCircle (-(y.2.1 w)) : Circle) : ℂ) := by
  rw [Yof, mul_inv, AddCircle.toCircle_neg, Circle.coe_inv, neg_div, Real.exp_neg]
  push_cast
  rfl

variable [IsTotallyComplex F]

lemma mult_eq_two (w : InfinitePlace F) : w.mult = 2 := by
  rw [InfinitePlace.mult, if_neg]
  exact InfinitePlace.not_isReal_iff_isComplex.mpr (IsTotallyComplex.isComplex w)

/-- **Reflected dictionary**: G2a's profile of type `−m` at `ν̃_w / Y_w` is the archimedean
factor of `H0.FmOf κ m J cl (sEmb ν̃ − y)` (`H0.FmOf_sEmb_sub`). -/
theorem arch_reflected (κ : ℝ → ℝ) (m : InfinitePlace F → ℤ) (hm : ∀ w, m w = 1 ∨ m w = -1)
    {ν : F} (hν : ν ≠ 0) (y : SModel 𝔪 k) :
    ∏ w : InfinitePlace F, (omg (-m w) (w.embedding ν * (Yof y w)⁻¹) *
        (κ (‖w.embedding ν * (Yof y w)⁻¹‖ ^ 2) : ℂ)) =
      ∏ w : InfinitePlace F, ((AddCircle.toCircle ((-m w) • ((Complex.arg (w.embedding ν) : ℝ) :
            AddCircle (2 * Real.pi))) : Circle) : ℂ) *
          ((AddCircle.toCircle (m w • y.2.1 w) : Circle) : ℂ) *
          (κ (w ν ^ w.mult * Real.exp (-(y.1 w))) : ℂ) := by
  refine Finset.prod_congr rfl fun w _ => ?_
  have hz : w.embedding ν ≠ 0 := (map_ne_zero _).mpr hν
  have hm' : -m w = 1 ∨ -m w = -1 := by rcases hm w with h | h <;> simp [h]
  rw [Yof_inv, omg_polar hm' hz (Real.exp_pos _), norm_polar _ (Real.exp_pos _),
    InfinitePlace.norm_embedding_eq, mult_eq_two, mul_pow, ← Real.exp_nat_mul, neg_smul_neg]
  congr 3
  push_cast
  ring_nf

end

end ArtinKP.GR
end

section
-- module Solutions.Artin.KP.GR_Flip
attribute [-instance] _root_.ArtinKP.N2.levelGroup_finiteIndex
/-! # WP-GR, file 2: MATH3 (2.3) — cusp change and Weyl flip for `Θ_m^Φ`

* `Dm_thetaX_affine`: the chain rule `∂_m[ζ ↦ θ̃_Φ(X₀ + Aζ, v)]_{ζ=0} = ∏_w A_w^{(m_w)}·(∂_m θ̃_Φ)(X₀, v)`
  (termwise on the Fourier series, `G2a.DList_series`).
* `orbit_cusp`: `γ·n(ξ)a(y)n(ζ)·j = n(a/c)·a(1/(cy))·w·n(ζ)·j` for `ξ = −d/c` (the K-part is
  exactly `w`); `smul_curveN`: the same on `X F`, in the coordinates `K.curveN`, `K.curveW`.
* `WeylFlip P hG hz6`: **named hypothesis** = the statement of the stub `G2a.weyl_flip_thetaT`
  (owner WP-GW), for all `m` with values `±1`.
* **`ThetaM_flip`** = MATH3 (2.3):
  `Θ_m^Φ(emb ξ, y²) = (−1)^r · Θ_{−m}^{γΦ}(emb(a/c), 1/(cy)²)`, `γΦ = translate γ Φ`.
-/

open scoped MatrixGroups ComplexConjugate ENNReal Topology Classical
open MeasureTheory Set NumberField Filter IsDedekindDomain ArtinPrimitiveRoots Metric

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace ArtinKP.GR

open ArtinKP.A ArtinKP.S ArtinKP.B ArtinKP.RF ArtinKP.X ArtinKP.B1 ArtinKP.C5 ArtinKP.N ArtinKP.K
  ArtinKP.G2a

noncomputable section

/-! ### One place: the orbit identity -/

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}

variable [IsTotallyComplex F] {ι : F →+* ℂ} {P : CubicPkg F}
variable (hG : Good 𝔪) {z6 : 𝓞 F} (hz6 : IsPrimitiveRoot z6 6)

/-! ### The chain rule along an affine map -/

variable {hG hz6} {g : AllowedGen ι 𝔪}

/-! ### The Weyl flip (named hypothesis) and MATH3 (2.3) -/

variable (hG hz6 P)

variable {hG hz6 P}

lemma ThetaM_congr (m : InfinitePlace F → ℤ) (Φ : GSection ι P 𝔪) (X₀ : InfinitePlace F → ℂ)
    {Y Y' : InfinitePlace F → ℂ} (h : Y = Y') (hY : ∀ w, Y w ≠ 0) (hY' : ∀ w, Y' w ≠ 0) :
    ThetaM hG hz6 m Φ X₀ Y hY = ThetaM hG hz6 m Φ X₀ Y' hY' := by
  subst h; rfl

end

end ArtinKP.GR
end

section
-- module Solutions.Artin.KP.GR_Theta
/-! # WP-GR, file 3: `Θ` and its two expansions (MATH3 §1, §2; §6.1 (6))

* `thmE`: G2a's named hypothesis `ThmE` from WP-GK (`GK.per_all`, `S2.cubicSymbol_gen`).
* `Ccon = kapC·(−2πi·C0)^r` (MATH3's `C`).
* **`ThetaG`**: `Θ(x, y) = C⁻¹·Θ_m^{nT(−x)Φ_{y_f}}(emb(−x), Y(y))`, `Φ_{y_f} = GK.PhiB hG Φ₀ (rep y_f)`.
* `xi_PhiB`: `ξ_{Φ_{y_f}}(β) = 1[[β] + y_f = 0]` for a delta section `Φ₀`.
* **`thetaG_forward`**: HB's forward expansion, for every `x ∈ F`.
* **`thetaG_reflected`**: HB's reflected expansion (MATH3 (2.4) with (4.1)), for every `x ∈ F` and
  `γ ∈ SL₂(R)` with bottom row `(c, cx)`, `c ≠ 0`; needs the named hypothesis `WeylFlip`.
-/

open scoped MatrixGroups ComplexConjugate ENNReal Topology Classical
open MeasureTheory Set NumberField Filter IsDedekindDomain ArtinPrimitiveRoots Metric

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace ArtinKP.GR

open ArtinKP.A ArtinKP.S ArtinKP.B ArtinKP.RF ArtinKP.X ArtinKP.B1 ArtinKP.C5 ArtinKP.N ArtinKP.K
  ArtinKP.G2a

noncomputable section

variable {F : Type*} [Field F] [NumberField F] [IsTotallyComplex F] {𝔪 : Ideal (𝓞 F)}
variable {ι : F →+* ℂ} {P : CubicPkg F}
variable (hG : Good 𝔪) {z6 : 𝓞 F} (hz6 : IsPrimitiveRoot z6 6)

lemma Ccon_ne_zero (h𝔪 : 𝔪 ≠ ⊥) : Ccon F ≠ 0 := by
  refine mul_ne_zero (kapC_ne_zero h𝔪) (pow_ne_zero _ (mul_ne_zero (neg_ne_zero.mpr ?_) C0_ne_zero))
  simp [Real.pi_ne_zero, Complex.I_ne_zero]

variable {k : ℕ}

variable {hG hz6}

variable {g : AllowedGen ι 𝔪}

/-- **The reflected expansion** (MATH3 (2.4) with (4.1); HB's `thetaG_reflected`): for every
`x ∈ F` and `γ = [[a,b],[c,d]] ∈ SL₂(R)` with `c ≠ 0`, `d = c·x`. -/
theorem thetaG_eq_tsum_reflected_oai (hE : ThmE hG hz6 g P)
    (hgood : ∀ (Q : Ideal (𝓞 F)) (hQ : Q.IsPrime) (hext : IsExterior 𝔪 Q),
      C3I.Good 𝔪 (⟨Q, hQ, hext.1⟩ : HeightOneSpectrum (𝓞 F)))
    (hd : DD.DiffInS 𝔪) (hW : WeylFlip (ι := ι) P hG hz6)
    (hk : P.IsDeepLevel 𝔪 (k + 1)) {Φ₀ : GSection ι P 𝔪} (hΦ₀ : GK.IsDelta hG hz6 k Φ₀)
    (m : InfinitePlace F → ℤ) (hm : ∀ w, m w = 1 ∨ m w = -1) (x : F)
    (γ : SL(2, SInt 𝔪)) (hc : ((γ.1 1 0 : SInt 𝔪) : F) ≠ 0)
    (hdx : ((γ.1 1 1 : SInt 𝔪) : F) = ((γ.1 1 0 : SInt 𝔪) : F) * x) (y : SModel 𝔪 k) :
    ThetaG hG hz6 m Φ₀ x y =
      ∑' μ : {μ : SInt 𝔪 // μ ≠ 0},
        (L3X.coefF' g ⊤ (H0.rowOf hG.ne_bot g μ) *
          sAddChar 𝔪 (((μ : SInt 𝔪) : F) * ((γ.1 0 0 : SInt 𝔪) : F) / ((γ.1 1 0 : SInt 𝔪) : F)) *
          kappa ι 𝔪 γ * brk ι P 𝔪 ((μ : SInt 𝔪) : F) ((γ.1 1 0 : SInt 𝔪) : F)) *
        H0.FmOf (kappaB (4 * Real.pi)) m (GK.Jdef hG hz6 Φ₀)
          (QuotientAddGroup.mk
            (sEmb 𝔪 k (((μ : SInt 𝔪) : F) / ((γ.1 1 0 : SInt 𝔪) : F) ^ 2)).2.2)
          (sEmb 𝔪 k (((μ : SInt 𝔪) : F) / ((γ.1 1 0 : SInt 𝔪) : F) ^ 2) - y) := by
  have hC := Ccon_ne_zero (F := F) hG.ne_bot
  set c : F := ((γ.1 1 0 : SInt 𝔪) : F) with hcdef
  set a : F := ((γ.1 0 0 : SInt 𝔪) : F) with hadef
  have hξ : -x = -((γ.1 1 1 : SInt 𝔪) : F) / c := by
    rw [hdx]; field_simp
  set Φy : GSection ι P 𝔪 := GK.PhiB hG Φ₀ (G1.repS y.2.2) with hΦy
  have hY : Yof y = fun w => Yrt y w ^ 2 := funext fun w => (Yrt_sq y w).symm
  rw [ThetaG, hξ, ThetaM_congr m _ _ hY (Yof_ne_zero y) (fun w => pow_ne_zero 2 (Yrt_ne_zero y w)),
    ThetaM_flip hE hd hW m hm _ γ hc (Yrt y) (Yrt_ne_zero y), ThetaM_forward hE, ← Ccon,
    mul_left_comm, inv_mul_cancel_left₀ hC, ← tsum_mul_left]
  refine tsum_congr fun μ => ?_
  have hμ : ((μ : SInt 𝔪) : F) ≠ 0 := H0.coe_ne_zero μ
  have hν : ((μ : SInt 𝔪) : F) / c ^ 2 ≠ 0 := div_ne_zero hμ (pow_ne_zero 2 hc)
  -- the Kirillov function of the rotated section
  have h1 := G1.xi_cusp hG hz6 (T.theta hG hz6) Φy γ hc hμ
  -- the class function `J`
  have h2 := GK.xi_wSec_phiB_eq_jdef hG hz6 g hgood hd hk hΦ₀ (G1.repS y.2.2) (Units.mk0 _ hν)
  rw [G1.mk_repS, Units.val_mk0] at h2
  -- the characters
  have h3 : eInf (emb ((μ : SInt 𝔪) : F) * emb (a / c)) *
      psiS hG.ne_bot (((μ : SInt 𝔪) : F) * (a / c)) = sAddChar 𝔪 (((μ : SInt 𝔪) : F) * a / c) := by
    rw [← emb_mul, eInf_emb_eq hG.ne_bot, mul_div_assoc, mul_assoc, mul_comm (conj _),
      G1.SfChar.mul_conj_self, mul_one]
  -- the archimedean factor
  have h4 : ∏ w : InfinitePlace F, (omg (-m w) (w.embedding ((μ : SInt 𝔪) : F) *
        ((w.embedding c * Yrt y w)⁻¹) ^ 2) *
      (kappaB (4 * Real.pi) (‖w.embedding ((μ : SInt 𝔪) : F) *
        ((w.embedding c * Yrt y w)⁻¹) ^ 2‖ ^ 2) : ℂ)) =
      ∏ w : InfinitePlace F, (omg (-m w) (w.embedding (((μ : SInt 𝔪) : F) / c ^ 2) * (Yof y w)⁻¹) *
        (kappaB (4 * Real.pi) (‖w.embedding (((μ : SInt 𝔪) : F) / c ^ 2) * (Yof y w)⁻¹‖ ^ 2) :
          ℂ)) := by
    refine Finset.prod_congr rfl fun w _ => ?_
    have e : w.embedding ((μ : SInt 𝔪) : F) * ((w.embedding c * Yrt y w)⁻¹) ^ 2 =
        w.embedding (((μ : SInt 𝔪) : F) / c ^ 2) * (Yof y w)⁻¹ := by
      rw [← Yrt_sq, map_div₀, map_pow]
      have := Yrt_ne_zero y w
      have hcw : w.embedding c ≠ 0 := (map_ne_zero _).mpr hc
      field_simp
    rw [e]
  rw [H0.FmOf_sEmb_sub _ _ _ _ hν, L3X.sEmb_fin hν, ← h2, h4,
    arch_reflected (kappaB (4 * Real.pi)) m hm hν y, h1, ← h3]
  ring

end

end ArtinKP.GR
end

theorem solution.{u_1} : type_of% @ArtinKP.GR.thetaG_eq_tsum_reflected_oai.{u_1} := @ArtinKP.GR.thetaG_eq_tsum_reflected_oai.{u_1}
