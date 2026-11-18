-- Prove2me | solution 1 for ArtinKP.GK.exists_isDelta
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T10:07:55.372832+00:00
-- url     : https://prove2.me/submissions/b6cfcf05-9b1b-41ce-b3ed-83c4b2dda261

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
import Theorems.Thm_ArtinKP_GK_hne

section
-- module Solutions.Artin.KP.S_Basic
attribute [-instance] _root_.ArtinKP.B1.PairClass.instNonempty _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
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

namespace Small

variable {𝔪 : Ideal (𝓞 F)} {N M : ℤ} {x y : F}

theorem deep_inv (hN : 1 ≤ N) (hx : Small 𝔪 N (x - 1)) : Small 𝔪 N (x⁻¹ - 1) := fun v hv => by
  have h1 := hx.val_eq_one hN v hv
  have hx0 : x ≠ 0 := by
    intro h0; rw [h0, map_zero] at h1; exact zero_ne_one h1
  have e : x⁻¹ - 1 = -(x - 1) * x⁻¹ := by field_simp; ring
  rw [e, map_mul, Valuation.map_neg, map_inv₀, h1, inv_one, mul_one]
  exact hx v hv

end Small

/-! ### Absolute values at `S_f` -/

/-! ### The pairing `⟨x, y⟩ = ι (x, y)_S` on `F` -/

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
-- module Solutions.Artin.KP.S_BigCell
attribute [-instance] _root_.ArtinKP.N2.levelGroup_finiteIndex _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
attribute [-simp] _root_.ArtinKP.G1.scal_apply _root_.ArtinKP.S2.cubicSymbol_sym
/-!
# WP-S, part 6: big-cell and small-cell sections

For `η ∈ Fˣ`, a deep level `N ≥ 1`, and a lattice coset `L = {u : Small M (u - t₀)}`:

* `InClass 𝔪 N η c`: `c ∈ η · U_S · (Fˣ)³ · U_N` (`U_N` = units `N`-close to `1`); this is the
  rational form of MATH2's cube-saturated class `η U_S U_𝔫 (F_{S_f}ˣ)³`.
* `bigCell`: `Φ^{big}_s(c, d) = ⟨η, c⟩ |c|_{S_f}^{-s} 1[c ∈ class η] 1[d/c ∈ L]`.
  The unitary factor `⟨η, c⟩` equals MATH2's `⟨η₀, ε⟩` for `c = η₀ ε t³ u` and needs no choice.
* `smallCell = w · bigCell`: `⟨c, d⟩ ⟨η, d⟩ |d|^{-s} 1[d ∈ class η] 1[-c/d ∈ L]`.
* `nT_bigCell`, `twist_smallCell`: the translates by `n(t)` and `w`.
* `sum_bigCell_apply`: the sum over pairwise disjoint classes (MATH2 §3.1, `Φ^Σ`).
-/

set_option autoImplicit false

open NumberField IsDedekindDomain ArtinPrimitiveRoots

noncomputable section

namespace ArtinKP.S

open ArtinKP.A

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}

/-! ### Classes -/

/-! ### The support of a big-cell section and its stability -/

/-! ### Small-cell sections -/

/-! ### Finite sums: the sum over classes and additive projections -/

namespace GSection

variable {ι : F →+* ℂ} {P : CubicPkg F}

theorem sum_apply {α : Type*} (T : Finset α) (f : α → GSection ι P 𝔪) (s : ℂ) (c d : F) :
    (∑ i ∈ T, f i) s c d = ∑ i ∈ T, f i s c d := by
  classical
  induction T using Finset.induction_on with
  | empty => simp
  | insert a T ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, add_apply, ih]

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

/-! ### The `S_f`-character -/

theorem psiS_apply [IsTotallyComplex F] (h𝔪 : 𝔪 ≠ ⊥) (x : F) :
    psiS h𝔪 x = sAddChar 𝔪 x * conj (eInf (emb x)) := rfl

/-- `ψ_{S_f}` is trivial on `𝔩_0`. -/
theorem psiS_small [IsTotallyComplex F] (h𝔪 : 𝔪 ≠ ⊥) {x : F} (hx : Small 𝔪 0 x) :
    psiS h𝔪 x = 1 := by
  have h2 : ∀ v ∈ placesOf 𝔪, v.valuation F x ≤ 1 := fun v hv => by
    have := hx v hv
    simpa using this
  rw [psiS_apply, C3I.sAddChar_eq_of_wit (y := x) (by simp) h2, ← eInf_emb, eInf_mul_conj]

/-! ### The archimedean kernel -/

/-! ### Shifted kernels -/

end ArtinKP.B
end
end

section
-- module Solutions.Artin.KP.S2_Lattice
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-!
# WP-S2, part 5: lattices with a depth function; the Kirillov function as a Jacquet functional

* `SmallD 𝔪 k x`: `v(x) ≤ exp(-k v)` at every `v ∣ 𝔪`, for a depth function
  `k : HeightOneSpectrum (𝓞 F) → ℤ`; `latD 𝔪 k`, `volD 𝔪 k`, `jacD ψ k f ν`, `lamD`.
  For a constant depth these are `Small`, `lat`, `vol`, `jac`, `lam` of WP-S, by `rfl`.
* `smallD_mul_iff`: `β · 𝔩_k = 𝔩_{k + ord β}`; `absS_eq_prod`: `|β|_{S_f} = ∏ q_v^{-ord_v β}`.
* `jacD_subst`: the substitution `u = β u'`,
  `∫ g(u/β) conj ψ(νu) du = |β| ∫ g(u') conj ψ(νβu') du'`.
* `kir_eq_lamD` (**MATH2 Lemma 6.1 (iii)** / §6.3): `kir ψ M Φ η β s = λ_η((Ã(β)Φ)_s; 1)`, the
  functional on the right taken on the lattice `β 𝔩_M` (depth `M + ord_v β`).
-/

set_option autoImplicit false

open NumberField IsDedekindDomain ArtinPrimitiveRoots

noncomputable section

namespace ArtinKP.S2

open ArtinKP.A ArtinKP.S

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}

namespace SmallD

variable {k k' : HeightOneSpectrum (𝓞 F) → ℤ} {x y : F}

theorem sub (hx : SmallD 𝔪 k x) (hy : SmallD 𝔪 k y) : SmallD 𝔪 k (x - y) := by
  rw [sub_eq_add_neg]; exact hx.add hy.neg

end SmallD

end ArtinKP.S2
end
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

theorem Valid.mono {ψ : SfChar 𝔪} {Φ : GSection ι P 𝔪} {ν : F}
    {k k' : HeightOneSpectrum (𝓞 F) → ℤ} (h : Valid ψ Φ ν k)
    (hk : ∀ v : HeightOneSpectrum (𝓞 F), 𝔪 ≤ v.asIdeal → k v ≤ k' v) : Valid ψ Φ ν k' :=
  ⟨fun b hb => h.1 b (SmallD.mono hk hb), fun x hx => h.2 x (SmallD.mono hk hx)⟩

theorem Lam_eq_lam (ψ : SfChar 𝔪) (hG : Good 𝔪) (Φ : GSection ι P 𝔪) {ν : F} {M : ℤ}
    (h : Valid ψ Φ ν (fun _ => M)) (c : F) (s : ℂ) :
    Lam ψ hG Φ c ν s = lam ψ M Φ c ν s :=
  Lam_eq_lamD ψ hG Φ h c s

/-! ### The interface `E.Kubota` -/

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

/-! ### Powers of `|x|_{S_f}` as multipliers -/

/-! ### The Weyl element -/

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

end ArtinKP.G1
end
end

section
-- module Solutions.Artin.KP.RF_SNorm
attribute [-instance] _root_.ArtinKP.N2.levelGroup_finiteIndex _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-!
# WP-RF, part 1: summability of the `S_f`-norm series (stub S-1 of WP-S)

`summable_normS_one`: for `σ > 1`, `Σ_{u ∈ F/𝔩_M} ∏_{v ∣ 𝔪} max(1, |u|_v)^{-σ} < ∞`.

Route (WP-S): a finite set of elements of `F` whose pairwise differences have `v(x-y) ≤ exp(k_v)`
for `v ∈ S` and which are pairwise incongruent modulo `{v(x) ≤ exp(k_v - n_v)}` has at most
`∏_v q_v^{n_v}` elements (`card_le_of_separated`; induction on `Σ n_v`, each step maps into the
residue field `𝓞/v`).  Grouping the cosets by the depth vector of their representative gives the
bound `∏_v q_v^{|M|} (1 - q_v^{1-σ})⁻¹` for every finite partial sum.
-/

set_option autoImplicit false

open NumberField IsDedekindDomain ArtinPrimitiveRoots

noncomputable section

namespace ArtinKP.RF

open ArtinKP.A ArtinKP.S

variable {F : Type*} [Field F] [NumberField F]

/-- A "residue" map at `v`: integral elements with the same residue are congruent. -/
theorem exists_residue (v : HeightOneSpectrum (𝓞 F)) :
    ∃ r : F → 𝓞 F ⧸ v.asIdeal, ∀ x y : F, v.valuation F x ≤ 1 → v.valuation F y ≤ 1 →
      r x = r y → v.valuation F (x - y) < 1 := by
  classical
  have := v.isMaximal
  let _ := Ideal.Quotient.field v.asIdeal
  have key : ∀ x : F, v.valuation F x ≤ 1 →
      ∃ p : 𝓞 F × 𝓞 F, p.2 ∉ v.asIdeal ∧ x * algebraMap (𝓞 F) F p.2 = algebraMap (𝓞 F) F p.1 := by
    intro x hx
    obtain ⟨n, d, h⟩ := v.exists_primeCompl_mul_eq_of_integer x hx
    exact ⟨(n, d.1), d.2, h⟩
  refine ⟨fun x => if h : v.valuation F x ≤ 1 then
      Ideal.Quotient.mk v.asIdeal (Classical.choose (key x h)).1
        / Ideal.Quotient.mk v.asIdeal (Classical.choose (key x h)).2 else 0, ?_⟩
  intro x y hx hy hxy
  simp only [dif_pos hx, dif_pos hy] at hxy
  obtain ⟨hdx, ex⟩ := Classical.choose_spec (key x hx)
  obtain ⟨hdy, ey⟩ := Classical.choose_spec (key y hy)
  set nx := (Classical.choose (key x hx)).1
  set dx := (Classical.choose (key x hx)).2
  set ny := (Classical.choose (key y hy)).1
  set dy := (Classical.choose (key y hy)).2
  have hdx0 : Ideal.Quotient.mk v.asIdeal dx ≠ 0 := by
    rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
  have hdy0 : Ideal.Quotient.mk v.asIdeal dy ≠ 0 := by
    rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
  rw [div_eq_div_iff hdx0 hdy0, ← map_mul, ← map_mul, ← sub_eq_zero, ← map_sub,
    Ideal.Quotient.eq_zero_iff_mem] at hxy
  have h1 : v.valuation F (algebraMap (𝓞 F) F (nx * dy - ny * dx)) < 1 :=
    (v.valuation_lt_one_iff_mem _).mpr hxy
  have vdx : v.valuation F (algebraMap (𝓞 F) F dx) = 1 :=
    (IsDedekindDomain.HeightOneSpectrum.valuation_eq_one_iff_notMem (K := F) (v := v)).mpr hdx
  have vdy : v.valuation F (algebraMap (𝓞 F) F dy) = 1 :=
    (IsDedekindDomain.HeightOneSpectrum.valuation_eq_one_iff_notMem (K := F) (v := v)).mpr hdy
  have e : (x - y) * (algebraMap (𝓞 F) F dx * algebraMap (𝓞 F) F dy)
      = algebraMap (𝓞 F) F (nx * dy - ny * dx) := by
    rw [map_sub, map_mul, map_mul, ← ex, ← ey]; ring
  have := congrArg (v.valuation F) e
  rw [map_mul, map_mul, vdx, vdy, mul_one, mul_one] at this
  rw [this]; exact h1

theorem natCard_quot (v : HeightOneSpectrum (𝓞 F)) :
    Nat.card (𝓞 F ⧸ v.asIdeal) = Ideal.absNorm v.asIdeal := by
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]

/-- **Counting.**  A finite set whose differences are `exp k`-bounded on `S` and which is
separated modulo depth `k - n` has at most `∏_{v ∈ S} q_v^{n_v}` elements. -/
theorem card_le_of_separated (S : Finset (HeightOneSpectrum (𝓞 F))) :
    ∀ (N : ℕ) (n : HeightOneSpectrum (𝓞 F) → ℕ) (k : HeightOneSpectrum (𝓞 F) → ℤ) (T : Finset F),
      ∑ v ∈ S, n v = N →
      (∀ x ∈ T, ∀ y ∈ T, ∀ v ∈ S, v.valuation F (x - y) ≤ WithZero.exp (k v)) →
      (∀ x ∈ T, ∀ y ∈ T, x ≠ y →
        ¬ ∀ v ∈ S, v.valuation F (x - y) ≤ WithZero.exp (k v - n v)) →
      T.card ≤ ∏ v ∈ S, Ideal.absNorm v.asIdeal ^ n v := by
  classical
  intro N
  induction N with
  | zero =>
    intro n k T hN h1 h2
    have hn : ∀ v ∈ S, n v = 0 := fun v hv => (Finset.sum_eq_zero_iff.mp hN) v hv
    rw [Finset.prod_eq_one fun v hv => by rw [hn v hv, pow_zero]]
    refine Finset.card_le_one.mpr fun x hx y hy => ?_
    by_contra hxy
    refine h2 x hx y hy hxy fun v hv => ?_
    rw [hn v hv]; simpa using h1 x hx y hy v hv
  | succ N ih =>
    intro n k T hN h1 h2
    obtain ⟨v₀, hv₀, hpos⟩ : ∃ v ∈ S, 0 < n v := by
      by_contra hcon
      push Not at hcon
      have : ∑ v ∈ S, n v = 0 := Finset.sum_eq_zero fun v hv => by have := hcon v hv; omega
      omega
    rcases T.eq_empty_or_nonempty with rfl | ⟨x₀, hx₀⟩
    · simp
    set n' := Function.update n v₀ (n v₀ - 1) with hn'
    set k' := Function.update k v₀ (k v₀ - 1) with hk'
    have hsum : ∑ v ∈ S, n' v = N := by
      have e1 := Finset.add_sum_erase S n hv₀
      have e2 := Finset.add_sum_erase S n' hv₀
      have e3 : ∑ v ∈ S.erase v₀, n' v = ∑ v ∈ S.erase v₀, n v :=
        Finset.sum_congr rfl fun v hv => by
          rw [hn', Function.update_of_ne (Finset.ne_of_mem_erase hv)]
      have e4 : n' v₀ = n v₀ - 1 := by rw [hn', Function.update_self]
      omega
    obtain ⟨r, hr⟩ := exists_residue v₀
    obtain ⟨π, hπ⟩ := v₀.valuation_surjective F (WithZero.exp (-(k v₀)))
    have : Finite (𝓞 F ⧸ v₀.asIdeal) :=
      Nat.finite_of_card_ne_zero (by rw [natCard_quot]; exact (NumberField.HeightOneSpectrum.one_lt_absNorm v₀).ne_bot)
    let _ := Fintype.ofFinite (𝓞 F ⧸ v₀.asIdeal)
    set c : F → 𝓞 F ⧸ v₀.asIdeal := fun x => r (π * (x - x₀)) with hc
    have hint : ∀ x ∈ T, v₀.valuation F (π * (x - x₀)) ≤ 1 := by
      intro x hx
      rw [map_mul, hπ]
      calc WithZero.exp (-(k v₀)) * v₀.valuation F (x - x₀)
          ≤ WithZero.exp (-(k v₀)) * WithZero.exp (k v₀) :=
            mul_le_mul' le_rfl (h1 x hx x₀ hx₀ v₀ hv₀)
        _ = 1 := by rw [← WithZero.exp_add]; simp
    have hfib : ∀ a ∈ T.image c, (T.filter fun x => c x = a).card
        ≤ ∏ v ∈ S, Ideal.absNorm v.asIdeal ^ n' v := by
      intro a _
      refine ih n' k' _ hsum ?_ ?_
      · intro x hx y hy v hv
        rw [Finset.mem_filter] at hx hy
        by_cases hvv : v = v₀
        · subst hvv
          rw [hk', Function.update_self]
          by_cases hxy : x = y
          · simp [hxy]
          have hlt := hr _ _ (hint x hx.1) (hint y hy.1) (hx.2.trans hy.2.symm)
          have e : π * (x - x₀) - π * (y - x₀) = π * (x - y) := by ring
          rw [e, map_mul, hπ, val_eq_exp_ordv v (sub_ne_zero.mpr hxy), ← WithZero.exp_add,
            ← WithZero.exp_zero, WithZero.exp_lt_exp] at hlt
          rw [val_eq_exp_ordv v (sub_ne_zero.mpr hxy), WithZero.exp_le_exp]
          omega
        · rw [hk', Function.update_of_ne hvv]
          exact h1 x hx.1 y hy.1 v hv
      · intro x hx y hy hxy hall
        rw [Finset.mem_filter] at hx hy
        refine h2 x hx.1 y hy.1 hxy fun v hv => ?_
        have := hall v hv
        by_cases hvv : v = v₀
        · subst hvv
          rw [hk', hn', Function.update_self, Function.update_self] at this
          have e : k v - 1 - ((n v - 1 : ℕ) : ℤ) = k v - (n v : ℤ) := by omega
          rwa [e] at this
        · rwa [hk', hn', Function.update_of_ne hvv, Function.update_of_ne hvv] at this
    have hcard := Finset.card_le_mul_card_image (f := c) T _ hfib
    have himg : (T.image c).card ≤ Ideal.absNorm v₀.asIdeal := by
      rw [← natCard_quot, Nat.card_eq_fintype_card]
      exact Finset.card_le_univ _
    calc T.card ≤ (∏ v ∈ S, Ideal.absNorm v.asIdeal ^ n' v) * (T.image c).card := hcard
      _ ≤ (∏ v ∈ S, Ideal.absNorm v.asIdeal ^ n' v) * Ideal.absNorm v₀.asIdeal :=
          Nat.mul_le_mul_left _ himg
      _ = ∏ v ∈ S, Ideal.absNorm v.asIdeal ^ n v := by
          rw [← Finset.mul_prod_erase S _ hv₀, ← Finset.mul_prod_erase S
            (fun v => Ideal.absNorm v.asIdeal ^ n v) hv₀]
          have e3 : ∏ v ∈ S.erase v₀, Ideal.absNorm v.asIdeal ^ n' v
              = ∏ v ∈ S.erase v₀, Ideal.absNorm v.asIdeal ^ n v :=
            Finset.prod_congr rfl fun v hv => by
              rw [hn', Function.update_of_ne (Finset.ne_of_mem_erase hv)]
          have e4 : n' v₀ = n v₀ - 1 := by rw [hn', Function.update_self]
          rw [e3, e4]
          have e5 : n v₀ = (n v₀ - 1) + 1 := by omega
          conv_rhs => rw [e5, pow_succ]
          ring

/-! ### Depth -/

theorem val_le_dep (v : HeightOneSpectrum (𝓞 F)) (x : F) :
    v.valuation F x ≤ WithZero.exp ((dep v x : ℕ) : ℤ) := by
  by_cases hx : x = 0
  · simp [hx]
  rw [dep, if_neg hx, val_eq_exp_ordv v hx, WithZero.exp_le_exp]
  omega

open NumberField.HeightOneSpectrum in
theorem adicAbv_eq_zpow (v : HeightOneSpectrum (𝓞 F)) {x : F} (hx : x ≠ 0) :
    adicAbv F v x = (Ideal.absNorm v.asIdeal : ℝ) ^ (-ordv v x) := by
  have hq : (0 : ℝ) < Ideal.absNorm v.asIdeal := by exact_mod_cast (NumberField.HeightOneSpectrum.one_lt_absNorm v).pos
  have h1 : adicAbv F v x ≤ (Ideal.absNorm v.asIdeal : ℝ) ^ (-ordv v x) :=
    abv_le_of_val_le v (val_eq_exp_ordv v hx).le
  have h2 : adicAbv F v x⁻¹ ≤ (Ideal.absNorm v.asIdeal : ℝ) ^ (-(-ordv v x)) := by
    refine abv_le_of_val_le v ?_
    rw [map_inv₀, val_eq_exp_ordv v hx, ← WithZero.exp_neg]
  rw [map_inv₀, zpow_neg] at h2
  have hpos : 0 < adicAbv F v x := (adicAbv F v).pos hx
  refine le_antisymm h1 ?_
  have h3 := (inv_le_inv₀ hpos (zpow_pos hq _)).mp h2
  exact h3

open NumberField.HeightOneSpectrum in
theorem max_one_adicAbv (v : HeightOneSpectrum (𝓞 F)) (x : F) :
    max 1 (adicAbv F v x) = (Ideal.absNorm v.asIdeal : ℝ) ^ dep v x := by
  have hq : (1 : ℝ) < Ideal.absNorm v.asIdeal := by exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v
  by_cases hx : x = 0
  · simp [hx, dep]
  rw [dep, if_neg hx, adicAbv_eq_zpow v hx]
  rcases le_or_gt 0 (ordv v x) with h | h
  · have e : (-ordv v x).toNat = 0 := by omega
    rw [e, pow_zero]
    exact max_eq_left (zpow_le_one_of_nonpos₀ hq.le (by omega))
  · have e : -ordv v x = ((-ordv v x).toNat : ℤ) := by omega
    rw [e, zpow_natCast]
    simp only [Int.toNat_natCast]
    exact max_eq_right (one_le_pow₀ hq.le)

theorem normS_one_eq (𝔪 : Ideal (𝓞 F)) (x : F) :
    normS 𝔪 1 x = ∏ v ∈ CubicPkg.sFin 𝔪, (Ideal.absNorm v.asIdeal : ℝ) ^ dep v x := by
  rw [normS]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [map_one, max_one_adicAbv]

theorem rpow_factor {a : ℝ} (ha : 0 < a) (κ m : ℕ) (σ : ℝ) :
    a ^ (κ + m) * (a ^ κ) ^ (-σ) = a ^ m * (a ^ (1 - σ)) ^ κ := by
  rw [← Real.rpow_natCast a (κ + m), ← Real.rpow_natCast a κ, ← Real.rpow_natCast a m,
    ← Real.rpow_natCast (a ^ (1 - σ)) κ, ← Real.rpow_mul ha.le, ← Real.rpow_mul ha.le,
    ← Real.rpow_add ha, ← Real.rpow_add ha]
  congr 1
  push_cast
  ring

/-- **Stub S-1 of WP-S, proved** (identical statement to `S.summable_normS_one`). -/
theorem summable_normS_one {𝔪 : Ideal (𝓞 F)} (hG : Good 𝔪) (M : ℤ) {σ : ℝ} (hσ : 1 < σ) :
    Summable fun u : F ⧸ lat 𝔪 M => normS 𝔪 1 u.out ^ (-σ) := by
  classical
  set S := CubicPkg.sFin 𝔪 with hS
  set m : ℕ := M.natAbs with hm
  set q : HeightOneSpectrum (𝓞 F) → ℝ := fun v => (Ideal.absNorm v.asIdeal : ℝ) with hq
  have hq1 : ∀ v, 1 < q v := fun v => by
    show (1 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ)
    exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v
  have hq0 : ∀ v, 0 < q v := fun v => zero_lt_one.trans (hq1 v)
  set ρ : HeightOneSpectrum (𝓞 F) → ℝ := fun v => q v ^ (1 - σ) with hρ
  have hρ0 : ∀ v, 0 ≤ ρ v := fun v => Real.rpow_nonneg (hq0 v).le _
  have hρ1 : ∀ v, ρ v < 1 := fun v => Real.rpow_lt_one_of_one_lt_of_neg (hq1 v) (by linarith)
  refine summable_of_sum_le (c := (∏ v ∈ S.attach, q v.1 ^ m) * ∏ v ∈ S.attach, (1 - ρ v.1)⁻¹)
    (fun u => Real.rpow_nonneg (normS_nonneg _ _) _) fun T => ?_
  -- depth vector
  set d : (F ⧸ lat 𝔪 M) → ({v // v ∈ S} → ℕ) := fun u v => dep v.1 u.out with hd
  set Kmax : ℕ := T.sup fun u => S.sup fun v => dep v u.out with hK
  set P : Finset ({v // v ∈ S} → ℕ) := Fintype.piFinset fun _ => Finset.range (Kmax + 1) with hP
  have hmaps : ∀ u ∈ T, d u ∈ P := by
    intro u hu
    rw [hP, Fintype.mem_piFinset]
    intro v
    rw [Finset.mem_range, Nat.lt_succ_iff]
    exact (Finset.le_sup (f := fun v => dep v u.out) v.2).trans
      (Finset.le_sup (f := fun u : F ⧸ lat 𝔪 M => S.sup fun v => dep v u.out) hu)
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  have hfiber : ∀ κ ∈ P, ∑ u ∈ T with d u = κ, normS 𝔪 1 u.out ^ (-σ)
      ≤ (∏ v ∈ S.attach, q v.1 ^ m) * ∏ v ∈ S.attach, ρ v.1 ^ κ v := by
    intro κ _
    have hval : ∀ u ∈ T.filter (fun u => d u = κ), normS 𝔪 1 u.out ^ (-σ)
        = ∏ v ∈ S.attach, (q v.1 ^ κ v) ^ (-σ) := by
      intro u hu
      rw [Finset.mem_filter] at hu
      rw [normS_one_eq, ← hS, ← Finset.prod_attach S,
        ← Real.finsetProd_rpow _ _ (fun v _ => pow_nonneg (hq0 v.1).le _)]
      refine Finset.prod_congr rfl fun v _ => ?_
      have : dep v.1 u.out = κ v := congrFun hu.2 v
      rw [this]
    rw [Finset.sum_congr rfl hval, Finset.sum_const, nsmul_eq_mul]
    -- count the fibre
    set k : HeightOneSpectrum (𝓞 F) → ℤ := fun v => if h : v ∈ S then (κ ⟨v, h⟩ : ℤ) else 0
      with hk
    set n : HeightOneSpectrum (𝓞 F) → ℕ := fun v => (if h : v ∈ S then κ ⟨v, h⟩ else 0) + m
      with hn
    have hcount : (T.filter fun u => d u = κ).card
        ≤ ∏ v ∈ S, Ideal.absNorm v.asIdeal ^ n v := by
      rw [← Finset.card_image_of_injective _ (Quotient.out_injective)]
      refine card_le_of_separated S _ n k _ rfl ?_ ?_
      · intro x hx y hy v hv
        obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx
        obtain ⟨u', hu', rfl⟩ := Finset.mem_image.mp hy
        rw [Finset.mem_filter] at hu hu'
        have e1 : dep v u.out = κ ⟨v, hv⟩ := congrFun hu.2 ⟨v, hv⟩
        have e2 : dep v u'.out = κ ⟨v, hv⟩ := congrFun hu'.2 ⟨v, hv⟩
        have b1 := val_le_dep v u.out
        have b2 := val_le_dep v u'.out
        rw [e1] at b1; rw [e2] at b2
        rw [hk]; simp only [dif_pos hv]
        exact (Valuation.map_sub _ _ _).trans (max_le b1 b2)
      · intro x hx y hy hxy hall
        obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx
        obtain ⟨u', hu', rfl⟩ := Finset.mem_image.mp hy
        apply hxy
        have hmem : u.out - u'.out ∈ lat 𝔪 M := by
          intro v hv
          have hvS : v ∈ S := (CubicPkg.mem_sFin hG.ne_bot v).mpr hv
          refine (hall v hvS).trans ?_
          rw [WithZero.exp_le_exp, hk, hn]
          simp only [dif_pos hvS]
          push_cast
          omega
        have : (QuotientAddGroup.mk u.out : F ⧸ lat 𝔪 M) = QuotientAddGroup.mk u'.out := by
          rw [QuotientAddGroup.eq]
          have := (lat 𝔪 M).neg_mem hmem
          rwa [neg_sub, sub_eq_neg_add] at this
        rw [QuotientAddGroup.out_eq', QuotientAddGroup.out_eq'] at this
        rw [this]
    have hcountR : ((T.filter fun u => d u = κ).card : ℝ) ≤ ∏ v ∈ S.attach, q v.1 ^ (κ v + m) := by
      have : ((T.filter fun u => d u = κ).card : ℝ)
          ≤ ((∏ v ∈ S, Ideal.absNorm v.asIdeal ^ n v : ℕ) : ℝ) := by exact_mod_cast hcount
      refine this.trans (le_of_eq ?_)
      push_cast
      rw [← Finset.prod_attach S]
      refine Finset.prod_congr rfl fun v _ => ?_
      rw [hn, hq]; simp only [dif_pos v.2, Subtype.coe_eta]
    calc ((T.filter fun u => d u = κ).card : ℝ) * ∏ v ∈ S.attach, (q v.1 ^ κ v) ^ (-σ)
        ≤ (∏ v ∈ S.attach, q v.1 ^ (κ v + m)) * ∏ v ∈ S.attach, (q v.1 ^ κ v) ^ (-σ) :=
          mul_le_mul_of_nonneg_right hcountR
            (Finset.prod_nonneg fun v _ => Real.rpow_nonneg (pow_nonneg (hq0 v.1).le _) _)
      _ = (∏ v ∈ S.attach, q v.1 ^ m) * ∏ v ∈ S.attach, ρ v.1 ^ κ v := by
          rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
          exact Finset.prod_congr rfl fun v _ => rpow_factor (hq0 v.1) _ _ _
  refine (Finset.sum_le_sum hfiber).trans ?_
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ (Finset.prod_nonneg fun v _ => pow_nonneg (hq0 v.1).le _)
  have hprod : ∑ κ ∈ P, ∏ v ∈ S.attach, ρ v.1 ^ κ v
      = ∏ v ∈ S.attach, ∑ j ∈ Finset.range (Kmax + 1), ρ v.1 ^ j := by
    rw [hP, ← Finset.univ_eq_attach]
    exact (Finset.prod_univ_sum (fun _ : {v // v ∈ S} => Finset.range (Kmax + 1))
      (fun v j => ρ v.1 ^ j)).symm
  rw [hprod]
  refine Finset.prod_le_prod (fun v _ => Finset.sum_nonneg fun j _ => pow_nonneg (hρ0 v.1) _)
    fun v _ => ?_
  rw [← tsum_geometric_of_lt_one (hρ0 v.1) (hρ1 v.1)]
  exact (summable_geometric_of_lt_one (hρ0 v.1) (hρ1 v.1)).sum_le_tsum _
    fun j _ => pow_nonneg (hρ0 v.1) _

end ArtinKP.RF
end
end

section
-- module Solutions.Artin.KP.GL_SNorm
attribute [-instance] _root_.ArtinKP.N2.levelGroup_finiteIndex _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-!
# WP-GL, part 2: stub S-1 plugged into the bounds of WP-S and WP-S2

`RF.summable_normS_one` (S-1, proved by WP-RF) discharges the summability hypothesis of
`S.norm_lam_le`, `S.norm_kir_le`, `S.xi_bound`, `S.lam_differentiableOn` and `S2.norm_Lam_le`;
the versions here are unconditional for `Re s > 1`.
-/

set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

open NumberField IsDedekindDomain ArtinPrimitiveRoots

noncomputable section

namespace ArtinKP.GL

open ArtinKP.A ArtinKP.S

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}
variable {ι : F →+* ℂ} {P : CubicPkg F}

/-- S-1 in the shape of the hypothesis `hS1` of WP-S2. -/
theorem hS1 (hG : Good 𝔪) : ∀ (M : ℤ) {σ : ℝ}, 1 < σ →
    Summable fun u : F ⧸ lat 𝔪 M => normS 𝔪 1 u.out ^ (-σ) :=
  fun M _ hσ => RF.summable_normS_one hG M hσ

end ArtinKP.GL
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

/-- The series defining `jac` for `u ↦ Φ_s(c, cu)` converges absolutely for `Re s > 1`. -/
theorem summable_jacTerm (ψ : SfChar 𝔪) (hG : Good 𝔪) (Φ : GSection ι P 𝔪) (M : ℤ) {c : F}
    (hc : c ≠ 0) (ν : F) {s : ℂ} (hs : 1 < s.re) :
    Summable fun u : F ⧸ lat 𝔪 M => Φ s c (c * u.out) * (starRingEnd ℂ) (ψ (ν * u.out)) := by
  obtain ⟨B, hB⟩ := Φ.bound ‖s‖
  have hpa := absS_pos (𝔪 := 𝔪) hc
  refine Summable.of_norm_bounded
    (((GL.hS1 hG M hs).mul_left (B * absS 𝔪 c ^ (-s.re)))) fun u => ?_
  rw [norm_mul, RCLike.norm_conj, ψ.norm_one, mul_one]
  have h1 := hB s le_rfl c (c * u.out)
  have e : normS 𝔪 c (c * u.out) = absS 𝔪 c * normS 𝔪 1 u.out := by
    rw [← normS_mul_left, mul_one]
  rw [e, Real.mul_rpow hpa.le (normS_nonneg _ _)] at h1
  exact h1.trans (le_of_eq (by ring))

theorem lam_add (ψ : SfChar 𝔪) (hG : Good 𝔪) (Φ Φ' : GSection ι P 𝔪) (M : ℤ) {c : F}
    (hc : c ≠ 0) (ν : F) {s : ℂ} (hs : 1 < s.re) :
    lam ψ M (Φ + Φ') c ν s = lam ψ M Φ c ν s + lam ψ M Φ' c ν s := by
  have h1 := summable_jacTerm ψ hG Φ M hc ν hs
  have h2 := summable_jacTerm ψ hG Φ' M hc ν hs
  simp only [lam, jac, GSection.add_apply, add_mul]
  rw [h1.tsum_add h2]
  ring

theorem valid_add {ψ : SfChar 𝔪} {Φ Φ' : GSection ι P 𝔪} {ν : F}
    {k : HeightOneSpectrum (𝓞 F) → ℤ} (h : Valid ψ Φ ν k) (h' : Valid ψ Φ' ν k) :
    Valid ψ (Φ + Φ') ν k :=
  ⟨fun b hb s c d => by rw [GSection.add_apply, GSection.add_apply, h.1 b hb, h'.1 b hb], h.2⟩

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

/-- A uniform depth valid for two sections at once. -/
theorem exists_valid₂ (ψ : SfChar 𝔪) (hG : Good 𝔪) (Φ Φ' : GSection ι P 𝔪) (ν : F) :
    ∃ M : ℤ, Valid ψ Φ ν (fun _ => M) ∧ Valid ψ Φ' ν (fun _ => M) :=
  ⟨max (depth ψ hG Φ ν) (depth ψ hG Φ' ν),
    (valid_depth ψ hG Φ ν).mono fun _ _ => le_max_left _ _,
    (valid_depth ψ hG Φ' ν).mono fun _ _ => le_max_right _ _⟩

/-- `Lam` is additive in the section for `Re s > 1`. -/
theorem Lam_add (ψ : SfChar 𝔪) (hG : Good 𝔪) (Φ Φ' : GSection ι P 𝔪) {c : F} (hc : c ≠ 0)
    (ν : F) {s : ℂ} (hs : 1 < s.re) :
    Lam ψ hG (Φ + Φ') c ν s = Lam ψ hG Φ c ν s + Lam ψ hG Φ' c ν s := by
  obtain ⟨M, h1, h2⟩ := exists_valid₂ ψ hG Φ Φ' ν
  rw [Lam_eq_lam ψ hG _ (valid_add h1 h2), Lam_eq_lam ψ hG _ h1, Lam_eq_lam ψ hG _ h2,
    lam_add ψ hG Φ Φ' M hc ν hs]

theorem Lam_zero (ψ : SfChar 𝔪) (hG : Good 𝔪) (c ν : F) (s : ℂ) :
    Lam ψ hG (0 : GSection ι P 𝔪) c ν s = 0 := by
  simp [Lam, lam, jac]

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

theorem Lam_sum (ψ : SfChar 𝔪) (hG : Good 𝔪) {α : Type*} (T : Finset α)
    (f : α → GSection ι P 𝔪) {c : F} (hc : c ≠ 0) (ν : F) {s : ℂ} (hs : 1 < s.re) :
    Lam ψ hG (∑ i ∈ T, f i) c ν s = ∑ i ∈ T, Lam ψ hG (f i) c ν s := by
  classical
  induction T using Finset.induction_on with
  | empty => simp [Lam_zero]
  | insert a T ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, Lam_add ψ hG _ _ hc ν hs, ih]

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

theorem torusT_sum (hG : Good 𝔪) {α : Type*} (T : Finset α) (f : α → GSection ι P 𝔪) {β : F}
    (hβ : β ≠ 0) :
    (∑ i ∈ T, f i).torusT hG β hβ = ∑ i ∈ T, (f i).torusT hG β hβ := by
  ext s c d
  simp only [GSection.torusT_apply, GSection.sum_apply, Finset.mul_sum]

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

/-- (K4) `𝒦_{n(t)Φ}(β) = ψ(βt) 𝒦_Φ(β)`. -/
theorem Kt_nT (ψ : SfChar 𝔪) (hG : Good 𝔪) (Φ : GSection ι P 𝔪) (t : F) (β η : F) (s : ℂ) :
    Kt ψ hG (Φ.nT hG t) β η s = ψ (β * t) * Kt ψ hG Φ β η s := by
  by_cases hβ : β = 0
  · simp [Kt, hβ]
  rw [Kt_of_ne ψ hG _ hβ, Kt_of_ne ψ hG _ hβ, torusT_nT hG Φ hβ, Lam_nT, one_mul]

/-- (K4) `𝒦_{h•Φ} = h(s) 𝒦_Φ`. -/
theorem Kt_smulFun (ψ : SfChar 𝔪) (hG : Good 𝔪) (Φ : GSection ι P 𝔪) (f : ℂ → ℂ)
    (hf : Differentiable ℂ f) (β η : F) (s : ℂ) :
    Kt ψ hG (GSection.smulFun f hf Φ) β η s = f s * Kt ψ hG Φ β η s := by
  by_cases hβ : β = 0
  · simp [Kt, hβ]
  rw [Kt_of_ne ψ hG _ hβ, Kt_of_ne ψ hG _ hβ, torusT_smulFun hG Φ hβ, Lam_smulFun]

theorem Kt_smul (ψ : SfChar 𝔪) (hG : Good 𝔪) (Φ : GSection ι P 𝔪) (a : ℂ) (β η : F) (s : ℂ) :
    Kt ψ hG (a • Φ) β η s = a * Kt ψ hG Φ β η s :=
  Kt_smulFun ψ hG Φ _ _ β η s

theorem Kt_sum (ψ : SfChar 𝔪) (hG : Good 𝔪) {α : Type*} (T : Finset α)
    (f : α → GSection ι P 𝔪) (β : F) {η : F} (hη : η ≠ 0) {s : ℂ} (hs : 1 < s.re) :
    Kt ψ hG (∑ i ∈ T, f i) β η s = ∑ i ∈ T, Kt ψ hG (f i) β η s := by
  by_cases hβ : β = 0
  · simp [Kt, hβ]
  simp only [Kt_of_ne ψ hG _ hβ]
  rw [torusT_sum hG T f hβ, Lam_sum ψ hG T _ hη 1 hs]

/-- (G2) the additive projection multiplies the Kirillov term by `Σ_t ϕ(t) ψ(βt)`. -/
theorem Kt_addProj (ψ : SfChar 𝔪) (hG : Good 𝔪) (Φ : GSection ι P 𝔪) (T : Finset F)
    (ϕ : F → ℂ) (β : F) {η : F} (hη : η ≠ 0) {s : ℂ} (hs : 1 < s.re) :
    Kt ψ hG (Φ.addProj hG T ϕ) β η s = (∑ t ∈ T, ϕ t * ψ (β * t)) * Kt ψ hG Φ β η s := by
  rw [GSection.addProj, Kt_sum ψ hG T _ β hη hs, Finset.sum_mul]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Kt_smul, Kt_nT]
  ring

/-! ### The cusp change for `Lam` and for the Kirillov term -/

/-! ### The normalized term `ξ^η = |β|^{1/3} Kt(·, 4/3)` -/

end ArtinKP.G1
end
end

section
-- module Solutions.Artin.KP.G1_DS
attribute [-instance] _root_.ArtinKP.B1.PairClass.instNonempty _root_.ArtinKP.N2.levelGroup_finiteIndex _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-!
# WP-G1, part 3: Lemma DS (diagonal smoothness) and the class decomposition of `Lam`

* `exists_split`: for `ρ ∈ F^×` an `e ∈ F`, `S_f`-integral, with `e/ρ` and `ρ(1-e)` `S_f`-integral
  (Chinese remainder theorem at the places of `S_f`).
* `GSection.exists_diag` — **Lemma DS** (MATH3 §4.3): for every genuine section `Φ` there is `N`
  with `Φ_s(ac, bd) = Φ_s(c, d)` whenever `a, b ∈ 1 + 𝔩_N`.
  Consequences: `exists_torusT_deep` ((K1) for all sections: `Ã(u)Φ = Φ` for deep `u`).
* `LamDeep ψ hG Ψ N`: `Lam Ψ (uη) = Lam Ψ η` for `u ∈ 1 + 𝔩_N`; `exists_lamDeep` (every section,
  all large `N`), `exists_lamDeep_torusT` (one level for all `Ã(β)Φ`, `β ∈ F^×`).
* `Lam_class`: `Lam Ψ c ν s = ⟨η, c⟩ Lam Ψ η ν s` for `c` in the class of `η`
  (`InClass 𝔪 N η c`, `N` deep, `Ψ` `LamDeep` at `N`).
* `Lam_bigCell`: `Lam` of a big-cell section at any `c`.
* `Lam_classDecomp` — **(CD)** at the level of `Lam`: for a complete system `T` of pairwise
  disjoint classes (`RO.exists_classReps`),
  `Lam Φ c ν s = Σ_{η ∈ T} Lam Φ η ν s · vol(𝔩_M)⁻¹ · Lam (bigCell_{η,M,0}) c ν s`.
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

/-! ### An `S_f`-adic partition of unity -/

theorem val_le_of_mem_pow (v : HeightOneSpectrum (𝓞 F)) (n : ℕ) {y : 𝓞 F}
    (hy : y ∈ v.asIdeal ^ n) : v.valuation F (algebraMap (𝓞 F) F y) ≤ WithZero.exp (-(n : ℤ)) := by
  rw [HeightOneSpectrum.valuation_of_algebraMap]
  exact (v.intValuation_le_pow_iff_mem y n).mpr hy

/-- For `ρ ≠ 0` there is `e ∈ F` with `e`, `e/ρ`, `ρ(1-e)` all integral at the places of `S_f`. -/
theorem exists_split (h𝔪 : 𝔪 ≠ ⊥) {ρ : F} (hρ : ρ ≠ 0) :
    ∃ e : F, ∀ v : HeightOneSpectrum (𝓞 F), 𝔪 ≤ v.asIdeal →
      v.valuation F e ≤ 1 ∧ v.valuation F (e / ρ) ≤ 1 ∧ v.valuation F (ρ * (1 - e)) ≤ 1 := by
  classical
  set n : ℕ := (CubicPkg.sFin 𝔪).sup fun v => (ordv v ρ).natAbs with hn
  obtain ⟨y, hy⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal
    (s := CubicPkg.sFin 𝔪) (fun v : HeightOneSpectrum (𝓞 F) => v.asIdeal) (fun _ => n)
    (fun v _ => v.prime) (fun v _ w _ hvw h => hvw (HeightOneSpectrum.ext h))
    (fun v => if v.1.valuation F ρ ≤ 1 then (0 : 𝓞 F) else 1)
  refine ⟨algebraMap (𝓞 F) F y, fun v hv => ?_⟩
  have hvs := (CubicPkg.mem_sFin h𝔪 v).mpr hv
  have hnv : (ordv v ρ).natAbs ≤ n := Finset.le_sup (f := fun v => (ordv v ρ).natAbs) hvs
  have he1 : v.valuation F (algebraMap (𝓞 F) F y) ≤ 1 :=
    HeightOneSpectrum.valuation_le_one (K := F) v y
  have h1e : v.valuation F (1 - algebraMap (𝓞 F) F y) ≤ 1 := by
    have := HeightOneSpectrum.valuation_le_one (K := F) v (1 - y)
    simpa using this
  have hyv := hy v hvs
  refine ⟨he1, ?_, ?_⟩
  · by_cases h : v.valuation F ρ ≤ 1
    · simp only [h, if_true, sub_zero] at hyv
      have h2 := val_le_of_mem_pow v n hyv
      rw [map_div₀, val_eq_exp_ordv v hρ, div_eq_mul_inv, ← WithZero.exp_neg]
      refine (mul_le_mul' h2 le_rfl).trans ?_
      rw [← WithZero.exp_add, ← WithZero.exp_zero, WithZero.exp_le_exp]
      omega
    · have h' : 1 ≤ v.valuation F ρ := le_of_lt (not_le.mp h)
      rw [map_div₀]
      exact div_le_one_of_le₀ (he1.trans h') zero_le
  · by_cases h : v.valuation F ρ ≤ 1
    · rw [map_mul]
      exact mul_le_one' h h1e
    · simp only [h, if_false] at hyv
      have h2 := val_le_of_mem_pow v n hyv
      rw [map_sub, map_one] at h2
      have h3 : v.valuation F (1 - algebraMap (𝓞 F) F y) ≤ WithZero.exp (-(n : ℤ)) := by
        rw [← Valuation.map_neg, neg_sub]
        exact h2
      rw [map_mul, val_eq_exp_ordv v hρ]
      refine (mul_le_mul' le_rfl h3).trans ?_
      rw [← WithZero.exp_add, ← WithZero.exp_zero, WithZero.exp_le_exp]
      omega

theorem small_zero_of_val {y : F}
    (h : ∀ v : HeightOneSpectrum (𝓞 F), 𝔪 ≤ v.asIdeal → v.valuation F y ≤ 1) : Small 𝔪 0 y :=
  fun v hv => by simpa using h v hv

theorem small_mul_int {N : ℤ} {x y : F} (hx : Small 𝔪 N x)
    (hy : ∀ v : HeightOneSpectrum (𝓞 F), 𝔪 ≤ v.asIdeal → v.valuation F y ≤ 1) :
    Small 𝔪 N (x * y) := by
  have := hx.mul (small_zero_of_val hy)
  rwa [add_zero] at this

/-! ### Lemma DS -/

/-- **Lemma DS (diagonal smoothness).**  Every genuine section is invariant under
`(c, d) ↦ (ac, bd)` for `a, b` in a deep neighbourhood of `1` at `S_f`. -/
theorem GSection.exists_diag (hG : Good 𝔪) (Φ : GSection ι P 𝔪) :
    ∃ N : ℕ, ∀ a b : F, Small 𝔪 N (a - 1) → Small 𝔪 N (b - 1) →
      ∀ (s : ℂ) (c d : F), Φ s (a * c) (b * d) = Φ s c d := by
  obtain ⟨N₀, hN₀1, hN₀⟩ := P.exists_isDeepLevel hG.ne_bot
  obtain ⟨N, hNle, hN⟩ := Φ.level_ge N₀
  obtain ⟨v₀, hv₀⟩ := hG.exists_place
  refine ⟨N, fun a b ha hb s c d => ?_⟩
  have hN1 : (1 : ℤ) ≤ N := by exact_mod_cast hN₀1.trans hNle
  have hNN : (N₀ : ℤ) ≤ N := by exact_mod_cast hNle
  have hva := fun v hv => ha.val_eq_one hN1 v hv
  have hvb := fun v hv => hb.val_eq_one hN1 v hv
  have ha0 : a ≠ 0 := by
    intro h; have := hva v₀ hv₀; rw [h, map_zero] at this; exact zero_ne_one this
  have hb0 : b ≠ 0 := by
    intro h; have := hvb v₀ hv₀; rw [h, map_zero] at this; exact zero_ne_one this
  have hvai : ∀ v : HeightOneSpectrum (𝓞 F), 𝔪 ≤ v.asIdeal → v.valuation F a⁻¹ ≤ 1 :=
    fun v hv => by rw [map_inv₀, hva v hv, inv_one]
  have hvbi : ∀ v : HeightOneSpectrum (𝓞 F), 𝔪 ≤ v.asIdeal → v.valuation F b⁻¹ ≤ 1 :=
    fun v hv => by rw [map_inv₀, hvb v hv, inv_one]
  have hal : ∀ y, brk ι P 𝔪 a y = 1 := fun y => brk_deep_left hG hN₀ y (ha.mono hNN)
  have hbl : ∀ y, brk ι P 𝔪 b y = 1 := fun y => brk_deep_left hG hN₀ y (hb.mono hNN)
  have hδ : Small 𝔪 N (a * b - 1) := Small.deep_mul hN1 ha hb
  by_cases hc : c = 0
  · -- the cell `c = 0`: `k = diag(b⁻¹, b)`
    by_cases hd : d = 0
    · rw [hc, hd, mul_zero, mul_zero]
    have hK : IsK 𝔪 N b⁻¹ 0 0 b :=
      ⟨by field_simp; ring, Small.deep_inv hN1 hb, Small.zero, Small.zero, hb⟩
    have h := hN _ _ _ _ hK s c d
    have hsig : sig ι P 𝔪 c d b⁻¹ 0 0 b = 1 := by
      rw [sig, hc]
      simp only [zero_mul, mul_zero, zero_add, add_zero, Xs_zero]
      rw [show d * b / d = b by field_simp, hbl]
    rw [hsig, one_mul, hc] at h
    rw [hc, mul_zero, ← h]
    congr 1 <;> ring
  by_cases hd : d = 0
  · -- the cell `d = 0`: `k = diag(a, a⁻¹)`
    have hK : IsK 𝔪 N a 0 0 a⁻¹ :=
      ⟨by field_simp; ring, ha, Small.zero, Small.zero, Small.deep_inv hN1 ha⟩
    have h := hN _ _ _ _ hK s c d
    have hsig : sig ι P 𝔪 c d a 0 0 a⁻¹ = 1 := by
      rw [sig, hd]
      simp only [zero_mul, mul_zero, zero_add, add_zero]
      rw [Xs_of_ne _ (mul_ne_zero hc ha0), Xs_of_ne _ hc, show c * a / c = a by field_simp, hal]
    rw [hsig, one_mul, hd] at h
    rw [hd, mul_zero, ← h]
    congr 1 <;> ring
  -- the generic cell
  set ρ : F := d / c with hρ
  have hρ0 : ρ ≠ 0 := div_ne_zero hd hc
  obtain ⟨e, he⟩ := exists_split hG.ne_bot hρ0
  set δ : F := a * b - 1 with hδdef
  have h1e : ∀ v : HeightOneSpectrum (𝓞 F), 𝔪 ≤ v.asIdeal → v.valuation F (1 - e) ≤ 1 :=
    fun v hv => by
      refine (Valuation.map_sub _ _ _).trans (max_le ?_ (he v hv).1)
      rw [map_one]
  have hK : IsK 𝔪 N (a - δ * e * b⁻¹) (δ * (ρ * (1 - e)) * a⁻¹) (δ * (e / ρ) * b⁻¹)
      (b - δ * (1 - e) * a⁻¹) := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [hδdef]; field_simp; ring
    · rw [show a - δ * e * b⁻¹ - 1 = (a - 1) - δ * e * b⁻¹ by ring]
      exact ha.sub (small_mul_int (small_mul_int hδ fun v hv => (he v hv).1) hvbi)
    · exact small_mul_int (small_mul_int hδ fun v hv => (he v hv).2.2) hvai
    · exact small_mul_int (small_mul_int hδ fun v hv => (he v hv).2.1) hvbi
    · rw [show b - δ * (1 - e) * a⁻¹ - 1 = (b - 1) - δ * (1 - e) * a⁻¹ by ring]
      exact hb.sub (small_mul_int (small_mul_int hδ h1e) hvai)
  have h := hN _ _ _ _ hK s c d
  have e1 : c * (a - δ * e * b⁻¹) + d * (δ * (e / ρ) * b⁻¹) = a * c := by
    rw [hρ]; field_simp; ring
  have e2 : c * (δ * (ρ * (1 - e)) * a⁻¹) + d * (b - δ * (1 - e) * a⁻¹) = b * d := by
    rw [hρ]; field_simp; ring
  have hsig : sig ι P 𝔪 c d (a - δ * e * b⁻¹) (δ * (ρ * (1 - e)) * a⁻¹) (δ * (e / ρ) * b⁻¹)
      (b - δ * (1 - e) * a⁻¹) = 1 := by
    rw [sig, e1, e2, Xs_of_ne _ (mul_ne_zero ha0 hc), Xs_of_ne _ hc,
      show a * c / c = a by field_simp, hal]
  rw [e1, e2, hsig, one_mul] at h
  exact h

/-- **(K1) for every section**: `Ã(u)Φ = Φ` for `u` in a deep neighbourhood of `1`. -/
theorem exists_torusT_deep (hG : Good 𝔪) (Φ : GSection ι P 𝔪) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ (u : F) (hu : u ≠ 0), Small 𝔪 N (u - 1) → Φ.torusT hG u hu = Φ := by
  obtain ⟨N₀, hN₀1, hN₀⟩ := P.exists_isDeepLevel hG.ne_bot
  obtain ⟨N₁, hN₁⟩ := GSection.exists_diag hG Φ
  refine ⟨max N₀ N₁, hN₀1.trans (le_max_left _ _), fun u hu hsm => ?_⟩
  have h0 : Small 𝔪 N₀ (u - 1) := hsm.mono (by exact_mod_cast le_max_left N₀ N₁)
  have h1 : Small 𝔪 N₁ (u - 1) := hsm.mono (by exact_mod_cast le_max_right N₀ N₁)
  have hN₀1' : (1 : ℤ) ≤ N₀ := by exact_mod_cast hN₀1
  have hN1' : (1 : ℤ) ≤ ((max N₀ N₁ : ℕ) : ℤ) := by exact_mod_cast hN₀1.trans (le_max_left _ _)
  have h2 : Small 𝔪 N₁ (u ^ 2 - 1) := by
    rw [pow_two]
    exact (Small.deep_mul hN1' hsm hsm).mono (by exact_mod_cast le_max_right N₀ N₁)
  ext s c d
  rw [GSection.torusT_apply, hN₁ _ _ h2 h1]
  have habs : absS 𝔪 u = 1 := absS_eq_one_of_val hG.ne_bot (fun v hv => h0.val_eq_one hN₀1' v hv)
  have htf : tf ι P 𝔪 u c d = 1 := by
    unfold tf
    split_ifs
    · exact brk_deep_right hG hN₀ _ h0
    · rw [brk_deep_right hG hN₀ _ h0, one_pow]
  rw [habs, htf, Complex.ofReal_one, Complex.one_cpow, one_mul, one_mul]

/-! ### `Lam` on a class -/

/-! ### Big cells -/

end ArtinKP.G1
end
end

section
-- module Solutions.Artin.KP.G1_Dual
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
attribute [-simp] _root_.ArtinKP.B.coe_latREquiv _root_.ArtinKP.B.embR_apply
/-!
# WP-G1, part 4: Lemma DUAL — the dual lattice of `ψ_{S_f} = B.psiS` is bounded

* `exists_trace_clear`: the trace dual `𝓞^∨` is a fractional ideal (Mathlib's
  `FractionalIdeal.dual ℤ ℚ 1`): one `a ≠ 0` with `a z ∈ 𝓞` whenever `Tr(z 𝓞) ⊂ ℤ`.
* `exists_pole`: for a prime `v₀` and `d`, an element of `F` with a pole of order exactly `d` at
  `v₀` and integral at all other finite places.
* `exists_idem`: an integer `≡ 1` at `v₀` and `≡ 0` at the other places of `S_f`, modulo `n`-th
  powers.
* `psiS_dual` — **Lemma DUAL** (MATH3 §4.4): there is `d₀` such that for all `M`, `β`:
  `ψ(β 𝔩_M) = 1 → β ∈ 𝔩_{-M-d₀}`.
  `Adual ψ M β` is the predicate "`ψ(β·)` is trivial on `𝔩_M`" (the dual lattice `A_M`);
  `HasDual ψ d₀` is the conclusion of DUAL for an arbitrary `SfChar`, the form in which the other
  files use it.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

open scoped ComplexConjugate nonZeroDivisors
open NumberField IsDedekindDomain ArtinPrimitiveRoots

noncomputable section

namespace ArtinKP.G1

open ArtinKP.A ArtinKP.S ArtinKP.S2

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}

/-! ### The trace dual is a fractional ideal -/

theorem exists_trace_clear (F : Type*) [Field F] [NumberField F] :
    ∃ a : 𝓞 F, a ≠ 0 ∧ ∀ z : F,
      (∀ w : 𝓞 F, ∃ n : ℤ, Algebra.trace ℚ F (z * algebraMap (𝓞 F) F w) = (n : ℚ)) →
      ∃ b : 𝓞 F, algebraMap (𝓞 F) F a * z = algebraMap (𝓞 F) F b := by
  obtain ⟨a, ha, h⟩ := (FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 F)⁰ F)).isFractional
  refine ⟨a, nonZeroDivisors.ne_zero ha, fun z hz => ?_⟩
  have hmem : z ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 F)⁰ F) := by
    rw [FractionalIdeal.mem_dual (one_ne_zero' (FractionalIdeal (𝓞 F)⁰ F))]
    intro x hx
    obtain ⟨w, rfl⟩ := (FractionalIdeal.mem_one_iff (𝓞 F)⁰).mp hx
    obtain ⟨n, hn⟩ := hz w
    refine ⟨n, ?_⟩
    rw [Algebra.traceForm_apply, hn]
    simp
  obtain ⟨b, hb⟩ := h z hmem
  exact ⟨b, by rw [hb, Algebra.smul_def]⟩

/-! ### Elements with prescribed local behaviour -/

/-- An element with a pole of order exactly `d` at `v₀`, integral at every other finite place. -/
theorem exists_pole (v₀ : HeightOneSpectrum (𝓞 F)) (d : ℕ) :
    ∃ z : F, v₀.valuation F z = WithZero.exp (d : ℤ) ∧
      ∀ v : HeightOneSpectrum (𝓞 F), v ≠ v₀ → v.valuation F z ≤ 1 := by
  classical
  obtain ⟨π, hπ⟩ := v₀.intValuation_exists_uniformizer
  have hπ0 : π ≠ 0 := by
    rintro rfl
    rw [map_zero] at hπ
    exact WithZero.exp_ne_zero hπ.symm
  set a : 𝓞 F := π ^ d with ha
  have ha0 : a ≠ 0 := pow_ne_zero d hπ0
  have haF : algebraMap (𝓞 F) F a ≠ 0 := by
    rwa [Ne, FaithfulSMul.algebraMap_eq_zero_iff]
  have hva : v₀.valuation F (algebraMap (𝓞 F) F a) = WithZero.exp (-(d : ℤ)) := by
    rw [HeightOneSpectrum.valuation_of_algebraMap, ha, map_pow, hπ, ← WithZero.exp_nsmul]
    simp
  have hfin : {v : HeightOneSpectrum (𝓞 F) | v.asIdeal ∣ Ideal.span {a}}.Finite :=
    Ideal.finite_factors (by simpa using ha0)
  set T : Finset (HeightOneSpectrum (𝓞 F)) := insert v₀ hfin.toFinset with hT
  set e : ℕ := 1 + T.sup (fun w => (ordv w (algebraMap (𝓞 F) F a)).natAbs) with he
  obtain ⟨c, hc⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal
    (s := T) (fun v : HeightOneSpectrum (𝓞 F) => v.asIdeal) (fun _ => e)
    (fun v _ => v.prime) (fun v _ w _ hvw h => hvw (HeightOneSpectrum.ext h))
    (fun v => if v.1 = v₀ then (1 : 𝓞 F) else 0)
  have hv₀T : v₀ ∈ T := Finset.mem_insert_self _ _
  have he1 : (1 : ℤ) ≤ e := by rw [he]; push_cast; omega
  have hc0 : v₀.valuation F (algebraMap (𝓞 F) F c) = 1 := by
    have h1 := hc v₀ hv₀T
    simp only [if_true] at h1
    have h2 := val_le_of_mem_pow v₀ e h1
    rw [map_sub, map_one] at h2
    have h3 : v₀.valuation F (algebraMap (𝓞 F) F c - 1) < 1 := by
      refine h2.trans_lt ?_
      rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
      omega
    have := Valuation.map_one_add_of_lt (v := v₀.valuation F) h3
    rwa [add_sub_cancel] at this
  refine ⟨algebraMap (𝓞 F) F c / algebraMap (𝓞 F) F a, ?_, fun v hv => ?_⟩
  · rw [map_div₀, hc0, hva, one_div, ← WithZero.exp_neg, neg_neg]
  · rw [map_div₀]
    by_cases hmem : v ∈ hfin.toFinset
    · have hvT : v ∈ T := Finset.mem_insert_of_mem hmem
      have h1 := hc v hvT
      simp only [hv, if_false, sub_zero] at h1
      have h2 := val_le_of_mem_pow v e h1
      have hle : (ordv v (algebraMap (𝓞 F) F a)).natAbs ≤ T.sup
          (fun w => (ordv w (algebraMap (𝓞 F) F a)).natAbs) :=
        Finset.le_sup (f := fun w => (ordv w (algebraMap (𝓞 F) F a)).natAbs) hvT
      rw [val_eq_exp_ordv v haF, div_eq_mul_inv, ← WithZero.exp_neg]
      refine (mul_le_mul' h2 le_rfl).trans ?_
      rw [← WithZero.exp_add, ← WithZero.exp_zero, WithZero.exp_le_exp, he]
      push_cast
      omega
    · have hnd : ¬ v.asIdeal ∣ Ideal.span {a} := fun h => hmem (hfin.mem_toFinset.mpr h)
      have h1 : v.valuation F (algebraMap (𝓞 F) F a) = 1 := by
        rw [HeightOneSpectrum.valuation_of_algebraMap]
        refine le_antisymm (v.intValuation_le_one a) (not_lt.mp fun hlt => hnd ?_)
        exact (v.intValuation_lt_one_iff_dvd a).mp hlt
      rw [h1, div_one]
      exact HeightOneSpectrum.valuation_le_one (K := F) v c

/-- An integer `≡ 1` at `v₀` and `≡ 0` at the other places of `S_f`, to the precision `n`. -/
theorem exists_idem (h𝔪 : 𝔪 ≠ ⊥) (v₀ : HeightOneSpectrum (𝓞 F)) (hv₀ : 𝔪 ≤ v₀.asIdeal) (n : ℕ) :
    ∃ e : 𝓞 F, v₀.valuation F (algebraMap (𝓞 F) F e - 1) ≤ WithZero.exp (-(n : ℤ)) ∧
      ∀ v : HeightOneSpectrum (𝓞 F), 𝔪 ≤ v.asIdeal → v ≠ v₀ →
        v.valuation F (algebraMap (𝓞 F) F e) ≤ WithZero.exp (-(n : ℤ)) := by
  classical
  obtain ⟨e, he⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal
    (s := CubicPkg.sFin 𝔪) (fun v : HeightOneSpectrum (𝓞 F) => v.asIdeal) (fun _ => n)
    (fun v _ => v.prime) (fun v _ w _ hvw h => hvw (HeightOneSpectrum.ext h))
    (fun v => if v.1 = v₀ then (1 : 𝓞 F) else 0)
  refine ⟨e, ?_, fun v hv hne => ?_⟩
  · have h1 := he v₀ ((CubicPkg.mem_sFin h𝔪 v₀).mpr hv₀)
    simp only [if_true] at h1
    have h2 := val_le_of_mem_pow v₀ n h1
    rwa [map_sub, map_one] at h2
  · have h1 := he v ((CubicPkg.mem_sFin h𝔪 v).mpr hv)
    simp only [hne, if_false, sub_zero] at h1
    exact val_le_of_mem_pow v n h1

/-! ### Lemma DUAL -/

/-- `ψ_{S_f}` on an `S`-integer `x`: `ψ(x) = 1` forces `Tr x ∈ ℤ`. -/
theorem trace_int_of_psiS_eq_one [IsTotallyComplex F] (h𝔪 : 𝔪 ≠ ⊥) {x : F}
    (hx : x ∈ (placesOf 𝔪).integer F) (h : B.psiS h𝔪 x = 1) :
    ∃ n : ℤ, Algebra.trace ℚ F x = (n : ℚ) := by
  rw [B.psiS_apply, C3B.sAddChar_of_mem x hx, one_mul, B.eInf_emb] at h
  have h' := congrArg conj h
  rw [Complex.conj_conj, map_one, Complex.exp_eq_one_iff] at h'
  obtain ⟨n, hn⟩ := h'
  refine ⟨-n, ?_⟩
  have h2 : ((Algebra.trace ℚ F x : ℚ) : ℂ) = ((-n : ℤ) : ℂ) := by
    have hpi : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
      simp [Real.pi_ne_zero, Complex.I_ne_zero]
    apply mul_left_cancel₀ hpi
    push_cast
    linear_combination -hn
  exact_mod_cast h2

/-- **Lemma DUAL** (MATH3 §4.4): the dual lattices of `ψ_{S_f}` are bounded, uniformly:
`ψ(β 𝔩_M) = 1 → β ∈ 𝔩_{-M-d₀}`. -/
theorem psiS_dual [IsTotallyComplex F] (h𝔪 : 𝔪 ≠ ⊥) : ∃ d₀ : ℤ, HasDual (B.psiS h𝔪) d₀ := by
  classical
  obtain ⟨a, ha0, ha⟩ := exists_trace_clear F
  have haF : algebraMap (𝓞 F) F a ≠ 0 := by
    rwa [Ne, FaithfulSMul.algebraMap_eq_zero_iff]
  set d₀ : ℕ := 1 + (CubicPkg.sFin 𝔪).sup (fun v => (ordv v (algebraMap (𝓞 F) F a)).natAbs)
    with hd₀
  refine ⟨d₀, fun M β hβ v₀ hv₀ => ?_⟩
  by_contra hlt
  rw [not_le] at hlt
  have hβ0 : β ≠ 0 := by
    rintro rfl
    rw [map_zero] at hlt
    exact not_lt_zero hlt
  rw [val_eq_exp_ordv v₀ hβ0, WithZero.exp_lt_exp] at hlt
  have hv₀s := (CubicPkg.mem_sFin h𝔪 v₀).mpr hv₀
  have hle₀ : (ordv v₀ (algebraMap (𝓞 F) F a)).natAbs
      ≤ (CubicPkg.sFin 𝔪).sup (fun v => (ordv v (algebraMap (𝓞 F) F a)).natAbs) :=
    Finset.le_sup (f := fun v => (ordv v (algebraMap (𝓞 F) F a)).natAbs) hv₀s
  obtain ⟨z, hz₀, hz⟩ := exists_pole v₀ d₀
  -- some integer multiple of `z` has non-integral trace
  have hw : ∃ w : 𝓞 F, ∀ n : ℤ, Algebra.trace ℚ F (z * algebraMap (𝓞 F) F w) ≠ (n : ℚ) := by
    by_contra hcon
    push Not at hcon
    obtain ⟨b, hb⟩ := ha z hcon
    have h1 : v₀.valuation F (algebraMap (𝓞 F) F a * z) ≤ 1 := by
      rw [hb]
      exact HeightOneSpectrum.valuation_le_one (K := F) v₀ b
    rw [map_mul, hz₀, val_eq_exp_ordv v₀ haF, ← WithZero.exp_add, ← WithZero.exp_zero,
      WithZero.exp_le_exp, hd₀] at h1
    push_cast at h1
    omega
  obtain ⟨w, hw⟩ := hw
  set n : ℕ := max d₀ ((CubicPkg.sFin 𝔪).sup fun v => (M + ordv v β).toNat) with hn
  obtain ⟨e, he₀, he⟩ := exists_idem h𝔪 v₀ hv₀ n
  set zw : F := z * algebraMap (𝓞 F) F w with hzw
  have hwv : ∀ v : HeightOneSpectrum (𝓞 F), v.valuation F (algebraMap (𝓞 F) F w) ≤ 1 :=
    fun v => HeightOneSpectrum.valuation_le_one (K := F) v w
  have hev : ∀ v : HeightOneSpectrum (𝓞 F), v.valuation F (algebraMap (𝓞 F) F e) ≤ 1 :=
    fun v => HeightOneSpectrum.valuation_le_one (K := F) v e
  have hzw₀ : v₀.valuation F zw ≤ WithZero.exp (d₀ : ℤ) := by
    rw [hzw, map_mul, hz₀]
    exact mul_le_of_le_one_right' (hwv v₀)
  have hzwv : ∀ v : HeightOneSpectrum (𝓞 F), v ≠ v₀ → v.valuation F zw ≤ 1 := fun v hv => by
    rw [hzw, map_mul]
    exact mul_le_one' (hz v hv) (hwv v)
  -- `h := zw · e / β ∈ 𝔩_M`
  have hsmall : Small 𝔪 M (zw * algebraMap (𝓞 F) F e / β) := by
    intro v hv
    rw [map_div₀, map_mul, val_eq_exp_ordv v hβ0, div_eq_mul_inv, ← WithZero.exp_neg, neg_neg]
    by_cases hvv : v = v₀
    · subst hvv
      refine (mul_le_mul' (mul_le_mul' hzw₀ (hev v)) le_rfl).trans ?_
      rw [mul_one, ← WithZero.exp_add, WithZero.exp_le_exp]
      omega
    · have hvs := (CubicPkg.mem_sFin h𝔪 v).mpr hv
      have hle : (M + ordv v β).toNat ≤ (CubicPkg.sFin 𝔪).sup fun v => (M + ordv v β).toNat :=
        Finset.le_sup (f := fun v => (M + ordv v β).toNat) hvs
      have hnle : (M + ordv v β) ≤ n := by
        have h1 : (M + ordv v β) ≤ ((M + ordv v β).toNat : ℤ) := Int.self_le_toNat _
        have h2 : ((CubicPkg.sFin 𝔪).sup fun v => (M + ordv v β).toNat) ≤ n := le_max_right _ _
        omega
      refine (mul_le_mul' (mul_le_mul' (hzwv v hvv) (he v hv hvv)) le_rfl).trans ?_
      rw [one_mul, ← WithZero.exp_add, WithZero.exp_le_exp]
      omega
  have h1 := hβ _ hsmall
  rw [mul_div_cancel₀ _ hβ0] at h1
  -- `zw·e - zw ∈ 𝔩_0`
  have hdiff : Small 𝔪 0 (zw * (algebraMap (𝓞 F) F e - 1)) := by
    intro v hv
    rw [map_mul, neg_zero, WithZero.exp_zero]
    by_cases hvv : v = v₀
    · subst hvv
      refine (mul_le_mul' hzw₀ he₀).trans ?_
      rw [← WithZero.exp_add, ← WithZero.exp_zero, WithZero.exp_le_exp]
      have : (d₀ : ℤ) ≤ n := by exact_mod_cast le_max_left d₀ _
      omega
    · refine mul_le_one' (hzwv v hvv) ?_
      refine (Valuation.map_sub _ _ _).trans (max_le (hev v) ?_)
      rw [map_one]
  have h2 : B.psiS h𝔪 zw = 1 := by
    have e1 : zw * algebraMap (𝓞 F) F e = zw + zw * (algebraMap (𝓞 F) F e - 1) := by ring
    rw [e1, (B.psiS h𝔪).map_add, B.psiS_small h𝔪 hdiff, mul_one] at h1
    exact h1
  have hint : zw ∈ (placesOf 𝔪).integer F := fun v hv =>
    hzwv v (fun hvv => hv (by rw [hvv]; exact hv₀))
  obtain ⟨m, hm⟩ := trace_int_of_psiS_eq_one h𝔪 hint h2
  exact hw m hm

end ArtinKP.G1
end
end

section
-- module Solutions.Artin.KP.G1_FI
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
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

theorem SfChar.map_sub' (ψ : SfChar 𝔪) (x y : F) : ψ (x - y) = ψ x * conj (ψ y) := by
  rw [sub_eq_add_neg, ψ.map_add, SfChar.map_neg']

/-- `𝔩_{M₀ - J} ⊂ A_J` when `ψ` is trivial on `𝔩_{M₀}`. -/
theorem adual_of_small {ψ : SfChar 𝔪} {M₀ : ℤ} (hM₀ : ∀ x : F, Small 𝔪 M₀ x → ψ x = 1) (J : ℤ)
    {β : F} (hβ : Small 𝔪 (M₀ - J) β) : Adual ψ J β := fun h hh =>
  hM₀ _ (by have := hβ.mul hh; rwa [sub_add_cancel] at this)

theorem finite_Qt (h𝔪 : 𝔪 ≠ ⊥) {J M : ℤ} (hJM : J ≤ M) : Finite (Qt 𝔪 J M) := by
  have hcard := card_latD_quot h𝔪 (k := fun _ => J) (k' := fun _ => M) (fun _ _ => hJM)
  refine Nat.finite_of_card_ne_zero ?_
  rw [hcard]
  refine (Finset.prod_pos fun v _ => pow_pos ?_ _).ne'
  have := NumberField.HeightOneSpectrum.one_lt_absNorm v
  omega

/-- The value `ψ(β · q)` on a class `q ∈ 𝔩_J/𝔩_M` does not depend on the representative, for
`β ∈ A_M`. -/
theorem psi_out (ψ : SfChar 𝔪) {J M : ℤ} {β : F} (hβ : Adual ψ M β)
    (x : ↥(latD 𝔪 fun _ => J)) :
    ψ (β * ((QuotientAddGroup.mk x : Qt 𝔪 J M).out : F)) = ψ (β * (x : F)) := by
  obtain ⟨h, hh⟩ := QuotientAddGroup.mk_out_eq_add
    ((latD 𝔪 fun _ => M).addSubgroupOf (latD 𝔪 fun _ => J)) x
  rw [hh]
  have hsm : Small 𝔪 M ((h : ↥(latD 𝔪 fun _ => J)) : F) := h.2
  push_cast
  rw [mul_add, ψ.map_add, hβ _ hsm, mul_one]

/-- **Orthogonality**: `Σ_{t ∈ 𝔩_J/𝔩_M} ψ(βt) = [𝔩_J : 𝔩_M]` if `β ∈ A_J`, and `0` otherwise
(`β ∈ A_M`). -/
theorem sum_char (ψ : SfChar 𝔪) {J M : ℤ} [Fintype (Qt 𝔪 J M)] {β : F} (hβ : Adual ψ M β) :
    ∑ q : Qt 𝔪 J M, ψ (β * (q.out : F))
      = open Classical in if Adual ψ J β then (Fintype.card (Qt 𝔪 J M) : ℂ) else 0 := by
  classical
  by_cases hJ : Adual ψ J β
  · rw [if_pos hJ]
    have : ∀ q : Qt 𝔪 J M, ψ (β * (q.out : F)) = 1 := fun q => hJ _ q.out.2
    simp [this]
  · rw [if_neg hJ]
    unfold Adual at hJ
    push Not at hJ
    obtain ⟨t₀, ht₀, hne⟩ := hJ
    set x₀ : ↥(latD 𝔪 fun _ => J) := ⟨t₀, ht₀⟩ with hx₀
    set q₀ : Qt 𝔪 J M := QuotientAddGroup.mk x₀ with hq₀
    have hshift : ∀ q : Qt 𝔪 J M,
        ψ (β * ((q + q₀).out : F)) = ψ (β * (q.out : F)) * ψ (β * t₀) := by
      intro q
      induction q using QuotientAddGroup.induction_on with
      | H x =>
        rw [hq₀, ← QuotientAddGroup.mk_add, psi_out ψ hβ, psi_out ψ hβ]
        push_cast
        rw [mul_add, ψ.map_add]
    have h1 : ∑ q : Qt 𝔪 J M, ψ (β * ((q + q₀).out : F)) = ∑ q : Qt 𝔪 J M, ψ (β * (q.out : F)) :=
      Equiv.sum_comp (Equiv.addRight q₀) (fun q : Qt 𝔪 J M => ψ (β * (q.out : F)))
    simp only [hshift] at h1
    rw [← Finset.sum_mul] at h1
    have h2 : (∑ q : Qt 𝔪 J M, ψ (β * (q.out : F))) * (ψ (β * t₀) - 1) = 0 := by
      rw [mul_sub, h1, mul_one, sub_self]
    exact (mul_eq_zero.mp h2).resolve_right (sub_ne_zero.mpr hne)

/-- `A_J` has finite index in `A_M` (`J ≤ M`), given DUAL. -/
theorem finite_dualQuot (ψ : SfChar 𝔪) (h𝔪 : 𝔪 ≠ ⊥) {d₀ : ℤ} (hd : HasDual ψ d₀) {J M : ℤ} :
    Finite (↥(dualLat ψ M) ⧸ (dualLat ψ J).addSubgroupOf (dualLat ψ M)) := by
  obtain ⟨M₀, hM₀⟩ := ψ.cont
  set D₂ : ℤ := M₀ - J with hD₂
  set D₁ : ℤ := min (-M - d₀) D₂ with hD₁
  have h21 : (latD 𝔪 fun _ => D₂).relIndex (latD 𝔪 fun _ => D₁) ≠ 0 := by
    have hcard := card_latD_quot h𝔪 (k := fun _ => D₁) (k' := fun _ => D₂)
      (fun _ _ => min_le_right _ _)
    rw [AddSubgroup.relIndex, AddSubgroup.index_eq_card, hcard]
    refine (Finset.prod_pos fun v _ => pow_pos ?_ _).ne'
    have := NumberField.HeightOneSpectrum.one_lt_absNorm v
    omega
  have hle2 : (latD 𝔪 fun _ => D₂) ≤ dualLat ψ J := fun β hβ => adual_of_small hM₀ J hβ
  have hle1 : dualLat ψ M ≤ latD 𝔪 fun _ => D₁ := fun β hβ =>
    (hd M β hβ).mono (min_le_left _ _)
  have h3 : (dualLat ψ J).relIndex (latD 𝔪 fun _ => D₁) ≠ 0 := fun h0 =>
    h21 (AddSubgroup.relIndex_eq_zero_of_le_left hle2 h0)
  have h4 : (dualLat ψ J).relIndex (dualLat ψ M) ≠ 0 := fun h0 =>
    h3 (AddSubgroup.relIndex_eq_zero_of_le_right hle1 h0)
  have : ((dualLat ψ J).addSubgroupOf (dualLat ψ M)).FiniteIndex :=
    AddSubgroup.finiteIndex_iff.mpr h4
  infer_instance

/-- **Lemma FI (finite Fourier inversion)**, MATH3 §4.4.  Let `J ≤ M`.  A function on the dual
lattice `A_M` that is invariant under translation by `A_J` is a finite trigonometric polynomial in
`ψ` with frequencies in `𝔩_J`. -/
theorem exists_fourier (ψ : SfChar 𝔪) (h𝔪 : 𝔪 ≠ ⊥) {d₀ : ℤ} (hd : HasDual ψ d₀) {J M : ℤ}
    (hJM : J ≤ M) (f : F → ℂ)
    (hf : ∀ β a : F, Adual ψ M β → Adual ψ J a → f (β + a) = f β) :
    ∃ (T : Finset F) (ϕ : F → ℂ), (∀ t ∈ T, Small 𝔪 J t) ∧
      ∀ β : F, Adual ψ M β → ∑ t ∈ T, ϕ t * ψ (β * t) = f β := by
  classical
  have := finite_Qt (𝔪 := 𝔪) h𝔪 hJM
  have := finite_dualQuot (J := J) (M := M) ψ h𝔪 hd
  cases nonempty_fintype (Qt 𝔪 J M)
  cases nonempty_fintype (↥(dualLat ψ M) ⧸ (dualLat ψ J).addSubgroupOf (dualLat ψ M))
  set G := ↥(dualLat ψ M) ⧸ (dualLat ψ J).addSubgroupOf (dualLat ψ M) with hG
  set rep : Qt 𝔪 J M → F := fun q => (q.out : F) with hrep
  have hinj : Function.Injective rep := fun q q' h =>
    Quotient.out_injective (Subtype.val_injective h)
  have hcard0 : (Fintype.card (Qt 𝔪 J M) : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  set ϕ : F → ℂ := fun t => (Fintype.card (Qt 𝔪 J M) : ℂ)⁻¹ *
    ∑ g : G, f ((g.out : ↥(dualLat ψ M)) : F) * conj (ψ (((g.out : ↥(dualLat ψ M)) : F) * t))
    with hϕ
  refine ⟨Finset.univ.image rep, ϕ, fun t ht => ?_, fun β hβ => ?_⟩
  · obtain ⟨q, -, rfl⟩ := Finset.mem_image.mp ht
    exact q.out.2
  rw [Finset.sum_image fun q _ q' _ h => hinj h]
  -- the class of `β`
  set g₀ : G := QuotientAddGroup.mk (⟨β, hβ⟩ : ↥(dualLat ψ M)) with hg₀
  have hterm : ∀ g : G, ∑ q : Qt 𝔪 J M,
      conj (ψ (((g.out : ↥(dualLat ψ M)) : F) * rep q)) * ψ (β * rep q)
        = if g = g₀ then (Fintype.card (Qt 𝔪 J M) : ℂ) else 0 := by
    intro g
    have hmem : Adual ψ M (β - ((g.out : ↥(dualLat ψ M)) : F)) :=
      (dualLat ψ M).sub_mem hβ g.out.2
    have h1 := sum_char ψ (J := J) (M := M) hmem
    have e : ∀ q : Qt 𝔪 J M, ψ ((β - ((g.out : ↥(dualLat ψ M)) : F)) * (q.out : F))
        = conj (ψ (((g.out : ↥(dualLat ψ M)) : F) * rep q)) * ψ (β * rep q) := by
      intro q
      rw [sub_mul, SfChar.map_sub', mul_comm]
    simp only [e] at h1
    rw [h1]
    have hiff : Adual ψ J (β - ((g.out : ↥(dualLat ψ M)) : F)) ↔ g = g₀ := by
      rw [hg₀, ← QuotientAddGroup.out_eq' g, QuotientAddGroup.eq, QuotientAddGroup.out_eq' g]
      rw [AddSubgroup.mem_addSubgroupOf]
      push_cast
      rw [neg_add_eq_sub]
      rfl
    by_cases hg : g = g₀
    · rw [if_pos hg, if_pos (hiff.mpr hg)]
    · rw [if_neg hg, if_neg fun h => hg (hiff.mp h)]
  have hcalc : ∑ q : Qt 𝔪 J M, ϕ (rep q) * ψ (β * rep q)
      = (Fintype.card (Qt 𝔪 J M) : ℂ)⁻¹ * ∑ g : G, f ((g.out : ↥(dualLat ψ M)) : F) *
          ∑ q : Qt 𝔪 J M, conj (ψ (((g.out : ↥(dualLat ψ M)) : F) * rep q)) * ψ (β * rep q) := by
    simp only [hϕ, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun g _ => Finset.sum_congr rfl fun q _ => ?_
    ring
  rw [hcalc]
  simp only [hterm]
  rw [Finset.sum_eq_single g₀ (fun g _ hg => by rw [if_neg hg, mul_zero])
    (fun h => absurd (Finset.mem_univ _) h), if_pos rfl, mul_comm (f _), ← mul_assoc,
    inv_mul_cancel₀ hcard0, one_mul]
  -- `f (rep of the class of β) = f β`
  have hout : Adual ψ J (β - ((g₀.out : ↥(dualLat ψ M)) : F)) := by
    have h := QuotientAddGroup.mk_out_eq_add ((dualLat ψ J).addSubgroupOf (dualLat ψ M))
      (⟨β, hβ⟩ : ↥(dualLat ψ M))
    obtain ⟨h', hh'⟩ := h
    have e : ((g₀.out : ↥(dualLat ψ M)) : F) = β + ((h' : ↥(dualLat ψ M)) : F) := by
      rw [hg₀, hh']
      rfl
    rw [e, sub_add_cancel_left]
    exact (dualLat ψ J).neg_mem h'.2
  have := hf _ _ g₀.out.2 hout
  rw [add_sub_cancel] at this
  exact this.symm

/-- **FI for the indicator of a coset** `β₁ + 𝔩_k` (depth function `k`), on `A_M`: the form used
in (G2).  Frequencies in `𝔩_J`, `J = min(M, -d₀ - max k)`. -/
theorem exists_fourier_indicator (ψ : SfChar 𝔪) (h𝔪 : 𝔪 ≠ ⊥) {d₀ : ℤ} (hd : HasDual ψ d₀)
    (M : ℤ) (k : HeightOneSpectrum (𝓞 F) → ℤ) (β₁ : F) :
    ∃ (T : Finset F) (ϕ : F → ℂ), ∀ β : F, Adual ψ M β →
      ∑ t ∈ T, ϕ t * ψ (β * t) = open Classical in if SmallD 𝔪 k (β - β₁) then 1 else 0 := by
  classical
  set K : ℕ := (CubicPkg.sFin 𝔪).sup fun v => (k v).toNat with hK
  set J : ℤ := min M (-d₀ - K) with hJ
  obtain ⟨T, ϕ, -, h⟩ := exists_fourier ψ h𝔪 hd (min_le_left M (-d₀ - K))
    (fun β => if SmallD 𝔪 k (β - β₁) then 1 else 0) (fun β a _ ha => by
      have h1 : Small 𝔪 (-J - d₀) a := hd J a ha
      have h2 : SmallD 𝔪 k a := by
        intro v hv
        refine (h1 v hv).trans (WithZero.exp_le_exp.mpr ?_)
        have hle : (k v).toNat ≤ K :=
          Finset.le_sup (f := fun v => (k v).toNat) ((CubicPkg.mem_sFin h𝔪 v).mpr hv)
        have h3 : k v ≤ ((k v).toNat : ℤ) := Int.self_le_toNat _
        have h4 : J ≤ -d₀ - K := min_le_right _ _
        omega
      have hiff : SmallD 𝔪 k (β + a - β₁) ↔ SmallD 𝔪 k (β - β₁) := by
        rw [show β + a - β₁ = (β - β₁) + a by ring]
        exact ⟨fun h => by simpa using h.sub h2, fun h => h.add h2⟩
      simp only [hiff])
  exact ⟨T, ϕ, h⟩

end ArtinKP.G1
end
end

section
-- module Solutions.Artin.KP.G1_Res
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
attribute [-simp] _root_.ArtinKP.S2.cubicSymbol_sym
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

/-- The series of a finite combination, on `Re s > 2`. -/
theorem aSer_sum {α : Type*} (I : Finset α) (Ψ : α → Sec) (g : α → ℂ → ℂ) {Φ : Sec} {ν : R}
    (hν : ν ≠ 0) {s : ℂ} (hs : 2 < s.re)
    (H : ∀ c : R, c ≠ 0 → D.Lam Φ c ν s = ∑ i ∈ I, g i s * D.Lam (Ψ i) c ν s) :
    D.aSer Φ ν s = ∑ i ∈ I, g i s * D.aSer (Ψ i) ν s := by
  unfold Kubota.aSer
  have hsum : ∀ i ∈ I, Summable fun a : Cls R => g i s * D.term (Ψ i) ν s (rp a.1) :=
    fun i _ => (D.summable (Ψ i) ν s hν hs).mul_left _
  simp only [← tsum_mul_left]
  rw [← Summable.tsum_finsetSum hsum]
  refine tsum_congr fun a => ?_
  unfold Kubota.term
  rw [H _ (rp_ne_zero a.2), Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- **Finite sums with multipliers holomorphic on `U`**: if
`Lam Φ c ν s = Σ_{i ∈ I} g_i(s) · Lam Ψ_i c ν s` for `c ≠ 0`, `Re s > 2`, then
`τ_Φ(ν) = Σ_{i ∈ I} g_i(s₀) τ_{Ψ_i}(ν)`. -/
theorem _root_.ArtinKP.E.Theta.tau_sum_at {U : Set ℂ} (hsm : T.toResFun.SmulOn U)
    {α : Type*} (I : Finset α) (Ψ : α → Sec) (g : α → ℂ → ℂ)
    (hg : ∀ i ∈ I, DifferentiableOn ℂ (g i) U) {Φ : Sec} {ν : R} (hν : ν ≠ 0)
    (H : ∀ (c : R) (s : ℂ), c ≠ 0 → 2 < s.re →
      D.Lam Φ c ν s = ∑ i ∈ I, g i s * D.Lam (Ψ i) c ν s) :
    T.tau Φ ν = ∑ i ∈ I, g i s₀ * T.tau (Ψ i) ν := by
  classical
  have hres : ∀ J : Finset α, J ⊆ I →
      T.HasRes (fun s => ∑ i ∈ J, g i s * D.aSer (Ψ i) ν s) (∑ i ∈ J, g i s₀ * T.tau (Ψ i) ν) := by
    intro J
    induction J using Finset.induction_on with
    | empty =>
      intro _
      have h0 := T.smul (fun _ => (0 : ℂ)) (differentiable_const 0) (T.tau_spec Φ ν hν)
      simp only [zero_mul] at h0
      simpa using h0
    | insert a J ha ih =>
      intro hJ
      have haI : a ∈ I := hJ (Finset.mem_insert_self a J)
      have h1 := hsm _ _ (g a) (hg a haI) (T.tau_spec (Ψ a) ν hν)
      have h2 := T.add h1 (ih fun x hx => hJ (Finset.mem_insert_of_mem hx))
      simp only [Finset.sum_insert ha]
      exact h2
  have h3 := T.congr (hres I subset_rfl) (fun s hs =>
    (aSer_sum I Ψ g hν hs (fun c hc => H c s hc hs)).symm)
  exact T.unique (T.tau_spec Φ ν hν) h3

/-- Additivity of `τ` (constant multipliers `1`): no `SmulOn` needed. -/
theorem _root_.ArtinKP.E.Theta.tau_finsum_at {α : Type*} (I : Finset α) (Ψ : α → Sec)
    (z : α → ℂ) {Φ : Sec} {ν : R} (hν : ν ≠ 0)
    (H : ∀ (c : R) (s : ℂ), c ≠ 0 → 2 < s.re →
      D.Lam Φ c ν s = ∑ i ∈ I, z i * D.Lam (Ψ i) c ν s) :
    T.tau Φ ν = ∑ i ∈ I, z i * T.tau (Ψ i) ν := by
  have hsm : T.toResFun.SmulOn Set.univ := fun f r h hh hf =>
    T.smul h (fun x => (hh x (Set.mem_univ x)).differentiableAt Filter.univ_mem) hf
  exact T.tau_sum_at hsm I Ψ (fun i _ => z i) (fun i _ => differentiableOn_const _) hν H

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

/-- **(K1)** for the Kirillov term: invariance under deep units. -/
theorem exists_Kt_deep (ψ : SfChar 𝔪) (hG : Good 𝔪) (Φ : GSection ι P 𝔪) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ u : F, Small 𝔪 N (u - 1) → ∀ (β η : F) (s : ℂ),
      Kt ψ hG Φ (β * u) η s = Kt ψ hG Φ β η s := by
  obtain ⟨N₀, hN₀1, hN₀⟩ := P.exists_isDeepLevel hG.ne_bot
  obtain ⟨N₁, hN₁1, hN₁⟩ := exists_torusT_deep hG Φ
  obtain ⟨v₀, hv₀⟩ := hG.exists_place
  refine ⟨max N₀ N₁, hN₀1.trans (le_max_left _ _), fun u hu β η s => ?_⟩
  have h0 : Small 𝔪 N₀ (u - 1) := hu.mono (by exact_mod_cast le_max_left N₀ N₁)
  have h1 : Small 𝔪 N₁ (u - 1) := hu.mono (by exact_mod_cast le_max_right N₀ N₁)
  have hu0 : u ≠ 0 := by
    intro h
    have := h0.val_eq_one (by exact_mod_cast hN₀1) v₀ hv₀
    rw [h, map_zero] at this
    exact zero_ne_one this
  by_cases hβ : β = 0
  · simp [Kt, hβ]
  have h2 := Kt_torusT ψ hG Φ hβ hu0 η s
  rw [hN₁ u hu0 h1, brk_deep_right hG hN₀ _ h0, one_mul] at h2
  exact h2.symm

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

theorem tau_sum {α : Type*} (I : Finset α) (f : α → GSection ι P 𝔪) {ν : SInt 𝔪}
    (hν : ν ≠ 0) : T.tau (∑ i ∈ I, f i) ν = ∑ i ∈ I, T.tau (f i) ν := by
  have h := T.tau_finsum_at I f (fun _ => 1) (Φ := ∑ i ∈ I, f i) hν (fun c s hc hs => by
    simp only [one_mul]
    exact Lam_sum (B.psiS hG.ne_bot) hG I f (coe_ne_zero' hc) _ (by linarith))
  simpa using h

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

/-- **(K4)** `𝒦_{n(t)Φ}(β) = ψ(βt) 𝒦_Φ(β)`. -/
theorem Kir_nT (Φ : GSection ι P 𝔪) (t : F) {β : F} (hβ : β ≠ 0) :
    Kir hG hz6 T (Φ.nT hG t) β = B.psiS hG.ne_bot (β * t) * Kir hG hz6 T Φ β :=
  Kir_congr hG hz6 T hβ hβ fun η s _ _ => Kt_nT _ hG Φ t β η s

theorem Kir_smul (Φ : GSection ι P 𝔪) (a : ℂ) {β : F} (hβ : β ≠ 0) :
    Kir hG hz6 T (a • Φ) β = a * Kir hG hz6 T Φ β :=
  Kir_congr hG hz6 T hβ hβ fun η s _ _ => Kt_smul _ hG Φ a β η s

/-- **(G2)** the additive projection multiplies `𝒦` by the trigonometric polynomial
`Σ_t ϕ(t) ψ(βt)`. -/
theorem Kir_addProj (Φ : GSection ι P 𝔪) (T₁ : Finset F) (ϕ : F → ℂ) {β : F} (hβ : β ≠ 0) :
    Kir hG hz6 T (Φ.addProj hG T₁ ϕ) β
      = (∑ t ∈ T₁, ϕ t * B.psiS hG.ne_bot (β * t)) * Kir hG hz6 T Φ β :=
  Kir_congr hG hz6 T hβ hβ fun _ _ hη hs => Kt_addProj _ hG Φ T₁ ϕ β hη hs

theorem Kir_sum {α : Type*} (I : Finset α) (f : α → GSection ι P 𝔪) {β : F} (hβ : β ≠ 0) :
    Kir hG hz6 T (∑ i ∈ I, f i) β = ∑ i ∈ I, Kir hG hz6 T (f i) β := by
  rw [Kir_of_ne hG hz6 T _ hβ, torusT_sum hG I f hβ, tau_sum hG hz6 T I _ one_ne_zero]
  exact Finset.sum_congr rfl fun i _ => (Kir_of_ne hG hz6 T (f i) hβ).symm

/-- **(K1)**: `𝒦_Φ(βu) = 𝒦_Φ(β)` for `u` in a deep neighbourhood of `1`. -/
theorem exists_Kir_deep (Φ : GSection ι P 𝔪) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ u : F, Small 𝔪 N (u - 1) → ∀ β : F,
      Kir hG hz6 T Φ (β * u) = Kir hG hz6 T Φ β := by
  obtain ⟨N, hN1, hN⟩ := exists_Kt_deep (B.psiS hG.ne_bot) hG Φ
  obtain ⟨v₀, hv₀⟩ := hG.exists_place
  refine ⟨N, hN1, fun u hu β => ?_⟩
  have hu0 : u ≠ 0 := by
    intro h
    have := hu.val_eq_one (by exact_mod_cast hN1) v₀ hv₀
    rw [h, map_zero] at this
    exact zero_ne_one this
  by_cases hβ : β = 0
  · simp [Kir, hβ]
  have := Kir_congr hG hz6 T (Φ := Φ) (Ψ := Φ) (mul_ne_zero hβ hu0) hβ (z := 1)
    fun η s _ _ => by rw [hN u hu β η s, one_mul]
  rwa [one_mul] at this

/-! ### The class decomposition and the majorant -/

end tau

end ArtinKP.G1
end
end

section
-- module Solutions.Artin.KP.G1_Delta
attribute [-instance] _root_.ArtinKP.N2.levelGroup_finiteIndex _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-!
# WP-G1, part 8: the delta section (MATH3 §1.2 (G1)–(G3), §5 (C10)), as far as it is algebra

For `D = B.kubota hG hz6`, `T : E.Theta D (4/3)`:

* `exists_Kir_adual`: `𝒦_Φ(β) ≠ 0 → β ∈ A_N` (support in a dual lattice; no class decomposition
  and no scalar law needed).
* `exists_delta` — **the delta section**: if the Kirillov function of *some* section is not
  identically zero (hypothesis `hne`, the analytic input (C9)+(C10′)+Theorem E of MATH3 (G1)),
  then for every `k` with `k + 1` deep there is `Φ₀` with
  `𝒦_{Φ₀}(β) = 1[β ∈ 1 + 𝔩_{k+1}]` for all `β ∈ F^×` (`= 1_{U_k}`, `U_k = SLevel 𝔪 k`), and
  `ξ_{Φ₀}` is the same function (`xi_delta`).
  Construction: additive projection `Φ₂ = Σ_t ϕ(t) n(t) Φ₁` by Lemma FI, then
  `Φ₀ = 𝒦_{Φ₁}(β₁)⁻¹ Σ_j Ã(β₁/u_j) Φ₂`, `u_j = 1 + a_j`, `a_j` running over `𝔩_{k+1}/𝔩_{K'}`.
* `KW T`: the statement of MATH3's Lemma KW (`𝒦_Φ ≡ 0 ⇒ 𝒦_{wΦ} ≡ 0`).  It is **not** section
  level (its proof needs (Exp), (Aut), (C10′) and Theorem E); it is a named hypothesis here.
* `Kir_w_delta_inv` — **(INV)** of MATH3 §4.2, from `KW`: `𝒦_{wΦ₀}(βu) = 𝒦_{wΦ₀}(β)` for
  `u ∈ 1 + 𝔩_{k+1}`, `Φ₀` a delta section.
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

variable [IsTotallyComplex F] (hG : Good 𝔪) {z6 : 𝓞 F} (hz6 : IsPrimitiveRoot z6 6)
  (T : Theta (B.kubota (ι := ι) (P := P) hG hz6) (4 / 3 : ℂ))

/-- **Support of `𝒦` in a dual lattice**: `𝒦_Φ(β) ≠ 0` forces `ψ(β 𝔩_N) = 1`, `𝔩_N` the lattice
of periods of `Φ`. -/
theorem exists_Kir_adual (Φ : GSection ι P 𝔪) :
    ∃ N : ℕ, ∀ β : F, β ≠ 0 → Kir hG hz6 T Φ β ≠ 0 → Adual (B.psiS hG.ne_bot) N β := by
  obtain ⟨N, hN⟩ := Φ.exists_unip
  refine ⟨N, fun β hβ hne => ?_⟩
  by_contra hA
  unfold Adual at hA
  push Not at hA
  obtain ⟨b, hb, hb1⟩ := hA
  have hΦ : Φ.nT hG b = Φ := by
    ext s c d
    rw [GSection.nT_apply, hN b hb]
  have h := Kir_nT hG hz6 T Φ b hβ
  rw [hΦ] at h
  have h2 : (B.psiS hG.ne_bot (β * b) - 1) * Kir hG hz6 T Φ β = 0 := by
    linear_combination -h
  exact hne ((mul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr hb1))

/-- For `u` a unit at `S_f`: `β/u - 1` and `β - u` have the same depth. -/
theorem small_div_sub_one_iff {K : ℤ} {β u : F}
    (hu : ∀ v : HeightOneSpectrum (𝓞 F), 𝔪 ≤ v.asIdeal → v.valuation F u = 1) (hu0 : u ≠ 0) :
    Small 𝔪 K (β / u - 1) ↔ Small 𝔪 K (β - u) := by
  refine forall_congr' fun v => forall_congr' fun hv => ?_
  rw [show β / u - 1 = (β - u) / u by field_simp, map_div₀, hu v hv, div_one]

/-- **The delta section** (MATH3 §1.2, (G1)–(G3)), conditional on the non-vanishing of some
Kirillov function: for `k + 1` a deep level there is a section `Φ₀` whose Kirillov function is
the indicator of `U_k = F^× ∩ (1 + 𝔩_{k+1})`, on all of `F^×`. -/
theorem exists_delta (k : ℕ) (hk : P.IsDeepLevel 𝔪 (k + 1))
    (hne : ∃ (Φ₁ : GSection ι P 𝔪) (β₁ : F), β₁ ≠ 0 ∧ Kir hG hz6 T Φ₁ β₁ ≠ 0) :
    ∃ Φ₀ : GSection ι P 𝔪, ∀ β : F, β ≠ 0 →
      Kir hG hz6 T Φ₀ β = open Classical in if Small 𝔪 ((k : ℤ) + 1) (β - 1) then 1 else 0 := by
  classical
  obtain ⟨Φ₁, β₁, hβ₁, hc⟩ := hne
  set c : ℂ := Kir hG hz6 T Φ₁ β₁ with hcdef
  obtain ⟨N₁, hN₁1, hN₁⟩ := exists_Kir_deep hG hz6 T Φ₁
  obtain ⟨Nd, hNd⟩ := exists_Kir_adual hG hz6 T Φ₁
  obtain ⟨d₀, hd⟩ := psiS_dual (F := F) hG.ne_bot
  obtain ⟨v₀, hv₀⟩ := hG.exists_place
  set K' : ℕ := max N₁ (k + 1) with hK'
  have hkK : ((k : ℤ) + 1) ≤ (K' : ℤ) := by exact_mod_cast le_max_right N₁ (k + 1)
  have hN₁K : (N₁ : ℤ) ≤ (K' : ℤ) := by exact_mod_cast le_max_left N₁ (k + 1)
  obtain ⟨T₁, ϕ, hFI⟩ := exists_fourier_indicator (B.psiS hG.ne_bot) hG.ne_bot hd Nd
    (fun v => (K' : ℤ) + ordv v β₁) β₁
  set Φ₂ : GSection ι P 𝔪 := Φ₁.addProj hG T₁ ϕ with hΦ₂
  -- the coset `β₁ (1 + 𝔩_{K'})`
  have hiff : ∀ β : F, SmallD 𝔪 (fun v => (K' : ℤ) + ordv v β₁) (β - β₁)
      ↔ Small 𝔪 K' (β / β₁ - 1) := by
    intro β
    rw [show β - β₁ = β₁ * (β / β₁ - 1) by field_simp, smallD_mul_iff _ hβ₁]
    simp only [add_sub_cancel_right]
    exact Iff.rfl
  have hval : ∀ β : F, Small 𝔪 K' (β / β₁ - 1) → Kir hG hz6 T Φ₁ β = c := by
    intro β hβ
    have := hN₁ (β / β₁) (hβ.mono hN₁K) β₁
    rwa [mul_div_cancel₀ _ hβ₁] at this
  -- (G2)
  have hA : ∀ β : F, β ≠ 0 →
      Kir hG hz6 T Φ₂ β = if Small 𝔪 K' (β / β₁ - 1) then c else 0 := by
    intro β hβ
    rw [hΦ₂, Kir_addProj hG hz6 T Φ₁ T₁ ϕ hβ]
    by_cases h0 : Kir hG hz6 T Φ₁ β = 0
    · rw [h0, mul_zero]
      by_cases hs : Small 𝔪 K' (β / β₁ - 1)
      · exact absurd ((hval β hs).symm.trans h0) hc
      · rw [if_neg hs]
    · rw [hFI β (hNd β hβ h0)]
      by_cases hs : Small 𝔪 K' (β / β₁ - 1)
      · rw [if_pos ((hiff β).mpr hs), if_pos hs, one_mul, hval β hs]
      · rw [if_neg fun h => hs ((hiff β).mp h), if_neg hs, zero_mul]
  -- (G3): representatives of `𝔩_{k+1}/𝔩_{K'}`
  have hfin := finite_Qt (𝔪 := 𝔪) hG.ne_bot hkK
  cases nonempty_fintype (Qt 𝔪 ((k : ℤ) + 1) K')
  set a : Qt 𝔪 ((k : ℤ) + 1) K' → F := fun q => (q.out : F) with ha
  have ha_small : ∀ q, Small 𝔪 ((k : ℤ) + 1) (a q) := fun q => q.out.2
  have hk1 : (1 : ℤ) ≤ (k : ℤ) + 1 := by omega
  have hu_small : ∀ q, Small 𝔪 ((k : ℤ) + 1) ((1 + a q) - 1) := fun q => by
    rw [add_sub_cancel_left]; exact ha_small q
  have hu_val : ∀ q, ∀ v : HeightOneSpectrum (𝓞 F), 𝔪 ≤ v.asIdeal →
      v.valuation F (1 + a q) = 1 := fun q v hv => (hu_small q).val_eq_one hk1 v hv
  have hu0 : ∀ q, (1 : F) + a q ≠ 0 := by
    intro q h
    have := hu_val q v₀ hv₀
    rw [h, map_zero] at this
    exact zero_ne_one this
  have hne' : ∀ q, β₁ / (1 + a q) ≠ 0 := fun q => div_ne_zero hβ₁ (hu0 q)
  refine ⟨c⁻¹ • ∑ q : Qt 𝔪 ((k : ℤ) + 1) K', Φ₂.torusT hG (β₁ / (1 + a q)) (hne' q),
    fun β hβ => ?_⟩
  rw [Kir_smul hG hz6 T _ _ hβ, Kir_sum hG hz6 T _ _ hβ]
  have hterm : ∀ q : Qt 𝔪 ((k : ℤ) + 1) K',
      Kir hG hz6 T (Φ₂.torusT hG (β₁ / (1 + a q)) (hne' q)) β
        = brk ι P 𝔪 β (β₁ / (1 + a q)) * if Small 𝔪 K' ((β - 1) - a q) then c else 0 := by
    intro q
    rw [Kir_torusT hG hz6 T Φ₂ hβ (hne' q), hA _ (mul_ne_zero hβ (hne' q))]
    have e : β * (β₁ / (1 + a q)) / β₁ = β / (1 + a q) := by
      field_simp
    rw [e]
    have hiff2 : Small 𝔪 K' (β / (1 + a q) - 1) ↔ Small 𝔪 K' ((β - 1) - a q) := by
      rw [small_div_sub_one_iff (hu_val q) (hu0 q), show β - (1 + a q) = (β - 1) - a q by ring]
    by_cases hs : Small 𝔪 K' ((β - 1) - a q)
    · rw [if_pos hs, if_pos (hiff2.mpr hs)]
    · rw [if_neg hs, if_neg fun h => hs (hiff2.mp h)]
  simp only [hterm]
  by_cases hβk : Small 𝔪 ((k : ℤ) + 1) (β - 1)
  · rw [if_pos hβk]
    set x : ↥(latD 𝔪 fun _ => ((k : ℤ) + 1)) := ⟨β - 1, hβk⟩ with hx
    set q₀ : Qt 𝔪 ((k : ℤ) + 1) K' := QuotientAddGroup.mk x with hq₀
    have huniq : ∀ q : Qt 𝔪 ((k : ℤ) + 1) K', Small 𝔪 K' ((β - 1) - a q) ↔ q = q₀ := by
      intro q
      rw [hq₀, ← QuotientAddGroup.out_eq' q, QuotientAddGroup.eq, QuotientAddGroup.out_eq' q,
        AddSubgroup.mem_addSubgroupOf]
      push_cast
      rw [neg_add_eq_sub]
      rfl
    rw [Finset.sum_eq_single q₀ (fun q _ hq => by
        rw [if_neg fun h => hq ((huniq q).mp h), mul_zero])
      (fun h => absurd (Finset.mem_univ _) h), if_pos ((huniq q₀).mpr rfl),
      brk_deep_left hG hk _ (by exact_mod_cast hβk), one_mul, inv_mul_cancel₀ hc]
  · rw [if_neg hβk, Finset.sum_eq_zero, mul_zero]
    intro q _
    rw [if_neg, mul_zero]
    intro hs
    refine hβk ?_
    have := (hs.mono hkK).add (ha_small q)
    rwa [sub_add_cancel] at this

/-! ### Lemma KW as a hypothesis, and (INV) -/

end ArtinKP.G1
end
end

section
-- module Solutions.Artin.KP.GK_J
/-! # WP-GK, file 2: the function `J` and its majorant `bf` (MATH3 §4)

For a section `Φ₀` and a level `k`:

* `Jdef hG hz6 Φ₀ cl y' = (−1)^r · ⟨ν̃, η′⟩ · ξ_{wΦ₀}(η′)` with chosen representatives `ν̃` of
  `cl : SFinCls 𝔪 k` and `η′` of `y' : SFin 𝔪 k` (MATH3 (2d)).
* `exists_bf_J`: a majorant `bf` on `SFin 𝔪 k` with `‖J cl y‖ ≤ bf y` and `Σ bf · |y|^σ < ∞` for
  `σ > −1/3`, for every section `Φ₀` (no hypothesis on `Φ₀`).
* `xi_w_inv` — **(INV)** for `ξ`: `ξ_{wΦ₀}(βu) = ξ_{wΦ₀}(β)` for `u ∈ U_k`, `Φ₀` a delta section.
* `Jdef_mk` — **well-definedness**: for a delta section `Φ₀` (level `k`, `k + 1` deep) and any
  representatives `x, η ∈ F^×`: `J([x], [η]) = (−1)^r ⟨x, η⟩ ξ_{wΦ₀}(η)`.
* `xi_w_PhiY` — MATH3 (4.1): `ξ_{wΦ_{y_f}}(ν̃) = ⟨ν̃, β₀⟩⁻¹ ξ_{wΦ₀}(ν̃/β₀)` for
  `Φ_{y_f} = |β₀|^{1/3} Ã(β₀) Φ₀`, and its `J`-form `xi_w_PhiY_eq_J`.
-/

open scoped MatrixGroups ComplexConjugate ENNReal Topology
open MeasureTheory Set NumberField Filter IsDedekindDomain ArtinPrimitiveRoots Metric

set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.GK

open ArtinKP.A ArtinKP.S ArtinKP.B7

noncomputable section

variable {F : Type*} [Field F] [NumberField F] [IsTotallyComplex F] {𝔪 : Ideal (𝓞 F)}
  {ι : F →+* ℂ} {P : CubicPkg F} {k : ℕ}

variable (hG : Good 𝔪) {z6 : 𝓞 F} (hz6 : IsPrimitiveRoot z6 6)

/-! ### (INV) and well-definedness for a delta section -/

section delta

variable (g : AllowedGen ι 𝔪)
  (hgood : ∀ (Q : Ideal (𝓞 F)) (hQ : Q.IsPrime) (hext : IsExterior 𝔪 Q),
    C3I.Good 𝔪 (⟨Q, hQ, hext.1⟩ : HeightOneSpectrum (𝓞 F)))
  (hd : DD.DiffInS 𝔪)

include g hgood hd in
/-- **The delta section exists** (MATH3 §1.2 (G1)–(G3)), unconditionally. -/
theorem exists_isDelta_oai (k : ℕ) (hk : P.IsDeepLevel 𝔪 (k + 1)) :
    ∃ Φ₀ : GSection ι P 𝔪, IsDelta hG hz6 k Φ₀ :=
  G1.exists_delta hG hz6 (T.theta hG hz6) k hk (hne hG hz6 g hgood hd)

/-! ### MATH3 (4.1) -/

end delta

end

end ArtinKP.GK
end

theorem solution.{u_1} : type_of% @ArtinKP.GK.exists_isDelta_oai.{u_1} := @ArtinKP.GK.exists_isDelta_oai.{u_1}
