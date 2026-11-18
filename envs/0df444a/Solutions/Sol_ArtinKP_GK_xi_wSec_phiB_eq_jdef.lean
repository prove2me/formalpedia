-- Prove2me | solution 1 for ArtinKP.GK.xi_wSec_phiB_eq_jdef
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T10:08:19.308257+00:00
-- url     : https://prove2.me/submissions/f82f5e09-ed06-4cc3-bdb4-2a2d62306fa1

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
import Theorems.Thm_ArtinKP_GK_kw_theta_of_diffInS

section
-- module Solutions.Artin.KP.A_Interface
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
/-!
# WP-A interface (symbols on global elements, Kubota symbol on `SL₂(R)`)

Later packages should import this file only.  Everything is in namespace `ArtinKP.A`, for
`F : Type*` a number field, `𝔪 : Ideal (𝓞 F)`, `R = SInt 𝔪`.

## Standing data (obtained once from `exists_cutoff_setup`)
* `P : CubicPkg F` — cubic Hilbert symbols `P.hv v : Fˣ →* Fˣ →* rootsOfUnity 3 F` on global
  elements; orientation pinned by `CubicPkg.tame`.
* `hG : Good 𝔪` — `𝔪 ≠ ⊥`, primes over `6` divide `𝔪`, extended ideals of `R` are principal.
* `hz6 : IsPrimitiveRoot z6 6`, `z6 : 𝓞 F`.

## Exported statements
* local: `IsTameSymbol`, `kubota_local`, `CubicPkg.isTame`;
* (A1) `CubicPkg.tame`, `CubicPkg.tame_zpow`, `CubicPkg.tame_formula`, `iota3_hv_eq`;
* (A2) `CubicPkg.HS`, `CubicPkg.HS_apply`, `CubicPkg.HS_mul_prod`, `CubicPkg.HS_mul_prod'`,
  `CubicPkg.HS_mul_finprod`;
* (A3) `cubicExt`, `cubicExt_eq_residueSymbol`, `cubicExt_eq_prod`, `cubicExt_reciprocity`,
  `cubicExt_unit_left`, `cubicExt_of_unit_right`, `cubicExt_mul_left`, `cubicExt_mul_right`,
  `cubicExt_pow_three`, `cubicExt_congr`;
* (A4) `CubicPkg.HS_self`, `CubicPkg.HS_skew`, `CubicPkg.HS_skew'`, `CubicPkg.HS_neg_left/right`,
  `CubicPkg.HS_pow_three_left/right`, `CubicPkg.HS_unit`, `CubicPkg.HS_add_eq_one`,
  `CubicPkg.HS_add_eq`, `CubicPkg.IsDeepLevel`, `CubicPkg.exists_isDeepLevel`,
  `CubicPkg.HS_deep_left/right`, `HS_of_mem_SLevel_right/left`;
* (A5) `toF`, `kappa`, `sigmaS`, `kappa_mul`, `kappa_eq_prod`, `IsRad`, `sigmaS_eq_one`;
* (A6) `Gamma`, `mem_Gamma_iff`, `kappa_mul_of_mem_Gamma`, `exists_level_kappa_mul`, `kappaHom`;
* existence: `exists_cutoff_good`, `nonempty_cubicPkg_cyclotomic`, `exists_cutoff_setup`.
-/

set_option autoImplicit false

open NumberField IsDedekindDomain ArtinPrimitiveRoots

noncomputable section

namespace ArtinKP.A

variable {F : Type*} [Field F] [NumberField F]

/-- Membership in the goal's level group `SLevel 𝔪 k` in terms of valuations:
`v(b - 1) ≤ exp (-(k+1))` at every `v ∣ 𝔪`. -/
theorem val_le_of_mem_SLevel {𝔪 : Ideal (𝓞 F)} {k : ℕ} {b : Fˣ} (hb : b ∈ SLevel 𝔪 k)
    (v : HeightOneSpectrum (𝓞 F)) (hv : 𝔪 ≤ v.asIdeal) :
    v.valuation F ((b : F) - 1) ≤ WithZero.exp (-((k + 1 : ℕ) : ℤ)) := by
  have h := hb v hv
  have hq := NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal v
  rw [NumberField.HeightOneSpectrum.adicAbv_def] at h
  have e : (Ideal.absNorm v.asIdeal : ℝ) ^ (-((k : ℤ) + 1))
      = ((WithZeroMulInt.toNNReal hq.ne_zero (WithZero.exp (-((k + 1 : ℕ) : ℤ)) :
          WithZero (Multiplicative ℤ)) : NNReal) : ℝ) := by
    rw [WithZeroMulInt.toNNReal_neg_apply _ WithZero.exp_ne_zero, WithZero.toAdd_unzero_eq_log,
      WithZero.log_exp]
    push_cast
    rfl
  rw [e, NNReal.coe_le_coe] at h
  exact (WithZeroMulInt.toNNReal_strictMono hq).le_iff_le.mp h

end ArtinKP.A
end
end

section
-- module Solutions.Artin.KP.S_Basic
attribute [-instance] _root_.ArtinKP.B1.PairClass.instNonempty _root_.ArtinKP.N2.levelGroup_finiteIndex _root_.ArtinKP.S.GSection.instAdd _root_.ArtinKP.S.GSection.instAddCommMonoid _root_.ArtinKP.S.GSection.instCoeFunForallComplexForallForall _root_.ArtinKP.S.GSection.instSMulComplex _root_.ArtinKP.S.GSection.instZero _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
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
-- module Solutions.Artin.KP.S2_Translate
attribute [-instance] _root_.ArtinKP.N2.levelGroup_finiteIndex _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
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

/-! ### The cusp change for `Lam` and for the Kirillov term -/

/-! ### The normalized term `ξ^η = |β|^{1/3} Kt(·, 4/3)` -/

end ArtinKP.G1
end
end

section
-- module Solutions.Artin.T12.L3X_Meas
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

theorem SFin.mk_mul (x y : Fˣ) : SFin.mk 𝔪 k (x * y) = SFin.mk 𝔪 k x + SFin.mk 𝔪 k y := rfl

theorem SFin.mk_inv (x : Fˣ) : SFin.mk 𝔪 k x⁻¹ = -SFin.mk 𝔪 k x := rfl

theorem SFin.mk_surjective : Function.Surjective (SFin.mk 𝔪 k) := by
  intro y
  obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (Additive.toMul y)
  exact ⟨x, by simp only [SFin.mk, hx]; rfl⟩

/-! ### `lnorm` -/

/-! ### Slices -/


/-! ### Measure preservation -/

end

end ArtinPrimitiveRoots.L3X
end

section
-- module Solutions.Artin.KP.H0_Coord
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

theorem SFin_mk_eq_mk_iff (x y : Fˣ) :
    SFin.mk 𝔪 k x = SFin.mk 𝔪 k y ↔ x⁻¹ * y ∈ SLevel 𝔪 k :=
  Additive.ofMul.injective.eq_iff.trans QuotientGroup.eq

/-! ### `SFinCls` -/

/-! ### Angular characters and rotations -/

/-! ### The two functions at `sEmb ν ± y` -/

end

end ArtinKP.H0
end

section
-- module Solutions.Artin.KP.G1_BfS
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

/-- `U_k = SLevel 𝔪 k` in the vocabulary of WP-S: `x ∈ U_k ↔ x - 1 ∈ 𝔩_{k+1}`. -/
theorem mem_SLevel_iff_small (x : Fˣ) :
    x ∈ SLevel 𝔪 k ↔ Small 𝔪 ((k : ℤ) + 1) ((x : F) - 1) := by
  constructor
  · intro h v hv
    have := val_le_of_mem_SLevel h v hv
    push_cast at this
    exact this
  · intro h v hv
    exact abv_le_of_val_le v (h v hv)

theorem mk_repS (y : SFin 𝔪 k) : SFin.mk 𝔪 k (repS y) = y := by
  show Additive.ofMul (QuotientGroup.mk (Quotient.out (Additive.toMul y))) = y
  rw [QuotientGroup.out_eq']
  rfl

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

theorem tau_smulFun (Φ : GSection ι P 𝔪) (f : ℂ → ℂ) (hf : Differentiable ℂ f) {ν : SInt 𝔪}
    (hν : ν ≠ 0) : T.tau (GSection.smulFun f hf Φ) ν = f (4 / 3) * T.tau Φ ν :=
  T.tau_smul_at f hf hν fun c s _ _ => Lam_smulFun _ hG Φ f hf (c : F) _ s

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

theorem Kir_smul (Φ : GSection ι P 𝔪) (a : ℂ) {β : F} (hβ : β ≠ 0) :
    Kir hG hz6 T (a • Φ) β = a * Kir hG hz6 T Φ β :=
  Kir_congr hG hz6 T hβ hβ fun η s _ _ => Kt_smul _ hG Φ a β η s

/-- **(K4)** `𝒦_{h•Φ} = h(4/3) 𝒦_Φ` for `h` entire. -/
theorem Kir_smulFun (Φ : GSection ι P 𝔪) (f : ℂ → ℂ) (hf : Differentiable ℂ f) {β : F}
    (hβ : β ≠ 0) : Kir hG hz6 T (GSection.smulFun f hf Φ) β = f (4 / 3) * Kir hG hz6 T Φ β := by
  rw [Kir_of_ne hG hz6 T _ hβ, Kir_of_ne hG hz6 T _ hβ, torusT_smulFun hG Φ hβ,
    tau_smulFun hG hz6 T _ f hf one_ne_zero]

theorem Kir_sum {α : Type*} (I : Finset α) (f : α → GSection ι P 𝔪) {β : F} (hβ : β ≠ 0) :
    Kir hG hz6 T (∑ i ∈ I, f i) β = ∑ i ∈ I, Kir hG hz6 T (f i) β := by
  rw [Kir_of_ne hG hz6 T _ hβ, torusT_sum hG I f hβ, tau_sum hG hz6 T I _ one_ne_zero]
  exact Finset.sum_congr rfl fun i _ => (Kir_of_ne hG hz6 T (f i) hβ).symm

/-- `|β₀|^{1/3} ξ_{Ã(β₀)Φ}(β) = ⟨β, β₀⟩ ξ_Φ(β β₀)`. -/
theorem xi_torusT (Φ : GSection ι P 𝔪) {β β₀ : F} (hβ : β ≠ 0) (hβ₀ : β₀ ≠ 0) :
    ((absS 𝔪 β₀ ^ (1 / 3 : ℝ) : ℝ) : ℂ) * xi hG hz6 T (Φ.torusT hG β₀ hβ₀) β
      = brk ι P 𝔪 β β₀ * xi hG hz6 T Φ (β * β₀) := by
  rw [xi, xi, Kir_torusT hG hz6 T Φ hβ hβ₀, absS_mul,
    Real.mul_rpow (absS_nonneg _) (absS_nonneg _)]
  push_cast
  ring

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

theorem Kir_add (Φ Φ' : GSection ι P 𝔪) {β : F} (hβ : β ≠ 0) :
    Kir hG hz6 T (Φ + Φ') β = Kir hG hz6 T Φ β + Kir hG hz6 T Φ' β := by
  have h := Kir_sum hG hz6 T (Finset.univ : Finset Bool) (fun b => if b then Φ else Φ') hβ
  simpa [Fintype.sum_bool] using h

/-! ### Lemma KW as a hypothesis, and (INV) -/

theorem wSec_add (Φ Φ' : GSection ι P 𝔪) : wSec hG (Φ + Φ') = wSec hG Φ + wSec hG Φ' := by
  ext s c d
  simp only [wSec_apply, GSection.add_apply]
  ring

theorem wSec_smul (a : ℂ) (Φ : GSection ι P 𝔪) : wSec hG (a • Φ) = a • wSec hG Φ := by
  ext s c d
  simp only [wSec_apply, GSection.smul_apply]
  ring

/-- **(INV)** (MATH3 §4.2), from `KW`: the Kirillov function of `wΦ₀`, `Φ₀` a delta section of
level `k` (`k + 1` deep), is invariant under `U_k`. -/
theorem Kir_w_delta_inv (hKW : KW hG hz6 T) (k : ℕ) (hk : P.IsDeepLevel 𝔪 (k + 1))
    {Φ₀ : GSection ι P 𝔪}
    (hΦ₀ : ∀ β : F, β ≠ 0 →
      Kir hG hz6 T Φ₀ β = open Classical in if Small 𝔪 ((k : ℤ) + 1) (β - 1) then 1 else 0)
    {u : F} (hu : Small 𝔪 ((k : ℤ) + 1) (u - 1)) {β : F} (hβ : β ≠ 0) :
    Kir hG hz6 T (wSec hG Φ₀) (β * u) = Kir hG hz6 T (wSec hG Φ₀) β := by
  classical
  obtain ⟨v₀, hv₀⟩ := hG.exists_place
  have hk1 : (1 : ℤ) ≤ (k : ℤ) + 1 := by omega
  have huv := fun v hv => hu.val_eq_one hk1 v hv
  have hu0 : u ≠ 0 := by
    intro h
    have := huv v₀ hv₀
    rw [h, map_zero] at this
    exact zero_ne_one this
  have hui : Small 𝔪 ((k : ℤ) + 1) (u⁻¹ - 1) := Small.deep_inv hk1 hu
  have hui0 : u⁻¹ ≠ 0 := inv_ne_zero hu0
  have hk' : P.IsDeepLevel 𝔪 (k + 1) := hk
  have hdl : ∀ {x : F}, Small 𝔪 ((k : ℤ) + 1) (x - 1) → ∀ y : F, brk ι P 𝔪 y x = 1 :=
    fun {x} hx y => brk_deep_right hG hk' y (by exact_mod_cast hx)
  -- `Δ = Ã(u⁻¹)Φ₀ - Φ₀` has vanishing Kirillov function
  set Δ : GSection ι P 𝔪 := Φ₀.torusT hG u⁻¹ hui0 + (-1 : ℂ) • Φ₀ with hΔ
  have hΔ0 : ∀ β' : F, β' ≠ 0 → Kir hG hz6 T Δ β' = 0 := by
    intro β' hβ'
    rw [hΔ, Kir_add hG hz6 T _ _ hβ', Kir_torusT hG hz6 T Φ₀ hβ' hui0, Kir_smul hG hz6 T _ _ hβ',
      hΦ₀ _ (mul_ne_zero hβ' hui0), hΦ₀ _ hβ', hdl hui β', one_mul]
    have hiff : Small 𝔪 ((k : ℤ) + 1) (β' * u⁻¹ - 1) ↔ Small 𝔪 ((k : ℤ) + 1) (β' - 1) := by
      constructor
      · intro h
        have := Small.deep_mul hk1 h hu
        rwa [mul_assoc, inv_mul_cancel₀ hu0, mul_one] at this
      · intro h
        exact Small.deep_mul hk1 h hui
    by_cases hs : Small 𝔪 ((k : ℤ) + 1) (β' - 1)
    · rw [if_pos hs, if_pos (hiff.mpr hs)]; ring
    · rw [if_neg hs, if_neg fun h => hs (hiff.mp h)]; ring
  have h := hKW Δ hΔ0 β hβ
  have habs : absS 𝔪 u⁻¹ = 1 :=
    absS_eq_one_of_val hG.ne_bot (fun v hv => hui.val_eq_one hk1 v hv)
  rw [hΔ, wSec_add, wSec_smul, w_torusT hG Φ₀ hui0, Kir_add hG hz6 T _ _ hβ, scal,
    Kir_smulFun hG hz6 T _ _ _ hβ, Kir_smul hG hz6 T _ _ hβ,
    Kir_torusT hG hz6 T (wSec hG Φ₀) hβ (inv_ne_zero hui0), habs, Complex.ofReal_one,
    Complex.one_cpow, one_mul, inv_inv, hdl hu β, one_mul] at h
  linear_combination h

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

theorem mk_repC (cl : SFinCls 𝔪 k) :
    (QuotientAddGroup.mk (SFin.mk 𝔪 k (repC cl)) : SFinCls 𝔪 k) = cl := by
  rw [repC, G1.mk_repS]
  exact QuotientAddGroup.out_eq' cl

theorem SFin_mk_pow (t : Fˣ) (n : ℕ) : SFin.mk 𝔪 k (t ^ n) = n • SFin.mk 𝔪 k t := rfl

/-- Two representatives of one class of `SFinCls` differ by a sixth power and an element of
`U_k`. -/
theorem exists_of_cls_eq {x x' : Fˣ}
    (h : (QuotientAddGroup.mk (SFin.mk 𝔪 k x') : SFinCls 𝔪 k)
      = QuotientAddGroup.mk (SFin.mk 𝔪 k x)) :
    ∃ t u : Fˣ, u ∈ SLevel 𝔪 k ∧ x' = x * t ^ 6 * u := by
  rw [eq_comm, QuotientAddGroup.eq] at h
  obtain ⟨z, hz⟩ := h
  obtain ⟨t, rfl⟩ := L3X.SFin.mk_surjective (𝔪 := 𝔪) (k := k) z
  have h1 : SFin.mk 𝔪 k (x * t ^ 6) = SFin.mk 𝔪 k x' := by
    rw [L3X.SFin.mk_mul, SFin_mk_pow]
    have : (6 : ℕ) • SFin.mk 𝔪 k t = -SFin.mk 𝔪 k x + SFin.mk 𝔪 k x' := hz
    rw [this]
    abel
  refine ⟨t, (x * t ^ 6)⁻¹ * x', (H0.SFin_mk_eq_mk_iff _ _).mp h1, ?_⟩
  group

variable (hG : Good 𝔪) {z6 : 𝓞 F} (hz6 : IsPrimitiveRoot z6 6)

/-! ### (INV) and well-definedness for a delta section -/

section delta

variable (g : AllowedGen ι 𝔪)
  (hgood : ∀ (Q : Ideal (𝓞 F)) (hQ : Q.IsPrime) (hext : IsExterior 𝔪 Q),
    C3I.Good 𝔪 (⟨Q, hQ, hext.1⟩ : HeightOneSpectrum (𝓞 F)))
  (hd : DD.DiffInS 𝔪)

include g hgood hd in
/-- **(INV)** (MATH3 §4.2), unconditional: `𝒦_{wΦ₀}(βu) = 𝒦_{wΦ₀}(β)` for `u ∈ U_k`. -/
theorem Kir_w_inv (k : ℕ) (hk : P.IsDeepLevel 𝔪 (k + 1)) {Φ₀ : GSection ι P 𝔪}
    (hΦ₀ : IsDelta hG hz6 k Φ₀) {u : F} (hu : Small 𝔪 ((k : ℤ) + 1) (u - 1)) {β : F}
    (hβ : β ≠ 0) :
    G1.Kir hG hz6 (T.theta hG hz6) (G1.wSec hG Φ₀) (β * u)
      = G1.Kir hG hz6 (T.theta hG hz6) (G1.wSec hG Φ₀) β :=
  G1.Kir_w_delta_inv hG hz6 (T.theta hG hz6) (kw_theta_of_diffInS hG hz6 g hgood hd) k hk hΦ₀ hu hβ

include g hgood hd in
/-- **(INV)** for `ξ`: `ξ_{wΦ₀}(βu) = ξ_{wΦ₀}(β)` for `u ∈ U_k`, `β ∈ F^×`. -/
theorem xi_w_inv (k : ℕ) (hk : P.IsDeepLevel 𝔪 (k + 1)) {Φ₀ : GSection ι P 𝔪}
    (hΦ₀ : IsDelta hG hz6 k Φ₀) {u : F} (hu : Small 𝔪 ((k : ℤ) + 1) (u - 1)) {β : F}
    (hβ : β ≠ 0) :
    G1.xi hG hz6 (T.theta hG hz6) (G1.wSec hG Φ₀) (β * u)
      = G1.xi hG hz6 (T.theta hG hz6) (G1.wSec hG Φ₀) β := by
  have hk1 : (1 : ℤ) ≤ (k : ℤ) + 1 := by omega
  have habs : absS 𝔪 u = 1 :=
    absS_eq_one_of_val hG.ne_bot (fun v hv => hu.val_eq_one hk1 v hv)
  rw [G1.xi, G1.xi, Kir_w_inv hG hz6 g hgood hd k hk hΦ₀ hu hβ, absS_mul, habs, mul_one]

include g hgood hd in
/-- **`J` is well defined** (MATH3 §4.1): for a delta section `Φ₀` and arbitrary representatives
`x` of the class and `η` of the point, `J([x], [η]) = (−1)^r · ⟨x, η⟩ · ξ_{wΦ₀}(η)`. -/
theorem Jdef_mk (hk : P.IsDeepLevel 𝔪 (k + 1)) {Φ₀ : GSection ι P 𝔪}
    (hΦ₀ : IsDelta hG hz6 k Φ₀) (x η : Fˣ) :
    Jdef hG hz6 Φ₀ (QuotientAddGroup.mk (SFin.mk 𝔪 k x)) (SFin.mk 𝔪 k η)
      = (-1) ^ Fintype.card (InfinitePlace F) * brk ι P 𝔪 (x : F) (η : F)
        * G1.xi hG hz6 (T.theta hG hz6) (G1.wSec hG Φ₀) (η : F) := by
  have hdeep : ∀ {u : Fˣ}, u ∈ SLevel 𝔪 k → Small 𝔪 ((k + 1 : ℕ) : ℤ) ((u : F) - 1) := by
    intro u hu
    have := (G1.mem_SLevel_iff_small u).mp hu
    exact_mod_cast this
  -- the representative of the point
  have h1 : SFin.mk 𝔪 k η = SFin.mk 𝔪 k (G1.repS (SFin.mk 𝔪 k η)) := (G1.mk_repS _).symm
  have hu := (H0.SFin_mk_eq_mk_iff _ _).mp h1
  set u : Fˣ := η⁻¹ * G1.repS (SFin.mk 𝔪 k η) with hudef
  have hη' : ((G1.repS (SFin.mk 𝔪 k η) : Fˣ) : F) = (η : F) * (u : F) := by
    rw [hudef]; push_cast; field_simp
  -- the representative of the class
  obtain ⟨t, u', hu', hx'⟩ := exists_of_cls_eq
    (mk_repC (QuotientAddGroup.mk (SFin.mk 𝔪 k x) : SFinCls 𝔪 k))
  have hx'F : ((repC (QuotientAddGroup.mk (SFin.mk 𝔪 k x) : SFinCls 𝔪 k) : Fˣ) : F)
      = (x : F) * ((t : F) ^ 2) ^ 3 * (u' : F) := by
    rw [hx']; push_cast; ring
  have hbr : brk ι P 𝔪 ((x : F) * ((t : F) ^ 2) ^ 3 * (u' : F)) ((η : F) * (u : F))
      = brk ι P 𝔪 (x : F) (η : F) := by
    rw [brk_mul_right _ η.ne_zero u.ne_zero, brk_deep_right hG hk _ (hdeep hu), mul_one,
      brk_mul_left _ (mul_ne_zero x.ne_zero (pow_ne_zero _ (pow_ne_zero _ t.ne_zero)))
        u'.ne_zero,
      brk_deep_left hG hk _ (hdeep hu'), mul_one,
      brk_mul_left _ x.ne_zero (pow_ne_zero _ (pow_ne_zero _ t.ne_zero)),
      brk_pow_three_left, mul_one]
  have hxi := xi_w_inv hG hz6 g hgood hd k hk hΦ₀ ((G1.mem_SLevel_iff_small u).mp hu)
    η.ne_zero
  rw [Jdef, hx'F, hη', hbr, hxi]

/-! ### MATH3 (4.1) -/

/-- **MATH3 (4.1)**, first equality: `ξ_{wΦ_{y_f}}(ν̃) = ⟨ν̃, β₀⟩⁻¹ · ξ_{wΦ₀}(ν̃ / β₀)`
(any section `Φ₀`). -/
theorem xi_w_PhiB (Φ₀ : GSection ι P 𝔪) (β₀ : Fˣ) {ν' : F} (hν' : ν' ≠ 0) :
    G1.xi hG hz6 (T.theta hG hz6) (G1.wSec hG (PhiB hG Φ₀ β₀)) ν'
      = (brk ι P 𝔪 ν' (β₀ : F))⁻¹
        * G1.xi hG hz6 (T.theta hG hz6) (G1.wSec hG Φ₀) (ν' / (β₀ : F)) := by
  have hβ := β₀.ne_zero
  have hβi : ((β₀ : F))⁻¹ ≠ 0 := inv_ne_zero hβ
  have ha : 0 < absS 𝔪 (β₀ : F) := absS_pos hβ
  have h1 := G1.xi_torusT hG hz6 (T.theta hG hz6) (G1.wSec hG Φ₀) hν' hβi
  rw [brk_inv_right, ← div_eq_mul_inv] at h1
  rw [PhiB, G1.wSec_smul, G1.w_torusT hG Φ₀ hβ, G1.scal, G1.xi,
    G1.Kir_smul hG hz6 _ _ _ hν', G1.Kir_smulFun hG hz6 _ _ _ _ hν']
  rw [← h1, G1.xi, absS_inv]
  -- the powers of `|β₀|`: `|β₀|^{1/3} · |β₀|^{4/3 − 2} = |β₀⁻¹|^{1/3}`
  have e1 : ((absS 𝔪 (β₀ : F) : ℝ) : ℂ) ^ ((1 : ℂ) * (4 / 3) + -2)
      = (((absS 𝔪 (β₀ : F)) ^ (-(2 / 3) : ℝ) : ℝ) : ℂ) := by
    rw [Complex.ofReal_cpow ha.le]
    congr 1
    push_cast
    ring
  have e2 : (absS 𝔪 (β₀ : F)) ^ (1 / 3 : ℝ) * (absS 𝔪 (β₀ : F)) ^ (-(2 / 3) : ℝ)
      = ((absS 𝔪 (β₀ : F))⁻¹) ^ (1 / 3 : ℝ) := by
    rw [← Real.rpow_add ha, Real.inv_rpow ha.le, ← Real.rpow_neg ha.le]
    norm_num
  rw [e1]
  have e3 := congrArg (fun r : ℝ => (r : ℂ)) e2
  simp only [Complex.ofReal_mul] at e3
  linear_combination
    (((absS 𝔪 ν' ^ (1 / 3 : ℝ) : ℝ) : ℂ)
      * G1.Kir hG hz6 (T.theta hG hz6) ((G1.wSec hG Φ₀).torusT hG (β₀ : F)⁻¹ hβi) ν') * e3

include g hgood hd in
/-- **MATH3 (4.1)** in terms of `J`: for a delta section `Φ₀`, a representative `β₀` of `y_f`
and `ν̃ ∈ F^×`,
`(−1)^r · ξ_{wΦ_{y_f}}(ν̃) = J([ν̃], [ν̃] − y_f)`. -/
theorem xi_wSec_phiB_eq_jdef_oai (hk : P.IsDeepLevel 𝔪 (k + 1)) {Φ₀ : GSection ι P 𝔪}
    (hΦ₀ : IsDelta hG hz6 k Φ₀) (β₀ : Fˣ) (ν' : Fˣ) :
    (-1) ^ Fintype.card (InfinitePlace F)
        * G1.xi hG hz6 (T.theta hG hz6) (G1.wSec hG (PhiB hG Φ₀ β₀)) (ν' : F)
      = Jdef hG hz6 Φ₀ (QuotientAddGroup.mk (SFin.mk 𝔪 k ν'))
          (SFin.mk 𝔪 k ν' - SFin.mk 𝔪 k β₀) := by
  have e : SFin.mk 𝔪 k ν' - SFin.mk 𝔪 k β₀ = SFin.mk 𝔪 k (ν' * β₀⁻¹) := by
    rw [L3X.SFin.mk_mul, L3X.SFin.mk_inv, sub_eq_add_neg]
  rw [e, Jdef_mk hG hz6 g hgood hd hk hΦ₀, xi_w_PhiB hG hz6 Φ₀ β₀ ν'.ne_zero]
  have e2 : ((ν' * β₀⁻¹ : Fˣ) : F) = (ν' : F) / (β₀ : F) := by
    push_cast; rw [div_eq_mul_inv]
  rw [e2, brk_div_right _ ν'.ne_zero β₀.ne_zero, brk_self, one_mul]
  ring

end delta

end

end ArtinKP.GK
end

theorem solution.{u_1} : type_of% @ArtinKP.GK.xi_wSec_phiB_eq_jdef_oai.{u_1} := @ArtinKP.GK.xi_wSec_phiB_eq_jdef_oai.{u_1}
