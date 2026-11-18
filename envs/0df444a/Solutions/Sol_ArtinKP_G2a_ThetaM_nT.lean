-- Prove2me | solution 1 for ArtinKP.G2a.ThetaM_nT
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T10:05:44.590268+00:00
-- url     : https://prove2.me/submissions/2f7b7bd2-56a1-4449-b509-d4e81bd8b7cc

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

theorem valid_nT {ψ : SfChar 𝔪} {Φ : GSection ι P 𝔪} {ν : F}
    {k : HeightOneSpectrum (𝓞 F) → ℤ} (h : Valid ψ Φ ν k) (hG : Good 𝔪) (t : F) :
    Valid ψ (Φ.nT hG t) ν k :=
  ⟨fun b hb s c d => by
    rw [GSection.nT_apply, GSection.nT_apply, show d + c * b + c * t = d + c * t + c * b by ring,
      h.1 b hb], h.2⟩

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

/-! ### The Kirillov term -/

theorem Kt_of_ne (ψ : SfChar 𝔪) (hG : Good 𝔪) (Φ : GSection ι P 𝔪) {β : F} (hβ : β ≠ 0)
    (η : F) (s : ℂ) : Kt ψ hG Φ β η s = Lam ψ hG (Φ.torusT hG β hβ) η 1 s := by
  rw [Kt, dif_neg hβ]

/-- (K4) `𝒦_{n(t)Φ}(β) = ψ(βt) 𝒦_Φ(β)`. -/
theorem Kt_nT (ψ : SfChar 𝔪) (hG : Good 𝔪) (Φ : GSection ι P 𝔪) (t : F) (β η : F) (s : ℂ) :
    Kt ψ hG (Φ.nT hG t) β η s = ψ (β * t) * Kt ψ hG Φ β η s := by
  by_cases hβ : β = 0
  · simp [Kt, hβ]
  rw [Kt_of_ne ψ hG _ hβ, Kt_of_ne ψ hG _ hβ, torusT_nT hG Φ hβ, Lam_nT, one_mul]

/-! ### The cusp change for `Lam` and for the Kirillov term -/

/-! ### The normalized term `ξ^η = |β|^{1/3} Kt(·, 4/3)` -/

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

theorem SfChar.mul_conj_self (ψ : SfChar 𝔪) (x : F) : ψ x * conj (ψ x) = 1 := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, ψ.norm_one]
  simp

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
attribute [-instance] _root_.ArtinPrimitiveRoots.L3X.instDiscrSFin
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
-- module Solutions.Artin.KP.H0_Row
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

/-- **(K4)** `𝒦_{n(t)Φ}(β) = ψ(βt) 𝒦_Φ(β)`. -/
theorem Kir_nT (Φ : GSection ι P 𝔪) (t : F) {β : F} (hβ : β ≠ 0) :
    Kir hG hz6 T (Φ.nT hG t) β = B.psiS hG.ne_bot (β * t) * Kir hG hz6 T Φ β :=
  Kir_congr hG hz6 T hβ hβ fun η s _ _ => Kt_nT _ hG Φ t β η s

/-- `ξ_{n(t)Φ}(β) = ψ(βt) ξ_Φ(β)`. -/
theorem xi_nT (Φ : GSection ι P 𝔪) (t : F) {β : F} (hβ : β ≠ 0) :
    xi hG hz6 T (Φ.nT hG t) β = B.psiS hG.ne_bot (β * t) * xi hG hz6 T Φ β := by
  rw [xi, xi, Kir_nT hG hz6 T Φ t hβ]
  ring

/-! ### The class decomposition and the majorant -/

end tau

end ArtinKP.G1
end
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

/-- **MATH3 §1.1/§1.3 for a general section**: with the section translate `nT t` and the point
`emb t` the character becomes `sAddChar (ν t)` (MATH3 takes `t = −x`). -/
theorem ThetaM_nT_oai (hE : ThmE hG hz6 g P) (m : InfinitePlace F → ℤ) (Φ : GSection ι P 𝔪)
    (t : F) (Y : InfinitePlace F → ℂ) (hY : ∀ w, Y w ≠ 0) :
    ThetaM hG hz6 m (Φ.nT hG t) (emb t) Y hY =
      kapC F * (-(2 * Real.pi * Complex.I) * C0) ^ Fintype.card (InfinitePlace F) *
        ∑' ν : {ν : SInt 𝔪 // ν ≠ 0}, sAddChar 𝔪 (((ν : SInt 𝔪) : F) * t) *
          (L3X.coefF' g ⊤ (H0.rowOf hG.ne_bot g ν) *
            G1.xi hG hz6 (T.theta hG hz6) Φ ((ν : SInt 𝔪) : F) *
            ∏ w : InfinitePlace F, (omg (m w) (w.embedding ((ν : SInt 𝔪) : F) * Y w) *
              (kappaB (4 * Real.pi) (‖w.embedding ((ν : SInt 𝔪) : F) * Y w‖ ^ 2) : ℂ))) := by
  rw [ThetaM_forward hE]
  congr 1
  refine tsum_congr fun ν => ?_
  rw [G1.xi_nT hG hz6 _ Φ t (H0.coe_ne_zero ν), ← emb_mul, eInf_emb_eq hG.ne_bot]
  have h1 := G1.SfChar.mul_conj_self (psiS hG.ne_bot) (((ν : SInt 𝔪) : F) * t)
  linear_combination (L3X.coefF' g ⊤ (H0.rowOf hG.ne_bot g ν) *
    G1.xi hG hz6 (T.theta hG hz6) Φ ((ν : SInt 𝔪) : F) * sAddChar 𝔪 (((ν : SInt 𝔪) : F) * t) *
    ∏ w : InfinitePlace F, (omg (m w) (w.embedding ((ν : SInt 𝔪) : F) * Y w) *
      (kappaB (4 * Real.pi) (‖w.embedding ((ν : SInt 𝔪) : F) * Y w‖ ^ 2) : ℂ))) * h1

end

end ArtinKP.G2a
end

theorem solution.{u_1} : type_of% @ArtinKP.G2a.ThetaM_nT_oai.{u_1} := @ArtinKP.G2a.ThetaM_nT_oai.{u_1}
