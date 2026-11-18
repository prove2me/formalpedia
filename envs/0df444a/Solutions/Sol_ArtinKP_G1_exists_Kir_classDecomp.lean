-- Prove2me | solution 1 for ArtinKP.G1.exists_Kir_classDecomp
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T09:54:30.748638+00:00
-- url     : https://prove2.me/submissions/31751c28-bef3-40b7-a4e0-aefda2930d92

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
import Definitions.Def_ArtinKPB016

section
-- module Solutions.Artin.KP.A_Pkg
attribute [-instance] _root_.ArtinKP.S.GSection.instAdd _root_.ArtinKP.S.GSection.instCoeFunForallComplexForallForall _root_.ArtinKP.S.GSection.instSMulComplex _root_.ArtinKP.S.GSection.instZero
/-!
# WP-A: the global cubic symbol package and the `S`-Hilbert pairing

`CubicPkg F` is a universe-polymorphic, completion-free form of `C0Y.SymbolPkg F 3`: local cubic
Hilbert symbols `hv v : Fˣ →* Fˣ →* μ₃(F)` evaluated on *global* elements, with Steinberg, the
product formula, triviality on units and the tame formula at places prime to `3`, and local
constancy (`deep`).  Everything in WP-A is derived from a `CubicPkg`.

The orientation is pinned by the field `tame`: `hv v a π ≡ a^{(Nv-1)/3} (mod v)` for a `v`-unit
`a` and a uniformizer `π`.

Main results: `CubicPkg.skew`, `CubicPkg.self`, `CubicPkg.isTame` (the bridge to `A_Local`),
`CubicPkg.tame_zpow` (A1 for a unit against any element), `CubicPkg.tame_formula` (A1),
`CubicPkg.HS` (the pairing `(a,b)_S`), `CubicPkg.HS_mul_prod` (A2, product formula),
`CubicPkg.HS_unit`, `CubicPkg.HS_add_eq_one`, `CubicPkg.exists_isDeepLevel`,
`CubicPkg.HS_deep_right/left` (A4).
-/

set_option autoImplicit false

open NumberField IsDedekindDomain ArtinPrimitiveRoots

noncomputable section

namespace ArtinKP.A

variable (F : Type*) [Field F] [NumberField F]

variable {F}

namespace CubicPkg

variable (P : CubicPkg F)

/-! ### The `S`-part -/

/-! ### Deep units -/

theorem IsDeepLevel.mono {𝔪 : Ideal (𝓞 F)} {N N' : ℕ} (h : P.IsDeepLevel 𝔪 N) (hN : N ≤ N') :
    P.IsDeepLevel 𝔪 N' := fun v hv a b hb =>
  h v hv a b (hb.trans (by rw [WithZero.exp_le_exp]; omega))

end CubicPkg

end ArtinKP.A
end
end

section
-- module Solutions.Artin.KP.S_Basic
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
-- module Solutions.Artin.KP.S_BigCell
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

theorem bigCell_apply (ι : F →+* ℂ) (P : CubicPkg F) (hG : Good 𝔪) {N : ℕ} (hN1 : 1 ≤ N)
    (hN : P.IsDeepLevel 𝔪 N) (η : F) (hη : η ≠ 0) (M : ℤ) (t₀ : F) (s : ℂ) (c d : F) :
    bigCell ι P hG hN1 hN η hη M t₀ s c d = bigFun ι P 𝔪 N η M t₀ s c d := rfl

/-! ### Small-cell sections -/

/-! ### Finite sums: the sum over classes and additive projections -/

end ArtinKP.S
end
end

section
-- module Solutions.Artin.KP.S_Jacquet
attribute [-simp] _root_.ArtinKP.G1.scal_apply _root_.ArtinKP.S2.cubicSymbol_sym
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

open Classical in
/-- The functional of the indicator of a coset `t₀ + 𝔩_M`. -/
theorem jac_indicator (A : ℂ) (t₀ : F) (hψ : ∀ h : F, Small 𝔪 M h → ψ (ν * h) = 1) :
    jac ψ M (fun u => if Small 𝔪 M (u - t₀) then A else 0) ν
      = (vol 𝔪 M : ℂ) * (A * (starRingEnd ℂ) (ψ (ν * t₀))) := by
  rw [jac]
  congr 1
  rw [tsum_eq_single (QuotientAddGroup.mk t₀ : F ⧸ lat 𝔪 M)]
  · obtain ⟨h, hh, he⟩ := out_spec (𝔪 := 𝔪) (M := M) t₀
    rw [he, if_pos (by rw [add_sub_cancel_left]; exact hh), mul_add, ψ.map_add, hψ h hh, mul_one]
  · intro u hu
    rw [if_neg, zero_mul]
    intro hs
    apply hu
    rw [← QuotientAddGroup.out_eq' u, QuotientAddGroup.eq]
    have e : -u.out + t₀ = -(u.out - t₀) := by ring
    rw [e]
    exact (lat 𝔪 M).neg_mem hs

end jac

variable {ι : F →+* ℂ} {P : CubicPkg F}

/-- `λ_η` of a big-cell section of another class vanishes. -/
theorem lam_bigCell_of_not_inClass (ψ : SfChar 𝔪) (hG : Good 𝔪) {N : ℕ} (hN1 : 1 ≤ N)
    (hN : P.IsDeepLevel 𝔪 N) (η' : F) (hη' : η' ≠ 0) (M M' : ℤ) (t₀ η ν : F)
    (h : ¬ InClass 𝔪 N η' η) (s : ℂ) :
    lam ψ M' (bigCell ι P hG hN1 hN η' hη' M t₀) η ν s = 0 := by
  have hfun : (fun u => bigCell ι P hG hN1 hN η' hη' M t₀ s η (η * u)) = fun _ => 0 := by
    funext u
    rw [bigCell_apply]
    exact bigFun_of_not_supp (fun hS => h hS.1) s
  rw [lam, hfun, jac]
  simp

/-! ### The Kirillov function -/

open NumberField.HeightOneSpectrum in
theorem one_le_normS_one (u : F) : 1 ≤ normS 𝔪 1 u := by
  have : ∏ _v ∈ CubicPkg.sFin 𝔪, (1 : ℝ) ≤ normS 𝔪 1 u :=
    Finset.prod_le_prod (fun _ _ => zero_le_one) fun v _ =>
      le_max_of_le_left (by rw [map_one])
  simpa using this

/-- **Holomorphy in `s`** of the finite Jacquet functional on `Re s > σ₀`, given the
convergence of `K_{σ₀}` (stub S-1: any `σ₀ > 1`). -/
theorem lam_differentiableOn (ψ : SfChar 𝔪) (Φ : GSection ι P 𝔪) (M : ℤ) (η ν : F) (hη : η ≠ 0)
    {σ₀ : ℝ} (hsum : Summable fun u : F ⧸ lat 𝔪 M => normS 𝔪 1 u.out ^ (-σ₀)) :
    DifferentiableOn ℂ (fun s => lam ψ M Φ η ν s) {s : ℂ | σ₀ < s.re} := by
  have hpa := absS_pos (𝔪 := 𝔪) hη
  have hx : ((absS 𝔪 η : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hpa.ne'
  have hopen : IsOpen {s : ℂ | σ₀ < s.re} := isOpen_lt continuous_const Complex.continuous_re
  intro x hx'
  set R : ℝ := ‖x‖ + 1 with hR
  have hUo : IsOpen ({s : ℂ | σ₀ < s.re} ∩ Metric.ball (0 : ℂ) R) := hopen.inter Metric.isOpen_ball
  have hxU : x ∈ {s : ℂ | σ₀ < s.re} ∩ Metric.ball (0 : ℂ) R :=
    ⟨hx', by rw [Metric.mem_ball, dist_zero_right, hR]; linarith⟩
  obtain ⟨B₀, hB₀⟩ := Φ.bound R
  set a := absS 𝔪 η with ha
  set K : ℝ := max 1 (max a a⁻¹) with hK
  have hK1 : 1 ≤ K := le_max_left _ _
  have h1 : a ≤ K * 1 := by rw [mul_one]; exact le_max_of_le_right (le_max_left _ _)
  have h2 : (1 : ℝ) ≤ K * a := by
    have : a⁻¹ ≤ K := le_max_of_le_right (le_max_right _ _)
    calc (1 : ℝ) = a⁻¹ * a := (inv_mul_cancel₀ hpa.ne').symm
      _ ≤ K * a := mul_le_mul_of_nonneg_right this hpa.le
  have hts : DifferentiableOn ℂ (fun s => ∑' u : F ⧸ lat 𝔪 M,
      Φ s η (η * u.out) * (starRingEnd ℂ) (ψ (ν * u.out)))
      ({s : ℂ | σ₀ < s.re} ∩ Metric.ball (0 : ℂ) R) := by
    refine Complex.differentiableOn_tsum_of_summable_norm (hsum.mul_left (|B₀| * K ^ R))
      (fun u => ((Φ.holo _ _).mul_const _).differentiableOn) hUo fun u s hs => ?_
    have hsR : ‖s‖ ≤ R := by
      have := hs.2
      rw [Metric.mem_ball, dist_zero_right] at this
      exact this.le
    have hw1 := one_le_normS_one (𝔪 := 𝔪) u.out
    have e : normS 𝔪 η (η * u.out) = a * normS 𝔪 1 u.out := by
      rw [← normS_mul_left, mul_one]
    have hb := hB₀ s hsR η (η * u.out)
    rw [e, Real.mul_rpow hpa.le (normS_nonneg _ _)] at hb
    have ha' : a ^ (-s.re) ≤ K ^ R := by
      have h3 := rpow_le_of_comparable hpa one_pos hK1 h1 h2 (-s.re)
      rw [Real.one_rpow, mul_one] at h3
      refine h3.trans (Real.rpow_le_rpow_of_exponent_le hK1 ?_)
      rw [abs_neg]
      exact (Complex.abs_re_le_norm s).trans hsR
    have hw' : normS 𝔪 1 u.out ^ (-s.re) ≤ normS 𝔪 1 u.out ^ (-σ₀) :=
      Real.rpow_le_rpow_of_exponent_le hw1 (by have := hs.1; simp only [Set.mem_ofPred_eq] at this; linarith)
    have hn : 0 ≤ normS 𝔪 1 u.out ^ (-s.re) := Real.rpow_nonneg (normS_nonneg _ _) _
    rw [norm_mul, RCLike.norm_conj, ψ.norm_one, mul_one]
    calc ‖Φ s η (η * u.out)‖ ≤ B₀ * (a ^ (-s.re) * normS 𝔪 1 u.out ^ (-s.re)) := hb
      _ ≤ |B₀| * (a ^ (-s.re) * normS 𝔪 1 u.out ^ (-s.re)) :=
          mul_le_mul_of_nonneg_right (le_abs_self _)
            (mul_nonneg (Real.rpow_nonneg hpa.le _) hn)
      _ ≤ |B₀| * (K ^ R * normS 𝔪 1 u.out ^ (-σ₀)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul ha' hw' hn
            (Real.rpow_nonneg (le_trans zero_le_one hK1) _)) (abs_nonneg _)
      _ = _ := by ring
  have hat := (hts x hxU).differentiableAt (hUo.mem_nhds hxU)
  have hcp : DifferentiableAt ℂ (fun s : ℂ => ((absS 𝔪 η : ℝ) : ℂ) ^ s) x :=
    (differentiable_id.const_cpow (Or.inl hx)).differentiableAt
  exact (hcp.mul ((differentiableAt_const _).mul hat)).differentiableWithinAt

end ArtinKP.S
end
end

section
-- module Solutions.Artin.KP.B_FourArch
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
-- module Solutions.Artin.KP.S2_Kubota
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
-- module Solutions.Artin.KP.RF_SNorm
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

/-- `S.lam_differentiableOn` with S-1 plugged in: holomorphy on `Re s > σ₀` for every
`σ₀ > 1`. -/
theorem lam_differentiableOn (ψ : SfChar 𝔪) (hG : Good 𝔪) (Φ : GSection ι P 𝔪) (M : ℤ)
    (η ν : F) (hη : η ≠ 0) {σ₀ : ℝ} (hσ₀ : 1 < σ₀) :
    DifferentiableOn ℂ (fun s => S.lam ψ M Φ η ν s) {s : ℂ | σ₀ < s.re} :=
  S.lam_differentiableOn ψ Φ M η ν hη (hS1 hG M hσ₀)

/-- Holomorphy of the finite Jacquet functional on the whole half-plane `Re s > 1`. -/
theorem lam_differentiableOn_one (ψ : SfChar 𝔪) (hG : Good 𝔪) (Φ : GSection ι P 𝔪) (M : ℤ)
    (η ν : F) (hη : η ≠ 0) :
    DifferentiableOn ℂ (fun s => S.lam ψ M Φ η ν s) {s : ℂ | 1 < s.re} := by
  intro s hs
  have hs' : (1 : ℝ) < s.re := hs
  have hmem : s ∈ {z : ℂ | (1 + s.re) / 2 < z.re} := by
    show (1 + s.re) / 2 < s.re
    linarith
  have hopen : IsOpen {z : ℂ | (1 + s.re) / 2 < z.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  exact ((lam_differentiableOn ψ hG Φ M η ν hη (σ₀ := (1 + s.re) / 2) (by linarith)).differentiableAt
    (hopen.mem_nhds hmem)).differentiableWithinAt

end ArtinKP.GL
end
end

section
-- module Solutions.Artin.KP.G1_Lam
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

/-! ### `Ã(β)` against the other operations -/

/-! ### The Kirillov term -/

theorem Kt_of_ne (ψ : SfChar 𝔪) (hG : Good 𝔪) (Φ : GSection ι P 𝔪) {β : F} (hβ : β ≠ 0)
    (η : F) (s : ℂ) : Kt ψ hG Φ β η s = Lam ψ hG (Φ.torusT hG β hβ) η 1 s := by
  rw [Kt, dif_neg hβ]

/-! ### The cusp change for `Lam` and for the Kirillov term -/

/-! ### The normalized term `ξ^η = |β|^{1/3} Kt(·, 4/3)` -/

end ArtinKP.G1
end
end

section
-- module Solutions.Artin.KP.G1_DS
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

/-! ### `Lam` on a class -/

/-- Every section is `LamDeep` at all large levels (from Lemma DS). -/
theorem exists_lamDeep (ψ : SfChar 𝔪) (hG : Good 𝔪) (Φ : GSection ι P 𝔪) :
    ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → LamDeep ψ hG Φ N := by
  obtain ⟨N₁, hN₁⟩ := GSection.exists_diag hG Φ
  refine ⟨max 1 N₁, le_max_left _ _, fun N hN u hu η ν s => ?_⟩
  have h1 : Small 𝔪 N₁ (u - 1) := hu.mono (by exact_mod_cast (le_max_right 1 N₁).trans hN)
  have hone : (1 : ℤ) ≤ (N : ℤ) := by exact_mod_cast (le_max_left 1 N₁).trans hN
  have habs : absS 𝔪 u = 1 := absS_eq_one_of_val hG.ne_bot (fun v hv => hu.val_eq_one hone v hv)
  rw [Lam, Lam, lam, lam, absS_mul, habs, mul_one]
  congr 2
  funext x
  rw [show η * u * x = u * (η * x) by ring, mul_comm η u, hN₁ _ _ h1 h1]

/-- The same level works for all the translates `Ã(β)Φ`, `β ∈ F^×`: the level of `Ã(β)Φ` as a
section depends on `β`, but its `Lam` is `LamDeep` at a level depending on `Φ` only.
(MATH3 §4.3 applies (CD) to `Ã(β)Φ` without saying why the set of classes can be kept fixed.) -/
theorem exists_lamDeep_torusT (ψ : SfChar 𝔪) (hG : Good 𝔪) (Φ : GSection ι P 𝔪) :
    ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N → P.IsDeepLevel 𝔪 N → ∀ (β : F) (hβ : β ≠ 0),
      LamDeep ψ hG (Φ.torusT hG β hβ) N := by
  obtain ⟨N₀, hN₀1, hN₀⟩ := exists_lamDeep ψ hG Φ
  obtain ⟨v₀, hv₀⟩ := hG.exists_place
  refine ⟨N₀, hN₀1, fun N hNle hN β hβ u hu η ν s => ?_⟩
  by_cases hη : η = 0
  · rw [hη, zero_mul]
  have hN1 : (1 : ℤ) ≤ N := by exact_mod_cast hN₀1.trans hNle
  have hu0 : u ≠ 0 := by
    intro h
    have := hu.val_eq_one hN1 v₀ hv₀
    rw [h, map_zero] at this
    exact zero_ne_one this
  rw [Lam_act ψ hG Φ hβ (mul_ne_zero hη hu0), Lam_act ψ hG Φ hβ hη,
    show β ^ 2 * (η * u) = β ^ 2 * η * u by ring, hN₀ N hNle u hu,
    brk_mul_left _ hη hu0, brk_deep_left hG hN _ hu, mul_one]

/-- **`Lam` on a class**: for `N` deep and `Ψ` `LamDeep` at `N`,
`Lam Ψ c ν s = ⟨η, c⟩ Lam Ψ η ν s` whenever `c ∈ η U_S (F^×)³ U_N`. -/
theorem Lam_class (ψ : SfChar 𝔪) (hG : Good 𝔪) (Ψ : GSection ι P 𝔪) {N : ℕ} (hN1 : 1 ≤ N)
    (hN : P.IsDeepLevel 𝔪 N) (hd : LamDeep ψ hG Ψ N) {η c : F} (ν : F) (s : ℂ) (hη : η ≠ 0)
    (hcl : InClass 𝔪 N η c) : Lam ψ hG Ψ c ν s = brk ι P 𝔪 η c * Lam ψ hG Ψ η ν s := by
  obtain ⟨v₀, hv₀⟩ := hG.exists_place
  obtain ⟨ε, t, u, ht, hu, rfl⟩ := hcl
  have hN1' : (1 : ℤ) ≤ N := by exact_mod_cast hN1
  have hu0 : u ≠ 0 := by
    intro h
    have := hu.val_eq_one hN1' v₀ hv₀
    rw [h, map_zero] at this
    exact zero_ne_one this
  have hε0 : ((ε : SInt 𝔪) : F) ≠ 0 := fun h => ε.ne_zero (Subtype.ext h)
  have hηu : η * u ≠ 0 := mul_ne_zero hη hu0
  rw [show η * ((ε : SInt 𝔪) : F) * t ^ 3 * u = ((ε : SInt 𝔪) : F) * (t ^ 3 * (η * u)) by ring,
    Lam_unit ψ hG Ψ ε (mul_ne_zero (pow_ne_zero 3 ht) hηu), Lam_cube ψ hG Ψ ht, hd u hu]
  congr 1
  have d1 : brk ι P 𝔪 u ((ε : SInt 𝔪) : F) = 1 := brk_deep_left hG hN _ hu
  have d2 : brk ι P 𝔪 η u = 1 := brk_deep_right hG hN _ hu
  simp [brk_mul_left, brk_mul_right, hη, hu0, hε0, ht, d1, d2]

/-! ### Big cells -/

theorem valid_bigCell (ψ : SfChar 𝔪) (hG : Good 𝔪) {N : ℕ} (hN1 : 1 ≤ N)
    (hN : P.IsDeepLevel 𝔪 N) (η : F) (hη : η ≠ 0) (M : ℤ) (t₀ : F) {ν : F}
    (hψ : ∀ h : F, Small 𝔪 M h → ψ (ν * h) = 1) :
    Valid ψ (bigCell ι P hG hN1 hN η hη M t₀) ν (fun _ => M) := by
  refine ⟨fun b hb s c d => ?_, hψ⟩
  by_cases hc : c = 0
  · rw [hc, zero_mul, add_zero]
  have e : (d + c * b) / c - t₀ = (d / c - t₀) + b := by field_simp; ring
  have hiff : Supp 𝔪 N η M t₀ c (d + c * b) ↔ Supp 𝔪 N η M t₀ c d := by
    unfold Supp
    rw [e]
    exact and_congr_right fun _ =>
      ⟨fun h => by simpa using Small.sub h hb, fun h => Small.add h hb⟩
  rw [bigCell_apply, bigCell_apply]
  simp only [bigFun]
  by_cases hS : Supp 𝔪 N η M t₀ c d
  · rw [if_pos hS, if_pos (hiff.mpr hS)]
  · rw [if_neg hS, if_neg fun h' => hS (hiff.mp h')]

open Classical in
/-- **`Lam` of a big-cell section**, at every `c ≠ 0`:
`vol(𝔩_M) ⟨η, c⟩ conj ψ(ν t₀)` on the class of `η`, `0` off it. -/
theorem Lam_bigCell (ψ : SfChar 𝔪) (hG : Good 𝔪) {N : ℕ} (hN1 : 1 ≤ N)
    (hN : P.IsDeepLevel 𝔪 N) (η : F) (hη : η ≠ 0) (M : ℤ) (t₀ : F) {ν : F}
    (hψ : ∀ h : F, Small 𝔪 M h → ψ (ν * h) = 1) {c : F} (hc : c ≠ 0) (s : ℂ) :
    Lam ψ hG (bigCell ι P hG hN1 hN η hη M t₀) c ν s
      = if InClass 𝔪 N η c
          then ((vol 𝔪 M : ℝ) : ℂ) * brk ι P 𝔪 η c * (starRingEnd ℂ) (ψ (ν * t₀)) else 0 := by
  rw [Lam_eq_lam ψ hG _ (valid_bigCell ψ hG hN1 hN η hη M t₀ hψ)]
  by_cases hcl : InClass 𝔪 N η c
  · rw [if_pos hcl, lam]
    have hfun : (fun u => bigCell ι P hG hN1 hN η hη M t₀ s c (c * u))
        = fun u => if Small 𝔪 M (u - t₀)
            then brk ι P 𝔪 η c * ((absS 𝔪 c : ℝ) : ℂ) ^ (-s) else 0 := by
      funext u
      rw [bigCell_apply]
      by_cases hu : Small 𝔪 M (u - t₀)
      · rw [if_pos hu, bigFun_of_supp ⟨hcl, by rw [mul_div_cancel_left₀ _ hc]; exact hu⟩]
      · rw [if_neg hu, bigFun_of_not_supp fun h => hu (by
          have := h.2
          rwa [mul_div_cancel_left₀ _ hc] at this)]
    rw [hfun, jac_indicator ψ _ t₀ hψ]
    have hcp := S2.cpow_mul_cpow_neg (absS_pos (𝔪 := 𝔪) hc) s
    linear_combination (((vol 𝔪 M : ℝ) : ℂ) * brk ι P 𝔪 η c * (starRingEnd ℂ) (ψ (ν * t₀))) * hcp
  · rw [if_neg hcl]
    exact lam_bigCell_of_not_inClass ψ hG hN1 hN η hη M M t₀ c ν hcl s

theorem vol_pos (M : ℤ) : 0 < vol 𝔪 M :=
  Finset.prod_pos fun v _ => zpow_pos (by
    have := NumberField.HeightOneSpectrum.one_lt_absNorm v
    exact_mod_cast (by omega : 0 < Ideal.absNorm v.asIdeal)) _

/-- **The class decomposition (CD) at the level of `Lam`**: for `N` deep, `Ψ` `LamDeep` at `N`,
a complete system `T` of pairwise disjoint classes of level `N` (`RO.exists_classReps`), every
frequency `ν` and every depth `M` with `ψ(ν 𝔩_M) = 1`,
`Lam Ψ c ν s = Σ_{η ∈ T} Lam Ψ η ν s · (vol(𝔩_M)⁻¹ · Lam (bigCell_{η,M,0}) c ν s)`, `c ≠ 0`. -/
theorem Lam_classDecomp (ψ : SfChar 𝔪) (hG : Good 𝔪) (Ψ : GSection ι P 𝔪) {N : ℕ}
    (hN1 : 1 ≤ N) (hN : P.IsDeepLevel 𝔪 N) (hd : LamDeep ψ hG Ψ N)
    (T : Finset {η : F // η ≠ 0})
    (hdisj : ∀ η ∈ T, ∀ η' ∈ T, η ≠ η' → ∀ c : F, InClass 𝔪 N η.1 c → ¬ InClass 𝔪 N η'.1 c)
    (hcov : ∀ c : F, c ≠ 0 → ∃ η ∈ T, InClass 𝔪 N η.1 c)
    (M : ℤ) {ν : F} (hψ : ∀ h : F, Small 𝔪 M h → ψ (ν * h) = 1) {c : F} (hc : c ≠ 0) (s : ℂ) :
    Lam ψ hG Ψ c ν s = ∑ η ∈ T, Lam ψ hG Ψ η.1 ν s *
      (((vol 𝔪 M : ℝ) : ℂ)⁻¹ * Lam ψ hG (bigCell ι P hG hN1 hN η.1 η.2 M 0) c ν s) := by
  classical
  obtain ⟨η₀, hη₀, hcl⟩ := hcov c hc
  have hvol : ((vol 𝔪 M : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (vol_pos M).ne'
  rw [Finset.sum_eq_single η₀]
  · rw [Lam_bigCell ψ hG hN1 hN η₀.1 η₀.2 M 0 hψ hc, if_pos hcl, mul_zero, ψ.map_zero, map_one,
      Lam_class ψ hG Ψ hN1 hN hd ν s η₀.2 hcl]
    field_simp
  · intro η hη hne
    rw [Lam_bigCell ψ hG hN1 hN η.1 η.2 M 0 hψ hc,
      if_neg (hdisj η₀ hη₀ η hη (Ne.symm hne) c hcl), mul_zero, mul_zero]
  · intro h
    exact absurd hη₀ h

end ArtinKP.G1
end
end

section
-- module Solutions.Artin.KP.G1_Res
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

end theta

end ArtinKP.G1
end

section
-- module Solutions.Artin.KP.RO_Bridge
/-! # WP-RO, file 3: the bridge `S.Row 𝔪 / U_S ≃ B1.PairClass (SOf 𝔪)`

`h𝔪 : 𝔪 ≠ ⊥` throughout (no other hypothesis on `𝔪`).

* `rowPair`, `rowClass h𝔪 : Row 𝔪 → PairClass (SOf 𝔪)`; `rowClass_eq_iff` (fibres = `U_S`-orbits),
  `rowClass_surjective`, `rowClassEquiv : orbitRel.Quotient (SInt 𝔪)ˣ (Row 𝔪) ≃ PairClass (SOf 𝔪)`.
* actions: `intMat 𝔪 : SL₂(𝓞) →* SL₂(R)` (the map defining `Gamma 𝔪 𝔫`), `rowClass_act_intMat`
  (`SL₂(𝓞)`), `rowClass_act` (`SL₂(R)`, through `A.toF` and `B1.PairClass.actR`), `rowClass_bot`,
  `exists_toF_eq` (every `IsSMat` matrix comes from `SL₂(R)`).
* norms and heights: `sNorm_SOf` (`X.sNorm (SOf 𝔪) = S.normS 𝔪`), `ht_rowClass`
  (`ht_p(P) = I_p(P) / ‖p‖`), `prod_SOf_eq_absS`, and the product formula for `S`-units
  `prod_normSq_mul_absS : N_∞(ε) · |ε|_{S_f} = 1` (WP-S open issue 7), `pairHt_smul_row`.
-/

open scoped MatrixGroups
open NumberField IsDedekindDomain ArtinPrimitiveRoots

set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.RO

open ArtinKP.A ArtinKP.B1 ArtinKP.X ArtinKP.S

noncomputable section

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}

/-! ### Rows and pair classes -/

/-! ### Actions -/

/-! ### Norms and heights -/

theorem finitePlace_mk_apply (v : HeightOneSpectrum (𝓞 F)) (x : F) :
    FinitePlace.mk v x = NumberField.HeightOneSpectrum.adicAbv F v x := by
  rw [FinitePlace.mk_apply, FinitePlace.norm_embedding]

open scoped Classical in
theorem prod_SOf (f : FinitePlace F → ℝ) :
    ∏ v ∈ SOf 𝔪, f v = ∏ v ∈ CubicPkg.sFin 𝔪, f (FinitePlace.mk v) := by
  rw [SOf, Finset.prod_image]
  intro v _ v' _ h
  exact FinitePlace.mk_eq_iff.mp h

/-- `‖(c, d)‖` of WP-B1/WP-X is `normS` of WP-S. -/
theorem sNorm_SOf (c d : F) : X.sNorm (SOf 𝔪) c d = normS 𝔪 c d := by
  unfold X.sNorm normS
  rw [prod_SOf]
  exact Finset.prod_congr rfl fun v _ => by rw [finitePlace_mk_apply, finitePlace_mk_apply]

end

end ArtinKP.RO
end

section
-- module Solutions.Artin.KP.RO_Classes
/-! # WP-RO, file 5: finiteness of the class set `𝒞 = F^× / U_S (F^×)³ U_N` (WP-S open issue 6)

Everything is `F : Type*`; no completion, no Hilbert symbol and none of the `F : Type` stubs is used:
already `F^× / U_S U_N` is finite, `U_N = {u : Small 𝔪 N (u - 1)}`.

* `exists_bdd_rescale`: there is `K` such that every `c ≠ 0` has an `S`-unit multiple `c' ∈ 𝓞` with
  `v(c') > exp(-K)` at all `v ∣ 𝔪` (from `B1.exists_unit_rescale`).
* `small_div_sub_one`: two such integers congruent modulo `𝔪^(K+N)` have quotient in `U_N`.
* `exists_finite_cover`: a finite `T ⊂ F^×` with `F^× = ⋃_{η ∈ T} η U_S U_N` (any `N`, `𝔪 ≠ ⊥`).
* `InClass.refl'`, `InClass.symm'`, `InClass.trans'`: `S.InClass 𝔪 N` is an equivalence relation on
  `F^×` for `N ≥ 1`.
* **`exists_classReps`**: for `Good 𝔪`, `N ≥ 1`, a finite complete set of pairwise disjoint classes,
  in exactly the form `S.sum_bigCell_apply` takes (`hdisj`).
-/

open scoped MatrixGroups
open NumberField IsDedekindDomain ArtinPrimitiveRoots

set_option autoImplicit false
set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.RO

open ArtinKP.A ArtinKP.B1 ArtinKP.X ArtinKP.S

noncomputable section

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}

theorem exists_bdd_rescale (h𝔪 : 𝔪 ≠ ⊥) : ∃ K : ℕ, ∀ a : 𝓞 F, a ≠ 0 →
    ∃ (ε : (SInt 𝔪)ˣ) (c' : 𝓞 F), (c' : F) = ((ε : SInt 𝔪) : F) * (a : F) ∧ Bdd 𝔪 K c' := by
  classical
  obtain ⟨δ, hδ, hres⟩ := exists_unit_rescale (SOf 𝔪)
  obtain ⟨K, hK⟩ := exists_pow_lt_of_lt_one hδ (by norm_num : (1 / 2 : ℝ) < 1)
  refine ⟨K, fun a ha => ?_⟩
  have haF : (a : F) ≠ 0 := by simpa using ha
  obtain ⟨u, hu0, huS, ⟨c', -, hc', -⟩, hle⟩ := hres (a : F) 0 (Or.inl haF)
    (fun v hv => isSInt_int (S := SOf 𝔪) a v hv) (fun v _ => by simp)
  obtain ⟨ε, hε⟩ := exists_unit_of_isSUnit h𝔪 (u := u) ⟨hu0, huS⟩
  have hc'F : (c' : F) ≠ 0 := by rw [hc']; exact mul_ne_zero hu0 haF
  refine ⟨ε, c', by rw [hε, hc'], fun h0 => hc'F (by rw [h0]; simp), fun v hv => ?_⟩
  by_contra hcon
  rw [not_lt] at hcon
  have h1 := abv_le_of_val_le v hcon
  rw [sNorm_SOf, ← hc'] at hle
  have hvS : v ∈ CubicPkg.sFin 𝔪 := (CubicPkg.mem_sFin h𝔪 v).mpr hv
  set f : HeightOneSpectrum (𝓞 F) → ℝ := fun w =>
    max (NumberField.HeightOneSpectrum.adicAbv F w (c' : F))
      (NumberField.HeightOneSpectrum.adicAbv F w (u * 0)) with hf
  have hf0 : ∀ w, 0 ≤ f w := fun w => le_max_of_le_left ((NumberField.HeightOneSpectrum.adicAbv F w).nonneg _)
  have hf1 : ∀ w, f w ≤ 1 := fun w => by
    have h2 : NumberField.HeightOneSpectrum.adicAbv F w (c' : F) ≤ 1 := by
      have := abv_le_of_val_le w (x := (c' : F)) (n := 0) (by simpa using w.valuation_le_one c')
      simpa using this
    simp only [hf, mul_zero, map_zero]
    exact max_le h2 zero_le_one
  have hfv : f v = NumberField.HeightOneSpectrum.adicAbv F v (c' : F) := by
    simp only [hf, mul_zero, map_zero]
    exact max_eq_left ((NumberField.HeightOneSpectrum.adicAbv F v).nonneg _)
  have h3 : normS 𝔪 (c' : F) (u * 0) ≤ f v := by
    unfold normS
    rw [← Finset.mul_prod_erase _ _ hvS]
    exact mul_le_of_le_one_right (hf0 v) (Finset.prod_le_one (fun w _ => hf0 w) fun w _ => hf1 w)
  have hq : (2 : ℝ) ≤ (Ideal.absNorm v.asIdeal : ℝ) := by
    have := NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal v
    have h' : 1 < Ideal.absNorm v.asIdeal := by exact_mod_cast this
    exact_mod_cast h'
  have h4 : (Ideal.absNorm v.asIdeal : ℝ) ^ (-(K : ℤ)) ≤ (1 / 2 : ℝ) ^ K := by
    rw [zpow_neg, zpow_natCast, one_div, inv_pow]
    exact inv_anti₀ (by positivity) (pow_le_pow_left₀ (by norm_num) hq K)
  linarith [hfv ▸ h3]

/-- Two bounded integers congruent modulo `𝔪^(K+N)` have quotient in `U_N`. -/
theorem small_div_sub_one {K N : ℕ} {a r : 𝓞 F} (hr : Bdd 𝔪 K r) (h : a - r ∈ 𝔪 ^ (K + N)) :
    Small 𝔪 N ((a : F) / (r : F) - 1) := by
  intro v hv
  have hmem : a - r ∈ v.asIdeal ^ (K + N) := Ideal.pow_right_mono hv _ h
  have h1 := (v.intValuation_le_pow_iff_mem _ (K + N)).mpr hmem
  rw [← v.valuation_of_algebraMap (K := F)] at h1
  have hrF : (r : F) ≠ 0 := by simpa using hr.1
  have hpos : 0 < v.valuation F (r : F) := lt_of_le_of_lt zero_le (hr.2 v hv)
  have e : (a : F) / (r : F) - 1 = algebraMap (𝓞 F) F (a - r) / (r : F) := by
    rw [map_sub]; field_simp
  rw [e, map_div₀, div_le_iff₀ hpos]
  refine h1.trans ?_
  have e2 : WithZero.exp (-((K + N : ℕ) : ℤ)) = WithZero.exp (-(N : ℤ)) * WithZero.exp (-(K : ℤ)) := by
    rw [← WithZero.exp_add]; congr 1; push_cast; ring
  rw [e2]
  exact mul_le_mul' le_rfl (hr.2 v hv).le

/-! ### `U_N` is a group for `N ≥ 1` -/

theorem small_mul_sub_one {N : ℕ} (hN1 : 1 ≤ N) {u u' : F} (h : Small 𝔪 N (u - 1))
    (h' : Small 𝔪 N (u' - 1)) : Small 𝔪 N (u * u' - 1) := by
  intro v hv
  have hu' := h'.val_eq_one (by exact_mod_cast hN1) v hv
  have e : u * u' - 1 = (u - 1) * u' + (u' - 1) := by ring
  rw [e]
  refine (Valuation.map_add _ _ _).trans (max_le ?_ (h' v hv))
  rw [map_mul, hu', mul_one]
  exact h v hv

theorem small_inv_sub_one {N : ℕ} (hN1 : 1 ≤ N) {u : F} (h : Small 𝔪 N (u - 1)) :
    Small 𝔪 N (u⁻¹ - 1) := by
  intro v hv
  have hu := h.val_eq_one (by exact_mod_cast hN1) v hv
  have hu0 : u ≠ 0 := by
    intro h0; rw [h0, map_zero] at hu; exact zero_ne_one hu
  have e : u⁻¹ - 1 = -(u - 1) * u⁻¹ := by field_simp; ring
  rw [e, map_mul, map_inv₀, hu, inv_one, mul_one, Valuation.map_neg]
  exact h v hv

/-! ### A finite cover -/

/-- Nonzero integers fall into finitely many classes modulo `U_S U_N`. -/
theorem exists_finite_cover_int (h𝔪 : 𝔪 ≠ ⊥) (N : ℕ) : ∃ T : Finset F, (∀ η ∈ T, η ≠ 0) ∧
    ∀ a : 𝓞 F, a ≠ 0 → ∃ η ∈ T, ∃ (ε : (SInt 𝔪)ˣ) (u : F), Small 𝔪 N (u - 1) ∧
      (a : F) = η * ((ε : SInt 𝔪) : F) * u := by
  classical
  obtain ⟨K, hK⟩ := exists_bdd_rescale h𝔪
  have h𝔑 : 𝔪 ^ (K + N) ≠ ⊥ := pow_ne_zero _ h𝔪
  have := Ideal.finiteQuotientOfFreeOfNeBot _ h𝔑
  have := Fintype.ofFinite (𝓞 F ⧸ 𝔪 ^ (K + N))
  set rep : 𝓞 F ⧸ 𝔪 ^ (K + N) → 𝓞 F := fun x =>
    if h : ∃ r : 𝓞 F, Bdd 𝔪 K r ∧ Ideal.Quotient.mk _ r = x then h.choose else 1 with hrep
  have hrep0 : ∀ x, (rep x : F) ≠ 0 := by
    intro x
    simp only [hrep]
    split_ifs with h
    · simpa using h.choose_spec.1.1
    · simp
  refine ⟨Finset.univ.image fun x => (rep x : F), fun η hη => ?_, fun a ha => ?_⟩
  · obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hη
    exact hrep0 x
  · obtain ⟨ε, c', hc', hb⟩ := hK a ha
    have hex : ∃ r : 𝓞 F, Bdd 𝔪 K r ∧ Ideal.Quotient.mk (𝔪 ^ (K + N)) r = Ideal.Quotient.mk _ c' :=
      ⟨c', hb, rfl⟩
    have hr : rep (Ideal.Quotient.mk _ c') = hex.choose := by simp only [hrep, dif_pos hex]
    obtain ⟨hrb, hrq⟩ := hex.choose_spec
    rw [← hr] at hrb hrq
    set r := rep (Ideal.Quotient.mk _ c') with hrdef
    have hmem : c' - r ∈ 𝔪 ^ (K + N) := Ideal.Quotient.eq.mp hrq.symm
    have hrF : (r : F) ≠ 0 := hrep0 _
    have hε0 : ((ε : SInt 𝔪) : F) ≠ 0 := (isSUnit_coe_unit h𝔪 ε).1
    have hεinv : (((ε⁻¹ : (SInt 𝔪)ˣ) : SInt 𝔪) : F) = (((ε : SInt 𝔪) : F))⁻¹ := by
      refine eq_inv_of_mul_eq_one_left ?_
      rw [← MulMemClass.coe_mul, ε.inv_mul]; rfl
    refine ⟨(r : F), Finset.mem_image_of_mem _ (Finset.mem_univ _), ε⁻¹, (c' : F) / (r : F),
      small_div_sub_one hrb hmem, ?_⟩
    rw [hεinv, hc']
    field_simp

/-- **`F^× / U_S U_N` is finite**: a finite set of representatives. -/
theorem exists_finite_cover (h𝔪 : 𝔪 ≠ ⊥) (N : ℕ) : ∃ T : Finset F, (∀ η ∈ T, η ≠ 0) ∧
    ∀ c : F, c ≠ 0 → ∃ η ∈ T, ∃ (ε : (SInt 𝔪)ˣ) (u : F), Small 𝔪 N (u - 1) ∧
      c = η * ((ε : SInt 𝔪) : F) * u := by
  classical
  obtain ⟨T, hT0, hT⟩ := exists_finite_cover_int h𝔪 (N + 1)
  refine ⟨Finset.image₂ (fun x y => x / y) T T, fun η hη => ?_, fun c hc => ?_⟩
  · obtain ⟨x, hx, y, hy, rfl⟩ := Finset.mem_image₂.mp hη
    exact div_ne_zero (hT0 x hx) (hT0 y hy)
  · obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 F) c
    have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
    have ha0 : a ≠ 0 := by
      rintro rfl
      simp at hc
    obtain ⟨η₁, hη₁, ε₁, u₁, hu₁, e₁⟩ := hT a ha0
    obtain ⟨η₂, hη₂, ε₂, u₂, hu₂, e₂⟩ := hT b hb0
    have hN1 : 1 ≤ N + 1 := Nat.le_add_left 1 N
    have hbF : algebraMap (𝓞 F) F b ≠ 0 := by simpa using hb0
    have hu₂0 : u₂ ≠ 0 := by
      intro h0
      have e₂' : algebraMap (𝓞 F) F b = η₂ * ((ε₂ : SInt 𝔪) : F) * u₂ := e₂
      rw [e₂', h0, mul_zero] at hbF; exact hbF rfl
    have hε₂0 : ((ε₂ : SInt 𝔪) : F) ≠ 0 := (isSUnit_coe_unit h𝔪 ε₂).1
    have hεinv : (((ε₂⁻¹ : (SInt 𝔪)ˣ) : SInt 𝔪) : F) = (((ε₂ : SInt 𝔪) : F))⁻¹ := by
      refine eq_inv_of_mul_eq_one_left ?_
      rw [← MulMemClass.coe_mul, ε₂.inv_mul]; rfl
    refine ⟨η₁ / η₂, Finset.mem_image₂_of_mem hη₁ hη₂, ε₁ * ε₂⁻¹, u₁ * u₂⁻¹,
      Small.mono (by omega) (small_mul_sub_one hN1 hu₁ (small_inv_sub_one hN1 hu₂)), ?_⟩
    have hη₂0 := hT0 η₂ hη₂
    have e₁' : algebraMap (𝓞 F) F a = η₁ * ((ε₁ : SInt 𝔪) : F) * u₁ := e₁
    have e₂' : algebraMap (𝓞 F) F b = η₂ * ((ε₂ : SInt 𝔪) : F) * u₂ := e₂
    rw [Units.val_mul, MulMemClass.coe_mul, hεinv, e₁', e₂']
    field_simp

/-! ### `InClass` is an equivalence relation on `F^×`; disjoint representatives -/

theorem InClass.trans' {N : ℕ} (hN1 : 1 ≤ N) {a b c : F} (h : InClass 𝔪 N a b)
    (h' : InClass 𝔪 N b c) : InClass 𝔪 N a c := by
  obtain ⟨ε, t, u, ht, hu, rfl⟩ := h
  obtain ⟨ε', t', u', ht', hu', rfl⟩ := h'
  refine ⟨ε * ε', t * t', u * u', mul_ne_zero ht ht', small_mul_sub_one hN1 hu hu', ?_⟩
  rw [Units.val_mul, MulMemClass.coe_mul]
  ring

theorem InClass.symm' {N : ℕ} (hN1 : 1 ≤ N) {a b : F} (h : InClass 𝔪 N a b) (hb : b ≠ 0) :
    InClass 𝔪 N b a := by
  obtain ⟨ε, t, u, ht, hu, rfl⟩ := h
  have hu0 : u ≠ 0 := right_ne_zero_of_mul hb
  have hε0 : ((ε : SInt 𝔪) : F) ≠ 0 := right_ne_zero_of_mul (left_ne_zero_of_mul (left_ne_zero_of_mul hb))
  have hεinv : (((ε⁻¹ : (SInt 𝔪)ˣ) : SInt 𝔪) : F) = (((ε : SInt 𝔪) : F))⁻¹ := by
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← MulMemClass.coe_mul, ε.inv_mul]; rfl
  refine ⟨ε⁻¹, t⁻¹, u⁻¹, inv_ne_zero ht, small_inv_sub_one hN1 hu, ?_⟩
  rw [hεinv]
  field_simp

open scoped Classical in
/-- **Finiteness of `𝒞 = F^× / U_S (F^×)³ U_N`** (WP-S open issue 6): a finite complete set of
pairwise disjoint classes, in the form used by `S.sum_bigCell_apply`. -/
theorem exists_classReps (hG : Good 𝔪) {N : ℕ} (hN1 : 1 ≤ N) :
    ∃ T : Finset {η : F // η ≠ 0},
      (∀ η ∈ T, ∀ η' ∈ T, η ≠ η' → ∀ c, InClass 𝔪 N η.1 c → ¬ InClass 𝔪 N η'.1 c) ∧
      ∀ c : F, c ≠ 0 → ∃ η ∈ T, InClass 𝔪 N η.1 c := by
  obtain ⟨T₀, hT₀0, hT₀⟩ := exists_finite_cover hG.ne_bot N
  have hcov : ∀ c : F, c ≠ 0 → ∃ η ∈ T₀, InClass 𝔪 N η c := by
    intro c hc
    obtain ⟨η, hη, ε, u, hu, rfl⟩ := hT₀ c hc
    exact ⟨η, hη, ε, 1, u, one_ne_zero, hu, by ring⟩
  -- the class of `c`, as a set, and a representative depending only on that set
  set cls : F → Set F := fun c => {η | InClass 𝔪 N η c} with hcls
  have hcls_eq : ∀ {a b : F}, InClass 𝔪 N a b → b ≠ 0 → cls a = cls b := by
    intro a b hab hb
    ext η
    exact ⟨fun h => InClass.trans' hN1 h hab, fun h => InClass.trans' hN1 h (InClass.symm' hN1 hab hb)⟩
  set g : Set F → F := fun A => if h : ∃ η ∈ T₀, η ∈ A then h.choose else 1 with hg
  have hgs : ∀ c : F, c ≠ 0 → g (cls c) ∈ T₀ ∧ InClass 𝔪 N (g (cls c)) c := by
    intro c hc
    have hex : ∃ η ∈ T₀, η ∈ cls c := hcov c hc
    simp only [hg, dif_pos hex]
    exact hex.choose_spec
  refine ⟨(T₀.image fun η => g (cls η)).subtype (· ≠ 0), ?_, ?_⟩
  · intro η hη η' hη' hne c hc hc'
    rw [Finset.mem_subtype] at hη hη'
    obtain ⟨a, ha, hae⟩ := Finset.mem_image.mp hη
    obtain ⟨b, hb, hbe⟩ := Finset.mem_image.mp hη'
    have hc0 : c ≠ 0 := InClass.ne_zero hG hN1 η.2 hc
    have h1 : cls a = cls c := by
      rw [← hcls_eq (hgs a (hT₀0 a ha)).2 (hT₀0 a ha), hae]
      exact hcls_eq hc hc0
    have h2 : cls b = cls c := by
      rw [← hcls_eq (hgs b (hT₀0 b hb)).2 (hT₀0 b hb), hbe]
      exact hcls_eq hc' hc0
    exact hne (Subtype.ext (by rw [← hae, ← hbe, h1, h2]))
  · intro c hc
    obtain ⟨η₀, hη₀, hin⟩ := hcov c hc
    obtain ⟨hmem, hin'⟩ := hgs η₀ (hT₀0 η₀ hη₀)
    refine ⟨⟨g (cls η₀), hT₀0 _ hmem⟩, ?_, InClass.trans' hN1 hin' hin⟩
    rw [Finset.mem_subtype]
    exact Finset.mem_image_of_mem _ hη₀

end

end ArtinKP.RO
end

section
-- module Solutions.Artin.KP.G1_Kir
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

/-! ### The Kirillov function -/

theorem Kir_of_ne (Φ : GSection ι P 𝔪) {β : F} (hβ : β ≠ 0) :
    Kir hG hz6 T Φ β = T.tau (Φ.torusT hG β hβ) 1 := by
  rw [Kir, dif_neg hβ]

/-! ### The class decomposition and the majorant -/

/-- **(CD)**, MATH3 §4.3: for `N` deep, `Ψ` `LamDeep` at `N`, a complete system `Tc` of pairwise
disjoint classes of level `N`, `ν ∈ R ∖ 0` and a depth `M` with `ψ(ν 𝔩_M) = 1`:
`τ_Ψ(ν) = Σ_{η ∈ Tc} Lam Ψ η ν (4/3) · (vol(𝔩_M)⁻¹ · τ_{bigCell_{η,M,0}}(ν))`.
Needs the scalar law for multipliers holomorphic on `Re s > 1`. -/
theorem tau_classDecomp (hsm : T.toResFun.SmulOn {s : ℂ | 1 < s.re}) (Ψ : GSection ι P 𝔪)
    {N : ℕ} (hN1 : 1 ≤ N) (hN : P.IsDeepLevel 𝔪 N) (hd : LamDeep (B.psiS hG.ne_bot) hG Ψ N)
    (Tc : Finset {η : F // η ≠ 0})
    (hdisj : ∀ η ∈ Tc, ∀ η' ∈ Tc, η ≠ η' → ∀ c : F, InClass 𝔪 N η.1 c → ¬ InClass 𝔪 N η'.1 c)
    (hcov : ∀ c : F, c ≠ 0 → ∃ η ∈ Tc, InClass 𝔪 N η.1 c)
    (M : ℤ) {ν : SInt 𝔪} (hν : ν ≠ 0)
    (hψ : ∀ h : F, Small 𝔪 M h → B.psiS hG.ne_bot ((ν : F) * h) = 1) :
    T.tau Ψ ν = ∑ η ∈ Tc, Lam (B.psiS hG.ne_bot) hG Ψ η.1 (ν : F) (4 / 3) *
      (((vol 𝔪 M : ℝ) : ℂ)⁻¹ * T.tau (bigCell ι P hG hN1 hN η.1 η.2 M 0) ν) := by
  have h := T.tau_sum_at hsm Tc (fun η => bigCell ι P hG hN1 hN η.1 η.2 M 0)
    (fun η s => Lam (B.psiS hG.ne_bot) hG Ψ η.1 (ν : F) s * ((vol 𝔪 M : ℝ) : ℂ)⁻¹)
    (fun η _ => (GL.lam_differentiableOn_one (B.psiS hG.ne_bot) hG Ψ _ η.1 (ν : F) η.2).mul
      (differentiableOn_const _)) (Φ := Ψ) hν
    (fun c s hc hs => by
      have := Lam_classDecomp (B.psiS hG.ne_bot) hG Ψ hN1 hN hd Tc hdisj hcov M hψ
        (coe_ne_zero' hc) s
      refine this.trans (Finset.sum_congr rfl fun η _ => ?_)
      show _ = _ * Lam (B.psiS hG.ne_bot) hG _ (c : F) (ν : F) s
      ring)
  rw [h]
  exact Finset.sum_congr rfl fun η _ => by ring

/-- **The Kirillov function as a finite sum over classes**, with a set of classes and weights
independent of `β`: `𝒦_Φ(β) = Σ_{η ∈ Tc} Kt Φ β η (4/3) · w(η)` for all `β ∈ F^×`. -/
theorem exists_Kir_classDecomp_oai (hsm : T.toResFun.SmulOn {s : ℂ | 1 < s.re})
    (Φ : GSection ι P 𝔪) :
    ∃ (Tc : Finset {η : F // η ≠ 0}) (w : {η : F // η ≠ 0} → ℂ), ∀ β : F, β ≠ 0 →
      Kir hG hz6 T Φ β = ∑ η ∈ Tc, Kt (B.psiS hG.ne_bot) hG Φ β η.1 (4 / 3) * w η := by
  obtain ⟨N₀, hN₀1, hN₀⟩ := exists_lamDeep_torusT (B.psiS hG.ne_bot) hG Φ
  obtain ⟨N₁, hN₁1, hN₁⟩ := P.exists_isDeepLevel hG.ne_bot
  have hN1 : 1 ≤ max N₀ N₁ := hN₀1.trans (le_max_left _ _)
  have hN : P.IsDeepLevel 𝔪 (max N₀ N₁) := CubicPkg.IsDeepLevel.mono P hN₁ (le_max_right _ _)
  obtain ⟨Tc, hdisj, hcov⟩ := RO.exists_classReps hG hN1
  refine ⟨Tc, fun η => ((vol 𝔪 0 : ℝ) : ℂ)⁻¹ * T.tau (bigCell ι P hG hN1 hN η.1 η.2 0 0) 1,
    fun β hβ => ?_⟩
  have h1 : ((1 : SInt 𝔪) : F) = 1 := rfl
  rw [Kir_of_ne hG hz6 T Φ hβ,
    tau_classDecomp hG hz6 T hsm _ hN1 hN (hN₀ _ (le_max_left _ _) hN β hβ) Tc hdisj hcov 0
      one_ne_zero (fun h hh => by rw [h1, one_mul]; exact B.psiS_small hG.ne_bot hh)]
  refine Finset.sum_congr rfl fun η _ => ?_
  rw [h1, Kt_of_ne _ hG Φ hβ]

end tau

end ArtinKP.G1
end
end

theorem solution.{u_1} : type_of% @ArtinKP.G1.exists_Kir_classDecomp_oai.{u_1} := @ArtinKP.G1.exists_Kir_classDecomp_oai.{u_1}
