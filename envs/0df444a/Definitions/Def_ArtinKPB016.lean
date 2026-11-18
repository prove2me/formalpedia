-- Prove2me | Definitions.Def_ArtinKPB016
-- name    : ArtinKPB016
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-11-17T09:53:08.862192+00:00
-- url     : https://prove2.me/theorems/e47ea7cc-bbd2-413e-80ca-b60c597f882f
-- title:
--   Definitions bundle ArtinKPB016 of the split of the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function)
-- statement:
--   A definitions bundle of the split of the formal proof of `ArtinPrimitiveRoots.exists_cutoff_exists_tsum_thetaWhittaker_sub_tsum_weylWhittaker_rotInvariant`, carved for this platform from the Lean development *the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function)* by the submitter, written with Claude. The declarations and their proofs are that development's. It formalizes part of the proof of Theorem 1.2 of OpenAI's paper *Primitive roots for every admissible integer base* (2026; github.com/openai/math, family 029), the step that rests on the cubic theta function of D. A. Kazhdan and S. J. Patterson, *Metaplectic forms*, Publ. Math. IHÉS 59 (1984), 35–142. It compiles with Lean 4.33.1 and Mathlib 0df444a.
--
--   **Contents.** It holds 58 declarations of that development: 29 definitions, 2 inductive types or structures and 27 theorems. The definitions and types are `ArtinKP.E.ResFun`, `ArtinKP.E.ResFun.SmulOn`, `ArtinKP.E.ResFun.ofContinuation`, `ArtinKP.E.Theta`, `ArtinKP.E.resFunSlit`, `ArtinKP.G1.Adual`, `ArtinKP.G1.HasDual`, `ArtinKP.G1.Kir`, `ArtinKP.G1.Kt`, `ArtinKP.G1.LamDeep`, `ArtinKP.G1.Qt`, `ArtinKP.G1.bfF`, `ArtinKP.G1.clsOf`, `ArtinKP.G1.localWeight`, `ArtinKP.G1.ordVec`, `ArtinKP.G1.repS`, `ArtinKP.G1.scal`, `ArtinKP.G1.tOf`, `ArtinKP.G1.wSec`, `ArtinKP.G1.xi`, `ArtinKP.GK.Jdef`, `ArtinKP.GK.repC`, `ArtinKP.RO.Bdd`, `ArtinKP.S.InClass`, `ArtinKP.S.Supp`, `ArtinKP.S.bigCell`, `ArtinKP.S.bigFun`, `ArtinKP.S.kir`, `ArtinKP.S2.GSection.translate`, `ArtinKP.S2.GSection.translateF`, `ArtinKP.T.theta`.
--
--   **Sources.** They come from these modules of the development, in whole or in part: `KP.E_Model`, `KP.E_Residue`, `KP.G1_Bf`, `KP.G1_BfS`, `KP.G1_Cusp`, `KP.G1_DS`, `KP.G1_Dual`, `KP.G1_FI`, `KP.G1_Kir`, `KP.G1_Lam`, `KP.G1_Res`, `KP.GK_J`, `KP.RO_Classes`, `KP.S2_Sig`, `KP.S2_Translate`, `KP.S_Basic`, `KP.S_BigCell`, `KP.S_Genuine`, `KP.S_Jacquet`, `KP.T_Theta`, `T12.L3X_Meas`.
--
--   **Imports.** It imports the published bundles `Def_ArtinHecke`, `Def_ArtinHeckeLocalCoeff`, `Def_ArtinHeckePoissonLocal`, `Def_ArtinHeckeProbe`, `Def_ArtinHeckeSModel`, `Def_ArtinHeckeTheta`, `Def_DedekindDomain_Completion_BaseChange`, `Def_ExtCitation_LocalLevelResidues`, `Def_IsDedekindDomain_FiniteUnitIdeles`, `Def_IsDedekindDomain_FiniteUnitIdelesOutside`, `Def_LanglandsTunnell_ArtinCoreCTM`, `Def_M4aHerbrand_GenuineDescent`, `Def_M4aHerbrand_IdeleClassVocab`, `Def_M4aHerbrand_SIdeleClassGroup`, `Def_NormIndex_AdmissibleExpOfDegree`, `Def_NumberField_ArchimedeanIdeleModule`, `Def_NumberField_PlaceDecompositionAction` and `Def_NumberField_TateGlobalZeta`; the bundle `ArtinKPB015` of this split; the published statements `ArtinKP.S2.exists_level_sig_mul_sig_conj_eq` and `ArtinKP.T.hasResOn_kubota_aSer`.
--
--   **Imported by** (directly, in this split): the bundle `ArtinKPB017`; the statements `ArtinKP.C9.exists_theta_bigCell_ne_zero`, `ArtinKP.G1.exists_Kir_classDecomp` and `ArtinKP.GK.exists_summable_majorant_norm_jdef`; the proofs of `ArtinKP.G1.exists_Kir_classDecomp` and `ArtinKP.GK.exists_summable_majorant_norm_jdef`.
-- source:
--   the submitter, written with Claude, the Kazhdan–Patterson leaf of Artin's primitive root conjecture (a twisted Voronoi identity for the cubic theta function); after part of the proof of Theorem 1.2 of OpenAI's paper *Primitive roots for every admissible integer base* (2026; github.com/openai/math, family 029), the step that rests on the cubic theta function of D. A. Kazhdan and S. J. Patterson, *Metaplectic forms*, Publ. Math. IHÉS 59 (1984), 35–142; definitions carved from that development

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
import Definitions.Def_ArtinKPB015
import Theorems.Thm_ArtinKP_S2_exists_level_sig_mul_sig_conj_eq
import Theorems.Thm_ArtinKP_T_hasResOn_kubota_aSer

section
-- module Solutions.Artin.KP.E_Residue
/-! # E_Residue: passage to residues and the solution of the system at one prime

* `ResFun s₀`: the abstract **residue functional** — a relation `HasRes f r` ("`f`, given on
  `Re s > 2`, has residue `r` at `s₀`") with exactly the properties (R3)/(R5) of MATH §3.0:
  it depends only on `f` on `Re s > 2`, is additive, is compatible with multiplication by entire
  functions, and the residue is unique.  (`E_Model` shows that the intended definition —
  holomorphic continuation to a connected open set followed by a limit along a ray — has these
  properties.)
* `Theta D s₀`: a residue functional together with the residues `tau Φ ν` of the coefficient
  series `D.aSer Φ ν`.
* `PER T π`: cube periodicity in the exact form of MATH2 §4.4, `τ_Φ(νπ³) = τ_{Ã(π)³Φ}(ν)`.
* Given `PER T π` and `q⁴ x₀³ = 1` (`x₀ = q^{-s₀}`, i.e. `s₀ = 4/3`), for `π ∤ ν₀`:
  `tau_mul_prime` (E1): `τ_Φ(ν₀π) = q² x₀² (ν₀/π)² g₂ · τ_{Ã(π)Φ}(ν₀)`,
  `tau_mul_prime_sq` (E2): `τ_Φ(ν₀π²) = 0`,
  `tau_mul_prime_pow`: `τ_Φ(ν₀π^e) = w(e) (ν₀/π)^{2e} τ_{Ã(π)^eΦ}(ν₀)`, `w = 1, q²x₀²g₂, 0`.
  No division by the determinant is needed and the `Y_m` need no residues: the unknowns are
  eliminated among `C₀, C₁, C₃, C₄` (resp. `C₂, C₅`) by polynomial multipliers.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace ArtinKP.E

open ArtinKP.B7

variable {R K : Type*} [CommRing R] [IsDomain R] [Field K] [Algebra R K]

/-- **Abstract residue functional at `s₀`** ((R3)/(R5) of MATH §3.0). -/
structure ResFun (s₀ : ℂ) where
  /-- `HasRes f r`: the function `f` (only its values on `Re s > 2` matter) has residue `r`. -/
  HasRes : (ℂ → ℂ) → ℂ → Prop
  congr : ∀ {f g : ℂ → ℂ} {r : ℂ}, HasRes f r → (∀ s : ℂ, 2 < s.re → f s = g s) → HasRes g r
  add : ∀ {f g : ℂ → ℂ} {r r' : ℂ}, HasRes f r → HasRes g r' →
    HasRes (fun s => f s + g s) (r + r')
  smul : ∀ {f : ℂ → ℂ} {r : ℂ} (h : ℂ → ℂ), Differentiable ℂ h → HasRes f r →
    HasRes (fun s => h s * f s) (h s₀ * r)
  unique : ∀ {f : ℂ → ℂ} {r r' : ℂ}, HasRes f r → HasRes f r' → r = r'

/-- A residue functional together with the residues of the coefficient series:
`tau Φ ν = Res_{s = s₀} 𝔞_Φ(ν, s)` (MATH2 §4: `τ_Φ(ν)`). -/
structure Theta {S : CubicSymbol R} {A : AddData R K} {Sec : Type*} (D : Kubota S A Sec)
    (s₀ : ℂ) extends ResFun s₀ where
  /-- `τ_Φ(ν)` -/
  tau : Sec → R → ℂ
  tau_spec : ∀ (Φ : Sec) (ν : R), ν ≠ 0 → HasRes (D.aSer Φ ν) (tau Φ ν)

end ArtinKP.E
end

section
-- module Solutions.Artin.KP.E_Model
/-! # E_Model: the intended residue functional satisfies the interface `ResFun`

`HasResOn Ω s₀ γ f r`: there is a function `Fc`, analytic on `Ω`, equal to `f` on `Re s > 2`, with
`(γ t − s₀) · Fc (γ t) → r` as `t ↓ 0`.  If `Ω` is preconnected and contains `Re s > 2`, and the path
`γ` tends to `s₀` inside `Ω`, this is a `ResFun s₀` (`ResFun.ofContinuation`): congruence is
trivial, additivity and multiplication by entire functions are limit laws, uniqueness is the
identity theorem.

`resFunSlit`: the concrete instance of MATH §3.3 — `Ω = {Re s > 1} ∖ (1, 2]`, `s₀ = 4/3`, the ray
`s₀ + t(1 + i)` (the ray of direction `e^{iπ/4}`).
-/

open Filter Topology

namespace ArtinKP.E

/-- The continuation-and-limit functional is a residue functional in the sense of `ResFun`. -/
noncomputable def ResFun.ofContinuation (Ω : Set ℂ) (s₀ : ℂ) (γ : ℝ → ℂ)
    (hΩ : IsPreconnected Ω) (h2 : {s : ℂ | 2 < s.re} ⊆ Ω)
    (hγ : Tendsto γ (𝓝[>] 0) (𝓝 s₀)) (hγΩ : ∀ᶠ t in 𝓝[>] (0 : ℝ), γ t ∈ Ω) : ResFun s₀ where
  HasRes := HasResOn Ω s₀ γ
  congr := by
    rintro f g r ⟨Fc, hF, hFf, hlim⟩ hfg
    exact ⟨Fc, hF, fun s hs => (hFf s hs).trans (hfg s hs), hlim⟩
  add := by
    rintro f g r r' ⟨F₁, hF₁, hf₁, hl₁⟩ ⟨F₂, hF₂, hf₂, hl₂⟩
    refine ⟨fun s => F₁ s + F₂ s, hF₁.add hF₂, fun s hs => by
      show F₁ s + F₂ s = f s + g s
      rw [hf₁ s hs, hf₂ s hs], ?_⟩
    have := hl₁.add hl₂
    refine this.congr fun t => ?_
    ring
  smul := by
    rintro f r h hh ⟨Fc, hF, hf, hl⟩
    refine ⟨fun s => h s * Fc s, ?_, fun s hs => by
      show h s * Fc s = h s * f s
      rw [hf s hs], ?_⟩
    · exact AnalyticOnNhd.mul (fun z _ => hh.analyticAt z) hF
    · have hc : Tendsto (fun t : ℝ => h (γ t)) (𝓝[>] 0) (𝓝 (h s₀)) :=
        (hh.continuous.tendsto s₀).comp hγ
      refine (hc.mul hl).congr fun t => ?_
      ring
  unique := by
    rintro f r r' ⟨F₁, hF₁, hf₁, hl₁⟩ ⟨F₂, hF₂, hf₂, hl₂⟩
    have h3 : (3 : ℂ) ∈ Ω := h2 (by show (2 : ℝ) < (3 : ℂ).re; norm_num)
    have hopen : IsOpen {s : ℂ | 2 < s.re} := isOpen_lt continuous_const Complex.continuous_re
    have hev : F₁ =ᶠ[𝓝 (3 : ℂ)] F₂ := by
      filter_upwards [hopen.mem_nhds (by show (2 : ℝ) < (3 : ℂ).re; norm_num)] with s hs
      rw [hf₁ s hs, hf₂ s hs]
    have heq := hF₁.eqOn_of_preconnected_of_eventuallyEq hF₂ hΩ h3 hev
    have hl₂' : Tendsto (fun t : ℝ => (γ t - s₀) * F₁ (γ t)) (𝓝[>] 0) (𝓝 r') := by
      refine hl₂.congr' ?_
      filter_upwards [hγΩ] with t ht
      rw [heq ht]
    exact tendsto_nhds_unique hl₁ hl₂'

/-- The residue functional of MATH §3.3: continuation to the slit half-plane, limit along the ray
`s₀ + t(1 + i)`, `t ↓ 0`, at `s₀ = 4/3`. -/
noncomputable def resFunSlit : ResFun (4 / 3 : ℂ) :=
  ResFun.ofContinuation slit (4 / 3) (fun t : ℝ => (4 / 3 : ℂ) + t * (1 + Complex.I))
    isPreconnected_slit (fun s hs => ⟨by have : (2 : ℝ) < s.re := hs; linarith, fun _ => hs⟩)
    (by
      have hc : Continuous (fun t : ℝ => (4 / 3 : ℂ) + t * (1 + Complex.I)) := by fun_prop
      have := hc.tendsto 0
      simp only [Complex.ofReal_zero, zero_mul, add_zero] at this
      exact this.mono_left nhdsWithin_le_nhds)
    (by
      filter_upwards [self_mem_nhdsWithin] with t ht
      have ht0 : (0 : ℝ) < t := ht
      have hre : ((4 / 3 : ℂ) + t * (1 + Complex.I)).re = 4 / 3 + t := by
        simp
      have him : ((4 / 3 : ℂ) + t * (1 + Complex.I)).im = t := by
        simp
      refine ⟨by rw [hre]; linarith, fun h0 => ?_⟩
      rw [him] at h0
      exact absurd h0 ht0.ne')

end ArtinKP.E
end

section
-- module Solutions.Artin.KP.G1_Bf
/-!
# WP-G1, part 9: two elementary summability lemmas for the majorant `bf` (MATH3 §4.5)

The two analytic ingredients of stub G1-1 (`G1_Stubs.exists_bf`); Mathlib only.

* `summable_pi_prod`: a finite product of non-negative summable families is summable over the
  product index set.
* `summable_local_weight`: for `q > 1`, `σ > -1/3`, the local weight
  `n ↦ 1[D ≤ n] · min(1, (q^{-n})^{1/3}) · (q^{-n})^σ` is summable over `n ∈ ℤ`.
-/

set_option autoImplicit false

namespace ArtinKP.G1

open Classical in
/-- The local weight of `bf · |y|^σ` at a place with residue cardinality `q`, as a function of
the valuation `n = ord_v y`. -/
noncomputable def localWeight (q : ℝ) (D : ℤ) (σ : ℝ) (n : ℤ) : ℝ :=
  if D ≤ n then min 1 ((q ^ (-n)) ^ (1 / 3 : ℝ)) * (q ^ (-n)) ^ σ else 0

end ArtinKP.G1
end

section
-- module Solutions.Artin.KP.S_Basic
attribute [-instance] _root_.ArtinKP.S.GSection.instAdd _root_.ArtinKP.S.GSection.instCoeFunForallComplexForallForall _root_.ArtinKP.S.GSection.instSMulComplex _root_.ArtinKP.S.GSection.instZero
attribute [-simp] _root_.ArtinKP.S.GSection.add_apply _root_.ArtinKP.S.GSection.nT_apply _root_.ArtinKP.S.GSection.smulFun_apply _root_.ArtinKP.S.GSection.smul_apply _root_.ArtinKP.S.GSection.twist_apply _root_.ArtinKP.S.GSection.zero_apply _root_.ArtinKP.S.TSection.translate_apply _root_.ArtinKP.S2.cubicSymbol_sym
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

theorem deep_mul (hN : 1 ≤ N) (hx : Small 𝔪 N (x - 1)) (hy : Small 𝔪 N (y - 1)) :
    Small 𝔪 N (x * y - 1) := by
  have e : x * y - 1 = x * (y - 1) + (x - 1) := by ring
  rw [e]
  refine add (fun v hv => ?_) hx
  rw [map_mul, hx.val_eq_one hN v hv, one_mul]
  exact hy v hv

end Small

/-! ### Absolute values at `S_f` -/

section abs

variable {𝔪 : Ideal (𝓞 F)}

open NumberField.HeightOneSpectrum

theorem absS_le_normS (c d : F) : absS 𝔪 c ≤ normS 𝔪 c d :=
  Finset.prod_le_prod (fun v _ => (adicAbv F v).nonneg c) fun v _ => le_max_left _ _

end abs

/-! ### The pairing `⟨x, y⟩ = ι (x, y)_S` on `F` -/

section brk

variable {ι : F →+* ℂ} {P : CubicPkg F} {𝔪 : Ideal (𝓞 F)}

theorem norm_brk (x y : F) : ‖brk ι P 𝔪 x y‖ = 1 := by
  have h := congrArg norm (brk_pow_three (ι := ι) (P := P) (𝔪 := 𝔪) x y)
  rw [norm_pow, norm_one] at h
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by norm_num)).mp h

end brk

/-! ### Kubota's `σ_S` on a pair and a matrix -/

theorem Xs_ne_zero {c d : F} (h : c ≠ 0 ∨ d ≠ 0) : Xs c d ≠ 0 := by
  by_cases hc : c = 0
  · subst hc; simpa using h
  · rwa [Xs_of_ne d hc]

/-! ### Primitive rows -/

/-! ### The Kubota symbol on rows -/

/-! ### The matrices `w` and `n(t)` -/

end ArtinKP.S
end
end

section
-- module Solutions.Artin.KP.S_Genuine
/-!
# WP-S, part 4: genuine sections on `F² ∖ 0`

A *genuine section* (`GSection`) is MATH2's `Φ_s` (§0.2), a family of functions on pairs
`(c, d) ∈ F²`, with

* `hom` (S1): `Φ_s(εc, εd) = ⟨X(c,d), ε⟩ |ε|^{-s} Φ_s(c, d)` for `ε ∈ U_S`
  (`X(c,d) = c` if `c ≠ 0`, else `d`; on the cell `c = 0` the symbol is `⟨d, ε⟩`, which is `1` on
  primitive pairs but not on all of `F²` — this corrects MATH2 (S1) for `c = 0`);
* `cube` (S1³): `Φ_s(t³c, t³d) = |t|^{-3s} Φ_s(c, d)` for `t ∈ Fˣ`;
* `level` (S4, `S_f`-adic form): `Φ_s((c,d)γ) = σ_S((c,d), γ) Φ_s(c, d)` for all pairs and all
  `γ ∈ SL₂(F)` that are `S_f`-adically `N`-close to `1` (`IsK 𝔪 N`); the sign is the one forced
  by `kappa_mul` (exponent `-1` in A5 ⇒ exponent `+1` here);
* `holo`, `bound` as for twisted sections.

`GSection.twist : GSection → TSection` is `Ψ = κ Φ` on primitive rows.
-/

set_option autoImplicit false

open NumberField IsDedekindDomain ArtinPrimitiveRoots

noncomputable section

namespace ArtinKP.S

open ArtinKP.A

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}

/-- The inverse matrix. -/
theorem IsK.inv {N : ℤ} {a b c' d' : F} (hK : IsK 𝔪 N a b c' d') : IsK 𝔪 N d' (-b) (-c') a :=
  ⟨by have := hK.det; linear_combination this, hK.hd, hK.hb.neg, hK.hc.neg, hK.ha⟩

end ArtinKP.S
end
end

section
-- module Solutions.Artin.KP.S_BigCell
attribute [-simp] _root_.ArtinKP.S2.cubicSymbol_sym
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

theorem Small.div_unit {M : ℤ} {x w : F} (hx : Small 𝔪 M x)
    (hw : ∀ v : HeightOneSpectrum (𝓞 F), 𝔪 ≤ v.asIdeal → v.valuation F w = 1) :
    Small 𝔪 M (x / w) := fun v hv => by
  rw [map_div₀, hw v hv, div_one]; exact hx v hv

/-! ### Classes -/

/-- `c ∈ η · U_S · (Fˣ)³ · U_N`. -/
def InClass (𝔪 : Ideal (𝓞 F)) (N : ℕ) (η c : F) : Prop :=
  ∃ (ε : (SInt 𝔪)ˣ) (t u : F), t ≠ 0 ∧ Small 𝔪 N (u - 1) ∧ c = η * ((ε : SInt 𝔪) : F) * t ^ 3 * u

namespace InClass

variable {N : ℕ} {η c : F}

theorem ne_zero (hG : Good 𝔪) (hN1 : 1 ≤ N) (hη : η ≠ 0) (h : InClass 𝔪 N η c) : c ≠ 0 := by
  obtain ⟨ε, t, u, ht, hu, rfl⟩ := h
  obtain ⟨v₀, hv₀⟩ := hG.exists_place
  have hu0 : u ≠ 0 := by
    intro h0
    have := hu.val_eq_one (by exact_mod_cast hN1) v₀ hv₀
    rw [h0, map_zero] at this
    exact zero_ne_one this
  have hε0 : ((ε : SInt 𝔪) : F) ≠ 0 := fun h => ε.ne_zero (Subtype.ext h)
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero hη hε0) (pow_ne_zero 3 ht)) hu0

theorem mul_unit (ε' : (SInt 𝔪)ˣ) (h : InClass 𝔪 N η c) :
    InClass 𝔪 N η (((ε' : SInt 𝔪) : F) * c) := by
  obtain ⟨ε, t, u, ht, hu, rfl⟩ := h
  refine ⟨ε' * ε, t, u, ht, hu, ?_⟩
  push_cast
  ring

theorem mul_unit_iff (ε' : (SInt 𝔪)ˣ) :
    InClass 𝔪 N η (((ε' : SInt 𝔪) : F) * c) ↔ InClass 𝔪 N η c := by
  refine ⟨fun h => ?_, mul_unit ε'⟩
  have := h.mul_unit ε'⁻¹
  have e : (((ε'⁻¹ : (SInt 𝔪)ˣ) : SInt 𝔪) : F) * (((ε' : SInt 𝔪) : F) * c) = c := by
    rw [← mul_assoc, ← MulMemClass.coe_mul, ε'.inv_mul]
    simp
  rwa [e] at this

theorem mul_cube {t' : F} (ht' : t' ≠ 0) (h : InClass 𝔪 N η c) : InClass 𝔪 N η (t' ^ 3 * c) := by
  obtain ⟨ε, t, u, ht, hu, rfl⟩ := h
  exact ⟨ε, t' * t, u, mul_ne_zero ht' ht, hu, by ring⟩

theorem mul_cube_iff {t' : F} (ht' : t' ≠ 0) : InClass 𝔪 N η (t' ^ 3 * c) ↔ InClass 𝔪 N η c := by
  refine ⟨fun h => ?_, mul_cube ht'⟩
  have := h.mul_cube (inv_ne_zero ht')
  have e : t'⁻¹ ^ 3 * (t' ^ 3 * c) = c := by field_simp
  rwa [e] at this

theorem mul_deep (hN1 : 1 ≤ N) {w : F} (hw : Small 𝔪 N (w - 1)) (h : InClass 𝔪 N η c) :
    InClass 𝔪 N η (c * w) := by
  obtain ⟨ε, t, u, ht, hu, rfl⟩ := h
  exact ⟨ε, t, u * w, ht, hu.deep_mul (by exact_mod_cast hN1) hw, by ring⟩

/-- On the class of `η` the character `⟨·, ε'⟩` of `U_S` is `⟨η, ε'⟩`. -/
theorem brk_unit {ι : F →+* ℂ} {P : CubicPkg F} (hG : Good 𝔪) (hN1 : 1 ≤ N)
    (hN : P.IsDeepLevel 𝔪 N) (hη : η ≠ 0) (h : InClass 𝔪 N η c) (ε' : (SInt 𝔪)ˣ) :
    brk ι P 𝔪 c ((ε' : SInt 𝔪) : F) = brk ι P 𝔪 η ((ε' : SInt 𝔪) : F) := by
  obtain ⟨ε, t, u, ht, hu, rfl⟩ := h
  obtain ⟨v₀, hv₀⟩ := hG.exists_place
  have hu0 : u ≠ 0 := by
    intro h0
    have := hu.val_eq_one (by exact_mod_cast hN1) v₀ hv₀
    rw [h0, map_zero] at this
    exact zero_ne_one this
  have hε0 : ((ε : SInt 𝔪) : F) ≠ 0 := fun h => ε.ne_zero (Subtype.ext h)
  rw [brk_mul_left _ (mul_ne_zero (mul_ne_zero hη hε0) (pow_ne_zero 3 ht)) hu0,
    brk_mul_left _ (mul_ne_zero hη hε0) (pow_ne_zero 3 ht), brk_mul_left _ hη hε0,
    brk_pow_three_left, brk_deep_left hG hN _ hu,
    brk_sunit hG (unit_val_eq_one ε) (unit_val_eq_one ε')]
  ring

end InClass

/-! ### The support of a big-cell section and its stability -/

/-- One step of the level computation: for `γ` deep relative to the lattice coset,
`c' = c·w` with `w` a deep unit and `d'/c' ≡ d/c` modulo the lattice. -/
theorem supp_step (hG : Good 𝔪) {N : ℕ} (hN1 : 1 ≤ N) {M : ℤ} {t₀ : F} {B₁ : ℕ}
    (hB : Small 𝔪 (-(B₁ : ℤ)) t₀) (hM : -(B₁ : ℤ) ≤ M) {N' : ℤ} (h1 : (N : ℤ) + B₁ ≤ N')
    (h2 : M + 2 * B₁ ≤ N') {a b c' d' : F} (hK : IsK 𝔪 N' a b c' d') {c d : F} (hc : c ≠ 0)
    (hu : Small 𝔪 M (d / c - t₀)) :
    ∃ w : F, Small 𝔪 N (w - 1) ∧ w ≠ 0 ∧ c * a + d * c' = c * w ∧
      Small 𝔪 M ((c * b + d * d') / (c * a + d * c') - t₀) := by
  obtain ⟨v₀, hv₀⟩ := hG.exists_place
  have hN1' : (1 : ℤ) ≤ N := by exact_mod_cast hN1
  set u : F := d / c with hudef
  have hub : Small 𝔪 (-(B₁ : ℤ)) u := by
    have e : u = (u - t₀) + t₀ := by ring
    rw [e]
    exact (hu.mono hM).add hB
  set w : F := a + u * c' with hw
  have hw1 : Small 𝔪 N (w - 1) := by
    have e : w - 1 = (a - 1) + u * c' := by rw [hw]; ring
    rw [e]
    exact (hK.ha.mono (by omega)).add (Small.mono (by omega) (hub.mul hK.hc))
  have hwv : ∀ v : HeightOneSpectrum (𝓞 F), 𝔪 ≤ v.asIdeal → v.valuation F w = 1 :=
    fun v hv => hw1.val_eq_one hN1' v hv
  have hw0 : w ≠ 0 := by
    intro h0
    have := hwv v₀ hv₀
    rw [h0, map_zero] at this
    exact zero_ne_one this
  have hcw : c * a + d * c' = c * w := by
    rw [hw, hudef]; field_simp
  refine ⟨w, hw1, hw0, hcw, ?_⟩
  have e : (c * b + d * d') / (c * a + d * c') - t₀
      = (b + u * (d' - 1) - u * (a - 1) - u * u * c') / w + (u - t₀) := by
    have hne : c * a + d * c' ≠ 0 := by rw [hcw]; exact mul_ne_zero hc hw0
    have hw0' : a + d / c * c' ≠ 0 := hw0
    rw [hw, hudef]
    field_simp
    ring
  rw [e]
  refine Small.add (Small.div_unit ?_ hwv) hu
  exact (((hK.hb.mono (by omega)).add (Small.mono (by omega) (hub.mul hK.hd))).sub
    (Small.mono (by omega) (hub.mul hK.ha))).sub
    (Small.mono (by omega) ((hub.mul hub).mul hK.hc))

/-- The support of a big-cell section: `c` in the class of `η`, `d/c ∈ t₀ + 𝔩_M`. -/
def Supp (𝔪 : Ideal (𝓞 F)) (N : ℕ) (η : F) (M : ℤ) (t₀ c d : F) : Prop :=
  InClass 𝔪 N η c ∧ Small 𝔪 M (d / c - t₀)

theorem supp_act_iff (hG : Good 𝔪) {N : ℕ} (hN1 : 1 ≤ N) {η : F} (hη : η ≠ 0) {M : ℤ} {t₀ : F}
    {B₁ : ℕ} (hB : Small 𝔪 (-(B₁ : ℤ)) t₀) (hM : -(B₁ : ℤ) ≤ M) {N' : ℤ}
    (h1 : (N : ℤ) + B₁ ≤ N') (h2 : M + 2 * B₁ ≤ N') {a b c' d' : F} (hK : IsK 𝔪 N' a b c' d')
    (c d : F) :
    Supp 𝔪 N η M t₀ (c * a + d * c') (c * b + d * d') ↔ Supp 𝔪 N η M t₀ c d := by
  constructor
  · rintro ⟨hcl, hu⟩
    obtain ⟨w, hw1, -, hcw, hu'⟩ :=
      supp_step hG hN1 hB hM h1 h2 hK.inv (hcl.ne_zero hG hN1 hη) hu
    have ec : (c * a + d * c') * d' + (c * b + d * d') * -c' = c := by
      linear_combination c * hK.det
    have ed : (c * a + d * c') * -b + (c * b + d * d') * a = d := by
      linear_combination d * hK.det
    rw [ec, ed] at hu'
    refine ⟨?_, hu'⟩
    rw [← ec, hcw]
    exact hcl.mul_deep hN1 hw1
  · rintro ⟨hcl, hu⟩
    obtain ⟨w, hw1, -, hcw, hu'⟩ := supp_step hG hN1 hB hM h1 h2 hK (hcl.ne_zero hG hN1 hη) hu
    refine ⟨?_, hu'⟩
    rw [hcw]
    exact hcl.mul_deep hN1 hw1

open Classical in
/-- The big-cell function `⟨η, c⟩ |c|^{-s} 1[c ∈ class η, d/c ∈ t₀ + 𝔩_M]`. -/
def bigFun (ι : F →+* ℂ) (P : CubicPkg F) (𝔪 : Ideal (𝓞 F)) (N : ℕ) (η : F) (M : ℤ) (t₀ : F) :
    ℂ → F → F → ℂ := fun s c d =>
  if Supp 𝔪 N η M t₀ c d then brk ι P 𝔪 η c * ((absS 𝔪 c : ℝ) : ℂ) ^ (-s) else 0

section bigFun

variable {ι : F →+* ℂ} {P : CubicPkg F} {N : ℕ} {η : F} {M : ℤ} {t₀ : F}

theorem bigFun_of_supp {c d : F} (h : Supp 𝔪 N η M t₀ c d) (s : ℂ) :
    bigFun ι P 𝔪 N η M t₀ s c d = brk ι P 𝔪 η c * ((absS 𝔪 c : ℝ) : ℂ) ^ (-s) := by
  rw [bigFun, if_pos h]

theorem bigFun_of_not_supp {c d : F} (h : ¬ Supp 𝔪 N η M t₀ c d) (s : ℂ) :
    bigFun ι P 𝔪 N η M t₀ s c d = 0 := by
  rw [bigFun, if_neg h]

end bigFun

/-- **Big-cell sections are sections** (MATH2 §0.2).  `N ≥ 1` must be a deep level. -/
def bigCell (ι : F →+* ℂ) (P : CubicPkg F) (hG : Good 𝔪) {N : ℕ} (hN1 : 1 ≤ N)
    (hN : P.IsDeepLevel 𝔪 N) (η : F) (hη : η ≠ 0) (M : ℤ) (t₀ : F) : GSection ι P 𝔪 where
  toFun := bigFun ι P 𝔪 N η M t₀
  zero s := bigFun_of_not_supp (fun h => h.1.ne_zero hG hN1 hη rfl) s
  hom s ε c d := by
    have hε0 : ((ε : SInt 𝔪) : F) ≠ 0 := fun h => ε.ne_zero (Subtype.ext h)
    have hiff : Supp 𝔪 N η M t₀ (((ε : SInt 𝔪) : F) * c) (((ε : SInt 𝔪) : F) * d)
        ↔ Supp 𝔪 N η M t₀ c d := by
      rw [Supp, Supp, InClass.mul_unit_iff, mul_div_mul_left _ _ hε0]
    by_cases hS : Supp 𝔪 N η M t₀ c d
    · have hc : c ≠ 0 := hS.1.ne_zero hG hN1 hη
      rw [bigFun_of_supp (hiff.mpr hS), bigFun_of_supp hS, Xs_of_ne _ hc,
        brk_mul_right _ hε0 hc, absS_mul, ofReal_mul_cpow (absS_nonneg _) (absS_nonneg _),
        hS.1.brk_unit hG hN1 hN hη]
      ring
    · rw [bigFun_of_not_supp (mt hiff.mp hS), bigFun_of_not_supp hS, mul_zero]
  cube s t ht c d := by
    have ht3 : t ^ 3 ≠ 0 := pow_ne_zero 3 ht
    have hiff : Supp 𝔪 N η M t₀ (t ^ 3 * c) (t ^ 3 * d) ↔ Supp 𝔪 N η M t₀ c d := by
      rw [Supp, Supp, InClass.mul_cube_iff ht, mul_div_mul_left _ _ ht3]
    by_cases hS : Supp 𝔪 N η M t₀ c d
    · have hc : c ≠ 0 := hS.1.ne_zero hG hN1 hη
      rw [bigFun_of_supp (hiff.mpr hS), bigFun_of_supp hS, brk_mul_right _ ht3 hc,
        brk_pow_three_right, one_mul, absS_mul, ofReal_mul_cpow (absS_nonneg _) (absS_nonneg _),
        absS_pow, ofReal_pow_cpow (absS_pos ht)]
      push_cast
      ring_nf
    · rw [bigFun_of_not_supp (mt hiff.mp hS), bigFun_of_not_supp hS, mul_zero]
  level := by
    obtain ⟨B, hB⟩ := exists_small_neg hG.ne_bot t₀
    obtain ⟨A, hA1, hA2⟩ : ∃ A : ℕ, M ≤ A ∧ -M ≤ A := ⟨M.natAbs, by omega, by omega⟩
    set B₁ : ℕ := B + A with hB₁
    have hB' : Small 𝔪 (-(B₁ : ℤ)) t₀ := Small.mono (by rw [hB₁]; push_cast; omega) hB
    have hM : -(B₁ : ℤ) ≤ M := by rw [hB₁]; push_cast; omega
    refine ⟨N + B₁ + (A + 2 * B₁), fun a b c' d' hK s c d => ?_⟩
    have h1 : (N : ℤ) + B₁ ≤ ((N + B₁ + (A + 2 * B₁) : ℕ) : ℤ) := by push_cast; omega
    have h2 : M + 2 * B₁ ≤ ((N + B₁ + (A + 2 * B₁) : ℕ) : ℤ) := by push_cast; omega
    have hiff := supp_act_iff hG hN1 hη hB' hM h1 h2 hK c d
    by_cases hS : Supp 𝔪 N η M t₀ c d
    · have hc : c ≠ 0 := hS.1.ne_zero hG hN1 hη
      obtain ⟨w, hw1, hw0, hcw, -⟩ := supp_step hG hN1 hB' hM h1 h2 hK hc hS.2
      have hwabs : absS 𝔪 w = 1 := absS_eq_one_of_val hG.ne_bot fun v hv =>
        hw1.val_eq_one (by exact_mod_cast hN1) v hv
      have hsig : sig ι P 𝔪 c d a b c' d' = 1 := by
        rw [sig, hcw, Xs_of_ne _ (mul_ne_zero hc hw0), Xs_of_ne _ hc, mul_div_cancel_left₀ _ hc]
        exact brk_deep_left hG hN _ hw1
      have hval := bigFun_of_supp (ι := ι) (P := P) (hiff.mpr hS) s
      rw [hval, bigFun_of_supp hS, hsig, one_mul, hcw, brk_mul_right _ hc hw0,
        brk_deep_right hG hN _ hw1, mul_one, absS_mul, hwabs, mul_one]
    · rw [bigFun_of_not_supp (mt hiff.mp hS), bigFun_of_not_supp hS, mul_zero]
  holo c d := by
    by_cases hS : Supp 𝔪 N η M t₀ c d
    · have hc : c ≠ 0 := hS.1.ne_zero hG hN1 hη
      have : (fun s => bigFun ι P 𝔪 N η M t₀ s c d)
          = fun s => brk ι P 𝔪 η c * ((absS 𝔪 c : ℝ) : ℂ) ^ (-s) := by
        funext s; exact bigFun_of_supp hS s
      rw [this]
      exact (differentiable_const _).mul (differentiable_id.neg.const_cpow
        (Or.inl (Complex.ofReal_ne_zero.mpr (absS_pos hc).ne')))
    · have : (fun s => bigFun ι P 𝔪 N η M t₀ s c d) = fun _ => 0 := by
        funext s; exact bigFun_of_not_supp hS s
      rw [this]
      exact differentiable_const _
  bound M₀ := by
    obtain ⟨B, hB⟩ := exists_small_neg hG.ne_bot t₀
    obtain ⟨A, hA1, hA2⟩ : ∃ A : ℕ, M ≤ A ∧ -M ≤ A := ⟨M.natAbs, by omega, by omega⟩
    set B₁ : ℕ := B + A with hB₁
    have hB' : Small 𝔪 (-(B₁ : ℤ)) t₀ := Small.mono (by rw [hB₁]; push_cast; omega) hB
    have hM : -(B₁ : ℤ) ≤ M := by rw [hB₁]; push_cast; omega
    set K : ℝ := max 1 (∏ v ∈ CubicPkg.sFin 𝔪,
      max 1 ((Ideal.absNorm v.asIdeal : ℝ) ^ (-(-(B₁ : ℤ))))) with hK
    have hK1 : 1 ≤ K := le_max_left _ _
    refine ⟨K ^ M₀, fun s hs c d => ?_⟩
    by_cases hS : Supp 𝔪 N η M t₀ c d
    · have hc : c ≠ 0 := hS.1.ne_zero hG hN1 hη
      have hub : Small 𝔪 (-(B₁ : ℤ)) (d / c) := by
        have e : d / c = (d / c - t₀) + t₀ := by ring
        rw [e]
        exact (hS.2.mono hM).add hB'
      have hpa := absS_pos (𝔪 := 𝔪) hc
      have hpb := normS_pos (𝔪 := 𝔪) (d := d) (Or.inl hc)
      have h1 : absS 𝔪 c ≤ K * normS 𝔪 c d :=
        (absS_le_normS c d).trans (le_mul_of_one_le_left hpb.le hK1)
      have h2 : normS 𝔪 c d ≤ K * absS 𝔪 c := by
        have e : normS 𝔪 c d = absS 𝔪 c * normS 𝔪 1 (d / c) := by
          rw [← normS_mul_left, mul_one, mul_div_cancel₀ _ hc]
        have h3 : normS 𝔪 1 (d / c) ≤ K := by
          refine le_trans ?_ (le_max_right _ _)
          refine Finset.prod_le_prod (fun v _ => le_max_of_le_left (AbsoluteValue.nonneg _ _))
            fun v hv => ?_
          rw [map_one]
          exact max_le_max le_rfl
            (abv_le_of_val_le v (hub v ((CubicPkg.mem_sFin hG.ne_bot v).mp hv)))
        rw [e, mul_comm]
        exact mul_le_mul_of_nonneg_right h3 hpa.le
      have h3 := rpow_le_of_comparable hpa hpb hK1 h1 h2 (-s.re)
      have h4 : K ^ |(-s.re)| ≤ K ^ M₀ := by
        refine Real.rpow_le_rpow_of_exponent_le hK1 ?_
        rw [abs_neg]
        exact (Complex.abs_re_le_norm s).trans hs
      rw [bigFun_of_supp hS, norm_mul, norm_brk, one_mul,
        Complex.norm_cpow_eq_rpow_re_of_pos hpa, Complex.neg_re]
      exact h3.trans (mul_le_mul_of_nonneg_right h4 (Real.rpow_nonneg hpb.le _))
    · rw [bigFun_of_not_supp hS, norm_zero]
      exact mul_nonneg (Real.rpow_nonneg (le_trans zero_le_one hK1) _)
        (Real.rpow_nonneg (normS_nonneg _ _) _)

/-! ### Small-cell sections -/

/-! ### Finite sums: the sum over classes and additive projections -/

end ArtinKP.S
end
end

section
-- module Solutions.Artin.KP.S_Jacquet
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

variable {ι : F →+* ℂ} {P : CubicPkg F}

/-! ### The Kirillov function -/

/-- The `η`-term of MATH2's `𝒦_Φ(β) = Σ_η τ_η(1) ⟨η, β⟩² |β²η|^s J_Φ(β²η; β, s)`. -/
def kir (ψ : SfChar 𝔪) (M : ℤ) (Φ : GSection ι P 𝔪) (η β : F) (s : ℂ) : ℂ :=
  brk ι P 𝔪 η β ^ 2 * lam ψ M Φ (β ^ 2 * η) β s

end ArtinKP.S
end
end

section
-- module Solutions.Artin.KP.S2_Sig
attribute [-simp] _root_.ArtinKP.S2.cubicSymbol_sym
/-!
# WP-S2, part 2: Kubota's cocycle identity for `σ_S` on `SL₂(F)`

* `isSteinberg`: `(·,·)_S` is a Steinberg symbol in the sense of `S2_Cocycle`.
* `sig_cocycle`: `σ_S(p, h) σ_S(ph, k) = σ_S(p, hk) σ_S(bot h, k)` for every non-zero pair
  `p ∈ F²` and all `h, k ∈ SL₂(F)` (no integrality, no depth).
* `sigmaS_cocycle`: the same on `Matrix.SpecialLinearGroup (Fin 2) F`.
* `sig_smul`: `σ_S(lp, h) = σ_S(p, h) ⟨X(ph)/X(p), l⟩`.
* `sig_conj`: for `σ ∈ SL₂(F)` and `k` deep enough (depending on `σ`),
  `σ_S(bot σ, σ⁻¹kσ) = σ_S(bot k, σ)`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open NumberField IsDedekindDomain ArtinPrimitiveRoots

noncomputable section

namespace ArtinKP.S2

open ArtinKP.A ArtinKP.S

variable {F : Type*} [Field F] [NumberField F] {𝔪 : Ideal (𝓞 F)}

variable {ι : F →+* ℂ} {P : CubicPkg F}

/-- Scaling the pair. -/
theorem sig_smul {l : F} (hl : l ≠ 0) {c d : F} (hcd : c ≠ 0 ∨ d ≠ 0) {α β γ δ : F}
    (det : α * δ - β * γ = 1) :
    sig ι P 𝔪 (l * c) (l * d) α β γ δ
      = sig ι P 𝔪 c d α β γ δ * brk ι P 𝔪 (Xs (c * α + d * γ) (c * β + d * δ) / Xs c d) l := by
  have hγδ : γ ≠ 0 ∨ δ ≠ 0 := by
    by_contra hh
    rw [not_or, not_not, not_not] at hh
    rw [hh.1, hh.2] at det
    simp at det
  have hq : c * α + d * γ ≠ 0 ∨ c * β + d * δ ≠ 0 := by
    by_contra hh
    rw [not_or, not_not, not_not] at hh
    rcases hcd with h0 | h0
    · exact h0 (by linear_combination δ * hh.1 - γ * hh.2 - c * det)
    · exact h0 (by linear_combination -β * hh.1 + α * hh.2 - d * det)
  have hx := Xs_ne_zero hcd
  have hx₁ := Xs_ne_zero hq
  have hz := Xs_ne_zero hγδ
  have e1 : l * c * α + l * d * γ = l * (c * α + d * γ) := by ring
  have e2 : l * c * β + l * d * δ = l * (c * β + d * δ) := by ring
  rw [sig, sig, e1, e2, Xs_smul hl, Xs_smul hl,
    show l * Xs (c * α + d * γ) (c * β + d * δ) / (l * Xs c d)
      = Xs (c * α + d * γ) (c * β + d * δ) / Xs c d by field_simp,
    show l * Xs (c * α + d * γ) (c * β + d * δ) / Xs γ δ
      = Xs (c * α + d * γ) (c * β + d * δ) / Xs γ δ * l by field_simp,
    brk_mul_right _ (div_ne_zero hx₁ hz) hl]

/-- `σ⁻¹ k σ` is close to `1` when `k` is. -/
theorem isK_conj {α β γ δ : F} (det : α * δ - β * γ = 1) {B : ℕ}
    (hα : Small 𝔪 (-(B : ℤ)) α) (hβ : Small 𝔪 (-(B : ℤ)) β) (hγ : Small 𝔪 (-(B : ℤ)) γ)
    (hδ : Small 𝔪 (-(B : ℤ)) δ) {N : ℤ} {a b c' d' : F} (hK : IsK 𝔪 (N + 2 * B) a b c' d') :
    IsK 𝔪 N (cj00 α β γ δ a b c' d') (cj01 α β γ δ a b c' d') (cj10 α β γ δ a b c' d')
      (cj11 α β γ δ a b c' d') := by
  have m3 : ∀ {x y e : F}, Small 𝔪 (-(B : ℤ)) x → Small 𝔪 (-(B : ℤ)) y →
      Small 𝔪 (N + 2 * B) e → Small 𝔪 N (x * y * e) := fun hx hy he =>
    Small.mono (by omega) ((hx.mul hy).mul he)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [cj00, cj01, cj10, cj11]
    linear_combination (a * d' - b * c') * (α * δ - β * γ + 1) * det + hK.det
  · have e : cj00 α β γ δ a b c' d' - 1
        = δ * α * (a - 1) + δ * γ * b - β * α * c' - β * γ * (d' - 1) := by
      simp only [cj00]; linear_combination det
    rw [e]
    exact (((m3 hδ hα hK.ha).add (m3 hδ hγ hK.hb)).sub (m3 hβ hα hK.hc)).sub (m3 hβ hγ hK.hd)
  · have e : cj01 α β γ δ a b c' d'
        = δ * β * (a - 1) + δ * δ * b - β * β * c' - β * δ * (d' - 1) := by
      simp only [cj01]; ring
    rw [e]
    exact (((m3 hδ hβ hK.ha).add (m3 hδ hδ hK.hb)).sub (m3 hβ hβ hK.hc)).sub (m3 hβ hδ hK.hd)
  · have e : cj10 α β γ δ a b c' d'
        = α * α * c' + α * γ * (d' - 1) - γ * α * (a - 1) - γ * γ * b := by
      simp only [cj10]; ring
    rw [e]
    exact (((m3 hα hα hK.hc).add (m3 hα hγ hK.hd)).sub (m3 hγ hα hK.ha)).sub (m3 hγ hγ hK.hb)
  · have e : cj11 α β γ δ a b c' d' - 1
        = α * β * c' + α * δ * (d' - 1) - γ * β * (a - 1) - γ * δ * b := by
      simp only [cj11]; linear_combination det
    rw [e]
    exact (((m3 hα hβ hK.hc).add (m3 hα hδ hK.hd)).sub (m3 hγ hβ hK.ha)).sub (m3 hγ hδ hK.hb)

end ArtinKP.S2
end
end

section
-- module Solutions.Artin.KP.S2_Translate
attribute [-simp] _root_.ArtinKP.S2.cubicSymbol_sym
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

theorem pair_act_ne_zero {c d α β γ δ : F} (det : α * δ - β * γ = 1) (hcd : c ≠ 0 ∨ d ≠ 0) :
    c * α + d * γ ≠ 0 ∨ c * β + d * δ ≠ 0 := by
  by_contra hh
  rw [not_or, not_not, not_not] at hh
  rcases hcd with h0 | h0
  · exact h0 (by linear_combination δ * hh.1 - γ * hh.2 - c * det)
  · exact h0 (by linear_combination -β * hh.1 + α * hh.2 - d * det)

theorem sig_ne_zero (c d a b c' d' : F) : sig ι P 𝔪 c d a b c' d' ≠ 0 := brk_ne_zero _ _

theorem norm_sig (c d a b c' d' : F) : ‖sig ι P 𝔪 c d a b c' d'‖ = 1 := norm_brk _ _

namespace GSection

/-- **Translation of a genuine section by `σ = [[α,β],[γ,δ]] ∈ SL₂(F)`**:
`(σ·Φ)_s(p) = σ_S(p, σ)⁻¹ Φ_s(pσ)`. -/
def translateF (hG : Good 𝔪) (α β γ δ : F) (det : α * δ - β * γ = 1) (Φ : GSection ι P 𝔪) :
    GSection ι P 𝔪 where
  toFun s c d := (sig ι P 𝔪 c d α β γ δ)⁻¹ * Φ s (c * α + d * γ) (c * β + d * δ)
  zero s := by simp [Φ.zero]
  hom s ε c d := by
    by_cases h0 : c = 0 ∧ d = 0
    · obtain ⟨rfl, rfl⟩ := h0
      simp [Φ.zero]
    have hcd : c ≠ 0 ∨ d ≠ 0 := by
      by_contra h; rw [not_or, not_not, not_not] at h; exact h0 h
    have he0 : ((ε : SInt 𝔪) : F) ≠ 0 := fun h => ε.ne_zero (Subtype.ext h)
    have hq := pair_act_ne_zero det hcd
    have e1 : ((ε : SInt 𝔪) : F) * c * α + ((ε : SInt 𝔪) : F) * d * γ
        = ((ε : SInt 𝔪) : F) * (c * α + d * γ) := by ring
    have e2 : ((ε : SInt 𝔪) : F) * c * β + ((ε : SInt 𝔪) : F) * d * δ
        = ((ε : SInt 𝔪) : F) * (c * β + d * δ) := by ring
    rw [e1, e2, Φ.hom, sig_smul he0 hcd det, brk_div_left _ (Xs_ne_zero hq) (Xs_ne_zero hcd)]
    have h1 := sig_ne_zero (ι := ι) (P := P) (𝔪 := 𝔪) c d α β γ δ
    have h2 := brk_ne_zero (ι := ι) (P := P) (𝔪 := 𝔪) (Xs (c * α + d * γ) (c * β + d * δ))
      ((ε : SInt 𝔪) : F)
    have h3 := brk_ne_zero (ι := ι) (P := P) (𝔪 := 𝔪) (Xs c d) ((ε : SInt 𝔪) : F)
    field_simp
  cube s t ht c d := by
    by_cases h0 : c = 0 ∧ d = 0
    · obtain ⟨rfl, rfl⟩ := h0
      simp [Φ.zero]
    have hcd : c ≠ 0 ∨ d ≠ 0 := by
      by_contra h; rw [not_or, not_not, not_not] at h; exact h0 h
    have e1 : t ^ 3 * c * α + t ^ 3 * d * γ = t ^ 3 * (c * α + d * γ) := by ring
    have e2 : t ^ 3 * c * β + t ^ 3 * d * δ = t ^ 3 * (c * β + d * δ) := by ring
    rw [e1, e2, Φ.cube s t ht, sig_smul (pow_ne_zero 3 ht) hcd det, brk_pow_three_right, mul_one]
    ring
  level := by
    obtain ⟨N₁, hN₁⟩ := exists_level_sig_mul_sig_conj_eq (ι := ι) (P := P) hG det
    obtain ⟨Bα, hα⟩ := exists_small_neg hG.ne_bot α
    obtain ⟨Bβ, hβ⟩ := exists_small_neg hG.ne_bot β
    obtain ⟨Bγ, hγ⟩ := exists_small_neg hG.ne_bot γ
    obtain ⟨Bδ, hδ⟩ := exists_small_neg hG.ne_bot δ
    obtain ⟨N, hN⟩ := Φ.level
    set B : ℕ := Bα + Bβ + Bγ + Bδ with hB
    refine ⟨N₁ + N + 2 * B, fun a b c' d' hK s c d => ?_⟩
    by_cases h0 : c = 0 ∧ d = 0
    · obtain ⟨rfl, rfl⟩ := h0
      simp [Φ.zero]
    have hcd : c ≠ 0 ∨ d ≠ 0 := by
      by_contra h; rw [not_or, not_not, not_not] at h; exact h0 h
    have hK₁ : IsK 𝔪 N₁ a b c' d' := hK.mono (by push_cast; omega)
    have hK₂ : IsK 𝔪 ((N : ℤ) + 2 * B) a b c' d' := hK.mono (by push_cast; omega)
    have hKc := isK_conj det (B := B) (hα.mono (by rw [hB]; push_cast; omega))
      (hβ.mono (by rw [hB]; push_cast; omega)) (hγ.mono (by rw [hB]; push_cast; omega))
      (hδ.mono (by rw [hB]; push_cast; omega)) hK₂
    have hΦ := hN _ _ _ _ hKc s (c * α + d * γ) (c * β + d * δ)
    have e1 : (c * α + d * γ) * cj00 α β γ δ a b c' d' + (c * β + d * δ) * cj10 α β γ δ a b c' d'
        = (c * a + d * c') * α + (c * b + d * d') * γ := by
      simp only [cj00, cj10]
      linear_combination ((c * a + d * c') * α + (c * b + d * d') * γ) * det
    have e2 : (c * α + d * γ) * cj01 α β γ δ a b c' d' + (c * β + d * δ) * cj11 α β γ δ a b c' d'
        = (c * a + d * c') * β + (c * b + d * d') * δ := by
      simp only [cj01, cj11]
      linear_combination ((c * a + d * c') * β + (c * b + d * d') * δ) * det
    rw [e1, e2] at hΦ
    rw [hΦ]
    have hs := hN₁ a b c' d' hK₁ c d hcd
    have h1 := sig_ne_zero (ι := ι) (P := P) (𝔪 := 𝔪) c d α β γ δ
    have h2 := sig_ne_zero (ι := ι) (P := P) (𝔪 := 𝔪) (c * a + d * c') (c * b + d * d') α β γ δ
    field_simp
    linear_combination (Φ s (c * α + d * γ) (c * β + d * δ)) * hs
  holo c d := (differentiable_const _).mul (Φ.holo _ _)
  bound M := by
    obtain ⟨B, -, hB⟩ := Φ.bound_comp M α β γ δ δ (-β) (-γ) α (fun c d => by
      constructor
      · linear_combination c * det
      · linear_combination d * det)
    refine ⟨B, fun s hs c d => ?_⟩
    rw [norm_mul, norm_inv, norm_sig, inv_one, one_mul]
    exact hB s hs c d

/-- **The genuine translate `Φ^σ` for `σ ∈ SL₂(R)`** (MATH2 §5.2):
`(σ·Φ)_s(p) = κ(σ) σ_S(p, σ)⁻¹ Φ_s(pσ)`. -/
def translate (hG : Good 𝔪) (σ : Matrix.SpecialLinearGroup (Fin 2) (SInt 𝔪))
    (Φ : GSection ι P 𝔪) : GSection ι P 𝔪 :=
  kappa ι 𝔪 σ • translateF hG ((σ.1 0 0 : SInt 𝔪) : F) ((σ.1 0 1 : SInt 𝔪) : F)
    ((σ.1 1 0 : SInt 𝔪) : F) ((σ.1 1 1 : SInt 𝔪) : F) (det_coe σ) Φ

end GSection

end ArtinKP.S2
end
end

section
-- module Solutions.Artin.KP.G1_Cusp
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

theorem differentiable_absPow (x : F) (hx : x ≠ 0) (a b : ℂ) :
    Differentiable ℂ fun s : ℂ => ((absS 𝔪 x : ℝ) : ℂ) ^ (a * s + b) :=
  ((differentiable_id.const_mul a).add_const b).const_cpow
    (Or.inl (Complex.ofReal_ne_zero.mpr (absS_pos hx).ne'))

/-- `Φ ↦ |x|_{S_f}^{a s + b} · Φ`. -/
def scal (x : F) (hx : x ≠ 0) (a b : ℂ) (Φ : GSection ι P 𝔪) : GSection ι P 𝔪 :=
  GSection.smulFun (fun s => ((absS 𝔪 x : ℝ) : ℂ) ^ (a * s + b)) (differentiable_absPow x hx a b) Φ

@[simp] theorem scal_apply (x : F) (hx : x ≠ 0) (a b : ℂ) (Φ : GSection ι P 𝔪) (s : ℂ)
    (c d : F) : scal x hx a b Φ s c d = ((absS 𝔪 x : ℝ) : ℂ) ^ (a * s + b) * Φ s c d := rfl

/-! ### The Weyl element -/

/-- `wΦ`: the genuine translate by `w = [[0,-1],[1,0]]`. -/
def wSec (hG : Good 𝔪) (Φ : GSection ι P 𝔪) : GSection ι P 𝔪 :=
  S2.GSection.translate hG (wMat 𝔪) Φ

/-! ### (N) and (W) -/

/-! ### (2.1): the cusp change -/

end ArtinKP.G1
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

open Classical in
/-- **The `η`-term of the Kirillov function**: `Kt Φ β η s = Lam (Ã(β)Φ) η 1 s` (`0` for
`β = 0`).  MATH3's `𝒦_Φ(β) = τ_{Ã(β)Φ}(1)` is `Σ_η Kt Φ β η (4/3) · τ_η` (class decomposition). -/
def Kt (ψ : SfChar 𝔪) (hG : Good 𝔪) (Φ : GSection ι P 𝔪) (β η : F) (s : ℂ) : ℂ :=
  if hβ : β = 0 then 0 else Lam ψ hG (Φ.torusT hG β hβ) η 1 s

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

/-! ### Lemma DS -/

/-! ### `Lam` on a class -/

/-- `Lam Ψ (uη) ν s = Lam Ψ η ν s` for `u ∈ 1 + 𝔩_N`. -/
def LamDeep (ψ : SfChar 𝔪) (hG : Good 𝔪) (Ψ : GSection ι P 𝔪) (N : ℕ) : Prop :=
  ∀ u : F, Small 𝔪 N (u - 1) → ∀ (η ν : F) (s : ℂ), Lam ψ hG Ψ (η * u) ν s = Lam ψ hG Ψ η ν s

/-! ### Big cells -/

end ArtinKP.G1
end
end

section
-- module Solutions.Artin.KP.G1_Dual
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

/-- `β` lies in the dual lattice `A_M` of `𝔩_M`: `ψ(β h) = 1` for all `h ∈ 𝔩_M`. -/
def Adual (ψ : SfChar 𝔪) (M : ℤ) (β : F) : Prop := ∀ h : F, Small 𝔪 M h → ψ (β * h) = 1

/-- The conclusion of Lemma DUAL for a character `ψ`: `A_M ⊂ 𝔩_{-M-d₀}` for all `M`. -/
def HasDual (ψ : SfChar 𝔪) (d₀ : ℤ) : Prop :=
  ∀ (M : ℤ) (β : F), Adual ψ M β → Small 𝔪 (-M - d₀) β

/-! ### The trace dual is a fractional ideal -/

/-! ### Elements with prescribed local behaviour -/

/-! ### Lemma DUAL -/

end ArtinKP.G1
end
end

section
-- module Solutions.Artin.KP.G1_FI
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

/-- The finite group `𝔩_J / 𝔩_M` (`J ≤ M`). -/
abbrev Qt (𝔪 : Ideal (𝓞 F)) (J M : ℤ) : Type _ :=
  ↥(latD 𝔪 fun _ => J) ⧸ (latD 𝔪 fun _ => M).addSubgroupOf (latD 𝔪 fun _ => J)

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

theorem finite_placesOf (h𝔪 : 𝔪 ≠ ⊥) : (placesOf 𝔪).Finite := by
  have := (Ideal.finite_factors h𝔪)
  refine this.subset fun v hv => ?_
  simp only [placesOf, Set.mem_ofPred_eq] at hv
  simpa [Set.mem_ofPred_eq] using Ideal.dvd_iff_le.mpr hv


/-! ### `lnorm` -/

/-! ### Slices -/


/-! ### Measure preservation -/

end

end ArtinPrimitiveRoots.L3X
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

/-- The valuation vector of `x` at the places of `S_f`. -/
def ordVec (𝔪 : Ideal (𝓞 F)) (x : Fˣ) : ↥(CubicPkg.sFin 𝔪) → ℤ := fun v => ordv v.1 (x : F)

open Classical in
/-- An element of `F^×` with prescribed valuations at the places of `S_f`. -/
def tOf (𝔪 : Ideal (𝓞 F)) (n : ↥(CubicPkg.sFin 𝔪) → ℤ) : F :=
  (exists_val_eq 𝔪 (fun v => if h : v ∈ CubicPkg.sFin 𝔪 then n ⟨v, h⟩ else 0)).choose

theorem val_tOf (n : ↥(CubicPkg.sFin 𝔪) → ℤ) (v : ↥(CubicPkg.sFin 𝔪)) :
    v.1.valuation F (tOf 𝔪 n) = WithZero.exp (-(n v)) := by
  classical
  have h := (exists_val_eq 𝔪
    (fun v => if h : v ∈ CubicPkg.sFin 𝔪 then n ⟨v, h⟩ else 0)).choose_spec.2 v.1 v.2
  rw [dif_pos v.2] at h
  exact h

/-- `x / t_{ord x}` is a unit at the places of `S_f`. -/
theorem val_div_tOf (h𝔪 : 𝔪 ≠ ⊥) (x : Fˣ) (v : HeightOneSpectrum (𝓞 F)) (hv : 𝔪 ≤ v.asIdeal) :
    v.valuation F ((x : F) / tOf 𝔪 (ordVec 𝔪 x)) = 1 := by
  have hvs := (CubicPkg.mem_sFin h𝔪 v).mpr hv
  rw [map_div₀, val_tOf (ordVec 𝔪 x) ⟨v, hvs⟩, ordVec, val_eq_exp_ordv v x.ne_zero]
  exact div_self WithZero.exp_ne_zero

/-- A chosen representative of a class. -/
def repS (y : SFin 𝔪 k) : Fˣ := Quotient.out (Additive.toMul y)

open Classical in
/-- The majorant as a function on `F^×`. -/
def bfF (𝔪 : Ideal (𝓞 F)) (C : ℝ) (D : ℤ) (x : Fˣ) : ℝ :=
  C * (∏ v ∈ CubicPkg.sFin 𝔪, min 1 (adicAbv F v (x : F) ^ (1 / 3 : ℝ)))
    * (if Small 𝔪 D (x : F) then 1 else 0)

/-- The class of `x / t_{ord x}` in the finite group `𝔩_0/𝔩_{k+1}`. -/
def clsOf (h𝔪 : 𝔪 ≠ ⊥) (k : ℕ) (x : Fˣ) : Qt 𝔪 0 ((k : ℤ) + 1) :=
  QuotientAddGroup.mk (⟨(x : F) / tOf 𝔪 (ordVec 𝔪 x), fun v hv => by
    rw [val_div_tOf h𝔪 x v hv]; simp⟩ : ↥(latD 𝔪 fun _ => (0 : ℤ)))

end ArtinKP.G1
end
end

section
-- module Solutions.Artin.KP.G1_Res
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

/-- The scalar law of a residue functional for multipliers holomorphic on `U`. -/
def _root_.ArtinKP.E.ResFun.SmulOn {s₀ : ℂ} (T : ResFun s₀) (U : Set ℂ) : Prop :=
  ∀ (f : ℂ → ℂ) (r : ℂ) (h : ℂ → ℂ), DifferentiableOn ℂ h U → T.HasRes f r →
    T.HasRes (fun s => h s * f s) (h s₀ * r)

end ArtinKP.G1
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

/-- `r ≠ 0` and `ord_v(r) < K` at every `v ∣ 𝔪`. -/
def Bdd (𝔪 : Ideal (𝓞 F)) (K : ℕ) (r : 𝓞 F) : Prop :=
  r ≠ 0 ∧ ∀ v : HeightOneSpectrum (𝓞 F), 𝔪 ≤ v.asIdeal →
    WithZero.exp (-(K : ℤ)) < v.valuation F (r : F)

/-! ### `U_N` is a group for `N ≥ 1` -/

/-! ### A finite cover -/

/-! ### `InClass` is an equivalence relation on `F^×`; disjoint representatives -/

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

/-! ### The Kirillov function -/

open Classical in
/-- **The Kirillov function** `𝒦_Φ(β) = τ_{Ã(β)Φ}(1)`, `β ∈ F^×` (`0` at `β = 0`). -/
def Kir (Φ : GSection ι P 𝔪) (β : F) : ℂ :=
  if hβ : β = 0 then 0 else T.tau (Φ.torusT hG β hβ) 1

/-- `ξ_Φ(β) = |β|_{S_f}^{1/3} 𝒦_Φ(β)`. -/
def xi (Φ : GSection ι P 𝔪) (β : F) : ℂ :=
  ((absS 𝔪 β ^ (1 / 3 : ℝ) : ℝ) : ℂ) * Kir hG hz6 T Φ β

/-! ### The class decomposition and the majorant -/

end tau

end ArtinKP.G1
end
end

section
-- module Solutions.Artin.KP.T_Theta
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

/-- **The `E.Theta` instance at `s₀ = 4/3`**, with `toResFun = E.resFunSlit`. -/
def theta : E.Theta (kubota (ι := ι) (P := P) hG hz6) (4 / 3) where
  toResFun := E.resFunSlit
  tau := fun Φ ν => tau hG hz6 Φ ν
  tau_spec := fun Φ _ hν => hasResOn_kubota_aSer hG hz6 Φ hν

/-! ### The archimedean factor as an integral over `v` -/


/-! ### Fourier coefficients of `θ` for the cells of `Γ` -/

end

end ArtinKP.T
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

/-- A chosen representative in `F^×` of a class of `SFinCls 𝔪 k`. -/
def repC (cl : SFinCls 𝔪 k) : Fˣ := G1.repS (Quotient.out cl)

variable (hG : Good 𝔪) {z6 : 𝓞 F} (hz6 : IsPrimitiveRoot z6 6)

/-- **`J`** (MATH3 (2d)): `J(cl, y′) = (−1)^r · ⟨ν̃, η′⟩ · ξ_{wΦ₀}(η′)`, with the chosen
representatives `ν̃ = repC cl`, `η′ = G1.repS y′`. -/
def Jdef (Φ₀ : GSection ι P 𝔪) (cl : SFinCls 𝔪 k) (y' : SFin 𝔪 k) : ℂ :=
  (-1) ^ Fintype.card (InfinitePlace F)
    * brk ι P 𝔪 ((repC cl : Fˣ) : F) ((G1.repS y' : Fˣ) : F)
    * G1.xi hG hz6 (T.theta hG hz6) (G1.wSec hG Φ₀) ((G1.repS y' : Fˣ) : F)

/-! ### (INV) and well-definedness for a delta section -/

end

end ArtinKP.GK
end


