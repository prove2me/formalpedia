-- Prove2me | solution 1 for ArtinKP.RC.grad2_chi_le
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T09:47:44.717803+00:00
-- url     : https://prove2.me/submissions/a7b3b9c0-9a95-4a8c-9b92-5415ac5d3a37

import Mathlib
import Definitions.Def_ArtinKPB015
import Theorems.Thm_ArtinKP_RC_exists_single

section
-- module Solutions.Artin.KP.X_H3
attribute [-instance] _root_.ArtinKP.X.instContinuousConstSMulGinfX _root_.ArtinKP.X.instContinuousConstSMulSpecialLinearGroupFinOfNatNatComplexH3 _root_.ArtinKP.X.instContinuousConstSMulSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instContinuousConstSMulSpecialLinearGroupFinOfNatNatX _root_.ArtinKP.X.instContinuousConstSMulSubgroup _root_.ArtinKP.X.instIsFiniteMeasureOnCompactsXVol _root_.ArtinKP.X.instIsFiniteMeasureXRestrictVolBox _root_.ArtinKP.X.instMeasurableConstSMulGinfX _root_.ArtinKP.X.instMeasurableConstSMulSpecialLinearGroupFinOfNatNatComplexH3 _root_.ArtinKP.X.instMeasurableConstSMulSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instMeasurableConstSMulSpecialLinearGroupFinOfNatNatX _root_.ArtinKP.X.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatRingOfIntegersXVol _root_.ArtinKP.X.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatXVol _root_.ArtinKP.X.instSigmaFiniteH3Vol _root_.ArtinKP.X.instSigmaFiniteXVol
/-! # WP-X, file 1: one factor — hyperbolic 3-space and the action of `SL(2,ℂ)`

`H3 = {(x, v) : ℂ × ℝ | 0 < v}` with the quaternionic Möbius action
`g • (x, v) = (((a x + b) conj(c x + d) + a conj(c) v²) / D, v / D)`,
`D = |c x + d|² + |c|² v²`.  The action axioms are proved through the quaternion `x + v j`:
`a P + b = (g • P) (c P + d)` in `ℍ[ℝ]`.
-/

open scoped MatrixGroups Quaternion ComplexConjugate

namespace ArtinKP.X

noncomputable section

namespace H3

lemma coe_eq (P : H3) : P.coe = (P.x, P.v) := rfl

end H3

open H3

end

end ArtinKP.X
end

section
-- module Solutions.Artin.KP.X_Space
attribute [-instance] _root_.ArtinKP.X.instContinuousConstSMulSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instContinuousConstSMulSubgroup _root_.ArtinKP.X.instIsFiniteMeasureOnCompactsXVol _root_.ArtinKP.X.instIsFiniteMeasureXRestrictVolBox _root_.ArtinKP.X.instMeasurableConstSMulSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instMulActionSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatRingOfIntegersXVol
attribute [-simp] _root_.ArtinKP.X.chart_apply _root_.ArtinKP.X.chart_symm_apply
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

lemma pairHt_eq_prod (c d : F) (P : X F) :
    pairHt c d P = ∏ w, P.v w / H3.rowDen (w.embedding c) (w.embedding d) (P w) := by
  unfold pairHt ht pairDen
  rw [Finset.prod_div_distrib]

/-- `ht (γ • P) = I_{(c,d)}(P)` for the bottom row `(c, d)` of `γ`. -/
theorem ht_smul (γ : SL(2, F)) (P : X F) : ht (γ • P) = pairHt (γ 1 0) (γ 1 1) P := by
  rw [pairHt_eq_prod]
  exact Finset.prod_congr rfl fun w _ => rfl

end X

/-! ### Topology and measure -/

/-! ### Upper triangular elements, translations and the torus -/

end

end ArtinKP.X
end

section
-- module Solutions.Artin.KP.X_Disjoint
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

end X

end

end ArtinKP.X
end

section
-- module Solutions.Artin.KP.B1_Pairs
attribute [-instance] _root_.ArtinKP.X.instContinuousConstSMulSubgroup _root_.ArtinKP.X.instIsFiniteMeasureOnCompactsXVol _root_.ArtinKP.X.instIsFiniteMeasureXRestrictVolBox
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

end PairClass

/-! ### (B1) for families of `S`-integer pairs -/

/-! ### Lemma M for pair classes -/

end

end ArtinKP.B1
end

section
-- module Solutions.Artin.KP.X2_Chart
attribute [-instance] _root_.ArtinKP.X.instContinuousConstSMulSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instContinuousConstSMulSubgroup _root_.ArtinKP.X.instIsFiniteMeasureOnCompactsXVol _root_.ArtinKP.X.instIsFiniteMeasureXRestrictVolBox _root_.ArtinKP.X.instMeasurableConstSMulSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instMulActionSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatRingOfIntegersXVol
/-! # WP-X2, file 1: the logarithmic chart of `X = (H³)^r`

`chart F : (InfinitePlace F → ℂ × ℝ) ≃ₜ X F`, `(x_w, t_w)_w ↦ (x_w, exp t_w)_w`.  In this chart
`X.vol F` is Lebesgue measure with the smooth density `rho y = exp (-2 ∑_w t_w)`
(`measurePreserving_chart`).  All calculus on `X` is done in this chart: a function on `X` is
smooth iff its pull-back to the vector space `Coord F` is.

Also: Tonelli for products of functions of one coordinate on a finite product
(`lintegral_fintype_prod_eq_prod`) and `pi_withDensity`.
-/

open scoped MatrixGroups ComplexConjugate ENNReal
open MeasureTheory Set NumberField

set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.X

noncomputable section

/-! ### Products of densities -/

/-! ### One factor -/

/-! ### The product -/

variable (F : Type*) [Field F] [NumberField F]

variable {F}

lemma chart_v (y : Coord F) (w : InfinitePlace F) : (chart F y).v w = Real.exp (y w).2 := rfl

end

end ArtinKP.X
end

section
-- module Solutions.Artin.KP.X2_Calc
/-! # WP-X2, file 2: calculus in the logarithmic chart

On `Coord F = InfinitePlace F → ℂ × ℝ` (coordinates `(x_w, t_w)`, `v_w = exp t_w`):

* `pd w k U` — partial derivative in the direction `bvec w k` (`k = 0, 1`: real and imaginary
  part of `x_w`; `k = 2`: `t_w`);
* `lapE U = ∑_w (-(e^{2t_w}(∂₀² + ∂₁²) + ∂₂²) U + 2 ∂₂ U)` — the Laplacian
  `∑_w (-v_w²(∂²_{x₁} + ∂²_{x₂} + ∂²_v) + v_w ∂_v)` in the chart;
* `gamE U W = ∑_w (e^{2t_w}(∂₀U ∂₀W + ∂₁U ∂₁W) + ∂₂U ∂₂W)` — the (bilinear) carré du champ
  `∑_w v_w² ∇_w U · ∇_w W`;
* `green_E`: `∫ ρ T ΔU = ∫ ρ Γ(T, U)` when one of `T`, `U` has compact support;
* Leibniz rules, compatibility with conjugation.
-/

open scoped MatrixGroups ComplexConjugate ENNReal
open MeasureTheory Set NumberField

set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.X

noncomputable section

open Classical

variable {F : Type*} [Field F] [NumberField F]

/-- Decomposition of a vector of `E1` in the basis `e1`. -/
lemma e1_decomp (v : E1) : v = v.1.re • e1 0 + v.1.im • e1 1 + v.2 • e1 2 := by
  apply Prod.ext
  · apply Complex.ext <;> simp
  · simp

lemma clm_decomp (α : E1 →L[ℝ] ℂ) (v : E1) :
    α v = v.1.re * α (e1 0) + v.1.im * α (e1 1) + v.2 * α (e1 2) := by
  conv_lhs => rw [e1_decomp v]
  simp only [map_add, map_smul, Complex.real_smul]

/-! ### Regularity -/

/-! ### Algebraic rules -/

lemma pd_congr {U W : Coord F → ℂ} {y : Coord F} (h : U =ᶠ[nhds y] W)
    (w : InfinitePlace F) (k : Fin 3) : pd w k U =ᶠ[nhds y] pd w k W := by
  filter_upwards [h.eventually_nhds] with z hz
  unfold pd
  rw [Filter.EventuallyEq.fderiv_eq (𝕜 := ℝ) hz]

lemma gamE_congr {U U' W W' : Coord F → ℂ} {y : Coord F} (h : U =ᶠ[nhds y] U')
    (h' : W =ᶠ[nhds y] W') : gamE U W y = gamE U' W' y := by
  unfold gamE
  refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun k _ => ?_
  rw [(pd_congr h w k).self_of_nhds, (pd_congr h' w k).self_of_nhds]

lemma pd_conj (U : Coord F → ℂ) (w : InfinitePlace F) (k : Fin 3) (y : Coord F) :
    pd w k (fun y => conj (U y)) y = conj (pd w k U y) := by
  unfold pd
  have h : (fun y => conj (U y)) = Complex.conjCLE ∘ U := rfl
  rw [h, Complex.conjCLE.comp_fderiv]
  rfl

/-! ### The weights `ρ · a_k` -/

lemma Ls_apply (y : Coord F) : Ls y = ∑ w, (y w).2 := by
  simp [Ls]

/-! ### Green's identity on the chart -/

end

end ArtinKP.X
end

section
-- module Solutions.Artin.KP.X2_Isom
attribute [-instance] _root_.ArtinKP.X.instContinuousConstSMulSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instContinuousConstSMulSubgroup _root_.ArtinKP.X.instIsFiniteMeasureOnCompactsXVol _root_.ArtinKP.X.instIsFiniteMeasureXRestrictVolBox _root_.ArtinKP.X.instMeasurableConstSMulSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instMulActionSpecialLinearGroupFinOfNatNatRingOfIntegersX _root_.ArtinKP.X.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatRingOfIntegersXVol
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

lemma Iso1.trans (b : ℂ) : Iso1 (fun p : E1 => (p.1 + b, p.2)) where
  smooth := by fun_prop
  conf p α β := by
    have h0 : (fun p : E1 => (p.1 + b, p.2)) = fun p => p + (b, 0) := by
      funext p; apply Prod.ext <;> simp
    have : fderiv ℝ (fun p : E1 => (p.1 + b, p.2)) p = ContinuousLinearMap.id ℝ E1 := by
      rw [h0, fderiv_add_const]; exact fderiv_id'
    simp [this, acoef]

lemma rhoJ_pos (p : E1) : 0 < rhoJ p := by
  unfold rhoJ; positivity

lemma contDiff_rhoJ : ContDiff ℝ (⊤ : ℕ∞) rhoJ := by
  unfold rhoJ
  have h1 : ContDiff ℝ (⊤ : ℕ∞) fun p : E1 => p.1.re :=
    Complex.reCLM.contDiff.comp contDiff_fst
  have h2 : ContDiff ℝ (⊤ : ℕ∞) fun p : E1 => p.1.im :=
    Complex.imCLM.contDiff.comp contDiff_fst
  have h3 : ContDiff ℝ (⊤ : ℕ∞) fun p : E1 => Real.exp (2 * p.2) := by fun_prop
  exact ((h1.pow 2).add (h2.pow 2)).add h3

lemma contDiff_Jmap : ContDiff ℝ (⊤ : ℕ∞) Jmap := by
  have h1 : ContDiff ℝ (⊤ : ℕ∞) fun p : E1 => p.1.re :=
    Complex.reCLM.contDiff.comp contDiff_fst
  have h2 : ContDiff ℝ (⊤ : ℕ∞) fun p : E1 => p.1.im :=
    Complex.imCLM.contDiff.comp contDiff_fst
  have hi : ContDiff ℝ (⊤ : ℕ∞) fun p : E1 => (rhoJ p)⁻¹ :=
    contDiff_rhoJ.inv fun p => (rhoJ_pos p).ne'
  have hA : ContDiff ℝ (⊤ : ℕ∞) fun p : E1 => ((-p.1.re * (rhoJ p)⁻¹ : ℝ) : ℂ) :=
    Complex.ofRealCLM.contDiff.comp (h1.neg.mul hi)
  have hB : ContDiff ℝ (⊤ : ℕ∞) fun p : E1 => ((p.1.im * (rhoJ p)⁻¹ : ℝ) : ℂ) :=
    Complex.ofRealCLM.contDiff.comp (h2.mul hi)
  have hC : ContDiff ℝ (⊤ : ℕ∞) fun p : E1 => p.2 - Real.log (rhoJ p) :=
    contDiff_snd.sub (contDiff_rhoJ.log fun p => (rhoJ_pos p).ne')
  exact (hA.add (hB.mul contDiff_const)).prodMk hC

lemma fderiv_Jmap (p h : E1) :
    fderiv ℝ Jmap p h =
      (((-h.1.re * (rhoJ p)⁻¹ + p.1.re * sJ p h * ((rhoJ p)⁻¹) ^ 2 : ℝ) : ℂ) +
          ((h.1.im * (rhoJ p)⁻¹ - p.1.im * sJ p h * ((rhoJ p)⁻¹) ^ 2 : ℝ) : ℂ) * Complex.I,
        h.2 - sJ p h * (rhoJ p)⁻¹) := by
  have hne : rhoJ p ≠ 0 := (rhoJ_pos p).ne'
  have hre : HasFDerivAt (fun p : E1 => p.1.re)
      (Complex.reCLM.comp (ContinuousLinearMap.fst ℝ ℂ ℝ)) p :=
    (Complex.reCLM.comp (ContinuousLinearMap.fst ℝ ℂ ℝ)).hasFDerivAt
  have him : HasFDerivAt (fun p : E1 => p.1.im)
      (Complex.imCLM.comp (ContinuousLinearMap.fst ℝ ℂ ℝ)) p :=
    (Complex.imCLM.comp (ContinuousLinearMap.fst ℝ ℂ ℝ)).hasFDerivAt
  have hsnd : HasFDerivAt (fun p : E1 => p.2) (ContinuousLinearMap.snd ℝ ℂ ℝ) p :=
    (ContinuousLinearMap.snd ℝ ℂ ℝ).hasFDerivAt
  have hρ := ((hre.pow 2).add (him.pow 2)).add ((hsnd.const_mul 2).exp)
  have hρ' : HasFDerivAt rhoJ _ p := hρ
  have hI := (hasDerivAt_inv hne).comp_hasFDerivAt p hρ'
  have hA := (hre.neg).mul hI
  have hB := him.mul hI
  have hC := hsnd.sub (hρ'.log hne)
  have hx := (Complex.ofRealCLM.hasFDerivAt.comp p hA).add
    ((Complex.ofRealCLM.hasFDerivAt.comp p hB).mul_const Complex.I)
  have hJ : HasFDerivAt Jmap _ p := hx.prodMk hC
  rw [hJ.fderiv]
  apply Prod.ext
  · apply Complex.ext
    · simp [sJ]
      ring
    · simp [sJ]
      ring
  · simp [sJ]
    ring

lemma acoef_Jmap (k : Fin 3) (p : E1) :
    acoef k (Jmap p) = if k = 2 then 1 else Real.exp (2 * p.2) * ((rhoJ p)⁻¹) ^ 2 := by
  unfold acoef
  split_ifs
  · rfl
  · have : 2 * (Jmap p).2 = 2 * p.2 - 2 * Real.log (rhoJ p) := by
      simp [Jmap]; ring
    have h2 : Real.exp (2 * Real.log (rhoJ p)) = rhoJ p ^ 2 := by
      rw [two_mul, Real.exp_add, Real.exp_log (rhoJ_pos p)]; ring
    rw [this, Real.exp_sub, h2, div_eq_mul_inv, inv_pow]

lemma iso1_Jmap : Iso1 Jmap where
  smooth := contDiff_Jmap
  conf p α β := by
    have hα : ∀ (γ : E1 →L[ℝ] ℂ) (h : E1), γ (fderiv ℝ Jmap p h) =
        ((-h.1.re * (rhoJ p)⁻¹ + p.1.re * sJ p h * ((rhoJ p)⁻¹) ^ 2 : ℝ) : ℂ) * γ (e1 0) +
        ((h.1.im * (rhoJ p)⁻¹ - p.1.im * sJ p h * ((rhoJ p)⁻¹) ^ 2 : ℝ) : ℂ) * γ (e1 1) +
        ((h.2 - sJ p h * (rhoJ p)⁻¹ : ℝ) : ℂ) * γ (e1 2) := by
      intro γ h
      have hr : ∀ a b : ℝ, ((a : ℂ) + (b : ℂ) * Complex.I).re = a := fun a b => by simp
      have hi : ∀ a b : ℝ, ((a : ℂ) + (b : ℂ) * Complex.I).im = b := fun a b => by simp
      rw [clm_decomp γ, fderiv_Jmap]
      simp only [hr, hi]
    simp only [hα, Fin.sum_univ_three, acoef_Jmap]
    have hE : Real.exp (2 * p.2) = rhoJ p - p.1.re ^ 2 - p.1.im ^ 2 := by
      unfold rhoJ; ring
    have hne : (rhoJ p : ℂ) ≠ 0 := by exact_mod_cast (rhoJ_pos p).ne'
    simp only [acoef, sJ, e1_zero, e1_one, e1_two, hE]
    generalize α (1, 0) = a0
    generalize α (Complex.I, 0) = a1
    generalize α (0, 1) = a2
    generalize β (1, 0) = b0
    generalize β (Complex.I, 0) = b1
    generalize β (0, 1) = b2
    generalize rhoJ p = r at hne ⊢
    generalize p.1.re = x1
    generalize p.1.im = x2
    simp
    field_simp
    ring

/-! ### Every element of `SL(2,ℂ)` acts by an `Iso1` -/

lemma nMat_mem_iso1 (b : ℂ) : nMat b ∈ iso1Submonoid := by
  refine ⟨fun p => (p.1 + b, p.2), Iso1.trans b, fun p => ?_⟩
  have h := nMat_smul b (chart1 p)
  apply H3.ext
  · exact congrArg Prod.fst h
  · exact congrArg Prod.snd h

lemma wMat_mem_iso1 : wMat ∈ iso1Submonoid := by
  refine ⟨Jmap, iso1_Jmap, fun p => ?_⟩
  have h := wMat_smul (chart1 p)
  have hn : nsq (chart1 p).coe = rhoJ p := by
    simp only [nsq, rhoJ, H3.coe_eq, chart1_x, chart1_v, Complex.normSq_apply]
    rw [← Real.exp_nat_mul]
    push_cast
    ring_nf
  have hpos := rhoJ_pos p
  apply H3.ext
  · have h1 : (wMat • chart1 p).x = -conj (inv3 (chart1 p).coe).1 := by
      have := congrArg Prod.fst h; exact this
    rw [h1, inv3_fst, hn]
    change _ = (Jmap p).1
    apply Complex.ext
    · simp [Jmap, H3.coe_eq, Complex.div_re, Complex.normSq_apply]
      field_simp
    · simp [Jmap, H3.coe_eq, Complex.div_im, Complex.normSq_apply]
      field_simp
  · have h2 : (wMat • chart1 p).v = (inv3 (chart1 p).coe).2 := by
      have := congrArg Prod.snd h; exact this
    rw [h2, inv3_snd, hn]
    change _ = Real.exp (Jmap p).2
    simp only [Jmap, H3.coe_eq, chart1_v]
    rw [Real.exp_sub, Real.exp_log hpos]

lemma wMat_inv_eq : wMat⁻¹ = wMat * wMat * wMat := by
  apply Subtype.ext
  rw [wMat_inv_coe]
  simp only [Matrix.SpecialLinearGroup.coe_mul, wMat_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- **Every element of `SL(2,ℂ)` acts in the chart by a conformal smooth map.** -/
theorem mem_iso1 (g : SL(2, ℂ)) : g ∈ iso1Submonoid := by
  have hn := nMat_mem_iso1
  have hw := wMat_mem_iso1
  have hwi : wMat⁻¹ ∈ iso1Submonoid := by
    rw [wMat_inv_eq]
    exact iso1Submonoid.mul_mem (iso1Submonoid.mul_mem hw hw) hw
  have key : ∀ g : SL(2, ℂ), g 1 0 ≠ 0 → g ∈ iso1Submonoid := by
    intro g hc
    rw [bruhat_of_ne hc]
    exact iso1Submonoid.mul_mem (iso1Submonoid.mul_mem (iso1Submonoid.mul_mem
      (iso1Submonoid.mul_mem (iso1Submonoid.mul_mem
      (iso1Submonoid.mul_mem (hn _) (hn _)) hwi) (hn _)) hw) (hn _)) (hn _)
  by_cases hc : g 1 0 = 0
  · have h1 : (g * wMat) 1 0 ≠ 0 := by
      have hd := det_eq g
      have : (g * wMat) 1 0 = g 1 1 := by
        rw [Matrix.SpecialLinearGroup.coe_mul, wMat_coe]
        simp [Matrix.mul_apply, Fin.sum_univ_two]
      rw [this]
      intro h
      rw [hc, h] at hd
      simp at hd
    have : g = (g * wMat) * wMat⁻¹ := by group
    rw [this]
    exact iso1Submonoid.mul_mem (key _ h1) hwi
  · exact key g hc

/-! ### Isometries of the chart -/

variable {F : Type*} [Field F] [NumberField F]

/-- A product of one-factor conformal maps is an isometry of the chart. -/
theorem isoHalf_pi {φ : InfinitePlace F → E1 → E1} (h : ∀ w, Iso1 (φ w)) :
    IsoHalf (fun (y : Coord F) w => φ w (y w)) where
  smooth := contDiff_pi.2 fun w => (h w).smooth.comp (contDiff_apply ℝ E1 w)
  gam_comp U W y hU hW := by
    show gamE (fun z => U (fun w => φ w (z w))) (fun z => W (fun w => φ w (z w))) y =
      gamE U W (fun w => φ w (y w))
    have hΦ : HasFDerivAt (fun (y : Coord F) w => φ w (y w)) (ContinuousLinearMap.pi fun w =>
        (fderiv ℝ (φ w) (y w)).comp (ContinuousLinearMap.proj w)) y :=
      hasFDerivAt_pi.2 fun w =>
        (((h w).smooth.differentiable (by simp) (y w)).hasFDerivAt).comp y
          (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : InfinitePlace F => E1) w).hasFDerivAt
    have key : ∀ (V : Coord F → ℂ), DifferentiableAt ℝ V (fun w => φ w (y w)) → ∀ w k,
        pd w k (fun z => V (fun w => φ w (z w))) y =
          ((fderiv ℝ V (fun w => φ w (y w))).comp
            (ContinuousLinearMap.single ℝ (fun _ : InfinitePlace F => E1) w))
            (fderiv ℝ (φ w) (y w) (e1 k)) := by
      intro V hV w k
      unfold pd
      have hcomp := (hV.hasFDerivAt.comp y hΦ).fderiv
      rw [show (fun z : Coord F => V (fun w => φ w (z w))) =
        V ∘ (fun (y : Coord F) w => φ w (y w)) from rfl, hcomp]
      simp only [ContinuousLinearMap.comp_apply]
      congr 1
      funext w'
      by_cases hw : w' = w
      · subst hw
        simp [bvec]
      · simp [bvec, Pi.single_apply, hw]
    unfold gamE
    refine Finset.sum_congr rfl fun w _ => ?_
    simp_rw [key U hU w, key W hW w]
    exact (h w).conf (y w) _ _

/-! ### The action of `G∞` in the chart -/

lemma chart_actE (g : Ginf F) (y : Coord F) : chart F (actE g y) = g • chart F y := by
  simp [actE]

theorem isoHalf_actE (g : Ginf F) : IsoHalf (actE g) := by
  choose φ hφ hg using fun w => mem_iso1 (g w)
  have : actE g = fun (y : Coord F) w => φ w (y w) := by
    funext y w
    change chart1.symm (g w • chart1 (y w)) = _
    rw [hg w, Homeomorph.symm_apply_apply]
  rw [this]
  exact isoHalf_pi hφ

/-! ### Calculus on `X` -/

/-- **The carré du champ is invariant under `G∞`.** -/
theorem X.gam_comp_Ginf {u w : X F → ℂ} (hu : X.Smooth u) (hw : X.Smooth w) (g : Ginf F)
    (P : X F) : X.gam (fun P => u (g • P)) (fun P => w (g • P)) P = X.gam u w (g • P) := by
  unfold X.gam
  have h1 : ∀ v : X F → ℂ,
      (fun y => v (g • chart F y)) = fun y => (fun z => v (chart F z)) (actE g y) := by
    intro v; funext y; simp only [chart_actE]
  have hu' : ContDiff ℝ (⊤ : ℕ∞) fun y => u (chart F y) := hu
  have hw' : ContDiff ℝ (⊤ : ℕ∞) fun y => w (chart F y) := hw
  rw [h1 u, h1 w, (isoHalf_actE g).gam_comp _ _ _ ((hu'.differentiable (by simp)) _)
    ((hw'.differentiable (by simp)) _)]
  congr 1
  simp [actE]

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

lemma X.Smooth.conj {u : X F → ℂ} (hu : X.Smooth u) : X.Smooth fun P => conj (u P) :=
  Complex.conjCLE.contDiff.comp hu.contDiff

lemma eventuallyEq_chart {β : Type*} {u w : X F → β} {P : X F} (h : u =ᶠ[𝓝 P] w) :
    (fun y => u (chart F y)) =ᶠ[𝓝 ((chart F).symm P)] fun y => w (chart F y) := by
  have ht : Tendsto (chart F) (𝓝 ((chart F).symm P)) (𝓝 P) := by
    have := (chart F).continuous.continuousAt (x := (chart F).symm P)
    rwa [ContinuousAt, Homeomorph.apply_symm_apply] at this
  exact ht.eventually h

lemma X.gam_congr {u u' w w' : X F → ℂ} {P : X F} (h : u =ᶠ[𝓝 P] u') (h' : w =ᶠ[𝓝 P] w') :
    X.gam u w P = X.gam u' w' P :=
  gamE_congr (eventuallyEq_chart h) (eventuallyEq_chart h')

/-! ### Invariance -/

/-! ### Local finiteness and averaging -/

/-! ### Unfolding -/

/-! ### Green's identity on the quotient -/

end

end ArtinKP.X
end

section
-- module Solutions.Artin.KP.X2_H1
attribute [-instance] _root_.ArtinKP.X.instContinuousConstSMulSubgroup
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

/-! ### Local integrability of pull-backs -/

/-! ### The core -/

variable (Γ)

variable {Γ}

variable (Γ)

variable {Γ}

lemma X.gam_conj_self (u : X F → ℂ) (P : X F) :
    X.gam (fun P => conj (u P)) u P = (X.grad2 u P : ℂ) := by
  unfold X.gam X.grad2 gamE
  push_cast
  refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun k _ => ?_
  rw [pd_conj, Complex.conj_mul']

/-! ### Density of the core -/

/-! ### The symmetric operator and the energy space -/

end

end ArtinKP.X
end

section
-- module Solutions.Artin.KP.X2_Eigen
attribute [-instance] _root_.ArtinKP.X.instContinuousConstSMulSubgroup
/-! # WP-X2, file 8: functions of the height

For `G : ℝ → ℂ` smooth, the function `P ↦ G (log (ht P))` on `X` is smooth and
`Δ (G ∘ log ht) = r · (-G'' + 2 G') ∘ log ht`, `∑_w v_w² |∇_w (G ∘ log ht)|² = r · |G'|² ∘ log ht`
(`r` = number of infinite places; in the variable `h = ht` this is `r(-(h∂_h)² + 2h∂_h)`).
The same holds for every pair height `pairHt c d`, `(c, d) ≠ 0`, by invariance under `SL(2,F)`.
In particular `ht^s` and `pairHt c d ^ s` are eigenfunctions with eigenvalue `r · s(2 - s)`.
-/

open scoped MatrixGroups ComplexConjugate ENNReal Topology
open MeasureTheory Set NumberField Filter

set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.X

noncomputable section

open Classical

variable {F : Type*} [Field F] [NumberField F]

lemma Ls_bvec (w : InfinitePlace F) (k : Fin 3) : Ls (bvec w k) = (e1 k).2 := by
  rw [Ls_apply]
  unfold bvec
  rw [Finset.sum_eq_single w]
  · simp
  · intro w' _ hw'
    simp [hw']
  · simp

/-- `log ht` is `∑_w t_w` in the chart. -/
lemma log_ht_chart (y : Coord F) : Real.log (X.ht (chart F y)) = Ls y := by
  unfold X.ht
  rw [Real.log_prod fun w _ => (X.v_pos _ w).ne', Ls_apply]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [chart_v, Real.log_exp]

lemma pd_comp_Ls {G : ℝ → ℂ} (hG : Differentiable ℝ G) (w : InfinitePlace F) (k : Fin 3) :
    pd w k (fun y : Coord F => G (Ls y)) = fun y => ((e1 k).2 : ℂ) * deriv G (Ls y) := by
  funext y
  unfold pd
  have h : HasFDerivAt (fun y : Coord F => G (Ls y)) ((fderiv ℝ G (Ls y)).comp Ls) y :=
    (hG (Ls y)).hasFDerivAt.comp y Ls.hasFDerivAt
  rw [h.fderiv, ContinuousLinearMap.comp_apply, Ls_bvec, fderiv_eq_smul_deriv, Complex.real_smul]

lemma contDiff_comp_Ls {G : ℝ → ℂ} (hG : ContDiff ℝ (⊤ : ℕ∞) G) :
    ContDiff ℝ (⊤ : ℕ∞) fun y : Coord F => G (Ls y) := hG.comp (Ls (F := F)).contDiff

lemma gamE_comp_Ls {G H : ℝ → ℂ} (hG : Differentiable ℝ G) (hH : Differentiable ℝ H)
    (y : Coord F) :
    gamE (fun y : Coord F => G (Ls y)) (fun y : Coord F => H (Ls y)) y =
      (Fintype.card (InfinitePlace F) : ℂ) * (deriv G (Ls y) * deriv H (Ls y)) := by
  unfold gamE
  simp_rw [pd_comp_Ls hG, pd_comp_Ls hH]
  simp [Fin.sum_univ_three, acoef]

/-! ### Functions of the height on `X` -/

/-- A smooth function of `log ht` is smooth on `X`. -/
theorem X.smooth_comp_log_ht {G : ℝ → ℂ} (hG : ContDiff ℝ (⊤ : ℕ∞) G) :
    X.Smooth fun P : X F => G (Real.log (X.ht P)) := by
  unfold X.Smooth
  simp_rw [log_ht_chart]
  exact contDiff_comp_Ls hG

/-- `Γ(G ∘ log ht, H ∘ log ht) = r G' H' ∘ log ht`. -/
theorem X.gam_comp_log_ht {G H : ℝ → ℂ} (hG : Differentiable ℝ G) (hH : Differentiable ℝ H)
    (P : X F) :
    X.gam (fun P : X F => G (Real.log (X.ht P))) (fun P : X F => H (Real.log (X.ht P))) P =
      (Fintype.card (InfinitePlace F) : ℂ) *
        (deriv G (Real.log (X.ht P)) * deriv H (Real.log (X.ht P))) := by
  unfold X.gam
  simp_rw [log_ht_chart]
  rw [gamE_comp_Ls hG hH, ← log_ht_chart, Homeomorph.apply_symm_apply]

/-- `∑_w v_w² |∇_w (G ∘ log ht)|² = r |G'|² ∘ log ht`. -/
theorem X.grad2_comp_log_ht {G : ℝ → ℂ} (hG : Differentiable ℝ G) (P : X F) :
    X.grad2 (fun P : X F => G (Real.log (X.ht P))) P =
      (Fintype.card (InfinitePlace F) : ℝ) * ‖deriv G (Real.log (X.ht P))‖ ^ 2 := by
  have hc : Differentiable ℝ fun t => conj (G t) := Complex.conjCLE.differentiable.comp hG
  have h1 := X.gam_conj_self (fun P : X F => G (Real.log (X.ht P))) P
  have h2 := X.gam_comp_log_ht (F := F) hc hG P
  have h3 : deriv (fun t => conj (G t)) (Real.log (X.ht P)) =
      conj (deriv G (Real.log (X.ht P))) := by
    have := ((hG (Real.log (X.ht P))).hasDerivAt.star)
    exact this.deriv
  rw [h3, Complex.conj_mul'] at h2
  rw [h2] at h1
  exact_mod_cast h1.symm

/-! ### Invariance: pair heights -/

lemma X.grad2_comp_Ginf {u : X F → ℂ} (hu : X.Smooth u) (g : Ginf F) (P : X F) :
    X.grad2 (fun P => u (g • P)) P = X.grad2 u (g • P) := by
  have h1 := X.gam_conj_self (fun P => u (g • P)) P
  have h2 := X.gam_comp_Ginf hu.conj hu g P
  have h3 := X.gam_conj_self u (g • P)
  have h4 : ((X.grad2 (fun P => u (g • P)) P : ℝ) : ℂ) = (X.grad2 u (g • P) : ℂ) := by
    rw [← h1, ← h3]; exact h2
  exact_mod_cast h4

/-- A matrix of `SL(2,F)` with prescribed nonzero bottom row. -/
lemma exists_bottom_row {c d : F} (h : c ≠ 0 ∨ d ≠ 0) :
    ∃ γ : SL(2, F), γ 1 0 = c ∧ γ 1 1 = d := by
  by_cases hc : c = 0
  · have hd : d ≠ 0 := by simpa [hc] using h
    refine ⟨⟨!![d⁻¹, 0; 0, d], by simp [Matrix.det_fin_two, hd]⟩, ?_, ?_⟩
    · simp [hc]
    · simp
  · refine ⟨⟨!![0, -c⁻¹; c, d], by simp [Matrix.det_fin_two, hc]⟩, ?_, ?_⟩ <;> simp

/-- `∑_w v_w² |∇_w (G ∘ log I_{(c,d)})|² = r |G'|² ∘ log I_{(c,d)}`. -/
theorem X.grad2_comp_log_pairHt {G : ℝ → ℂ} (hG : ContDiff ℝ (⊤ : ℕ∞) G) {c d : F}
    (h : c ≠ 0 ∨ d ≠ 0) (P : X F) :
    X.grad2 (fun P : X F => G (Real.log (X.pairHt c d P))) P =
      (Fintype.card (InfinitePlace F) : ℝ) * ‖deriv G (Real.log (X.pairHt c d P))‖ ^ 2 := by
  obtain ⟨γ, rfl, rfl⟩ := exists_bottom_row h
  simp_rw [← X.ht_smul]
  have h1 := X.grad2_comp_Ginf (X.smooth_comp_log_ht (F := F) hG) (sigma F γ) P
  rw [X.grad2_comp_log_ht (hG.differentiable (by simp))] at h1
  exact h1

/-! ### Eigenfunctions -/

end

end ArtinKP.X
end

section
-- module Solutions.Artin.KP.RC_Cutoff
/-! # WP-RC, file 3: the height cut-offs `χ_n` of MATH2 §1.6

`chi S n P = 1 − ∑_{p ∈ PairClass S} ϑ(log ht_p(P) / (n+1))`, `ϑ = 0` on `(−∞,1]`, `ϑ = 1` on `[2,∞)`.
Near every point at most one fixed term is nonzero (`exists_single`: local finiteness from the
summable majorant, uniqueness from (H1)), so `χ_n` is smooth, `0 ≤ χ_n ≤ 1`, and
`∑_w v_w²|∇_w χ_n|² = r ϑ'(…)²/(n+1)² ≤ r C²/(n+1)²` by `X.grad2_comp_log_pairHt` ((H2) in exact form).
`χ_n` is `SL₂(𝓞_F)`-invariant, `χ_n → 1` pointwise (eventually `= 1`), and `χ_n ≠ 0` forces all
heights `≤ e^{2(n+1)}`, a set that is compact modulo `Γ` (MATH2 1.4(d)).

* `exists_cutoffs`: the sequence, in exactly the form of the hypotheses of `X.exists_weakSol`.
* `exists_weakSol`: `X.exists_weakSol` with the cut-off hypotheses discharged.
-/

open scoped MatrixGroups ComplexConjugate ENNReal Topology
open MeasureTheory Set NumberField Module Filter

set_option linter.dupNamespace false
set_option linter.unusedSectionVars false

namespace ArtinKP.RC

open ArtinKP.X ArtinKP.B1

noncomputable section

/-! ### The profile `ϑ` -/

lemma contDiff_theta : ContDiff ℝ (⊤ : ℕ∞) theta :=
  Real.smoothTransition.contDiff.comp (contDiff_id.sub contDiff_const)

lemma contDiff_Gf (ℓ : ℝ) (n : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (Gf ℓ n) := by
  unfold Gf
  refine Complex.ofRealCLM.contDiff.comp (contDiff_const.sub (contDiff_theta.comp ?_))
  exact (contDiff_id.sub contDiff_const).div_const _

lemma norm_deriv_Gf_le {C : ℝ} (hC : ∀ t, |deriv theta t| ≤ C) (ℓ : ℝ) (n : ℕ) (τ : ℝ) :
    ‖deriv (Gf ℓ n) τ‖ ≤ C / ((n : ℝ) + 1) := by
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hθ : DifferentiableAt ℝ theta ((τ - ℓ) / ((n : ℝ) + 1)) :=
    (contDiff_theta.differentiable (by simp)).differentiableAt
  have h1 : HasDerivAt (fun τ : ℝ => (τ - ℓ) / ((n : ℝ) + 1)) (1 / ((n : ℝ) + 1)) τ :=
    ((hasDerivAt_id τ).sub_const ℓ).div_const _
  have h2' : HasDerivAt (theta ∘ fun τ : ℝ => (τ - ℓ) / ((n : ℝ) + 1))
      (deriv theta ((τ - ℓ) / ((n : ℝ) + 1)) * (1 / ((n : ℝ) + 1))) τ :=
    hθ.hasDerivAt.comp τ h1
  have h2 : HasDerivAt (fun τ : ℝ => 1 - theta ((τ - ℓ) / ((n : ℝ) + 1)))
      (-(deriv theta ((τ - ℓ) / ((n : ℝ) + 1)) * (1 / ((n : ℝ) + 1)))) τ :=
    h2'.const_sub 1
  have h3 : HasDerivAt (Gf ℓ n)
      ((-(deriv theta ((τ - ℓ) / ((n : ℝ) + 1)) * (1 / ((n : ℝ) + 1))) : ℝ) : ℂ) τ :=
    h2.ofReal_comp
  rw [h3.deriv, Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_mul,
    abs_of_pos (one_div_pos.mpr hn), mul_one_div]
  exact div_le_div_of_nonneg_right (hC _) hn.le

variable {F : Type*} [Field F] [NumberField F] [IsTotallyComplex F] {S : Finset (FinitePlace F)}

/-! ### Local finiteness -/

/-! ### The cut-offs -/

lemma chi_eq_of_single {n : ℕ} {P : X F} {p₁ : PairClass S}
    (h : ∀ p : PairClass S, p ≠ p₁ → theta (Real.log (p.ht P) / ((n : ℝ) + 1)) = 0) :
    chi S n P = 1 - theta (Real.log (p₁.ht P) / ((n : ℝ) + 1)) := by
  unfold chi
  rw [tsum_eq_single p₁ h]

lemma chi_eventually (S : Finset (FinitePlace F)) (n : ℕ) (P₀ : X F) :
    ∃ p₁ : PairClass S, ∀ᶠ P in 𝓝 P₀,
      chi S n P = 1 - theta (Real.log (p₁.ht P) / ((n : ℝ) + 1)) := by
  obtain ⟨p₁, h⟩ := exists_single S n P₀
  exact ⟨p₁, h.mono fun P hP => chi_eq_of_single hP⟩

/-! ### Smoothness and the gradient bound -/

lemma single_eq_Gf (n : ℕ) (p : PairClass S) (P : X F) :
    ((1 - theta (Real.log (p.ht P) / ((n : ℝ) + 1)) : ℝ) : ℂ) =
      Gf (Real.log (X.sNorm S p.out.c p.out.d)) n (Real.log (X.pairHt p.out.c p.out.d P)) := by
  unfold Gf
  rw [PairClass.ht_eq_out]
  unfold X.sHt
  rw [Real.log_div (X.pairHt_pos p.out.ne_zero P).ne' (X.sNorm_pos S p.out.ne_zero).ne']

lemma chi_eventually_Gf (S : Finset (FinitePlace F)) (n : ℕ) (P₀ : X F) :
    ∃ p₁ : PairClass S, (fun P => (chi S n P : ℂ)) =ᶠ[𝓝 P₀] fun P =>
      Gf (Real.log (X.sNorm S p₁.out.c p₁.out.d)) n (Real.log (X.pairHt p₁.out.c p₁.out.d P)) := by
  obtain ⟨p₁, h⟩ := chi_eventually S n P₀
  refine ⟨p₁, h.mono fun P hP => ?_⟩
  change ((chi S n P : ℝ) : ℂ) = _
  rw [hP]
  exact single_eq_Gf n p₁ P

lemma grad2_congr {u w : X F → ℂ} {P : X F} (h : u =ᶠ[𝓝 P] w) : X.grad2 u P = X.grad2 w P := by
  have h1 : (fun P => conj (u P)) =ᶠ[𝓝 P] fun P => conj (w P) := h.mono fun Q hQ => by
    change conj (u Q) = conj (w Q)
    rw [hQ]
  have h2 := X.gam_congr h1 h
  rw [X.gam_conj_self, X.gam_conj_self] at h2
  exact_mod_cast h2

/-- **Gradient bound** (H2): `∑_w v_w² |∇_w χ_n|² ≤ r C² / (n+1)²`. -/
theorem grad2_chi_le_oai {C : ℝ} (hC : ∀ t, |deriv theta t| ≤ C) (S : Finset (FinitePlace F)) (n : ℕ)
    (P : X F) :
    X.grad2 (fun P : X F => (chi S n P : ℂ)) P ≤
      (Fintype.card (InfinitePlace F) : ℝ) * (C / ((n : ℝ) + 1)) ^ 2 := by
  obtain ⟨p₁, h⟩ := chi_eventually_Gf S n P
  rw [grad2_congr h, X.grad2_comp_log_pairHt (contDiff_Gf _ n) p₁.out.ne_zero]
  refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_deriv_Gf_le hC _ n _) 2

/-! ### The cut-off sequence for `X.exists_weakSol` -/

end

end ArtinKP.RC
end

theorem solution.{u_1} : type_of% @ArtinKP.RC.grad2_chi_le_oai.{u_1} := @ArtinKP.RC.grad2_chi_le_oai.{u_1}
