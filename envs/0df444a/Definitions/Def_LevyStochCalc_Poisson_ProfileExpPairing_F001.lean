-- Prove2me | Definitions.Def_LevyStochCalc_Poisson_ProfileExpPairing_F001
-- name    : LevyStochCalc_Poisson_ProfileExpPairing_F001
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T18:05:09.543177+00:00
-- url     : https://prove2.me/theorems/1f651107-23c8-441d-8774-ae638c36f377
-- title:
--   Source declarations: LevyStochCalc.Poisson.ProfileExpPairing
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Poisson.ProfileExpPairing. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Poisson_ProfileExpPairing_F000
import Definitions.Def_SourceProof_d45b0d1b29b0668aa7ebd17b
import Definitions.Def_SourceProof_d7ae88512b435ecbc76009a2

open private tendsto_compensatedProfile_simple tendsto_eLpNorm_exp_sub_one from Definitions.Def_LevyStochCalc_Poisson_ProfileExpPairing_F000
/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# The character of a compensated profile integral against first- and second-order elements

For a Poisson random measure with intensity `ν`, the compensated integral `J` over the step
`(a, b]`, square-integrable mark profiles `h, f, g`, a real frequency `u` and the mark function
`γ_u = e^{iuh} − 1`,

  `E[e^{iuJ(h)} J(f)] = (b − a) ∫ γ_u f dν · E[e^{iuJ(h)}]`,
  `E[e^{iuJ(h)} J(f) J(g)]`
  `  = ((b − a)² ∫ γ_u f dν ∫ γ_u g dν + (b − a) ∫ e^{iuh} f g dν) · E[e^{iuJ(h)}]`.

No bound is placed on the profiles.

At simple profiles these are the identities of `Poisson/ProfileExpPairingSimple.lean`. At
general profiles both sides are limits along simple approximants: the characters
`e^{iuJ(h_n)}`, the compensated integrals `J(f_n)` and the mark functions `e^{iuh_n} − 1`
converge in `L²`, and the complex pairing is continuous along `L²` convergence. For the
second-order identity `h` is approximated first, with `f` and `g` simple so that `J(f) J(g)` is
a fixed square-integrable variable, and `f`, `g` afterwards, with `h` fixed.

## Main statements

* `LevyStochCalc.Poisson.integral_exp_I_mul_compensatedProfile_mul` — the first-order pairing.
* `LevyStochCalc.Poisson.integral_exp_I_mul_compensatedProfile_mul_mul` — the second-order
  pairing.
-/

open MeasureTheory ProbabilityTheory Filter LevyStochCalc.Probability
open scoped NNReal ENNReal Topology

namespace LevyStochCalc.Poisson

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

/-! ### `L²` limits -/

/-! ### The pairings at square-integrable profiles -/

/-- The second-order pairing at a square-integrable profile `h` and simple profiles. -/
private theorem pairing_two_simple (N : PoissonRandomMeasure P ν) {h : E → ℝ} (hh : MemLp h 2 ν)
    (F K : SimpleProfile E ν) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (u : ℝ) :
    ∫ ω, Complex.exp (Complex.I * ((u * compensatedProfile N h a b ω : ℝ) : ℂ))
        * (compensatedProfile N F.toFun a b ω : ℂ) * (compensatedProfile N K.toFun a b ω : ℂ) ∂P
      = (((b - a : ℝ) : ℂ) ^ 2
          * (∫ e, (Complex.exp (Complex.I * ((u * h e : ℝ) : ℂ)) - 1) * (F.toFun e : ℂ) ∂ν)
          * (∫ e, (Complex.exp (Complex.I * ((u * h e : ℝ) : ℂ)) - 1) * (K.toFun e : ℂ) ∂ν)
          + ((b - a : ℝ) : ℂ)
            * ((∫ e, (Complex.exp (Complex.I * ((u * h e : ℝ) : ℂ)) - 1) * (F.toFun e : ℂ)
                * (K.toFun e : ℂ) ∂ν) + ∫ e, (F.toFun e : ℂ) * (K.toFun e : ℂ) ∂ν))
        * ∫ ω, Complex.exp (Complex.I * ((u * compensatedProfile N h a b ω : ℝ) : ℂ)) ∂P := by
  obtain ⟨G, hG⟩ := _root_.Prove2MeSourceProof.h_abfa6819f153687cc685dc62 hh
  have hJm : ∀ g : E → ℝ, MemLp (compensatedProfile N g a b) 2 P :=
    fun g => memLp_compensatedProfile N g a b
  have he := _root_.Prove2MeSourceProof.h_d975e82a4c940db7d3cd3990 u (tendsto_compensatedProfile_simple N hh ha hab hG)
  have hXr : MemLp (fun ω => compensatedProfile N F.toFun a b ω
      * compensatedProfile N K.toFun a b ω) 2 P := by
    refine (((SimpleProfile.memLp_compensatedProduct N F K ha hab).add
      (hJm fun e => F.toFun e * K.toFun e)).add
        (memLp_const ((b - a) * ∫ e, F.toFun e * K.toFun e ∂ν))).ae_eq
      (Eventually.of_forall fun ω => ?_)
    simp only [Pi.add_apply, compensatedProduct]
    ring
  have hX : MemLp (fun ω => (compensatedProfile N F.toFun a b ω : ℂ)
      * (compensatedProfile N K.toFun a b ω : ℂ)) 2 P :=
    hXr.ofReal.ae_eq (Eventually.of_forall fun ω => Complex.ofReal_mul _ _)
  have hFK : MemLp (fun e => (F.toFun e : ℂ) * (K.toFun e : ℂ)) 2 ν := by
    refine (memLp_mul_of_norm_le (Z := fun e => (K.toFun e : ℂ))
      (K.measurable_toFun.complex_ofReal).aestronglyMeasurable (C := ∑ k, |K.c k|)
      (fun e => by
        rw [Complex.norm_real, Real.norm_eq_abs]; exact SimpleProfile.abs_toFun_le K e)
      F.memLp_toFun.ofReal).ae_eq (Eventually.of_forall fun e => mul_comm _ _)
  have hL := _root_.Prove2MeSourceProof.h_d7ae88512b435ecbc76009a2 (G := fun _ => _)
    (fun n => memLp_exp_I_mul u (hJm (G n).toFun).1) (fun _ => hX) (memLp_exp_I_mul u (hJm h).1)
    hX he
    (by simp)
  simp only [← mul_assoc] at hL
  have hγ : ∀ {X : E → ℂ}, MemLp X 2 ν → Tendsto (fun n => ∫ e,
      (Complex.exp (Complex.I * ((u * (G n).toFun e : ℝ) : ℂ)) - 1) * X e ∂ν) atTop
      (𝓝 (∫ e, (Complex.exp (Complex.I * ((u * h e : ℝ) : ℂ)) - 1) * X e ∂ν)) := fun hX =>
    _root_.Prove2MeSourceProof.h_d7ae88512b435ecbc76009a2 (G := fun _ => _)
      (fun n => memLp_exp_I_mul_sub_one u (G n).memLp_toFun) (fun _ => hX)
      (memLp_exp_I_mul_sub_one u hh) hX (tendsto_eLpNorm_exp_sub_one u hG) (by simp)
  have hγFK := hγ hFK
  simp only [← mul_assoc] at hγFK
  have hχ := _root_.Prove2MeSourceProof.h_d7ae88512b435ecbc76009a2 (G := fun _ _ => (1 : ℂ))
    (fun n => memLp_exp_I_mul u (hJm (G n).toFun).1) (fun _ => memLp_const 1)
    (memLp_exp_I_mul u (hJm h).1)
    (memLp_const 1) he (by simp)
  simp only [mul_one] at hχ
  exact tendsto_nhds_unique (hL.congr fun n =>
    _root_.Prove2MeSourceProof.h_d45b0d1b29b0668aa7ebd17b N (G n) F K ha hab u)
    ((((tendsto_const_nhds.mul (hγ F.memLp_toFun.ofReal)).mul (hγ K.memLp_toFun.ofReal)).add
      (tendsto_const_nhds.mul (hγFK.add tendsto_const_nhds))).mul hχ)
/-- The second-order pairing at square-integrable profiles, with `∫ e^{iuh} f g dν` split as
`∫ (e^{iuh} − 1) f g dν + ∫ f g dν`. -/
private theorem pairing_two (N : PoissonRandomMeasure P ν) {h f g : E → ℝ} (hh : MemLp h 2 ν)
    (hf : MemLp f 2 ν) (hg : MemLp g 2 ν) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (u : ℝ) :
    ∫ ω, Complex.exp (Complex.I * ((u * compensatedProfile N h a b ω : ℝ) : ℂ))
        * (compensatedProfile N f a b ω : ℂ) * (compensatedProfile N g a b ω : ℂ) ∂P
      = (((b - a : ℝ) : ℂ) ^ 2
          * (∫ e, (Complex.exp (Complex.I * ((u * h e : ℝ) : ℂ)) - 1) * (f e : ℂ) ∂ν)
          * (∫ e, (Complex.exp (Complex.I * ((u * h e : ℝ) : ℂ)) - 1) * (g e : ℂ) ∂ν)
          + ((b - a : ℝ) : ℂ)
            * ((∫ e, (Complex.exp (Complex.I * ((u * h e : ℝ) : ℂ)) - 1) * (f e : ℂ)
                * (g e : ℂ) ∂ν) + ∫ e, (f e : ℂ) * (g e : ℂ) ∂ν))
        * ∫ ω, Complex.exp (Complex.I * ((u * compensatedProfile N h a b ω : ℝ) : ℂ)) ∂P := by
  obtain ⟨F, hF⟩ := _root_.Prove2MeSourceProof.h_abfa6819f153687cc685dc62 hf
  obtain ⟨K, hK⟩ := _root_.Prove2MeSourceProof.h_abfa6819f153687cc685dc62 hg
  have hJm : ∀ g : E → ℝ, MemLp (compensatedProfile N g a b) 2 P :=
    fun g => memLp_compensatedProfile N g a b
  have hem := (memLp_exp_I_mul u (hJm h).1).1
  have heC : ∀ ω, ‖Complex.exp (Complex.I * ((u * compensatedProfile N h a b ω : ℝ) : ℂ))‖
      ≤ 1 := fun ω => le_of_eq (Complex.norm_exp_I_mul_ofReal _)
  have hγm := (memLp_exp_I_mul_sub_one u hh).1
  have hγC : ∀ e, ‖Complex.exp (Complex.I * ((u * h e : ℝ) : ℂ)) - 1‖ ≤ 2 :=
    fun e => norm_exp_I_mul_sub_one_le_two _
  have hL := _root_.Prove2MeSourceProof.h_d7ae88512b435ecbc76009a2
    (fun n => memLp_mul_of_norm_le hem heC (hJm (F n).toFun).ofReal)
    (fun n => (hJm (K n).toFun).ofReal) (memLp_mul_of_norm_le hem heC (hJm f).ofReal)
    (hJm g).ofReal
    (tendsto_eLpNorm_mul_sub_mul heC
      (tendsto_eLpNorm_ofReal_sub (tendsto_compensatedProfile_simple N hf ha hab hF)))
    (tendsto_eLpNorm_ofReal_sub (tendsto_compensatedProfile_simple N hg ha hab hK))
  have hγ : ∀ {X : ℕ → E → ℝ} {X' : E → ℝ}, (∀ n, MemLp (X n) 2 ν) → MemLp X' 2 ν →
      Tendsto (fun n => eLpNorm (fun e => X n e - X' e) 2 ν) atTop (𝓝 0) →
      Tendsto (fun n => ∫ e, (Complex.exp (Complex.I * ((u * h e : ℝ) : ℂ)) - 1)
        * (X n e : ℂ) ∂ν) atTop
        (𝓝 (∫ e, (Complex.exp (Complex.I * ((u * h e : ℝ) : ℂ)) - 1) * (X' e : ℂ) ∂ν)) :=
    fun hX hX' hc => _root_.Prove2MeSourceProof.h_d7ae88512b435ecbc76009a2 (F := fun _ => _)
      (fun _ => memLp_exp_I_mul_sub_one u hh) (fun n => (hX n).ofReal)
      (memLp_exp_I_mul_sub_one u hh)
      hX'.ofReal (by simp) (tendsto_eLpNorm_ofReal_sub hc)
  have hγFK := _root_.Prove2MeSourceProof.h_d7ae88512b435ecbc76009a2
    (fun n => memLp_mul_of_norm_le hγm hγC (F n).memLp_toFun.ofReal)
    (fun n => (K n).memLp_toFun.ofReal) (memLp_mul_of_norm_le hγm hγC hf.ofReal) hg.ofReal
    (tendsto_eLpNorm_mul_sub_mul hγC (tendsto_eLpNorm_ofReal_sub hF))
    (tendsto_eLpNorm_ofReal_sub hK)
  have hFK := _root_.Prove2MeSourceProof.h_d7ae88512b435ecbc76009a2 (fun n => (F n).memLp_toFun.ofReal)
    (fun n => (K n).memLp_toFun.ofReal) hf.ofReal hg.ofReal (tendsto_eLpNorm_ofReal_sub hF)
    (tendsto_eLpNorm_ofReal_sub hK)
  exact tendsto_nhds_unique (hL.congr fun n => pairing_two_simple N hh (F n) (K n) ha hab u)
    ((((tendsto_const_nhds.mul (hγ (fun n => (F n).memLp_toFun) hf hF)).mul
      (hγ (fun n => (K n).memLp_toFun) hg hK)).add
        (tendsto_const_nhds.mul (hγFK.add hFK))).mul tendsto_const_nhds)
end LevyStochCalc.Poisson


