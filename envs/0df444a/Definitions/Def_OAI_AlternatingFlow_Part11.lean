-- Prove2me | Definitions.Def_OAI_AlternatingFlow_Part11
-- name    : OAI_AlternatingFlow_Part11
-- status  : Definition
-- author  : @SamenHossain
-- created : 2026-10-12T03:50:07.57628+00:00
-- url     : https://prove2.me/theorems/c4560ed1-e30e-4d9a-8f68-946b3d6a6277
-- title:
--   Alternating-flow construction, part 11 of 11 (port of OpenAI's formalization): named programs for the velocity derivatives
-- statement:
--   Part 11 of 11 of a port of OpenAI's Lean formalization of the alternating-flow construction from the manuscript *Computation under Rapidly Vanishing Navier–Stokes Forcing* (OpenAI, September 27, 2026). This part contains named programs for the velocity derivatives.
--
--   **Attribution.** The code is adapted verbatim from the OpenAI "math" repository, commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`, modules `VelocityNames` of `lean/OAI/MathematicalPhysics/AlternatingFlow`. It is © OpenAI and licensed under the Apache License 2.0; the adapted code is redistributed under the same license.
--
--   **Modifications.** Modules are concatenated in dependency order with their imports replaced by the previous part. The model definitions come from the platform definition `NavierStokesAlternating`. Part 1 adds compatibility shims for three core lemmas renamed after Lean 4.33.1, and part 3 adjusts one side-goal tactic for Mathlib 0df444a.
--
--   The development is split into eleven parts only so that each compiles within the platform's time limit. Together the parts supply the velocity construction used to prove `OAI.AlternatingNS.velocity_construction`.
-- source:
--   OpenAI, openai/math, commit adc7f1241b42e322a6451854ab7e4b4c146bf78a, lean/OAI/MathematicalPhysics/AlternatingFlow: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/AlternatingFlow/VelocityNames.lean (Apache License 2.0); manuscript https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Computation-under-Rapidly-Vanishing-Navier-Stokes-Forcing-September-27-2026/manuscript.pdf

/-
Alternating-flow construction (port of OpenAI's formalization), part 11 of 11: named programs for the velocity derivatives.

Adapted from the OpenAI "math" repository (https://github.com/openai/math, commit
adc7f1241b42e322a6451854ab7e4b4c146bf78a), lean/OAI/MathematicalPhysics/AlternatingFlow/: VelocityNames.lean
These files formalize the manuscript "Computation under Rapidly Vanishing Navier-Stokes Forcing"
(OpenAI, September 27, 2026). Copyright OpenAI. Licensed under the Apache License, Version 2.0
(http://www.apache.org/licenses/LICENSE-2.0); the adapted code is distributed under the same license,
on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND.

Modifications: modules concatenated in dependency order with their import lines removed; the model
definitions come from the platform definition `NavierStokesAlternating`.
-/
import Mathlib
import Definitions.Def_OAI_AlternatingFlow_Part10

set_option autoImplicit false

-- ===== Adapted from lean/OAI/MathematicalPhysics/AlternatingFlow/VelocityNames.lean =====
namespace OAI

section VelocityNamesDevelopment

open scoped BigOperators Topology ContDiff
namespace AlternatingNS.Effective
attribute [local instance] Arithmetic.rationalCoding

variable {A : Type*} [Primcodable A]

lemma JetBound.curl_named {f : A → Space → ℝ} (hf : JetBound f)
    (hn : Named (fun z : A × RationalPoint => f z.1 (rationalPoint z.2).2))
    (i j : A → Fin 3) (hi : Computable i) (hj : Computable j) :
    Named (fun z : (A × Fin 3) × RationalPoint =>
      Spatial.curl (i z.1.1) (j z.1.1) (f z.1.1) (rationalPoint z.2).2 z.1.2) := by
  have hp : Computable (fun z : (A × Fin 3) × RationalPoint => (z.1.1,z.2)) :=
    (Computable.fst.comp Computable.fst).pair Computable.snd
  have hdj := (hf.spatial_d_named hn j hj).comp hp
  have hdi := (hf.spatial_d_named hn i hi).comp hp
  have hqi : Computable (fun z : (A × Fin 3) × RationalPoint => decide (z.1.2 = i z.1.1)) := Primrec.eq.decide.to_comp.comp (Computable.snd.comp Computable.fst)
    (hi.comp (Computable.fst.comp Computable.fst))
  have hqj : Computable (fun z : (A × Fin 3) × RationalPoint => decide (z.1.2 = j z.1.1)) := Primrec.eq.decide.to_comp.comp (Computable.snd.comp Computable.fst)
    (hj.comp (Computable.fst.comp Computable.fst))
  exact ((Named.ite _ hqi hdj (Named.const 0)).sub
    (Named.ite _ hqj hdi (Named.const 0))).congr (by
      intro z; simp [Spatial.curl, Spatial.e_apply])

lemma loading_named : Named (fun z : ((Machine × List ℕ) × Fin 3) × RationalPoint =>
    Construction.loading z.1.1.1 z.1.1.2 (rationalPoint z.2).2 z.1.2) := by
  exact loadPotential_bound.curl_named loadPotential_named (fun _ => 1) (fun _ => 0)
    (Computable.const 1) (Computable.const 0)

lemma slot_named : Named (fun z : (((Machine × ℕ) × ℕ) × Fin 3) × RationalPoint =>
    Construction.slot z.1.1.1.1 z.1.1.1.2 z.1.1.2 (rationalPoint z.2).2 z.1.2) := by
  exact slotPotential_bound.curl_named slotPotential_named
    (fun p => Construction.receiverIndex p.2) (fun _ => 0)
    (receiver_computable.comp Computable.snd) (Computable.const 0)

lemma piece_named : Named (fun z : (((Machine × List ℕ) × ℕ) × Fin 3) × RationalPoint =>
    Construction.piece z.1.1.1.1 z.1.1.1.2 z.1.1.2 (rationalPoint z.2).2 z.1.2) := by
  let P := (((Machine × List ℕ) × ℕ) × Fin 3) × RationalPoint
  have hM : Computable (fun z : P => z.1.1.1.1) :=
    Computable.fst.comp (Computable.fst.comp (Computable.fst.comp Computable.fst))
  have hw : Computable (fun z : P => z.1.1.1.2) :=
    Computable.snd.comp (Computable.fst.comp (Computable.fst.comp Computable.fst))
  have hn : Computable (fun z : P => z.1.1.2) :=
    Computable.snd.comp (Computable.fst.comp Computable.fst)
  have hi : Computable (fun z : P => z.1.2) := Computable.snd.comp Computable.fst
  have hload := loading_named.comp (((hM.pair hw).pair hi).pair Computable.snd)
  have hslot := slot_named.comp ((((hM.pair (Computable.list_length.comp hw)).pair
    (Primrec.nat_sub.to_comp.comp hn (Computable.const 1))).pair hi).pair Computable.snd)
  exact (Named.ite (fun z : P => z.1.1.2 = 0)
    (Primrec.eq.decide.to_comp.comp hn (Computable.const 0)) hload hslot).congr
      (by rintro ⟨⟨⟨⟨M,w⟩,n⟩,i⟩,q⟩; cases n <;> rfl)

lemma clock_bound : JetBound (fun _ : Unit => Profiles.clock) := by
  have hclock := transition_scaled.affine (fun _ _ => zero_le_one) (fun _ _ => 2)
    (fun _ _ => -1/2) (fun _ => 2) (Computable.const 2) (by intros; norm_num)
  obtain ⟨hs,B,hB,h⟩ := hclock
  refine ⟨fun _ => Profiles.clock_smooth, B, hB, fun p r x => ?_⟩
  have he : (fun t => Real.smoothTransition (2 * t + -1/2)) = Profiles.clock := by
    funext t; unfold Profiles.clock; congr 1; ring
  simpa only [one_pow, mul_one, he] using h p r 0 x

lemma pulse_rational_named : Named (fun q : ℚ => Profiles.pulse (q : ℝ)) := by
  have hf := clock_bound.comp_unit (fun _ => ContinuousLinearMap.fst ℝ ℝ Space) (fun _ => norm_fst)
  have hn : Named (fun z : Unit × RationalPoint => Profiles.clock (rationalPoint z.2).1) := by
    have ht := Named.rational (Computable.fst.comp (Computable.snd : Computable (Prod.snd : Unit × RationalPoint → _)))
    exact (((Named.const 2).mul ht).sub (Named.const (1/2))).transition.congr (by
      intro z; simp [Profiles.clock, rationalPoint])
  have hd := hf.named_directional hn (fun _ => 0) (Computable.const 0)
  have hdc := hd.comp ((Computable.const ()).pair (Computable.id.pair
    ((Computable.const (0:ℚ)).pair ((Computable.const (0:ℚ)).pair (Computable.const (0:ℚ))))))
  apply hdc.congr
  intro q
  change fderiv ℝ (Profiles.clock ∘ Prod.fst) ((q:ℝ),_) (1,0) = deriv Profiles.clock (q:ℝ)
  rw [fderiv_comp _ (Profiles.clock_smooth.differentiable (by simp) _) differentiableAt_fst, fderiv_fst]
  rfl

lemma velocity_named : Named (fun z : ((Machine × List ℕ) × Fin 3) × RationalPoint =>
    Construction.velocity z.1.1.1 z.1.1.2 (rationalPoint z.2).1 (rationalPoint z.2).2 z.1.2) := by
  let P := ((Machine × List ℕ) × Fin 3) × RationalPoint
  have hq : Computable (fun z : P => z.2.1) := Computable.fst.comp Computable.snd
  let N : P → ℕ := fun z => z.2.1.num.natAbs+1
  have hN : Computable N := Computable.succ.comp (Arithmetic.int_abs.to_comp.comp (Arithmetic.rat_num.to_comp.comp hq))
  have hterm : Named (fun z : P × ℕ => Profiles.pulse ((rationalPoint z.1.2).1 - z.2) *
      Construction.piece z.1.1.1.1 z.1.1.1.2 z.2 (rationalPoint z.1.2).2 z.1.1.2) := by
    have hh := pulse_rational_named.comp (Arithmetic.rat_sub.to_comp.comp
      (hq.comp Computable.fst) (Arithmetic.rat_natCast.to_comp.comp Computable.snd))
    have hp := piece_named.comp
      ((((Computable.fst.comp (Computable.fst.comp Computable.fst)).pair Computable.snd).pair
        (Computable.snd.comp (Computable.fst.comp Computable.fst))).pair
        (Computable.snd.comp Computable.fst))
    exact (hh.mul hp).congr (by intro z; simp [rationalPoint])
  apply (hterm.sum_range N hN).congr
  intro z
  have ht : (rationalPoint z.2).1 ≤ (N z : ℝ) := by
    have hr := le_trans (le_abs_self (z.2.1 : ℝ)) (abs_rat_cast_le_num z.2.1)
    dsimp [N, rationalPoint]; push_cast; linarith
  rw [Construction.velocity, TimeGlue.eq_sum _ Profiles.pulse_zero_left _ _ _ (N z) ht]
  simp [WithLp.ofLp_sum, Finset.sum_apply]

end AlternatingNS.Effective

end VelocityNamesDevelopment

end OAI


