-- Prove2me | Definitions.Def_OAI_AlternatingFlow_Part06
-- name    : OAI_AlternatingFlow_Part06
-- status  : Definition
-- author  : @SamenHossain
-- created : 2026-10-12T03:36:43.479628+00:00
-- url     : https://prove2.me/theorems/f23acbdd-12a1-497e-bf96-aff1d9c5c60d
-- title:
--   Alternating-flow construction, part 6 of 11 (port of OpenAI's formalization): constructive, decay and certified bounds
-- statement:
--   Part 6 of 11 of a port of OpenAI's Lean formalization of the alternating-flow construction from the manuscript *Computation under Rapidly Vanishing Navier–Stokes Forcing* (OpenAI, September 27, 2026). This part contains constructive, decay and certified bounds.
--
--   **Attribution.** The code is adapted verbatim from the OpenAI "math" repository, commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`, modules `ConstructiveBounds`, `InitialNames`, `DecayBounds`, `CertifiedBounds` of `lean/OAI/MathematicalPhysics/AlternatingFlow`. It is © OpenAI and licensed under the Apache License 2.0; the adapted code is redistributed under the same license.
--
--   **Modifications.** Modules are concatenated in dependency order with their imports replaced by the previous part. The model definitions come from the platform definition `NavierStokesAlternating`. Part 1 adds compatibility shims for three core lemmas renamed after Lean 4.33.1, and part 3 adjusts one side-goal tactic for Mathlib 0df444a.
--
--   The development is split into eleven parts only so that each compiles within the platform's time limit. Together the parts supply the velocity construction used to prove `OAI.AlternatingNS.velocity_construction`.
-- source:
--   OpenAI, openai/math, commit adc7f1241b42e322a6451854ab7e4b4c146bf78a, lean/OAI/MathematicalPhysics/AlternatingFlow: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/AlternatingFlow/ConstructiveBounds.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/AlternatingFlow/InitialNames.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/AlternatingFlow/DecayBounds.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/AlternatingFlow/CertifiedBounds.lean (Apache License 2.0); manuscript https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Computation-under-Rapidly-Vanishing-Navier-Stokes-Forcing-September-27-2026/manuscript.pdf

/-
Alternating-flow construction (port of OpenAI's formalization), part 6 of 11: constructive, decay and certified bounds.

Adapted from the OpenAI "math" repository (https://github.com/openai/math, commit
adc7f1241b42e322a6451854ab7e4b4c146bf78a), lean/OAI/MathematicalPhysics/AlternatingFlow/: ConstructiveBounds.lean, InitialNames.lean, DecayBounds.lean, CertifiedBounds.lean
These files formalize the manuscript "Computation under Rapidly Vanishing Navier-Stokes Forcing"
(OpenAI, September 27, 2026). Copyright OpenAI. Licensed under the Apache License, Version 2.0
(http://www.apache.org/licenses/LICENSE-2.0); the adapted code is distributed under the same license,
on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND.

Modifications: modules concatenated in dependency order with their import lines removed; the model
definitions come from the platform definition `NavierStokesAlternating`.
-/
import Mathlib
import Definitions.Def_OAI_AlternatingFlow_Part05

set_option autoImplicit false

-- ===== Adapted from lean/OAI/MathematicalPhysics/AlternatingFlow/ConstructiveBounds.lean =====
namespace OAI

section ConstructiveBoundsDevelopment

open scoped BigOperators Topology ContDiff
open Filter

namespace AlternatingNS.Effective
attribute [local instance] Arithmetic.rationalCoding

variable {A : Type*} [Primcodable A]

lemma Scaled.nat {s : A → ℕ → ℝ} (hs : ∀ a n, 0 ≤ s a n)
    (c : A → ℕ) (hc : Computable c) : Scaled s (fun a _ (_ : ℝ) => (c a : ℝ)) :=
  Scaled.const hs _ c hc (by intro a n; simp)

lemma Scaled.cmul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {s : A → ℕ → ℝ} (hs : ∀ a n, 0 ≤ s a n) {f : A → ℕ → E → ℝ}
    (hf : Scaled s f) (c : ℝ) (B : ℕ) (hc : |c| ≤ B) :
    Scaled s (fun a n x => c * f a n x) :=
  hf.smul hs (fun _ _ => c) (fun _ => B) (Computable.const B) (fun _ _ => hc)

lemma Scaled.affine {s : A → ℕ → ℝ} (hs : ∀ a n, 0 ≤ s a n)
    {f : A → ℝ → ℝ} (hf : Scaled (fun _ _ => 1) (fun a _ => f a))
    (c d : A → ℕ → ℝ) (B : A → ℕ) (hB : Computable B)
    (hc : ∀ a n, |c a n| ≤ (B a : ℝ) * s a n) :
    Scaled s (fun a n x => f a (c a n * x + d a n)) := by
  obtain ⟨sf,C,hC,hfC⟩ := hf
  refine ⟨fun a n => (sf a 0).comp (contDiff_const.mul contDiff_id |>.add contDiff_const),
    fun z => C z * B z.1 ^ z.2,
    Primrec.nat_mul.to_comp.comp hC (nat_pow.to_comp.comp (hB.comp Computable.fst) Computable.snd),
    fun a r n x => ?_⟩
  change ‖iteratedFDeriv ℝ r ((fun y => f a (y + d a n)) ∘
    (c a n • ContinuousLinearMap.id ℝ ℝ)) x‖ ≤ _
  apply (Bounds.norm_comp_linear _ ((sf a 0).comp (contDiff_id.add contDiff_const)) _ r x).trans
  change ‖iteratedFDeriv ℝ r (fun y => f a (y + d a n)) (c a n * x)‖ *
    ‖c a n • ContinuousLinearMap.id ℝ ℝ‖ ^ r ≤ _
  rw [iteratedFDeriv_comp_add_right]
  simp only [norm_smul, Real.norm_eq_abs, ContinuousLinearMap.norm_id, mul_one]
  push_cast
  calc
    _ ≤ (C (a,r) : ℝ) * ((B a : ℝ) * s a n) ^ r := by
      rw [mul_comm, mul_comm (C (a,r) : ℝ)]
      exact mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) (hc a n) r)
        (by simpa using hfC a r 0 (c a n * x + d a n)) (norm_nonneg _)
        (pow_nonneg (mul_nonneg (Nat.cast_nonneg _) (hs a n)) r)
    _ = _ := by ring

lemma transition_scaled : Scaled (fun _ : Unit => fun _ => 1)
    (fun _ _ => Real.smoothTransition) :=
  ⟨fun _ _ => Real.smoothTransition.contDiff, fun z => Quantitative.transitionBound z.2,
    transitionBound.to_comp.comp Computable.snd, by intro _ r n x; simpa using Quantitative.transition_jet_bound r x⟩

lemma selector_scaled (b a : A → ℕ) (hB : Computable b) :
    Scaled (fun _ _ => 1) (fun p _ => Profiles.selector (b p) (a p)) := by
  have hT := transition_scaled.param (fun _ : A => ()) (Computable.const ())
  have h₁ := hT.affine (fun _ _ => zero_le_one) (fun p _ => 8 * (b p : ℝ))
    (fun p _ => 2 - 16 * (a p : ℝ)) (fun p => 8 * b p)
    (Primrec.nat_mul.to_comp.comp (Computable.const 8) hB) (by intro p n; simp)
  have h₂ := hT.affine (fun _ _ => zero_le_one) (fun p _ => -(8 * (b p : ℝ)))
    (fun p _ => 16 * (a p : ℝ) + 10) (fun p => 8 * b p)
    (Primrec.nat_mul.to_comp.comp (Computable.const 8) hB) (by intro p n; simp)
  exact (h₁.mul (fun _ _ => zero_le_one) h₂).congr (by intros; dsimp [Profiles.selector]; congr 2 <;> ring)

lemma decoder_scaled : Scaled (fun _ : Machine => fun _ => 1)
    (fun M _ => Profiles.decoder M.base) := by
  refine ⟨fun M _ => Profiles.decoder_smooth M.base (by have := M.base_ge_four; omega),
    fun z => Quantitative.decoderBound z.1.base z.2,
    decoderBound.to_comp.comp (base.to_comp.comp Computable.fst) Computable.snd, ?_⟩
  intro M r n x
  simp only [one_pow, mul_one]
  exact Quantitative.decoder_jet_bound M.base (by have := M.base_ge_four; omega) r x

lemma read_scaled (M : A → Machine) (N : A → ℕ) (hM : Computable M)
    (k : A → ℕ → ℕ) (hk : ∀ a n, k a n ≤ Scales.s (N a) n + 1 + Scales.K (N a) n) :
    Scaled (fun a => Bounds.readScale (M a) (N a))
      (fun a n D => Profiles.decoder (M a).base (((M a).base : ℝ) ^ k a n * D)) := by
  apply (decoder_scaled.param M hM).comp_scaled_linear (fun a => Bounds.readScale_nonneg _ _)
    (fun a n => ((M a).base : ℝ) ^ k a n • ContinuousLinearMap.id ℝ ℝ)
  intro a n
  have hb : (1 : ℝ) ≤ (M a).base := by have := (M a).base_ge_four; exact_mod_cast (by omega : 1 ≤ (M a).base)
  simpa only [norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (le_trans zero_le_one hb) _),
    ContinuousLinearMap.norm_id, mul_one, Bounds.readScale] using pow_le_pow_right₀ hb (hk a n)

lemma readC_scaled (M : A → Machine) (N : A → ℕ) (hM : Computable M) :
    Scaled (fun a => Bounds.readScale (M a) (N a)) (fun a => LocalRule.readC (M a) (N a)) :=
  read_scaled M N hM (fun a => Scales.s (N a)) (by intros; omega)

lemma readB_scaled (M : A → Machine) (N : A → ℕ) (hM : Computable M) :
    Scaled (fun a => Bounds.readScale (M a) (N a)) (fun a => LocalRule.readB (M a) (N a)) :=
  read_scaled M N hM _ (by intros; rfl)

lemma readA_scaled (M : A → Machine) (N : A → ℕ) (hM : Computable M) :
    Scaled (fun a => Bounds.readScale (M a) (N a)) (fun a => LocalRule.readA (M a) (N a)) :=
  (read_scaled M N hM (fun a n => Scales.s (N a) n + 1) (by intros; omega)).sub
    ((readB_scaled M N hM).smul (fun a => Bounds.readScale_nonneg _ _) _
      (fun _ => 1) (Computable.const 1) (fun a n => by simpa using Bounds.inverse_power_bound (M a) (Scales.K (N a) n)))

lemma updates_scaled (M : A → Machine) (N a l : A → ℕ) (r : A → Rule)
    (hM : Computable M) (ha : Computable a) (hl : Computable l) (hr : Computable r) :
    Scaled (fun p => Bounds.readScale (M p) (N p))
      (fun p n D => LocalRule.updateLeft (M p).base (a p) (l p) (r p)
        (LocalRule.readA (M p) (N p) n D) (LocalRule.readB (M p) (N p) n D)) ∧
    Scaled (fun p => Bounds.readScale (M p) (N p))
      (fun p n D => LocalRule.updateRight (M p).base (a p) (l p) (r p)
        (LocalRule.readA (M p) (N p) n D) (LocalRule.readB (M p) (N p) n D)) := by
  let s := fun p => Bounds.readScale (M p) (N p)
  have hs : ∀ p n, 0 ≤ s p n := fun p => Bounds.readScale_nonneg _ _
  have hhA := readA_scaled M N hM
  have hhB := readB_scaled M N hM
  have cb := base.to_comp.comp hM
  have hrw := Computable.fst.comp (Computable.snd.comp hr)
  have hb (p : A) (n : ℕ) : |((M p).base : ℝ)| ≤ ((M p).base : ℝ) := by simp
  have hdiv {f : A → ℕ → ℝ → ℝ} (hf : Scaled s f) :
      Scaled s (fun p n D => f p n D / (M p).base) := by
    have h := hf.smul hs (fun p _ => ((M p).base : ℝ)⁻¹) (fun _ => 1) (Computable.const 1)
      (fun p _ => by simpa using Bounds.inverse_power_bound (M p) 1)
    exact h.congr (by intros; simp [div_eq_mul_inv, mul_comm])
  have h2l := Scaled.nat hs (fun p => 2 * l p) (Primrec.nat_mul.to_comp.comp (Computable.const 2) hl)
  have h2a := Scaled.nat hs (fun p => 2 * a p) (Primrec.nat_mul.to_comp.comp (Computable.const 2) ha)
  have h2w := Scaled.nat hs (fun p => 2 * (r p).2.1) (Primrec.nat_mul.to_comp.comp (Computable.const 2) hrw)
  have hLeft := ((hhA.smul hs (fun p _ => ((M p).base : ℝ)) (fun p => (M p).base) cb hb).sub h2l).ite hs
    (hhA.ite hs (hdiv (h2w.add hhA)) (fun p _ => (r p).2.2 = 1)) (fun p _ => (r p).2.2 = 0)
  have hR := (hhB.smul hs (fun p _ => ((M p).base : ℝ)) (fun p => (M p).base) cb hb).sub h2a
  have hRight := (hdiv (h2l.add (hdiv (h2w.add hR)))).ite hs
    ((hdiv (h2w.add hR)).ite hs hR (fun p _ => (r p).2.2 = 1)) (fun p _ => (r p).2.2 = 0)
  constructor
  · exact hLeft.congr (by intro p n x; dsimp [LocalRule.updateLeft]; push_cast; split_ifs <;> rfl)
  · exact hRight.congr (by intro p n x; dsimp [LocalRule.updateRight]; push_cast; split_ifs <;> rfl)

lemma branchNumerator_scaled (M : A → Machine) (N a l : A → ℕ) (r : A → Rule)
    (hM : Computable M) (ha : Computable a) (hl : Computable l) (hr : Computable r) :
    Scaled (fun p => Bounds.readScale (M p) (N p))
      (fun p n D => LocalRule.branchNumerator (M p).base (Scales.K (N p) (n+1)) (a p) (l p) (r p)
        (LocalRule.readA (M p) (N p) n D) (LocalRule.readB (M p) (N p) n D)) := by
  have hs := fun p => Bounds.readScale_nonneg (M p) (N p)
  obtain ⟨hl',hr'⟩ := updates_scaled M N a l r hM ha hl hr
  exact ((Scaled.nat hs (fun p => 2 * (r p).1)
    (Primrec.nat_mul.to_comp.comp (Computable.const 2) (Computable.fst.comp hr))).add hl').add
    (hr'.smul hs (fun p n => (((M p).base : ℝ) ^ Scales.K (N p) (n+1))⁻¹)
      (fun _ => 1) (Computable.const 1) (fun p n => by simpa using Bounds.inverse_power_bound (M p) (Scales.K (N p) (n+1))))

attribute [local irreducible] LocalRule.readA LocalRule.readB LocalRule.readC
  Profiles.selector LocalRule.branchNumerator

lemma branch_scaled (M : A → Machine) (N q a : A → ℕ)
    (hM : Computable M) (hq : Computable q) (ha : Computable a) :
    Scaled (fun p => Bounds.readScale (M p) (N p))
      (fun p n D => LocalRule.branch (M p) (N p) n (q p) (a p)
        (LocalRule.readA (M p) (N p) n D) (LocalRule.readB (M p) (N p) n D)) := by
  have hs := fun p => Bounds.readScale_nonneg (M p) (N p)
  let r := fun p => (M p).command (q p) (a p)
  have hr : Computable r := command.to_comp.comp (hM.pair (hq.pair ha))
  have hb := base.to_comp.comp hM
  have hread := (readA_scaled M N hM).param
    (Prod.fst : A × ℕ → A) Computable.fst
  have hout : Scaled (fun _ : A × ℕ => fun _ => (1:ℝ)) (fun p _ => Profiles.selector (M p.1).base p.2) := selector_scaled (fun p : A × ℕ => (M p.1).base) Prod.snd (hb.comp Computable.fst)
  have hsel : Scaled (fun p : A × ℕ => Bounds.readScale (M p.1) (N p.1))
      (fun p n => Profiles.selector (M p.1).base p.2 ∘ LocalRule.readA (M p.1) (N p.1) n) :=
    Scaled.comp (A := A × ℕ) (E := ℝ) (F := ℝ) (G := ℝ)
      (s := fun p => Bounds.readScale (M p.1) (N p.1))
      (f := fun p => LocalRule.readA (M p.1) (N p.1))
      (g := fun p => Profiles.selector (M p.1).base p.2) (fun p => hs p.1) hread hout
  have hnum := branchNumerator_scaled (fun p : A × ℕ => M p.1) (fun p => N p.1)
    (fun p => a p.1) Prod.snd (fun p => r p.1) (hM.comp Computable.fst)
    (ha.comp Computable.fst) Computable.snd (hr.comp Computable.fst)
  let S := fun (p : A × ℕ) n => Profiles.selector (M p.1).base p.2 ∘ LocalRule.readA (M p.1) (N p.1) n
  let V := fun (p : A × ℕ) n D => LocalRule.branchNumerator (M p.1).base (Scales.K (N p.1) (n+1)) (a p.1) p.2 (r p.1)
    (LocalRule.readA (M p.1) (N p.1) n D) (LocalRule.readB (M p.1) (N p.1) n D)
  have hprod : Scaled (fun p : A × ℕ => Bounds.readScale (M p.1) (N p.1)) (fun p n D => S p n D * V p n D) :=
    Scaled.mul (A := A × ℕ) (E := ℝ) (s := fun p => Bounds.readScale (M p.1) (N p.1)) (f := S) (g := V) (fun p => hs p.1) hsel hnum
  have hsum := hprod.sum_range hs
    (fun p => (M p).alphabet) (alphabet.to_comp.comp hM)
  exact (hsum.ite hs (branchNumerator_scaled M N a (fun _ => 0) r hM ha (Computable.const 0) hr)
    (fun p _ => (r p).2.2 = 0)).congr (by intros; simp only [LocalRule.branch, S, V, r, Function.comp_apply, ite_apply])

attribute [local irreducible] LocalRule.branch

lemma writeCore_scaled : Scaled (fun p : Machine × ℕ => Bounds.readScale p.1 p.2)
    (fun p => Bounds.writeCore p.1 p.2) := by
  let A := ((Machine × ℕ) × ℕ) × ℕ
  let M := fun p : A => p.1.1.1
  let N := fun p : A => p.1.1.2
  let q := fun p : A => p.1.2
  let a := fun p : A => p.2
  have hM : Computable M := Computable.fst.comp (Computable.fst.comp Computable.fst)
  have hq : Computable q := Computable.snd.comp Computable.fst
  have ha : Computable a := Computable.snd
  have hs := fun p => Bounds.readScale_nonneg (M p) (N p)
  have hC := (readC_scaled M N hM).comp (A := A) (E := ℝ) (F := ℝ) (G := ℝ) (s := fun p => Bounds.readScale (M p) (N p)) (g := fun p => Profiles.selector (M p).base (q p)) hs (selector_scaled (fun p => (M p).base) q (base.to_comp.comp hM))
  have hB := (readB_scaled M N hM).comp (A := A) (E := ℝ) (F := ℝ) (G := ℝ) (s := fun p => Bounds.readScale (M p) (N p)) (g := fun p => Profiles.selector (M p).base (a p)) hs (selector_scaled (fun p => (M p).base) a (base.to_comp.comp hM))
  have hsum := ((hC.mul (E := ℝ) hs hB).mul (E := ℝ) hs (branch_scaled M N q a hM hq ha)).sum_range
    (fun p : (Machine × ℕ) × ℕ => Bounds.readScale_nonneg p.1.1 p.1.2)
    (fun p => p.1.1.alphabet) (alphabet.to_comp.comp (Computable.fst.comp Computable.fst))
  have hsum' := hsum.sum_range (fun p : Machine × ℕ => Bounds.readScale_nonneg p.1 p.2)
    (fun p => p.1.states + 1) (Computable.succ.comp (states.to_comp.comp Computable.fst))
  exact (hsum'.smul (A := Machine × ℕ) (E := ℝ) (F := ℝ) (fun p => Bounds.readScale_nonneg p.1 p.2) (fun p _ => 1 / (p.1.base : ℝ))
    (fun _ => 1) (Computable.const 1) (fun p _ => by simpa using Bounds.inverse_power_bound p.1 1)).congr
    (by intros; rfl)

lemma haltWeight_scaled : Scaled (fun p : Machine × ℕ => Bounds.readScale p.1 p.2)
    (fun p => LocalRule.haltWeight p.1 p.2) := by
  have hs := fun p : (Machine × ℕ) × ℕ => Bounds.readScale_nonneg p.1.1 p.1.2
  have h := (readC_scaled (fun p : (Machine × ℕ) × ℕ => p.1.1) (fun p => p.1.2)
    (Computable.fst.comp Computable.fst)).comp (A := (Machine × ℕ) × ℕ) (s := fun p => Bounds.readScale p.1.1 p.1.2) (E := ℝ) (F := ℝ) (G := ℝ) (g := fun p : (Machine × ℕ) × ℕ => Profiles.selector p.1.1.base p.2) hs
    (selector_scaled (fun p : (Machine × ℕ) × ℕ => p.1.1.base) Prod.snd (base.to_comp.comp (Computable.fst.comp Computable.fst)))
  have hzero : Scaled (fun p : (Machine × ℕ) × ℕ => Bounds.readScale p.1.1 p.1.2)
      (fun _ _ (_ : ℝ) => (0 : ℝ)) := Scaled.const hs _ (fun _ => 0) (Computable.const 0) (by intros; simp)
  have hi := (h.ite (A := (Machine × ℕ) × ℕ) (E := ℝ) (F := ℝ) hs hzero (fun p _ => p.2 = p.1.1.states ∨ p.2 ∈ p.1.1.haltingStates)).sum_range (A := Machine × ℕ) (E := ℝ) (F := ℝ)
    (fun p => Bounds.readScale_nonneg p.1 p.2) (fun p => p.1.states + 1)
    (Computable.succ.comp (states.to_comp.comp Computable.fst))

  exact hi.congr (by intros; simp only [LocalRule.haltWeight, Function.comp_apply, ite_apply])

lemma Scaled.coord {s : A → ℕ → ℝ} (hs : ∀ a n, 0 ≤ s a n)
    {f : A → ℕ → ℝ → ℝ} (hf : Scaled s f) (idx : A → ℕ → Fin 3) :
    Scaled s (fun a n (x : Space) => f a n (x (idx a n))) := by
  apply hf.comp_linear (E := ℝ) (F := ℝ) (G := Space) hs
    (fun a n => PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin 3 => ℝ) (idx a n))
    (fun _ => 1) (Computable.const 1)
  intro a n
  simp only [Nat.cast_one]
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  simpa only [one_mul, PiLp.proj_apply] using PiLp.norm_apply_le x (idx a n)

lemma cutoff_scaled : Scaled (fun _ : Unit => fun _ => 1) (fun _ _ => Spatial.cutoff) := by
  have h₁ := transition_scaled.affine (fun _ _ => zero_le_one)
    (fun _ _ => -1) (fun _ _ => 3) (fun _ => 1) (Computable.const 1) (by intros; norm_num)
  have h₂ := transition_scaled.affine (fun _ _ => zero_le_one)
    (fun _ _ => 1) (fun _ _ => 3) (fun _ => 1) (Computable.const 1) (by intros; norm_num)
  have h := h₁.mul (E := ℝ) (fun _ _ => zero_le_one) h₂
  have hi (i : Fin 3) := h.coord (fun _ _ => zero_le_one) (fun _ _ => i)
  exact (((hi 0).mul (E := Space) (fun _ _ => zero_le_one) (hi 1)).mul
    (E := Space) (fun _ _ => zero_le_one) (hi 2)).congr
    (by intro p n x; simp [Spatial.cutoff, Fin.prod_univ_succ, mul_assoc, sub_eq_add_neg,
      add_comm])

lemma coord_jet_on_box (i : Fin 3) (r : ℕ) (x : Space) (hx : x ∈ Spatial.box) :
    ‖iteratedFDeriv ℝ r (fun x : Space => x i) x‖ ≤ 3 := by
  cases r with
  | zero => simpa using hx i
  | succ r =>
    let L := PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin 3 => ℝ) i
    have hd : fderiv ℝ (fun x : Space => x i) = fun _ => L := by
      funext x; exact (Spatial.coord_hasFDeriv i x).fderiv
    rw [← norm_iteratedFDeriv_fderiv, hd]
    cases r with
    | zero =>
      simp only [norm_iteratedFDeriv_zero]
      have hL : ‖L‖ ≤ 1 := ContinuousLinearMap.opNorm_le_bound _ zero_le_one
        (fun y => by simpa only [L, PiLp.proj_apply, one_mul] using PiLp.norm_apply_le y i)
      linarith
    | succ r => rw [iteratedFDeriv_const_of_ne (Nat.succ_ne_zero _), Pi.zero_apply, norm_zero]; norm_num

lemma cutoff_coordinate_scaled (idx : A → ℕ → Fin 3) :
    Scaled (fun _ _ => 1) (fun a n (x : Space) => Spatial.cutoff x * x (idx a n)) := by
  obtain ⟨_,B,hB,hcut⟩ := cutoff_scaled
  have hc : Computable (fun r => B ((),r)) := hB.comp ((Computable.const ()).pair Computable.id)
  let C := fun r => ∑ i ∈ Finset.range (r+1), r.choose i * B ((),i) * 3
  have hi : Computable₂ (fun r i : ℕ => r.choose i * B ((),i) * 3) :=
    Primrec.nat_mul.to_comp.comp (Primrec.nat_mul.to_comp.comp
      (choose.to_comp.comp Computable.fst Computable.snd) (hc.comp Computable.snd)) (Computable.const 3)
  have hC : Computable C := (nat_sum_range hi).comp Computable.id Computable.succ
  refine ⟨fun a n => Spatial.cutoff_smooth.mul (Spatial.coord_smooth (idx a n)),
    fun z => C z.2, hC.comp Computable.snd, fun a r n x => ?_⟩
  simp only [one_pow, mul_one]
  by_cases hx : x ∈ Spatial.box
  · apply (norm_iteratedFDeriv_mul_le Spatial.cutoff_smooth (Spatial.coord_smooth (idx a n)) x
      (WithTop.coe_le_coe.mpr le_top : (r : ℕ∞ω) ≤ ∞)).trans
    simp only [C, Nat.cast_sum, Nat.cast_mul, Nat.cast_ofNat]
    apply Finset.sum_le_sum
    intro i _
    exact mul_le_mul (mul_le_mul_of_nonneg_left (by simpa using hcut () i 0 x) (Nat.cast_nonneg _))
      (coord_jet_on_box _ _ _ hx) (norm_nonneg _) (by positivity)
  · have hn : x ∉ tsupport (fun x : Space => Spatial.cutoff x * x (idx a n)) :=
      fun h => hx (Spatial.cutoff_support (tsupport_mul_subset_left h))
    rw [image_eq_zero_of_notMem_tsupport (fun h => hn (tsupport_iteratedFDeriv_subset r h)), norm_zero]
    positivity

lemma fixedPotential_scaled : Scaled (fun _ : Unit => fun _ => 1) (fun _ => Bounds.fixedPotential) :=
  ((cutoff_coordinate_scaled (fun _ : Unit => Construction.receiverIndex)).cmul
    (fun _ _ => zero_le_one) (-1) 1 (by norm_num)).congr (by intros; simp [Bounds.fixedPotential])

lemma Scaled.grow {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {s : A → ℕ → ℝ} (hs : ∀ a n, 1 ≤ s a n) {f : A → ℕ → E → F}
    (hf : Scaled (fun _ _ => 1) f) : Scaled s f := by
  obtain ⟨sf,B,hB,hfB⟩ := hf
  refine ⟨sf,B,hB,fun a r n x => ?_⟩
  have h : ‖iteratedFDeriv ℝ r (f a n) x‖ ≤ (B (a,r) : ℝ) := by simpa using hfB a r n x
  exact h.trans (le_mul_of_one_le_right (Nat.cast_nonneg _) (one_le_pow₀ (hs a n)))

lemma corePotential_scaled : Scaled (fun p : Machine × ℕ => Bounds.readScale p.1 p.2)
    (fun p => Bounds.corePotential p.1 p.2) := by
  have hs := fun p : Machine × ℕ => Bounds.readScale_nonneg p.1 p.2
  have h (idx : (Machine × ℕ) → ℕ → Fin 3) :=
    (cutoff_coordinate_scaled idx).grow (A := Machine × ℕ) (E := Space) (F := ℝ) (s := fun p => Bounds.readScale p.1 p.2) (fun p => Bounds.readScale_ge_one p.1 p.2)
  have hw := writeCore_scaled.coord hs (fun _ => Construction.donorIndex)
  have hh := (haltWeight_scaled.coord hs (fun _ => Construction.donorIndex)).cmul hs 2 2 (by norm_num)
  exact ((h (fun _ _ => 0)).mul (E := Space) hs hw).sub
    ((h (fun _ => Construction.receiverIndex)).mul (E := Space) hs hh)

end AlternatingNS.Effective

end ConstructiveBoundsDevelopment

end OAI

-- ===== Adapted from lean/OAI/MathematicalPhysics/AlternatingFlow/InitialNames.lean =====
namespace OAI

section InitialNamesDevelopment

open scoped BigOperators Topology ContDiff
namespace AlternatingNS.Effective
attribute [local instance] Arithmetic.rationalCoding

def ratCode (b : ℕ) (ds : List ℕ) : ℚ :=
  ds.foldr (fun (d : ℕ) (q : ℚ) => ((d : ℚ) + q) / b) 0

lemma ratCode_cast (b : ℕ) (ds : List ℕ) :
    (ratCode b ds : ℝ) = Encoding.code b ds := by
  induction ds with
  | nil => simp [ratCode, Encoding.code]
  | cons d ds ih => simp only [ratCode, List.foldr_cons, Rat.cast_div, Rat.cast_add,
      Rat.cast_natCast, Encoding.code] at *; rw [ih]

lemma ratCode_primrec : Primrec₂ ratCode :=
  Primrec.list_foldr Primrec.snd (Primrec.const 0)
    ((Arithmetic.rat_div.comp (Arithmetic.rat_add.comp
      (Arithmetic.rat_natCast.comp (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd))
      (Arithmetic.rat_natCast.comp (Primrec.fst.comp Primrec.fst)))).to₂

lemma digits_eq_map (K : ℕ) (f : ℕ → ℕ) :
    Encoding.digits K f = (List.range K).map f := by
  induction K generalizing f with
  | zero => simp [Encoding.digits]
  | succ K ih => rw [Encoding.digits_succ, ih, List.range_succ_eq_map]; simp only [List.map_cons,
      List.map_map, Function.comp_def, Nat.succ_eq_add_one]

lemma initial_digits_primrec : Primrec (fun z : Machine × List ℕ => z.1.recordedDigits z.2 0) := by
  have hK : Primrec (fun z : Machine × List ℕ => Scales.K z.2.length 0) :=
    capacity.comp (Primrec.list_length.comp Primrec.snd) (Primrec.const 0)
  have hL : Primrec (fun z : Machine × List ℕ => (List.range (Scales.K z.2.length 0)).map (fun _ : ℕ => 0)) := Primrec.list_map (Primrec.list_range.comp hK) (Primrec.const (0 : ℕ)).to₂
  have hR : Primrec (fun z : Machine × List ℕ => (List.range (Scales.K z.2.length 0)).map (fun j : ℕ => 2 * z.2[j]?.getD 0)) := Primrec.list_map (Primrec.list_range.comp hK)
    ((Primrec.nat_mul.comp (Primrec.const 2)
      (Primrec.option_getD.comp (Primrec.list_getElem?.comp (Primrec.snd.comp Primrec.fst)
        Primrec.snd) (Primrec.const 0)))).to₂
  refine (Primrec.list_cons.comp
    (Primrec.nat_mul.comp (Primrec.const 2) (initialState.comp Primrec.fst))
    (Primrec.list_append.comp hL hR)).of_eq ?_
  intro z
  simp only [Machine.recordedDigits, Machine.run, Function.iterate_zero, id_eq, Machine.initial,
    digits_eq_map]
  congr 1
  apply congrArg₂ List.append
  · apply List.map_congr_left; intro j hj
    have h : ¬ (0 : ℤ) ≤ 0 - ((j : ℤ) + 1) := by omega
    simp [Machine.leftDigits]; omega
  · apply List.map_congr_left; intro j hj
    simp [Machine.rightDigits]

def initialBlock (M : Machine) (w : List ℕ) : ℚ := ratCode M.base (M.recordedDigits w 0)

lemma initialBlock_primrec : Primrec₂ initialBlock :=
  ratCode_primrec.comp (base.comp Primrec.fst) initial_digits_primrec

lemma initialBlock_cast (M : Machine) (w : List ℕ) :
    (initialBlock M w : ℝ) = M.recordedBlock w 0 := ratCode_cast _ _

lemma epsilon_named : Named (fun z : (Machine × ℕ) × ℕ => Scales.ε z.1.1.base z.1.2 z.2) := by
  have h := Named.rational (Arithmetic.rat_inv.to_comp.comp
    (Arithmetic.rat_pow.to_comp.comp
      (Arithmetic.rat_natCast.to_comp.comp (base.to_comp.comp (Computable.fst.comp Computable.fst)))
      (exponent.to_comp.comp (Computable.snd.comp Computable.fst) Computable.snd)))
  exact h.congr (by intros; simp only [Scales.ε, Rat.cast_inv, Rat.cast_pow, Rat.cast_natCast])

lemma loadingPotential_scaled : Scaled (fun _ : Machine × List ℕ => fun _ => 1)
    (fun z _ (x : Space) => Spatial.cutoff x *
      Spatial.shearPotential 2 1 0 (fun _ => Scales.ε z.1.base z.2.length 0 * z.1.recordedBlock z.2 0)
        (fun _ => 1 - Scales.ε z.1.base z.2.length 0) x) := by
  let B := fun z : Machine × List ℕ => (initialBlock z.1 z.2).num.natAbs
  have hB : Computable B := Arithmetic.int_abs.to_comp.comp
    (Arithmetic.rat_num.to_comp.comp initialBlock_primrec.to_comp)
  have he (z : Machine × List ℕ) : 0 ≤ Scales.ε z.1.base z.2.length 0 ∧
      Scales.ε z.1.base z.2.length 0 ≤ 1 := by
    refine ⟨Scales.ε_nonneg _ _ _ (by have := z.1.base_ge_four; omega), ?_⟩
    simpa [Scales.ε] using (Bounds.inverse_power_bound z.1 (Scales.s z.2.length 0))
  have h₁ := (cutoff_coordinate_scaled (fun _ : Machine × List ℕ => fun _ => (0 : Fin 3))).smul
    (fun _ _ => zero_le_one)
    (fun z _ => Scales.ε z.1.base z.2.length 0 * z.1.recordedBlock z.2 0) B hB (by
      intro z n
      rw [abs_mul, abs_of_nonneg (he z).1, ← initialBlock_cast]
      exact (mul_le_mul_of_nonneg_right (he z).2 (abs_nonneg _)).trans (by
        simpa [B] using abs_rat_cast_le_num (initialBlock z.1 z.2)))
  have h₂ := (cutoff_coordinate_scaled (fun _ : Machine × List ℕ => fun _ => (1 : Fin 3))).smul
    (fun _ _ => zero_le_one) (fun z _ => 1 - Scales.ε z.1.base z.2.length 0)
    (fun _ => 1) (Computable.const 1) (by
      intro z n
      rw [abs_of_nonneg (sub_nonneg.mpr (he z).2)]
      simpa using sub_le_self (1 : ℝ) (he z).1)
  exact (h₁.sub h₂).congr (by intros; dsimp [Spatial.shearPotential]; ring)
end AlternatingNS.Effective

end InitialNamesDevelopment

end OAI

-- ===== Adapted from lean/OAI/MathematicalPhysics/AlternatingFlow/DecayBounds.lean =====
namespace OAI

section DecayBoundsDevelopment

open scoped BigOperators Topology ContDiff
open Filter
namespace AlternatingNS.Effective
attribute [local instance] Arithmetic.rationalCoding
open Bounds (readScale readScale_nonneg potential_decomposition norm_iterated_curl amplitude norm_comp_linear)

lemma potential_bound : ∃ C : (Machine × ℕ) × ℕ → ℕ, Computable C ∧ ∀ M N r n x,
    ‖iteratedFDeriv ℝ r (fun x => Spatial.cutoff x *
      Spatial.shearPotential (Construction.donorIndex n) (Construction.receiverIndex n) 0
        (LocalRule.write M N n) (LocalRule.signal M N n) x) x‖ ≤
        (C ((M,N),r) : ℝ) * (Scales.ε M.base N n + Scales.ε M.base N (n + 1) * readScale M N n ^ r) := by
  obtain ⟨sA, A, cA, ha⟩ := fixedPotential_scaled
  obtain ⟨sB, B, cB, hb⟩ := corePotential_scaled
  refine ⟨fun z => A ((), z.2) + B z,
    Primrec.nat_add.to_comp.comp
      (cA.comp ((Computable.const ()).pair Computable.snd)) cB, fun M N r n x => ?_⟩
  have hA : 0 ≤ (A ((),r) : ℝ) := Nat.cast_nonneg _
  have hB : 0 ≤ (B ((M,N),r) : ℝ) := Nat.cast_nonneg _
  simp only [Nat.cast_add]
  have hε : 0 ≤ Scales.ε M.base N (n + 1) := Scales.ε_nonneg _ _ _ (by have := M.base_ge_four; omega)
  have hε' : Scales.ε M.base N (n + 1) ≤ Scales.ε M.base N n :=
    (Scales.ε_strictAnti M.base N (by have := M.base_ge_four; omega)).antitone (by omega)
  have h₁ := sA () n
  have h₂ := sB (M,N) n
  simp_rw [potential_decomposition]
  change ‖iteratedFDeriv ℝ r (fun x =>
    (Scales.ε M.base N n - Scales.ε M.base N (n + 1)) • Bounds.fixedPotential n x +
      Scales.ε M.base N (n + 1) • Bounds.corePotential M N n x) x‖ ≤ _
  have hs₁ : ContDiff ℝ ∞ (fun x =>
      (Scales.ε M.base N n - Scales.ε M.base N (n + 1)) • Bounds.fixedPotential n x) := h₁.const_smul _
  have hs₂ : ContDiff ℝ ∞ (fun x =>
      Scales.ε M.base N (n + 1) • Bounds.corePotential M N n x) := h₂.const_smul _
  rw [fun_iteratedFDeriv_add_apply
    (hs₁.of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt
    (hs₂.of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt]
  apply (norm_add_le _ _).trans
  rw [iteratedFDeriv_const_smul_apply' (h₁.of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt,
    iteratedFDeriv_const_smul_apply' (h₂.of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt,
    norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (sub_nonneg.mpr hε'), abs_of_nonneg hε]
  have haa : ‖iteratedFDeriv ℝ r (Bounds.fixedPotential n) x‖ ≤ (A ((),r) : ℝ) := by simpa using ha () r n x
  have hbb := hb (M,N) r n x
  have hscale := pow_nonneg (readScale_nonneg M N n) r
  calc
    _ ≤ Scales.ε M.base N n * (A ((),r) : ℝ) +
      Scales.ε M.base N (n + 1) * ((B ((M,N),r) : ℝ) * readScale M N n ^ r) := by
      exact add_le_add
        (mul_le_mul (by linarith) haa (norm_nonneg _) (by linarith))
        (mul_le_mul_of_nonneg_left hbb hε)
    _ ≤ _ := by nlinarith [mul_nonneg (show 0 ≤ Scales.ε M.base N n by linarith) hB,
      mul_nonneg hA (mul_nonneg hε hscale)]

lemma slot_estimate : ∃ C : (Machine × ℕ) × ℕ → ℕ, Computable C ∧ ∀ M N r n x,
    ‖iteratedFDeriv ℝ r (Construction.slot M N n) x‖ ≤
      (C ((M,N),r) : ℝ) * (Scales.ε M.base N n + Scales.ε M.base N (n + 1) * readScale M N n ^ (r + 1)) := by
  obtain ⟨C, hC, hc⟩ := potential_bound
  refine ⟨fun z => 2 * C (z.1,z.2+1),
    Primrec.nat_mul.to_comp.comp (Computable.const 2)
      (hC.comp (Computable.fst.pair (Computable.succ.comp Computable.snd))), fun M N r n x => ?_⟩
  have h := norm_iterated_curl (Construction.receiverIndex n) 0 _
    (Spatial.cutoff_smooth.mul (Spatial.shearPotential_smooth (Construction.donorIndex n)
      (Construction.receiverIndex n) 0 _ _
      (LocalRule.write_smooth M N n) (LocalRule.signal_smooth M N n))) r x
  apply h.trans
  push_cast
  nlinarith [hc M N (r+1) n x]

def readCost (z : (Machine × ℕ) × ℕ) : ℕ :=
  1 + ∑ n ∈ Finset.range z.2, z.1.1.base ^
    (Scales.s z.1.2 n + (z.2+1) * (Scales.s z.1.2 n + 1 + Scales.K z.1.2 n))

lemma readCost_computable : Computable readCost := by
  have hM : Computable (fun z : ((Machine × ℕ) × ℕ) × ℕ => z.1.1.1) :=
    Computable.fst.comp (Computable.fst.comp Computable.fst)
  have hN : Computable (fun z : ((Machine × ℕ) × ℕ) × ℕ => z.1.1.2) :=
    Computable.snd.comp (Computable.fst.comp Computable.fst)
  have hs : Computable (fun z : ((Machine × ℕ) × ℕ) × ℕ => Scales.s z.1.1.2 z.2) := exponent.to_comp.comp hN Computable.snd
  have hK : Computable (fun z : ((Machine × ℕ) × ℕ) × ℕ => Scales.K z.1.1.2 z.2) := capacity.to_comp.comp hN Computable.snd
  have hp : Computable₂ (fun z : (Machine × ℕ) × ℕ => fun n : ℕ => z.1.1.base ^ (Scales.s z.1.2 n + (z.2+1) * (Scales.s z.1.2 n + 1 + Scales.K z.1.2 n))) := nat_pow.to_comp.comp (base.to_comp.comp hM)
    (Primrec.nat_add.to_comp.comp hs (Primrec.nat_mul.to_comp.comp
      (Computable.succ.comp (Computable.snd.comp Computable.fst))
      (Primrec.nat_add.to_comp.comp (Computable.succ.comp hs) hK)))
  unfold readCost
  exact Primrec.nat_add.to_comp.comp (Computable.const 1)
    ((nat_sum_range hp).comp Computable.id Computable.snd)

lemma uniform_read_cost (M : Machine) (N r n : ℕ) :
    Scales.ε M.base N (n + 1) * readScale M N n ^ (r + 1) ≤
      (readCost ((M,N),r) : ℝ) * Scales.ε M.base N n := by
  have hb : (1 : ℝ) ≤ M.base := by have := M.base_ge_four; exact_mod_cast (by omega : 1 ≤ M.base)
  have hε (n : ℕ) : 0 < Scales.ε M.base N n :=
    Scales.ε_pos _ _ _ (by have := M.base_ge_four; omega)
  have hD : (1 : ℝ) ≤ readCost ((M,N),r) := by
    dsimp [readCost]; push_cast
    exact le_add_of_nonneg_right (Finset.sum_nonneg (by intros; positivity))
  have he : readScale M N n ^ (r + 1) =
      (M.base : ℝ) ^ ((r+1) * (Scales.s N n + 1 + Scales.K N n)) := by
    rw [readScale, ← pow_mul, Nat.mul_comm]
  by_cases hn : n < r
  · have hle : M.base ^ (Scales.s N n + (r+1) * (Scales.s N n + 1 + Scales.K N n)) ≤ readCost ((M,N),r) :=
      (Finset.single_le_sum (f := fun n => M.base ^ (Scales.s N n + (r+1) * (Scales.s N n + 1 + Scales.K N n)))
        (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr hn)).trans (Nat.le_add_left _ _)
    have hpow : ((M.base : ℝ) ^ Scales.s N n) ≠ 0 := ne_of_gt (pow_pos (zero_lt_one.trans_le hb) _)
    calc
      _ ≤ readScale M N n ^ (r+1) := by
        apply mul_le_of_le_one_left (pow_nonneg (readScale_nonneg M N n) _)
        simpa [Scales.ε, abs_of_nonneg (inv_nonneg.mpr (pow_nonneg (zero_le_one.trans hb) _))] using
          Bounds.inverse_power_bound M (Scales.s N (n+1))
      _ = (M.base : ℝ) ^ (Scales.s N n + (r+1) * (Scales.s N n + 1 + Scales.K N n)) * Scales.ε M.base N n := by
        rw [he, pow_add, Scales.ε]; field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hle) (hε n).le
  · rw [he]
    exact (Scales.derivative_cost_bound M.base N r n (by have := M.base_ge_four; omega)
      (by omega)).trans (le_mul_of_one_le_left (hε n).le hD)

lemma slot_decay : ∃ C : (Machine × ℕ) × ℕ → ℕ, Computable C ∧ ∀ M N r n x,
    ‖iteratedFDeriv ℝ r (Construction.slot M N n) x‖ ≤ (C ((M,N),r) : ℝ) * Scales.ε M.base N n := by
  obtain ⟨C,hC,hc⟩ := slot_estimate
  refine ⟨fun z => C z * (1 + readCost z), Primrec.nat_mul.to_comp.comp hC
    (Primrec.nat_add.to_comp.comp (Computable.const 1) readCost_computable), fun M N r n x => ?_⟩
  apply (hc M N r n x).trans
  push_cast
  have h := mul_le_mul_of_nonneg_left (uniform_read_cost M N r n) (Nat.cast_nonneg (C ((M,N),r)) : (0 : ℝ) ≤ _)
  nlinarith

lemma loading_bound : ∃ C : (Machine × List ℕ) × ℕ → ℕ, Computable C ∧ ∀ M w r x,
    ‖iteratedFDeriv ℝ r (Construction.loading M w) x‖ ≤ C ((M,w),r) := by
  obtain ⟨hs,C,hC,hc⟩ := loadingPotential_scaled
  refine ⟨fun z => 2 * C (z.1,z.2+1), Primrec.nat_mul.to_comp.comp (Computable.const 2)
    (hC.comp (Computable.fst.pair (Computable.succ.comp Computable.snd))), fun M w r x => ?_⟩
  apply (norm_iterated_curl 1 0 _ (hs (M,w) 0) r x).trans
  have h := hc (M,w) (r+1) 0 x
  simp only [one_pow, mul_one] at h
  push_cast
  linarith

lemma piece_decay : ∃ C : (Machine × List ℕ) × ℕ → ℕ, Computable C ∧ ∀ M w r n x,
    ‖iteratedFDeriv ℝ r (Construction.piece M w n) x‖ ≤ (C ((M,w),r) : ℝ) * amplitude M w.length n := by
  obtain ⟨A,hA,ha⟩ := loading_bound
  obtain ⟨B,hB,hb⟩ := slot_decay
  refine ⟨fun z => A z + B ((z.1.1,z.1.2.length),z.2), Primrec.nat_add.to_comp.comp hA
    (hB.comp (((Computable.fst.comp Computable.fst).pair
      (Primrec.list_length.to_comp.comp (Computable.snd.comp Computable.fst))).pair Computable.snd)), fun M w r n x => ?_⟩
  cases n with
  | zero =>
    simp only [Construction.piece, amplitude, mul_one, Nat.cast_add]
    exact (ha M w r x).trans (le_add_of_nonneg_right (Nat.cast_nonneg _))
  | succ n =>
    simp only [Construction.piece, amplitude, Nat.cast_add]
    exact (hb M w.length r n x).trans (mul_le_mul_of_nonneg_right
      (le_add_of_nonneg_left (Nat.cast_nonneg _)) (Scales.ε_nonneg _ _ _ (by have := M.base_ge_four; omega)))

lemma pulse_scaled : Scaled (fun _ : Unit => fun _ => 1) (fun _ _ => Profiles.pulse) := by
  have hclock := transition_scaled.affine (fun _ _ => zero_le_one) (fun _ _ => 2)
    (fun _ _ => -1/2) (fun _ => 2) (Computable.const 2) (by intros; norm_num)
  have he : (fun t => Real.smoothTransition (2 * t + -1/2)) = Profiles.clock := by
    funext t; unfold Profiles.clock; congr 1; ring
  obtain ⟨hs,C,hC,hc⟩ := hclock
  refine ⟨fun _ _ => Profiles.pulse_smooth, fun z => C ((),z.2+1),
    hC.comp ((Computable.const ()).pair (Computable.succ.comp Computable.snd)), fun a r n x => ?_⟩
  rw [he] at hc
  change ‖iteratedFDeriv ℝ r (deriv Profiles.clock) x‖ ≤ _
  simpa [one_pow, norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_succ'] using hc () (r+1) 0 x

lemma pulsePiece_decay : ∃ C : (Machine × List ℕ) × ℕ → ℕ, Computable C ∧ ∀ M w r n z,
    ‖iteratedFDeriv ℝ r (Bounds.pulsePiece M w n) z‖ ≤ (C ((M,w),r) : ℝ) * amplitude M w.length n := by
  obtain ⟨_,A,hA,ha⟩ := pulse_scaled
  obtain ⟨B,hB,hb⟩ := piece_decay
  let C := fun z : (Machine × List ℕ) × ℕ => ∑ i ∈ Finset.range (z.2+1), z.2.choose i * A ((),i) * B (z.1,z.2-i)
  have hi : Computable₂ (fun z : (Machine × List ℕ) × ℕ => fun i : ℕ => z.2.choose i * A ((),i) * B (z.1,z.2-i)) :=
    Primrec.nat_mul.to_comp.comp (Primrec.nat_mul.to_comp.comp
      (choose.to_comp.comp (Computable.snd.comp Computable.fst) Computable.snd)
      (hA.comp ((Computable.const ()).pair Computable.snd)))
      (hB.comp ((Computable.fst.comp Computable.fst).pair
        (Primrec.nat_sub.to_comp.comp (Computable.snd.comp Computable.fst) Computable.snd)))
  refine ⟨C, (nat_sum_range hi).comp Computable.id (Computable.succ.comp Computable.snd), fun M w r n z => ?_⟩
  have hp (i : ℕ) :
      ‖iteratedFDeriv ℝ i (fun z : ℝ × Space => Profiles.pulse (z.1 - n)) z‖ ≤ (A ((),i) : ℝ) := by
    apply (norm_comp_linear (fun t => Profiles.pulse (t - n))
      (Profiles.pulse_smooth.comp (contDiff_id.sub contDiff_const)) (ContinuousLinearMap.fst ℝ ℝ Space)
      i z).trans
    rw [iteratedFDeriv_comp_sub]
    have h₁ : ‖iteratedFDeriv ℝ i Profiles.pulse (z.1 - n)‖ ≤ (A ((),i) : ℝ) := by simpa using ha () i 0 (z.1 - n)
    have h₂ := pow_le_pow_left₀ (norm_nonneg _) (ContinuousLinearMap.norm_fst_le ℝ ℝ Space) i
    simpa only [one_pow, mul_one, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd'] using mul_le_mul h₁ h₂ (pow_nonneg (norm_nonneg _) _) (Nat.cast_nonneg (A ((),i)))
  have hw (i : ℕ) :
      ‖iteratedFDeriv ℝ i (fun z : ℝ × Space => Construction.piece M w n z.2) z‖ ≤
        (B ((M,w),i) : ℝ) * amplitude M w.length n := by
    apply (norm_comp_linear (Construction.piece M w n) (Construction.piece_smooth M w n)
      (ContinuousLinearMap.snd ℝ ℝ Space) i z).trans
    have h₁ := hb M w i n z.2
    have h₂ := pow_le_pow_left₀ (norm_nonneg _) (ContinuousLinearMap.norm_snd_le ℝ ℝ Space) i
    simpa only [one_pow, mul_one, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd'] using mul_le_mul h₁ h₂ (pow_nonneg (norm_nonneg _) _)
      (mul_nonneg (Nat.cast_nonneg (B ((M,w),i))) (Bounds.amplitude_nonneg M w.length n))
  apply (norm_iteratedFDeriv_smul_le
    (Profiles.pulse_smooth.comp (contDiff_fst.sub contDiff_const))
    ((Construction.piece_smooth M w n).comp contDiff_snd) z (WithTop.coe_le_coe.mpr le_top)).trans
  calc
    _ ≤ ∑ i ∈ Finset.range (r + 1), (r.choose i : ℝ) * (A ((),i) : ℝ) * ((B ((M,w),r-i) : ℝ) * amplitude M w.length n) := by
      apply Finset.sum_le_sum
      intro i _
      apply mul_le_mul _ (hw (r - i)) (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg (A ((),i))))
      exact mul_le_mul_of_nonneg_left (hp i) (Nat.cast_nonneg _)
    _ = (C ((M,w),r) : ℝ) * amplitude M w.length n := by
      simp only [C, Nat.cast_sum, Nat.cast_mul, Finset.sum_mul, mul_assoc]

lemma epsilon_small (M : Machine) (N n : ℕ) : Scales.ε M.base N n ≤ (1/8:ℝ)^n := by
  have hb : (2 : ℝ) ≤ M.base := by exact_mod_cast (le_trans (by decide : 2 ≤ 4) M.base_ge_four)
  have hs : 3*n ≤ Scales.s N n := by have := Scales.s_lower N n; nlinarith
  unfold Scales.ε
  have hp : (8:ℝ)^n ≤ (M.base:ℝ)^Scales.s N n := by
    calc
      _ = (2:ℝ)^(3*n) := by rw [pow_mul]; norm_num
      _ ≤ (2:ℝ)^Scales.s N n := pow_le_pow_right₀ (by norm_num) hs
      _ ≤ _ := pow_le_pow_left₀ (by norm_num) hb _
  simpa only [one_div, inv_pow] using inv_anti₀ (by positivity : (0:ℝ) < 8^n) hp

lemma weighted_epsilon (M : Machine) (N J n : ℕ) :
    (1+(n:ℝ))^J * Scales.ε M.base N n ≤ 4 * J.factorial * (1/2:ℝ)^n := by
  have hpoly : (1+(n:ℝ))^J ≤ (J.factorial:ℝ) * (4 * 4^n) := by
    have h := (div_le_iff₀ (by positivity : (0:ℝ) < J.factorial)).mp
      (Real.pow_div_factorial_le_exp (1+(n:ℝ)) (by positivity) J)
    have he : Real.exp (1+(n:ℝ)) ≤ 4 * 4^n := by
      rw [Real.exp_add, show (n:ℝ) = n*1 by ring, Real.exp_nat_mul]
      exact mul_le_mul (Real.exp_one_lt_three.le.trans (by norm_num))
        (pow_le_pow_left₀ (Real.exp_pos _).le (Real.exp_one_lt_three.le.trans (by norm_num)) n)
        (by positivity) (by norm_num)
    exact h.trans (by nlinarith [mul_le_mul_of_nonneg_right he (Nat.cast_nonneg J.factorial : (0:ℝ) ≤ _)])
  calc
    _ ≤ ((J.factorial:ℝ) * (4 * 4^n)) * (1/8:ℝ)^n :=
      mul_le_mul hpoly (epsilon_small M N n) (Scales.ε_nonneg _ _ _ (by have := M.base_ge_four; omega)) (by positivity)
    _ = _ := by rw [mul_assoc _ (4*4^n), mul_assoc 4, ← mul_pow]; norm_num; ring

lemma weighted_amplitude_sum (M : Machine) (N J : ℕ) :
    (∑' n : ℕ, (1+(n:ℝ))^J * amplitude M N n) ≤ (1 + 8 * 2^J * J.factorial : ℕ) := by
  have hs := Bounds.weighted_amplitude_summable M N J
  rw [hs.tsum_eq_zero_add]
  simp only [amplitude, Nat.cast_zero, add_zero, one_pow, mul_one]
  have hc : ∀ n : ℕ, (1+(n+1:ℕ))^J * amplitude M N (n+1) ≤
      (2:ℝ)^J * (4 * J.factorial * (1/2:ℝ)^n) := by
    intro n
    simp only [amplitude, Nat.cast_add, Nat.cast_one]
    calc
      _ ≤ (2*(1+(n:ℝ)))^J * Scales.ε M.base N n := mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (by positivity) (by nlinarith) J)
        (Scales.ε_nonneg _ _ _ (by have := M.base_ge_four; omega))
      _ ≤ _ := by rw [mul_pow, mul_assoc]; exact mul_le_mul_of_nonneg_left (weighted_epsilon M N J n) (by positivity)
  have h := (hs.comp_injective Nat.succ_injective).tsum_le_tsum hc
    ((summable_geometric_two.mul_left (4*(J.factorial:ℝ))).mul_left ((2:ℝ)^J))
  simp only [tsum_mul_left, tsum_geometric_two, amplitude, Nat.cast_add, Nat.cast_one] at h
  push_cast
  nlinarith

end AlternatingNS.Effective

end DecayBoundsDevelopment

end OAI

-- ===== Adapted from lean/OAI/MathematicalPhysics/AlternatingFlow/CertifiedBounds.lean =====
namespace OAI

section CertifiedBoundsDevelopment

open scoped BigOperators Topology ContDiff
open Filter
namespace AlternatingNS.Effective

variable {A E F : Type*} [Primcodable A]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

noncomputable def weight (z : ℝ × Space) : ℝ := 1 + |z.1| + ‖z.2‖

lemma weight_pos (z : ℝ × Space) : 0 < weight z := by unfold weight; positivity

def Certified (f : A → ℝ × Space → F) : Prop :=
  (∀ a, ContDiff ℝ ∞ (f a)) ∧ ∃ B : A × ℕ × ℕ → ℕ, Computable B ∧
    ∀ a J r z, weight z ^ J * ‖iteratedFDeriv ℝ r (f a) z‖ ≤ B (a,J,r)

lemma velocity_certified : Certified (fun z : Machine × List ℕ => Function.uncurry (Construction.velocity z.1 z.2)) := by
  obtain ⟨C,hC,hc⟩ := pulsePiece_decay
  let B := fun z : (Machine × List ℕ) × ℕ × ℕ =>
    11^z.2.1 * C (z.1,z.2.2) * (1 + 8 * 2^z.2.1 * z.2.1.factorial)
  have cb : Computable B := by
    have hJ : Computable (fun z : (Machine × List ℕ) × ℕ × ℕ => z.2.1) := Computable.fst.comp Computable.snd
    exact Primrec.nat_mul.to_comp.comp
      (Primrec.nat_mul.to_comp.comp (nat_pow.to_comp.comp (Computable.const 11) hJ)
        (hC.comp (Computable.fst.pair (Computable.snd.comp Computable.snd))))
      (Primrec.nat_add.to_comp.comp (Computable.const 1)
        (Primrec.nat_mul.to_comp.comp
          (Primrec.nat_mul.to_comp.comp (Computable.const 8) (nat_pow.to_comp.comp (Computable.const 2) hJ))
          (factorial.to_comp.comp hJ)))
  refine ⟨fun z => Construction.velocity_smooth z.1 z.2, B, cb, ?_⟩
  rintro ⟨M,w⟩ J r z
  have hc' (n : ℕ) : weight z ^ J * ‖iteratedFDeriv ℝ r (Bounds.pulsePiece M w n) z‖ ≤
      11^J * (C ((M,w),r) : ℝ) * ((1+(n:ℝ))^J * Bounds.amplitude M w.length n) := by
    by_cases hz : z ∈ tsupport (iteratedFDeriv ℝ r (Bounds.pulsePiece M w n))
    · have hsupport := Bounds.pulsePiece_support M w n (tsupport_iteratedFDeriv_subset r hz)
      have ht : 0 ≤ z.1 := (Nat.cast_nonneg n).trans hsupport.1.1
      have hw : weight z ^ J ≤ (11 * (1+(n:ℝ)))^J := by
        apply pow_le_pow_left₀ (weight_pos z).le
        dsimp [weight]; rw [abs_of_nonneg ht]
        linarith [hsupport.1.2, Bounds.box_norm z.2 hsupport.2, Nat.cast_nonneg (α := ℝ) n]
      calc
        _ ≤ (11*(1+(n:ℝ)))^J * ((C ((M,w),r) : ℝ) * Bounds.amplitude M w.length n) :=
          mul_le_mul hw (hc M w r n z) (norm_nonneg _) (by positivity)
        _ = _ := by rw [mul_pow]; ring
    · rw [image_eq_zero_of_notMem_tsupport hz, norm_zero, mul_zero]
      exact mul_nonneg (by positivity) (mul_nonneg (by positivity) (Bounds.amplitude_nonneg M w.length n))
  obtain ⟨N,hN⟩ := TimeGlue.locally_eq_sum Profiles.pulse Profiles.pulse_zero_left (Construction.piece M w) z
  change Function.uncurry (Construction.velocity M w) =ᶠ[𝓝 z]
    (fun z => ∑ n ∈ Finset.range N, Bounds.pulsePiece M w n z) at hN
  rw [(hN.iteratedFDeriv ℝ r).eq_of_nhds,
    iteratedFDeriv_fun_sum_apply (fun n _ => (Bounds.pulsePiece_smooth M w n).of_le
      (WithTop.coe_le_coe.mpr le_top) |>.contDiffAt)]
  have ha := Bounds.weighted_amplitude_summable M w.length J
  calc
    _ ≤ weight z ^ J * ∑ n ∈ Finset.range N, ‖iteratedFDeriv ℝ r (Bounds.pulsePiece M w n) z‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (pow_nonneg (weight_pos z).le J)
    _ ≤ ∑ n ∈ Finset.range N, 11^J * (C ((M,w),r):ℝ) * ((1+(n:ℝ))^J * Bounds.amplitude M w.length n) := by
      rw [Finset.mul_sum]; exact Finset.sum_le_sum (fun n _ => hc' n)
    _ ≤ (11^J * (C ((M,w),r):ℝ)) * ∑' n : ℕ, (1+(n:ℝ))^J * Bounds.amplitude M w.length n := by
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (ha.sum_le_tsum _ (fun n _ => mul_nonneg (by positivity) (Bounds.amplitude_nonneg M w.length n))) (by positivity)
    _ ≤ B ((M,w),J,r) := by
      have h := mul_le_mul_of_nonneg_left (weighted_amplitude_sum M w.length J)
        (show (0:ℝ) ≤ 11^J * C ((M,w),r) by positivity)
      simpa only [B, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using h

lemma Certified.congr {f g : A → ℝ × Space → F} (hf : Certified f) (h : ∀ a z, f a z = g a z) : Certified g := by
  rwa [← funext (fun a => funext (h a))]

lemma Certified.param {B : Type*} [Primcodable B] {f : A → ℝ × Space → F}
    (hf : Certified f) (g : B → A) (hg : Computable g) : Certified (fun b => f (g b)) := by
  obtain ⟨hs,C,hC,h⟩ := hf
  exact ⟨fun b => hs (g b), fun z => C (g z.1,z.2), hC.comp ((hg.comp Computable.fst).pair Computable.snd), fun b => h (g b)⟩

lemma Certified.add {f g : A → ℝ × Space → F} (hf : Certified f) (hg : Certified g) :
    Certified (fun a z => f a z + g a z) := by
  obtain ⟨sf,B,hB,hf⟩ := hf
  obtain ⟨sg,C,hC,hg⟩ := hg
  refine ⟨fun a => (sf a).add (sg a), fun z => B z + C z,
    Primrec.nat_add.to_comp.comp hB hC, fun a J r z => ?_⟩
  rw [fun_iteratedFDeriv_add_apply ((sf a).of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt
    ((sg a).of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt, Nat.cast_add]
  calc
    _ ≤ weight z ^ J * (‖iteratedFDeriv ℝ r (f a) z‖ + ‖iteratedFDeriv ℝ r (g a) z‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le _ _) (pow_nonneg (weight_pos z).le _)
    _ ≤ _ := by rw [mul_add]; exact add_le_add (hf a J r z) (hg a J r z)

lemma Certified.linear {f : A → ℝ × Space → F} (hf : Certified f)
    (L : A → F →L[ℝ] E) (D : A → ℕ) (hD : Computable D) (hL : ∀ a, ‖L a‖ ≤ D a) :
    Certified (fun a => L a ∘ f a) := by
  obtain ⟨hs,B,hB,hf⟩ := hf
  refine ⟨fun a => (L a).contDiff.comp (hs a), fun z => D z.1 * B z,
    Primrec.nat_mul.to_comp.comp (hD.comp Computable.fst) hB, fun a J r z => ?_⟩
  calc
    _ ≤ weight z ^ J * ((D a : ℝ) * ‖iteratedFDeriv ℝ r (f a) z‖) :=
      mul_le_mul_of_nonneg_left ((Bounds.norm_postcomp_linear (f a) (hs a) (L a) r z).trans
        (mul_le_mul_of_nonneg_right (hL a) (norm_nonneg _))) (pow_nonneg (weight_pos z).le _)
    _ ≤ _ := by rw [mul_left_comm, Nat.cast_mul]; exact mul_le_mul_of_nonneg_left (hf a J r z) (Nat.cast_nonneg _)

lemma Certified.csmul {f : A → ℝ × Space → F} (hf : Certified f) (c : ℝ) (D : ℕ) (hc : |c| ≤ D) :
    Certified (fun a z => c • f a z) := by
  apply hf.linear (fun _ => c • ContinuousLinearMap.id ℝ F) (fun _ => D) (Computable.const D)
  intro _
  simpa only [norm_smul, Real.norm_eq_abs, mul_one] using
    (mul_le_mul_of_nonneg_left (ContinuousLinearMap.norm_id_le (𝕜 := ℝ) (E := F)) (abs_nonneg c)).trans (by simpa using hc)

lemma Certified.sub {f g : A → ℝ × Space → F} (hf : Certified f) (hg : Certified g) :
    Certified (fun a z => f a z - g a z) := by
  exact (hf.add (hg.csmul (-1) 1 (by norm_num))).congr (by intros; simp [sub_eq_add_neg])

lemma Certified.directional {f : A → ℝ × Space → F} (hf : Certified f)
    (v : A → ℝ × Space) (hv : ∀ a, ‖v a‖ ≤ 1) :
    Certified (fun a z => fderiv ℝ (f a) z (v a)) := by
  obtain ⟨sf,B,hB,hf⟩ := hf
  refine ⟨fun a => ((sf a).fderiv_right (by simp)).clm_apply contDiff_const,
    fun z => B (z.1,z.2.1,z.2.2+1), hB.comp (Computable.fst.pair
      ((Computable.fst.comp Computable.snd).pair (Computable.succ.comp (Computable.snd.comp Computable.snd)))), fun a J r z => ?_⟩
  apply le_trans _ (hf a J (r+1) z)
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg (weight_pos z).le _)
  exact (Bounds.norm_directional_iterated (f a) (sf a) (v a) r z).trans
    (mul_le_of_le_one_left (norm_nonneg _) (hv a))

lemma Certified.smul {f : A → ℝ × Space → ℝ} {g : A → ℝ × Space → F}
    (hf : Certified f) (hg : Certified g) : Certified (fun a z => f a z • g a z) := by
  obtain ⟨sf,B,hB,hf⟩ := hf
  obtain ⟨sg,C,hC,hg⟩ := hg
  let D := fun z : A × ℕ × ℕ => ∑ i ∈ Finset.range (z.2.2+1), z.2.2.choose i * B (z.1,z.2.1,i) * C (z.1,0,z.2.2-i)
  have hi : Computable₂ (fun z : A × ℕ × ℕ => fun i : ℕ => z.2.2.choose i * B (z.1,z.2.1,i) * C (z.1,0,z.2.2-i)) := by
    have ha : Computable (fun z : (A × ℕ × ℕ) × ℕ => z.1.1) := Computable.fst.comp Computable.fst
    have hJ : Computable (fun z : (A × ℕ × ℕ) × ℕ => z.1.2.1) := Computable.fst.comp (Computable.snd.comp Computable.fst)
    have hr : Computable (fun z : (A × ℕ × ℕ) × ℕ => z.1.2.2) := Computable.snd.comp (Computable.snd.comp Computable.fst)
    exact Primrec.nat_mul.to_comp.comp (Primrec.nat_mul.to_comp.comp
      (choose.to_comp.comp hr Computable.snd) (hB.comp (ha.pair (hJ.pair Computable.snd))))
      (hC.comp (ha.pair ((Computable.const 0).pair (Primrec.nat_sub.to_comp.comp hr Computable.snd))))
  refine ⟨fun a => (sf a).fun_smul (sg a), D,
    (nat_sum_range hi).comp Computable.id (Computable.succ.comp (Computable.snd.comp Computable.snd)), fun a J r z => ?_⟩
  apply (mul_le_mul_of_nonneg_left (norm_iteratedFDeriv_smul_le (sf a) (sg a) z
    (WithTop.coe_le_coe.mpr le_top)) (pow_nonneg (weight_pos z).le J)).trans
  simp only [D, Nat.cast_sum, Nat.cast_mul, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  calc
    _ = (r.choose i : ℝ) * (weight z^J * ‖iteratedFDeriv ℝ i (f a) z‖) * ‖iteratedFDeriv ℝ (r-i) (g a) z‖ := by ring
    _ ≤ _ := mul_le_mul (mul_le_mul_of_nonneg_left (hf a J i z) (Nat.cast_nonneg _))
      (by simpa using hg a 0 (r-i) z) (norm_nonneg _) (by positivity)

end AlternatingNS.Effective

end CertifiedBoundsDevelopment

end OAI


