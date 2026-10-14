-- Prove2me | Definitions.Def_OAI_AlternatingFlow_Part08
-- name    : OAI_AlternatingFlow_Part08
-- status  : Definition
-- author  : @SamenHossain
-- created : 2026-10-12T03:41:19.065791+00:00
-- url     : https://prove2.me/theorems/8186d7d7-5e02-4c60-99b0-d4f86381f617
-- title:
--   Alternating-flow construction, part 8 of 11 (port of OpenAI's formalization): local names and base names
-- statement:
--   Part 8 of 11 of a port of OpenAI's Lean formalization of the alternating-flow construction from the manuscript *Computation under Rapidly Vanishing Navier–Stokes Forcing* (OpenAI, September 27, 2026). This part contains local names and base names.
--
--   **Attribution.** The code is adapted verbatim from the OpenAI "math" repository, commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`, modules `LocalNames`, `BaseNames` of `lean/OAI/MathematicalPhysics/AlternatingFlow`. It is © OpenAI and licensed under the Apache License 2.0; the adapted code is redistributed under the same license.
--
--   **Modifications.** Modules are concatenated in dependency order with their imports replaced by the previous part. The model definitions come from the platform definition `NavierStokesAlternating`. Part 1 adds compatibility shims for three core lemmas renamed after Lean 4.33.1, and part 3 adjusts one side-goal tactic for Mathlib 0df444a.
--
--   The development is split into eleven parts only so that each compiles within the platform's time limit. Together the parts supply the velocity construction used to prove `OAI.AlternatingNS.velocity_construction`.
-- source:
--   OpenAI, openai/math, commit adc7f1241b42e322a6451854ab7e4b4c146bf78a, lean/OAI/MathematicalPhysics/AlternatingFlow: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/AlternatingFlow/LocalNames.lean, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/AlternatingFlow/BaseNames.lean (Apache License 2.0); manuscript https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Computation-under-Rapidly-Vanishing-Navier-Stokes-Forcing-September-27-2026/manuscript.pdf

/-
Alternating-flow construction (port of OpenAI's formalization), part 8 of 11: local names and base names.

Adapted from the OpenAI "math" repository (https://github.com/openai/math, commit
adc7f1241b42e322a6451854ab7e4b4c146bf78a), lean/OAI/MathematicalPhysics/AlternatingFlow/: LocalNames.lean, BaseNames.lean
These files formalize the manuscript "Computation under Rapidly Vanishing Navier-Stokes Forcing"
(OpenAI, September 27, 2026). Copyright OpenAI. Licensed under the Apache License, Version 2.0
(http://www.apache.org/licenses/LICENSE-2.0); the adapted code is distributed under the same license,
on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND.

Modifications: modules concatenated in dependency order with their import lines removed; the model
definitions come from the platform definition `NavierStokesAlternating`.
-/
import Mathlib
import Definitions.Def_OAI_AlternatingFlow_Part07

set_option autoImplicit false

-- ===== Adapted from lean/OAI/MathematicalPhysics/AlternatingFlow/LocalNames.lean =====
namespace OAI

section LocalNamesDevelopment

open scoped BigOperators Topology ContDiff
namespace AlternatingNS.Effective
attribute [local instance] Arithmetic.rationalCoding

variable {A : Type*} [Primcodable A]

lemma Named.nat (f : A → ℕ) (hf : Computable f) : Named (fun a => (f a : ℝ)) :=
  (Named.rational (Arithmetic.rat_natCast.to_comp.comp hf)).congr (fun _ => Rat.cast_natCast _)

lemma Named.natPow (b n : A → ℕ) (hb : Computable b) (hn : Computable n) :
    Named (fun a => (b a : ℝ) ^ n a) :=
  (Named.rational (Arithmetic.rat_pow.to_comp.comp
    (Arithmetic.rat_natCast.to_comp.comp hb) hn)).congr (by intro a; simp)

lemma Named.invNatPow (b n : A → ℕ) (hb : Computable b) (hn : Computable n) :
    Named (fun a => ((b a : ℝ) ^ n a)⁻¹) :=
  (Named.rational (Arithmetic.rat_inv.to_comp.comp (Arithmetic.rat_pow.to_comp.comp
    (Arithmetic.rat_natCast.to_comp.comp hb) hn))).congr (by intro a; simp)

lemma Named.divNat {f : A → ℝ} (hf : Named f) (b : A → ℕ) (hb : Computable b) :
    Named (fun a => f a / b a) :=
  (hf.mul (Named.invNatPow b (fun _ => 1) hb (Computable.const 1))).congr
    (by intro a; simp [div_eq_mul_inv])

lemma Named.selector {f : A → ℝ} (hf : Named f) (b a : A → ℕ)
    (hb : Computable b) (ha : Computable a) :
    Named (fun z => Profiles.selector (b z) (a z) (f z)) := by
  have h1 := (((Named.const 8).mul (((Named.nat b hb).mul hf).sub
    ((Named.const 2).mul (Named.nat a ha)))).add (Named.const 2)).transition
  have h2 := (((Named.const 8).mul ((((Named.const 2).mul (Named.nat a ha)).add
    (Named.const 1)).sub ((Named.nat b hb).mul hf))).add (Named.const 2)).transition
  exact (h1.mul h2).congr (by intro; simp only [Profiles.selector, Rat.cast_ofNat, Rat.cast_one])

lemma read_named (M : A → Machine) (N n : A → ℕ) (D : A → ℝ)
    (hM : Computable M) (hN : Computable N) (hn : Computable n) (hD : Named D) :
    Named (fun z => LocalRule.readC (M z) (N z) (n z) (D z)) ∧
    Named (fun z => LocalRule.readB (M z) (N z) (n z) (D z)) ∧
    Named (fun z => LocalRule.readA (M z) (N z) (n z) (D z)) := by
  have hb := base.to_comp.comp hM
  have hs := exponent.to_comp.comp hN hn
  have hK := capacity.to_comp.comp hN hn
  have hbase (z : A) : 2 ≤ (M z).base := by have := (M z).base_ge_four; omega
  have hC := ((Named.natPow (fun z => (M z).base) _ hb hs).mul hD).decoder
    (fun z => (M z).base) hb hbase
  have hB := ((Named.natPow (fun z => (M z).base) _ hb
    (Primrec.nat_add.to_comp.comp (Computable.succ.comp hs) hK)).mul hD).decoder
    (fun z => (M z).base) hb hbase
  have hA := ((Named.natPow (fun z => (M z).base) _ hb (Computable.succ.comp hs)).mul hD).decoder
    (fun z => (M z).base) hb hbase
  exact ⟨hC,hB,hA.sub ((Named.invNatPow (fun z => (M z).base) _ hb hK).mul hB)⟩

lemma numerator_named (b K a l : A → ℕ) (r : A → Rule) (u v : A → ℝ)
    (hb : Computable b) (hK : Computable K) (ha : Computable a) (hl : Computable l)
    (hr : Computable r) (hu : Named u) (hv : Named v) :
    Named (fun z => LocalRule.branchNumerator (b z) (K z) (a z) (l z) (r z) (u z) (v z)) := by
  have h2a := Named.nat (fun z => 2 * a z) (Primrec.nat_mul.to_comp.comp (Computable.const 2) ha)
  have h2l := Named.nat (fun z => 2 * l z) (Primrec.nat_mul.to_comp.comp (Computable.const 2) hl)
  have h2w := Named.nat (fun z => 2 * (r z).2.1)
    (Primrec.nat_mul.to_comp.comp (Computable.const 2) (Computable.fst.comp (Computable.snd.comp hr)))
  have h2q := Named.nat (fun z => 2 * (r z).1)
    (Primrec.nat_mul.to_comp.comp (Computable.const 2) (Computable.fst.comp hr))
  have hi (i : Fin 3) : Computable (fun z => decide ((r z).2.2 = i)) :=
    Primrec.eq.decide.to_comp.comp (Computable.snd.comp (Computable.snd.comp hr)) (Computable.const i)
  have hL := Named.ite (fun z => (r z).2.2 = 0) (hi 0)
    (((Named.nat b hb).mul hu).sub h2l)
    (Named.ite (fun z => (r z).2.2 = 1) (hi 1) hu ((h2w.add hu).divNat b hb))
  have hR := ((Named.nat b hb).mul hv).sub h2a
  have hR' := Named.ite (fun z => (r z).2.2 = 0) (hi 0)
    ((h2l.add ((h2w.add hR).divNat b hb)).divNat b hb)
    (Named.ite (fun z => (r z).2.2 = 1) (hi 1) ((h2w.add hR).divNat b hb) hR)
  exact ((h2q.add hL).add ((Named.invNatPow b K hb hK).mul hR')).congr (by
    intro z; dsimp [LocalRule.branchNumerator, LocalRule.updateLeft, LocalRule.updateRight]
    push_cast; split_ifs <;> rfl)

lemma branch_named (M : A → Machine) (N n q a : A → ℕ) (u v : A → ℝ)
    (hM : Computable M) (hN : Computable N) (hn : Computable n) (hq : Computable q)
    (ha : Computable a) (hu : Named u) (hv : Named v) :
    Named (fun z => LocalRule.branch (M z) (N z) (n z) (q z) (a z) (u z) (v z)) := by
  let r := fun z => (M z).command (q z) (a z)
  have hr : Computable r := command.to_comp.comp (hM.pair (hq.pair ha))
  have hb := base.to_comp.comp hM
  have hK := capacity.to_comp.comp hN (Computable.succ.comp hn)
  have hsel := (hu.comp (g := (Prod.fst : A × ℕ → A)) Computable.fst).selector
    (fun z => (M z.1).base) Prod.snd (hb.comp Computable.fst) Computable.snd
  have hnum := numerator_named (fun z : A × ℕ => (M z.1).base)
    (fun z => Scales.K (N z.1) (n z.1+1)) (fun z => a z.1) Prod.snd (fun z => r z.1)
    (fun z => u z.1) (fun z => v z.1) (hb.comp Computable.fst) (hK.comp Computable.fst)
    (ha.comp Computable.fst) Computable.snd (hr.comp Computable.fst)
    (hu.comp Computable.fst) (hv.comp Computable.fst)
  have hsum := (hsel.mul hnum).sum_range (fun z => (M z).alphabet) (alphabet.to_comp.comp hM)
  have hother := numerator_named (fun z => (M z).base) (fun z => Scales.K (N z) (n z+1))
    a (fun _ => 0) r u v hb hK ha (Computable.const 0) hr hu hv
  have hi : Computable (fun z => decide ((r z).2.2 = 0)) :=
    Primrec.eq.decide.to_comp.comp (Computable.snd.comp (Computable.snd.comp hr)) (Computable.const (0 : Fin 3))
  exact (Named.ite (fun z => (r z).2.2 = 0) hi hsum hother).congr (by intro z; rfl)

lemma writeCore_named (M : A → Machine) (N n : A → ℕ) (D : A → ℝ)
    (hM : Computable M) (hN : Computable N) (hn : Computable n) (hD : Named D) :
    Named (fun z => Bounds.writeCore (M z) (N z) (n z) (D z)) := by
  let P := (A × ℕ) × ℕ
  let M' := fun z : P => M z.1.1
  let N' := fun z : P => N z.1.1
  let n' := fun z : P => n z.1.1
  let D' := fun z : P => D z.1.1
  have hp : Computable (fun z : P => z.1.1) := Computable.fst.comp Computable.fst
  have hm : Computable M' := hM.comp hp
  have hnn : Computable n' := hn.comp hp
  have hnd : Computable N' := hN.comp hp
  obtain ⟨hC,hB,hA⟩ := read_named M' N' n' D' hm hnd hnn (hD.comp hp)
  have hb := base.to_comp.comp hm
  have hQ : Computable (fun z : P => z.1.2) := Computable.snd.comp Computable.fst
  have hterm := ((hC.selector (fun z => (M' z).base) (fun z => z.1.2) hb hQ).mul
    (hB.selector (fun z => (M' z).base) Prod.snd hb Computable.snd)).mul
    (branch_named M' N' n' (fun z => z.1.2) Prod.snd _ _ hm hnd hnn hQ Computable.snd hA hB)
  have hsum := (hterm.sum_range (fun z : A × ℕ => (M z.1).alphabet)
    (alphabet.to_comp.comp (hM.comp Computable.fst))).sum_range
      (fun z => (M z).states+1) (Computable.succ.comp (states.to_comp.comp hM))
  exact (hsum.divNat (fun z => (M z).base) (base.to_comp.comp hM)).congr (by
    intro z; dsimp [P,M',N',n',D',Bounds.writeCore]; ring)

lemma haltWeight_named (M : A → Machine) (N n : A → ℕ) (D : A → ℝ)
    (hM : Computable M) (hN : Computable N) (hn : Computable n) (hD : Named D) :
    Named (fun z => LocalRule.haltWeight (M z) (N z) (n z) (D z)) := by
  have hC := (read_named M N n D hM hN hn hD).1
  have hsel := (hC.comp (g := (Prod.fst : A × ℕ → A)) Computable.fst).selector
    (fun z => (M z.1).base) Prod.snd (base.to_comp.comp (hM.comp Computable.fst)) Computable.snd
  have hp : Computable (fun z : A × ℕ =>
      decide (z.2 = (M z.1).states ∨ z.2 ∈ (M z.1).haltingStates)) :=
    (Computable.cond
      (Primrec.eq.decide.to_comp.comp Computable.snd (states.to_comp.comp (hM.comp Computable.fst)))
      (Computable.const true)
      (member.decide.to_comp.comp (haltingStates.to_comp.comp (hM.comp Computable.fst)) Computable.snd)).of_eq
        (by intro z; simp)
  exact ((Named.ite _ hp hsel (Named.const 0)).sum_range
    (fun z => (M z).states+1) (Computable.succ.comp (states.to_comp.comp hM))).congr
    (by intro z; simp only [LocalRule.haltWeight, Function.comp_apply, Rat.cast_zero])

lemma write_named (M : A → Machine) (N n : A → ℕ) (D : A → ℝ)
    (hM : Computable M) (hN : Computable N) (hn : Computable n) (hD : Named D) :
    Named (fun z => LocalRule.write (M z) (N z) (n z) (D z)) := by
  have he := epsilon_named.comp ((hM.pair hN).pair (Computable.succ.comp hn))
  exact (he.mul (writeCore_named M N n D hM hN hn hD)).congr
    (fun z => (Bounds.write_factor _ _ _ _).symm)

lemma signal_named (M : A → Machine) (N n : A → ℕ) (D : A → ℝ)
    (hM : Computable M) (hN : Computable N) (hn : Computable n) (hD : Named D) :
    Named (fun z => LocalRule.signal (M z) (N z) (n z) (D z)) := by
  have he := epsilon_named.comp ((hM.pair hN).pair hn)
  have he' := epsilon_named.comp ((hM.pair hN).pair (Computable.succ.comp hn))
  exact ((he.sub he').add (((Named.const 2).mul he').mul
    (haltWeight_named M N n D hM hN hn hD))).congr (by intro z; simp [LocalRule.signal])

end AlternatingNS.Effective

end LocalNamesDevelopment

end OAI


-- ===== Adapted from lean/OAI/MathematicalPhysics/AlternatingFlow/BaseNames.lean =====
namespace OAI

section BaseNamesDevelopment

open scoped BigOperators Topology ContDiff
namespace AlternatingNS.Effective
attribute [local instance] Arithmetic.rationalCoding

variable {A : Type*} [Primcodable A]

def ratCoord (q : RationalVector) (i : Fin 3) : ℚ := ![q.1,q.2.1,q.2.2] i

lemma ratCoord_computable : Computable (fun z : RationalVector × Fin 3 => ratCoord z.1 z.2) := by
  have hi (i : Fin 3) : Computable (fun z : RationalVector × Fin 3 => decide (z.2 = i)) :=
    Primrec.eq.decide.to_comp.comp Computable.snd (Computable.const i)
  exact (Computable.cond (hi 0) (Computable.fst.comp Computable.fst)
    (Computable.cond (hi 1) (Computable.fst.comp (Computable.snd.comp Computable.fst))
      (Computable.snd.comp (Computable.snd.comp Computable.fst)))).of_eq
        (by rintro ⟨q,i⟩; fin_cases i <;> rfl)

lemma ratCoord_cast (q : RationalVector) (i : Fin 3) :
    (ratCoord q i : ℝ) = rationalVector q i := by
  fin_cases i <;> rfl

lemma coord_named (q : A → RationalPoint) (i : A → Fin 3)
    (hq : Computable q) (hi : Computable i) :
    Named (fun a => (rationalPoint (q a)).2 (i a)) :=
  (Named.rational (ratCoord_computable.comp ((Computable.snd.comp hq).pair hi))).congr
    (fun a => ratCoord_cast (q a).2 (i a))

lemma cutoff_named (q : A → RationalPoint) (hq : Computable q) :
    Named (fun a => Spatial.cutoff (rationalPoint (q a)).2) := by
  have h (i : Fin 3) := coord_named q (fun _ => i) hq (Computable.const i)
  have ht (i : Fin 3) := (((Named.const 3).sub (h i)).transition).mul
    (((Named.const 3).add (h i)).transition)
  exact (((ht 0).mul (ht 1)).mul (ht 2)).congr (by
    intro a; simp [Spatial.cutoff, Fin.prod_univ_succ]; ring)

lemma direction_succ (i : Fin 3) : direction i.succ = (0,e i) := by
  fin_cases i <;> rfl

lemma JetBound.spatial_d_named {f : A → Space → ℝ} (hf : JetBound f)
    (hn : Named (fun z : A × RationalPoint => f z.1 (rationalPoint z.2).2))
    (i : A → Fin 3) (hi : Computable i) :
    Named (fun z : A × RationalPoint => Spatial.d (i z.1) (f z.1) (rationalPoint z.2).2) := by
  have hf' := hf.comp_unit (fun _ => ContinuousLinearMap.snd ℝ ℝ Space) (fun _ => norm_snd)
  have hd := hf'.named_directional hn (fun a => (i a).succ) (Primrec.fin_succ.to_comp.comp hi)
  apply hd.congr
  intro z
  rw [direction_succ]
  dsimp [Spatial.d, Function.comp_def]
  rw [fderiv_fun_comp _ ((hf.1 z.1).differentiable (by simp) _) (differentiableAt_snd)]
  simp [fderiv_snd]

noncomputable def slotPotential (p : (Machine × ℕ) × ℕ) (x : Space) : ℝ :=
  Spatial.cutoff x * Spatial.shearPotential (Construction.donorIndex p.2)
    (Construction.receiverIndex p.2) 0 (LocalRule.write p.1.1 p.1.2 p.2)
      (LocalRule.signal p.1.1 p.1.2 p.2) x

noncomputable def loadPotential (p : Machine × List ℕ) (x : Space) : ℝ :=
  Spatial.cutoff x * Spatial.shearPotential 2 1 0
    (fun _ => Scales.ε p.1.base p.2.length 0 * p.1.recordedBlock p.2 0)
    (fun _ => 1 - Scales.ε p.1.base p.2.length 0) x

lemma loadPotential_bound : JetBound loadPotential := by
  obtain ⟨hs,B,hB,h⟩ := loadingPotential_scaled
  refine ⟨fun p => hs p 0, B, hB, fun p r x => ?_⟩
  change ‖iteratedFDeriv ℝ r (fun x : Space => Spatial.cutoff x *
    Spatial.shearPotential 2 1 0 (fun _ => Scales.ε p.1.base p.2.length 0 * p.1.recordedBlock p.2 0)
      (fun _ => 1 - Scales.ε p.1.base p.2.length 0) x) x‖ ≤ _
  simpa only [one_pow, mul_one] using h p r 0 x

lemma slotPotential_bound : JetBound slotPotential := by
  obtain ⟨C,hC,hc⟩ := potential_bound
  let S : (Machine × ℕ) × ℕ → ℕ := fun p => p.1.1.base ^
    (Scales.s p.1.2 p.2 + 1 + Scales.K p.1.2 p.2)
  have hS : Computable S := nat_pow.to_comp.comp
    (base.to_comp.comp (Computable.fst.comp Computable.fst))
    (Primrec.nat_add.to_comp.comp
      (Computable.succ.comp (exponent.to_comp.comp (Computable.snd.comp Computable.fst) Computable.snd))
      (capacity.to_comp.comp (Computable.snd.comp Computable.fst) Computable.snd))
  refine ⟨fun p => Spatial.cutoff_smooth.mul (Spatial.shearPotential_smooth _ _ _ _ _
    (LocalRule.write_smooth p.1.1 p.1.2 p.2) (LocalRule.signal_smooth p.1.1 p.1.2 p.2)),
    fun z => C (z.1.1,z.2) * (1 + S z.1 ^ z.2),
    Primrec.nat_mul.to_comp.comp
      (hC.comp ((Computable.fst.comp Computable.fst).pair Computable.snd))
      (Primrec.nat_add.to_comp.comp (Computable.const 1)
        (nat_pow.to_comp.comp (hS.comp Computable.fst) Computable.snd)), ?_⟩
  intro p r x
  have e₁ : Scales.ε p.1.1.base p.1.2 p.2 ≤ 1 :=
    (le_abs_self _).trans (Bounds.inverse_power_bound _ _)
  have e₂ : Scales.ε p.1.1.base p.1.2 (p.2+1) ≤ 1 :=
    (le_abs_self _).trans (Bounds.inverse_power_bound _ _)
  have hsc : Bounds.readScale p.1.1 p.1.2 p.2 = (S p : ℝ) := by
    simp [Bounds.readScale, S]
  apply (hc p.1.1 p.1.2 r p.2 x).trans
  push_cast
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  rw [hsc]
  exact add_le_add e₁ (mul_le_of_le_one_left (by positivity) e₂)

lemma donor_computable : Computable Construction.donorIndex := by
  exact (Computable.cond
    (Primrec.eq.decide.to_comp.comp (Primrec.nat_mod.to_comp.comp Computable.id (Computable.const 2)) (Computable.const 0))
    (Computable.const (1 : Fin 3)) (Computable.const 2)).of_eq (by intros; simp [Construction.donorIndex])

lemma receiver_computable : Computable Construction.receiverIndex := by
  exact (Computable.cond
    (Primrec.eq.decide.to_comp.comp (Primrec.nat_mod.to_comp.comp Computable.id (Computable.const 2)) (Computable.const 0))
    (Computable.const (2 : Fin 3)) (Computable.const 1)).of_eq (by intros; simp [Construction.receiverIndex])

lemma loadPotential_named :
    Named (fun z : (Machine × List ℕ) × RationalPoint => loadPotential z.1 (rationalPoint z.2).2) := by
  let P := (Machine × List ℕ) × RationalPoint
  have hM : Computable (fun z : P => z.1.1) := Computable.fst.comp Computable.fst
  have hw : Computable (fun z : P => z.1.2) := Computable.snd.comp Computable.fst
  have he := epsilon_named.comp ((hM.pair (Computable.list_length.comp hw)).pair (Computable.const 0))
  have hblock := (Named.rational (initialBlock_primrec.to_comp.comp hM hw)).congr
    (fun z : P => initialBlock_cast z.1.1 z.1.2)
  have hcoord (i : Fin 3) := coord_named (Prod.snd : P → RationalPoint) (fun _ => i)
    Computable.snd (Computable.const i)
  exact ((cutoff_named (Prod.snd : P → RationalPoint) Computable.snd).mul
    (((hcoord 0).mul (he.mul hblock)).sub ((hcoord 1).mul ((Named.const 1).sub he)))).congr
      (by intro z; simp only [loadPotential, Spatial.shearPotential, Rat.cast_one, Function.comp_def])

lemma slotPotential_named :
    Named (fun z : ((Machine × ℕ) × ℕ) × RationalPoint => slotPotential z.1 (rationalPoint z.2).2) := by
  let P := ((Machine × ℕ) × ℕ) × RationalPoint
  let M := fun z : P => z.1.1.1
  let N := fun z : P => z.1.1.2
  let n := fun z : P => z.1.2
  have hM : Computable M := Computable.fst.comp (Computable.fst.comp Computable.fst)
  have hN : Computable N := Computable.snd.comp (Computable.fst.comp Computable.fst)
  have hn : Computable n := Computable.snd.comp Computable.fst
  have hd := coord_named (Prod.snd : P → RationalPoint) (fun z => Construction.donorIndex (n z))
    Computable.snd (donor_computable.comp hn)
  have hi := coord_named (Prod.snd : P → RationalPoint) (fun z => Construction.receiverIndex (n z))
    Computable.snd (receiver_computable.comp hn)
  have h0 := coord_named (Prod.snd : P → RationalPoint) (fun _ => 0) Computable.snd (Computable.const 0)
  have hw := write_named M N n _ hM hN hn hd
  have hs := signal_named M N n _ hM hN hn hd
  exact ((cutoff_named (Prod.snd : P → RationalPoint) Computable.snd).mul
    ((h0.mul hw).sub (hi.mul hs))).congr (by intro z; rfl)

end AlternatingNS.Effective

end BaseNamesDevelopment

end OAI


