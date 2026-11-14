-- Prove2me | Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_OCountedIteration
-- name    : Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_OCountedIteration
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:47:59.309217+00:00
-- url     : https://prove2.me/theorems/4a64cf09-2e29-4e15-8f50-e52d511d304b
-- title:
--   Complexity.Computability.Machines.Turing.MultiTape.Internal.OCountedIteration — Direct charged iteration with a binary counter
-- statement:
--   This is module `Complexity.Computability.Machines.Turing.MultiTape.Internal.OCountedIteration` of [complexitylib](https://github.com/cslib-community/complexitylib), the complexity-theory library of the CSLib community (machine models, polynomial time, and the `polytime` tactic; Apache-2.0), at commit `0ebd467`. It is published here because the formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) states and proves its running-time bounds with it.
--
--   A normalized plain round machine is iterated by the exact machine-level loop combinator. The
--   same realizing machines retain independent time/workspace and complete encoded-output charges.
--   Only actual trajectory states up to and including the final round must satisfy the given bounds.
--   No unary representation of the runtime count is materialized.
--
--   **Contents.** The module is published as a whole: 2 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_OCountedIteration`.
-- source:
--   https://github.com/cslib-community/complexitylib/blob/0ebd4671c2e7278a91f5671c11109bb254ae413c/Complexity/Computability/Machines/Turing/MultiTape/Internal/OCountedIteration.lean

/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/
module
-- upstream: candidate

public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_BinaryPrimitives
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_BinaryCounter
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_BinarySizeFacts
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_DegreeOptionPrimitives
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Complexity_Degree_Bounds
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_KernelIterateWhile
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_KernelComp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/- Prove2me definition bundle for `Complexity.Computability.Machines.Turing.MultiTape.Internal.OCountedIteration` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-! # Direct charged iteration with a binary counter

A normalized plain round machine is iterated by the exact machine-level loop combinator. The
same realizing machines retain independent time/workspace and complete encoded-output charges.
Only actual trajectory states up to and including the final round must satisfy the given bounds.
No unary representation of the runtime count is materialized.
-/

@[expose] public section
namespace Turing.MultiTapeTM.ComputableInO

open Internal.BinaryCounter
open ComputableTidilyInO (length_encNat_mono)

variable {γ β : Type} [Inhabited β] {encIn : γ ↪ List Bool} {encB : β ↪ List Bool}

/-- A round of the counted iteration. -/
lemma countStep_inO {step : β → β} {Ts Ss : β → ℕ}
    (hstep : ComputableInO step encB encB Ts Ss) :
    ComputableInO (countStep step) (encOption (encPair encNat encB))
      (encOption (encPair encNat encB))
      (fun o => (encOption (encPair encNat encB) o).length +
        ((encNat (o.getD default).1).length + 1) ^ 2 + Ts (o.getD default).2)
      fun o => (encOption (encPair encNat encB) o).length + Ss (o.getD default).2 := by
  have hget := (ComputableInDegree.getD (enc₁ := encPair encNat encB)
    (enc := encOption (encPair encNat encB)) default).inO_one
  have hcond := (ComputableInDegree.of_finite (encIn := encPair encBool encBool)
    (encMid := encBool) fun q : Bool × Bool => q.1 && !q.2).inO_one.comp_linear
    ((ComputableInDegree.isSome (encPair encNat encB)).inO_one.prod
      (natIsZero.comp_linear hget.fst'))
  have hnext := (ComputableInDegree.optionSome (enc₁ := encPair encNat encB)
    (enc := encOption (encPair encNat encB))).inO_one.comp_linear
    ((natPred.comp hget.fst').prod (hstep.comp hget.snd'))
  refine ((hcond.ite hnext (const none)).mono 8 (fun o => ?_) fun o => ?_).of_enc_eq
    fun o => by rw [countStep_eq]; rfl
  all_goals
    have h₁ : (encNat (o.getD default).1).length + 1 ≤
        (encOption (encPair encNat encB) o).length + 1 := by
      rcases o with _ | ⟨i, b⟩
      · simp only [Option.getD_none, encOption_none]
        exact Nat.le_of_eq (congrArg (·.length + 1) Nat.zero_bits)
      · simp only [Option.getD_some, encOption_some, List.length_cons, length_encPair]; omega
    simp only [Function.comp_apply]
    split_ifs <;> omega

/-- **Iterating `n x` times, with `n x` in binary.** If the rounds are within the time `R x` and
the space `Q x`, and the iterates have length at most `B x`, the iteration takes the time of the
counter and of the start, plus `R x`, `B x` and the square of the length of the counter for every
round, and the space of the counter and of the start, plus `Q x`, `B x` and the length of the
counter. -/
public theorem iterate {n : γ → ℕ} {init : γ → β} {step : β → β}
    {Tn Ti Sn Si R Q B : γ → ℕ} {Ts Ss : β → ℕ}
    (hn : ComputableInO n encIn encNat Tn Sn)
    (hinit : ComputableInO init encIn encB Ti Si)
    (hstep : ComputableInO step encB encB Ts Ss)
    (hround : ∀ x, ∀ k ≤ n x, Ts (step^[k] (init x)) ≤ R x)
    (hspace : ∀ x, ∀ k ≤ n x, Ss (step^[k] (init x)) ≤ Q x)
    (hstate : ∀ x, ∀ k ≤ n x, (encB (step^[k] (init x))).length ≤ B x) :
    ComputableInO (fun x => step^[n x] (init x)) encIn encB
      (fun x => Tn x + Ti x + (n x + 1) * (R x + B x + ((encNat (n x)).length + 1) ^ 2))
      fun x => Sn x + Si x + Q x + B x + (encNat (n x)).length := by
  -- the iteration on `Option (ℕ × β)`, until the counter is exhausted
  obtain ⟨c, ⟨kf, Qf, _, tmf, hf⟩, -⟩ :=
    Internal.NormalForm.inO (countStep_inO (Ts := Ts) (Ss := Ss) hstep)
  have hr (o : Option (ℕ × β)) :
      IsLeast {m | encOption (encPair encNat encB) ((countStep step)^[m + 1] o) = []}
        ((o.map Prod.fst).getD 0) := by
    rcases o with _ | ⟨t, b⟩
    · refine ⟨rfl, fun _ _ => Nat.zero_le _⟩
    · refine ⟨?_, fun m hm => ?_⟩
      · simp only [Set.mem_ofPred_eq, Option.map_some, Option.getD_some]
        rw [Function.iterate_succ_apply', iterate_countStep step t b le_rfl, Nat.sub_self]
        rfl
      · by_contra hlt
        simp only [Set.mem_ofPred_eq, Option.map_some, Option.getD_some, not_le] at hm hlt
        rw [iterate_countStep step t b hlt] at hm
        simp at hm
  let encC := encOption (encPair encNat encB)
  let r (o : Option (ℕ × β)) := (o.map Prod.fst).getD 0
  let tf (o : Option (ℕ × β)) := c * ((encC o).length +
    ((encNat (o.getD default).1).length + 1) ^ 2 + Ts (o.getD default).2 + 1)
  let sf (o : Option (ℕ × β)) := c * ((encC o).length + Ss (o.getD default).2 + 1)
  let d := 2 * (kf + 3) * (6 * kf + 54) + (4 * kf + 42)
  have hit (o : Option (ℕ × β)) : (tmf.iterateWhile true).ComputesTidilyInTimeAndSpace
      (encC o) (encC ((countStep step)^[r o] o))
      ((r o + 1) * ((Finset.Iic (r o)).sup (fun j => tf ((countStep step)^[j] o)) +
        d * ((Finset.Iic (r o)).sup (fun j => (encC ((countStep step)^[j] o)).length) + 1)))
      (d * ((Finset.Iic (r o)).sup (fun j => sf ((countStep step)^[j] o)) +
        (Finset.Iic (r o)).sup (fun j => (encC ((countStep step)^[j] o)).length) + 1)) := by
    have h := computesTidily_iterateWhile
      (w := fun j => encC ((countStep step)^[j] o)) (r := r o)
      (fun j hj => by
        simpa only [Function.iterate_succ_apply'] using (hf ((countStep step)^[j] o)).mono
          (Finset.le_sup (f := fun j => tf ((countStep step)^[j] o)) (Finset.mem_Iic.mpr hj))
          (Finset.le_sup (f := fun j => sf ((countStep step)^[j] o)) (Finset.mem_Iic.mpr hj)))
      (fun j hj => Finset.le_sup (f := fun j => (encC ((countStep step)^[j] o)).length)
        (Finset.mem_Iic.mpr hj))
      (fun j hj he => absurd ((hr o).2 he) (by dsimp only [r] at hj; omega)) (hr o).1 true
    refine h.mono ?_ ?_ <;> dsimp [d] <;> ring_nf <;> omega
  -- the start, and its iterates
  have hstart := (ComputableInDegree.optionSome (enc₁ := encPair encNat encB)
    (enc := encOption (encPair encNat encB))).inO_one.comp_linear (hn.prod hinit)
  obtain ⟨c₀, ⟨k₀, Q₀, _, tm₀, h₀⟩, l₀⟩ := Internal.NormalForm.inO hstart
  -- Compose these same two machines, retaining independent bounds and the output charge.
  let c₁ := 6 * max k₀ (kf + 1 + 2) + 29
  have h (x : γ) : ((tmf.iterateWhile true).comp tm₀ true).ComputesTidilyInTimeAndSpace
      (encIn x) (encC ((countStep step)^[n x] (some (n x, init x))))
      (c₀ * (Tn x + Ti x + 1) +
        (n x + 1) * ((Finset.Iic (n x)).sup
          (fun j => tf ((countStep step)^[j] (some (n x, init x)))) +
          d * ((Finset.Iic (n x)).sup
            (fun j => (encC ((countStep step)^[j] (some (n x, init x)))).length) + 1)) +
        c₁ * ((encC (some (n x, init x))).length + 1))
      (c₀ * (Sn x + Si x + 1) +
        d * ((Finset.Iic (n x)).sup (fun j => sf ((countStep step)^[j] (some (n x, init x)))) +
          (Finset.Iic (n x)).sup
            (fun j => (encC ((countStep step)^[j] (some (n x, init x)))).length) + 1) +
        c₁ * ((encC (some (n x, init x))).length + 1)) := by
    have hx := (h₀ x).comp (hit (some (n x, init x))) true
    simp only [r, Option.map_some, Option.getD_some, Function.comp_apply] at hx
    apply hx.mono
    all_goals dsimp only [c₁, encC]; ring_nf; omega
  have hiter (x : γ) {k : ℕ} (hk : k ≤ n x) :
      (countStep step)^[k] (some (n x, init x)) = some (n x - k, step^[k] (init x)) :=
    iterate_countStep step _ _ hk
  have hlen (x : γ) {k : ℕ} (hk : k ≤ n x) :
      ((encOption (encPair encNat encB)) ((countStep step)^[k] (some (n x, init x)))).length ≤
        2 * (encNat (n x)).length + B x + 2 := by
    rw [hiter x hk]
    have := length_encNat_mono (Nat.sub_le (n x) k)
    have := hstate x k hk
    simp only [encOption_some, List.length_cons, length_encPair]
    omega
  have hcount (x : γ) {k : ℕ} (hk : k ≤ n x) :
      (encNat (((countStep step)^[k] (some (n x, init x))).getD default).1).length ≤
        (encNat (n x)).length := by
    rw [hiter x hk]
    exact length_encNat_mono (Nat.sub_le (n x) k)
  -- the bounds of the rounds and of the iterates
  have hrx (x : γ) : ((some (n x, init x)).map Prod.fst).getD 0 = n x := rfl
  have hT (x : γ) : (Finset.Iic (n x)).sup (fun k => c *
      ((encOption (encPair encNat encB) ((countStep step)^[k] (some (n x, init x)))).length +
      ((encNat (((countStep step)^[k] (some (n x, init x))).getD default).1).length + 1) ^ 2 +
      Ts (((countStep step)^[k] (some (n x, init x))).getD default).2 + 1)) ≤
      c * (2 * (encNat (n x)).length + B x + 2 + ((encNat (n x)).length + 1) ^ 2 + R x + 1) :=
    Finset.sup_le fun k hk => by
      have hk := Finset.mem_Iic.mp hk
      have h₁ := hlen x hk
      have h₂ := Nat.pow_le_pow_left (Nat.add_le_add_right (hcount x hk) 1) 2
      have h₃ := hround x k hk
      rw [hiter x hk] at h₂ ⊢
      rw [hiter x hk] at h₁
      simp only [Option.getD_some] at h₂ ⊢
      exact Nat.mul_le_mul_left c (by omega)
  have hS (x : γ) : (Finset.Iic (n x)).sup (fun k => c *
      ((encOption (encPair encNat encB) ((countStep step)^[k] (some (n x, init x)))).length +
      Ss (((countStep step)^[k] (some (n x, init x))).getD default).2 + 1)) ≤
      c * (2 * (encNat (n x)).length + B x + 2 + Q x + 1) :=
    Finset.sup_le fun k hk => by
      have hk := Finset.mem_Iic.mp hk
      have h₁ := hlen x hk
      have h₂ := hspace x k hk
      rw [hiter x hk] at h₁ ⊢
      simp only [Option.getD_some]
      exact Nat.mul_le_mul_left c (by omega)
  have hL (x : γ) : (Finset.Iic (n x)).sup (fun k =>
      (encOption (encPair encNat encB) ((countStep step)^[k] (some (n x, init x)))).length) ≤
      2 * (encNat (n x)).length + B x + 2 :=
    Finset.sup_le fun k hk => hlen x (Finset.mem_Iic.mp hk)
  have hO : ComputableInO (fun x => (countStep step)^[n x] (some (n x, init x))) encIn
      (encOption (encPair encNat encB))
      (fun x => Tn x + Ti x + (n x + 1) * (R x + B x + ((encNat (n x)).length + 1) ^ 2))
      fun x => Sn x + Si x + Q x + B x + (encNat (n x)).length := by
    refine of_bounds ⟨_, _, inferInstance, (tmf.iterateWhile true).comp tm₀ true,
      fun x => (h x).computesInTimeAndSpace⟩
      (c₀ + c₁ * (c₀ + 1) + 8 * (c + d + 1) + 4 * d * (c + 1)) (fun x => ?_)
      (fun x => ?_)
      (fun x => ?_)
    · set P := R x + B x + ((encNat (n x)).length + 1) ^ 2
      have h₁ := hT x
      have h₂ := hL x
      have h₃ := (h₀ x).length_output_le
      have h₄ : (encNat (n x)).length + 1 ≤ ((encNat (n x)).length + 1) ^ 2 :=
        Nat.le_self_pow two_ne_zero _
      have e₁ : c * (2 * (encNat (n x)).length + B x + 2 + ((encNat (n x)).length + 1) ^ 2 +
          R x + 1) ≤ c * (4 * P) := Nat.mul_le_mul_left c (by omega)
      have e₀ := (Nat.add_le_add_right h₂ 1).trans
        (show 2 * (encNat (n x)).length + B x + 2 + 1 ≤ 3 * P by omega)
      have e₂ := Nat.mul_le_mul_left (n x + 1) (Nat.add_le_add (h₁.trans e₁)
        (Nat.mul_le_mul_left d e₀))
      have e₃ : (n x + 1) * (c * (4 * P) + d * (3 * P)) ≤
          8 * (c + d + 1) * ((n x + 1) * P) := by
        ring_nf; nlinarith [Nat.zero_le (n x * P), Nat.zero_le P]
      exact sum_le (k' := 4 * d * (c + 1))
        ((e₂.trans e₃).trans (Nat.mul_le_mul_left _ (by omega))) h₃
    · set W := Q x + B x + (encNat (n x)).length
      have h₁ := (hS x).trans (Nat.mul_le_mul_left c
        (show 2 * (encNat (n x)).length + B x + 2 + Q x + 1 ≤ 3 * (W + 1) by omega))
      have h₂ := (Nat.add_le_add_right (hL x) 1).trans
        (show 2 * (encNat (n x)).length + B x + 2 + 1 ≤ 3 * (W + 1) by omega)
      have e₁ := Nat.mul_le_mul_left d (Nat.add_le_add h₁ h₂)
      have e₂ : d * (c * (3 * (W + 1)) + 3 * (W + 1)) ≤ 4 * d * (c + 1) * (W + 1) := by
        ring_nf; omega
      have h₃ := l₀ x
      simp only [Function.comp_apply] at h₃
      have := sum_le (k := 4 * d * (c + 1)) (k' := 8 * (c + d + 1)) (c₁ := c₁)
        (e₁.trans e₂) h₃
      rw [show c₀ + c₁ * (c₀ + 1) + 4 * d * (c + 1) + 8 * (c + d + 1) =
        c₀ + c₁ * (c₀ + 1) + 8 * (c + d + 1) + 4 * d * (c + 1) by ring] at this
      simp only [W] at this
      linarith
    · refine (hlen x le_rfl).trans ((show 2 * (encNat (n x)).length + B x + 2 ≤
        2 * (Sn x + Si x + Q x + B x + (encNat (n x)).length + 1) by omega).trans
        (Nat.mul_le_mul_right _ (by omega)))
  refine (((ComputableInDegree.getD (enc₁ := encPair encNat encB)
    (enc := encOption (encPair encNat encB))
    default).inO_one.comp_linear hO).snd').of_enc_eq fun x => ?_
  simp only [Function.comp_apply, hiter x le_rfl, Option.getD_some]

end Turing.MultiTapeTM.ComputableInO


