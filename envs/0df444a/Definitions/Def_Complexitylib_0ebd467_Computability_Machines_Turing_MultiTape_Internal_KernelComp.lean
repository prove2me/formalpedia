-- Prove2me | Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_KernelComp
-- name    : Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_KernelComp
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:37:56.905028+00:00
-- url     : https://prove2.me/theorems/a24ee524-cd7c-4576-b897-ec1a6ad7e426
-- title:
--   Complexity.Computability.Machines.Turing.MultiTape.Internal.KernelComp — The existing composition machine and its run theorem
-- statement:
--   This is module `Complexity.Computability.Machines.Turing.MultiTape.Internal.KernelComp` of [complexitylib](https://github.com/cslib-community/complexitylib), the complexity-theory library of the CSLib community (machine models, polynomial time, and the `polytime` tactic; Apache-2.0), at commit `0ebd467`. It is published here because the formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) states and proves its running-time bounds with it.
--
--   Machine declarations are moved from their original module without changing programs or resource
--   formulas. Higher computability-calculus theorems remain in the original facade.
--
--   **Contents.** The module is published as a whole: 3 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_KernelComp`.
-- source:
--   https://github.com/cslib-community/complexitylib/blob/0ebd4671c2e7278a91f5671c11109bb254ae413c/Complexity/Computability/Machines/Turing/MultiTape/Internal/KernelComp.lean

/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: submitted #1111 @3441fa81
-- `transformsTapes_clearWork_only` and `ComputableTidilyInTimeAndSpace.comp_linear` are from
-- crei:crei/tidy-universal @7f7c0696 (unsubmitted).

public import Mathlib.Data.Finite.Sum
public import Definitions.Def_Cslib_254e30e_Foundations_Data_Fin_Tuple
public import Definitions.Def_Cslib_254e30e_Computability_Machines_Turing_MultiTape_Plumbing_ClearWork
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Plumbing_InputFromTape
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Plumbing_OutputToTape
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_KernelFacts

/- Prove2me definition bundle for `Complexity.Computability.Machines.Turing.MultiTape.Internal.KernelComp` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-! # The existing composition machine and its run theorem

Machine declarations are moved from their original module without changing programs or resource
formulas. Higher computability-calculus theorems remain in the original facade.
-/

namespace Turing.MultiTapeTM

variable {k₁ k₂ : ℕ} {Symbol S₁ S₂ : Type*}

/-- `tm₂` after `tm₁`, both with their work tapes padded to `max k₁ k₂`: run `tm₁` with its output
written to the work tape `Fin.natAdd (max k₁ k₂) 0`, run `tm₂` reading its input from that tape
(using `mark` on the last work tape to flag the left end of the input), then clear that tape. -/
public noncomputable def comp (tm₂ : MultiTapeTM k₂ Symbol S₂) (tm₁ : MultiTapeTM k₁ Symbol S₁)
    (mark : Symbol) : MultiTapeTM (max k₁ k₂ + 2) Symbol
      ((S₁ ⊕ RewindWorkState) ⊕ (MarkWorkState ⊕ S₂ ⊕ MarkWorkState) ⊕ Unit ⊕ RewindWorkState) :=
  ((tm₁.extendTapes (Fin.castLEEmb (le_max_left k₁ k₂))).outputToWord.extendTapes
      Fin.castSuccEmb).seq
    (((tm₂.extendTapes (Fin.castLEEmb (le_max_right k₁ k₂))).inputFromWord mark).seq
      ((clearWork Symbol).extendTapes (tapeEmb (Fin.natAdd (max k₁ k₂) 0))))

/-- Clearing the only non-blank work tape leaves all work tapes blank. -/
public theorem transformsTapes_clearWork_only {k : ℕ} (i : Fin k) (w : List Symbol) :
    TransformsTapes ((clearWork Symbol).extendTapes (tapeEmb i))
      (fun _ ws => ws = Function.update (fun _ => []) i w)
      (fun _ _ ws' e => ws' = (fun _ => []) ∧ e = []) (3 * (w.length + 1)) (w.length + 1 + k) :=
  (transformsTapes_clearWork_tapeEmb i w).imp (fun _ _ hws => by rw [hws, Function.update_self])
    (fun _ _ _ _ hws ⟨hws', he⟩ => ⟨by simp [hws', hws], he⟩) le_rfl le_rfl

/-- If `tm₁` computes `w` from `x` tidily and `tm₂` computes `y` from `w` tidily, then
`tm₂.comp tm₁ mark` computes `y` from `x` tidily. -/
public theorem ComputesTidilyInTimeAndSpace.comp {tm₁ : MultiTapeTM k₁ Symbol S₁}
    {tm₂ : MultiTapeTM k₂ Symbol S₂} {x w y : List Symbol} {t₁ s₁ t₂ s₂ : ℕ}
    (h₁ : tm₁.ComputesTidilyInTimeAndSpace x w t₁ s₁)
    (h₂ : tm₂.ComputesTidilyInTimeAndSpace w y t₂ s₂) (mark : Symbol) :
    (tm₂.comp tm₁ mark).ComputesTidilyInTimeAndSpace x y (t₁ + t₂ + 4 * w.length + 9)
      (s₁ + s₂ + 5 * w.length + (6 * max k₁ k₂ + 20)) := by
  set K := max k₁ k₂
  -- the work tape holding the intermediate word `w`
  set A : Fin (K + 2) := Fin.natAdd K 0
  have hA : Fin.append (fun _ : Fin K => ([] : List Symbol)) ![w, []] =
      Function.update (fun _ => []) A w := by
    funext l
    cases l using Fin.addCases with
    | left j => simp [A, Function.update_of_ne (Fin.castAdd_ne_natAdd j 0)]
    | right i => match i with | 0 | 1 => simp [A]
  -- phase 1: `tm₁` writes `w` to `A`
  have hQ₁ (ws' : Fin (K + 1 + 1) → List Symbol)
      (hv : (fun j => ws' (Fin.castSuccEmb j)) = Function.update (fun _ => []) (Fin.last K) w)
      (hx : ∀ l ∉ Set.range Fin.castSuccEmb, ws' l = []) :
      ws' = Function.update (fun _ => []) A w := by
    funext l
    induction l using Fin.lastCases with
    | last =>
      rw [hx _ fun ⟨j, hj⟩ => Fin.castSucc_ne_last j hj]
      simp [A, Fin.ext_iff]
    | cast j =>
      rw [show ws' j.castSucc = _ from congrFun hv j]
      simp [A, Function.update_apply, Fin.ext_iff]
  have hp₁ := ((h₁.extendTapes (Fin.castLEEmb (le_max_left k₁ k₂))).outputToWord.extendTapes
    Fin.castSuccEmb).imp (P' := fun inp ws => inp = x ∧ ws = fun _ => [])
    (Q' := fun _ _ ws' e => ws' = Function.update (fun _ => []) A w ∧ e = [])
    (fun _ _ ⟨hin, hws⟩ => ⟨hin, by simp [hws]⟩)
    (fun _ _ ws' _ ⟨_, hws⟩ ⟨⟨hv, he⟩, hx⟩ => ⟨hQ₁ ws' hv fun l hl => (hx l hl).trans
      (congrFun hws l), he⟩) le_rfl le_rfl
  -- phase 2: `tm₂` reads `w` from `A` and emits `y`
  have hp₂ := (transformsTapes_inputFromWord mark
      (computesTidily_iff.mp (h₂.extendTapes (Fin.castLEEmb (le_max_right k₁ k₂))))).imp
    (P' := fun _ ws => ws = Function.update (fun _ => []) A w)
    (Q' := fun _ _ ws' e => ws' = Function.update (fun _ => []) A w ∧ e = y)
    (fun _ _ hws => hws.trans hA.symm) (fun _ _ _ _ _ ⟨hws', he⟩ => ⟨hws'.trans hA, he⟩)
    le_rfl le_rfl
  -- phase 3: clear `A`
  have hclear : Function.update (Function.update (fun _ => []) A w) A [] = fun _ => [] := by
    rw [Function.update_idem]
    exact Function.update_eq_self A _
  have hp₃ := (transformsTapes_clearWork_tapeEmb (Symbol := Symbol) A w).imp
    (P' := fun _ ws => ws = Function.update (fun _ => []) A w)
    (Q' := fun _ _ ws' e => ws' = (fun _ => []) ∧ e = [])
    (fun _ _ hws => by rw [hws, Function.update_self])
    (fun _ _ _ _ hws ⟨hws', he⟩ => ⟨by rw [hws', hws, hclear], he⟩) le_rfl le_rfl
  refine (transformsTapes_seq hp₁ (transformsTapes_seq hp₂ hp₃ fun _ _ _ _ _ hQ => hQ.1)
    fun _ _ _ _ _ hQ => hQ.1).imp (fun _ _ h => h) ?_ (by omega) (by omega)
  rintro _ _ _ _ _ ⟨_, _, _, ⟨-, rfl⟩, ⟨_, _, _, ⟨-, rfl⟩, ⟨hws, rfl⟩, rfl⟩, rfl⟩
  exact ⟨hws, by simp⟩

end Turing.MultiTapeTM


