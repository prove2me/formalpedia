-- Prove2me | Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Combinators_Ite
-- name    : Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Combinators_Ite
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:39:20.717772+00:00
-- url     : https://prove2.me/theorems/faeaa586-40d0-4827-ae4c-13e08d54ab9e
-- title:
--   Complexity.Computability.Machines.Turing.MultiTape.Combinators.Ite — Case distinction
-- statement:
--   This is module `Complexity.Computability.Machines.Turing.MultiTape.Combinators.Ite` of [complexitylib](https://github.com/cslib-community/complexitylib), the complexity-theory library of the CSLib community (machine models, polynomial time, and the `polytime` tactic; Apache-2.0), at commit `0ebd467`. It is published here because the formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) states and proves its running-time bounds with it.
--
--   If `c`, `f` and `g` are tidily computable from a common input, so is
--   `fun x => if c x then f x else g x`, within the bounds of `c` plus those of the branch taken.
--
--   `iteTM tmc tm₁ tm₂` runs `tmc` with its output written to a new work tape, runs `tm₁` if that word
--   is non-empty and `tm₂` otherwise (`Turing.MultiTapeTM.branch`), and clears the tape. The condition
--   `c` may be computed with any encoding of `Bool`: a finite-state transducer turns its output into a
--   word that is empty exactly for `false`.
--
--   ### Main definitions
--
--   * `Turing.MultiTapeTM.iteTM`: the machine for a case distinction.
--
--   ### Main results
--
--   * `Turing.MultiTapeTM.ComputesTidilyInTimeAndSpace.ite`: the machine-level case distinction.
--   * `Turing.MultiTapeTM.ComputableTidilyInTimeAndSpace.ite`: case distinctions are tidily computable;
--     each branch need only be computable on the inputs where it is taken.
--
--   **Contents.** The module is published as a whole: 2 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Combinators_Ite`.
-- source:
--   https://github.com/cslib-community/complexitylib/blob/0ebd4671c2e7278a91f5671c11109bb254ae413c/Complexity/Computability/Machines/Turing/MultiTape/Combinators/Ite.lean

/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

-- upstream: vendored crei:crei/tidy-universal @7f7c0696 (unsubmitted)

public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_KernelIte
public import Mathlib.Data.Finite.Sum
public import Mathlib.Data.Fintype.Option
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Combinators_Comp
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Combinators_Transducer
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Plumbing_Branch

/- Prove2me definition bundle for `Complexity.Computability.Machines.Turing.MultiTape.Combinators.Ite` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# Case distinction

If `c`, `f` and `g` are tidily computable from a common input, so is
`fun x => if c x then f x else g x`, within the bounds of `c` plus those of the branch taken.

`iteTM tmc tm₁ tm₂` runs `tmc` with its output written to a new work tape, runs `tm₁` if that word
is non-empty and `tm₂` otherwise (`Turing.MultiTapeTM.branch`), and clears the tape. The condition
`c` may be computed with any encoding of `Bool`: a finite-state transducer turns its output into a
word that is empty exactly for `false`.

## Main definitions

* `Turing.MultiTapeTM.iteTM`: the machine for a case distinction.

## Main results

* `Turing.MultiTapeTM.ComputesTidilyInTimeAndSpace.ite`: the machine-level case distinction.
* `Turing.MultiTapeTM.ComputableTidilyInTimeAndSpace.ite`: case distinctions are tidily computable;
  each branch need only be computable on the inputs where it is taken.
-/

namespace Turing.MultiTapeTM

/-- A function tidily computable on all inputs is tidily computable on the inputs satisfying `p`, by
the same machine. -/
public theorem ComputableTidilyInTimeAndSpace.restrict {α β : Type*} {encIn : α ↪ List Bool}
    {encOut : β ↪ List Bool} {f : α → β} {t s : α → ℕ}
    (h : ComputableTidilyInTimeAndSpace f encIn encOut t s) (p : α → Prop) :
    ComputableTidilyInTimeAndSpace (f ∘ Subtype.val) ((Function.Embedding.subtype p).trans encIn)
      encOut (t ∘ Subtype.val) (s ∘ Subtype.val) :=
  let ⟨k, S, hS, tm, htm⟩ := h
  ⟨k, S, hS, tm, fun x => htm x⟩

/-- Case distinctions are tidily computable: if `c` is tidily computable, `f` on the inputs where
`c` holds and `g` on the others, then `fun x => if c x then f x else g x` is tidily computable,
within the bounds of `c` plus those of the branch taken, up to a constant. The condition may be
computed with any encoding of `Bool`. -/
public theorem ComputableTidilyInTimeAndSpace.ite {γ β : Type*} {encIn : γ ↪ List Bool}
    {encC : Bool ↪ List Bool} {encOut : β ↪ List Bool} {c : γ → Bool} {f g : γ → β}
    {tc sc tf sf tg sg : γ → ℕ}
    (hc : ComputableTidilyInTimeAndSpace c encIn encC tc sc)
    (hf : ComputableTidilyInTimeAndSpace (f ∘ Subtype.val)
      ((Function.Embedding.subtype (c · = true)).trans encIn) encOut (tf ∘ Subtype.val)
      (sf ∘ Subtype.val))
    (hg : ComputableTidilyInTimeAndSpace (g ∘ Subtype.val)
      ((Function.Embedding.subtype (c · = false)).trans encIn) encOut (tg ∘ Subtype.val)
      (sg ∘ Subtype.val)) :
    ∃ k, ComputableTidilyInTimeAndSpace (fun x => if c x then f x else g x) encIn encOut
      (fun x => tc x + (if c x then tf x else tg x) + k)
      (fun x => sc x + (if c x then sf x else sg x) + k) := by
  -- the test word of the condition, in time bounded by the longer encoding of a truth value
  obtain ⟨l, hl⟩ : ∃ l, ∀ b, (encC b).length ≤ l :=
    ⟨(encC true).length + (encC false).length, fun b => by cases b <;> omega⟩
  have htest := (eqWordT (encC true)).computableTidilyInTimeAndSpace (f := id) (encIn := encC)
    (encOut := encTest) fun b => by
      rw [eqWordT_run_q₀]; cases b <;> simp [encTest_true, encTest_false]
  -- vendored: crei's `comp` is `comp_linear` here, as cslib #1111 restates `comp`
  obtain ⟨ct, hct⟩ := ComputableTidilyInTimeAndSpace.comp_linear htest hc
  have hb (x : γ) : 4 * (encC (c x)).length + 8 + ct * ((encC (c x)).length + 1) ≤
      (ct + 4) * (l + 2) := by
    have := hl (c x)
    have := Nat.mul_le_mul_left ct this
    simp only [Nat.mul_add_one, Nat.add_mul]; omega
  obtain ⟨k₀, S₀, _, tmc, htmc⟩ := hct.mono (t' := fun x => tc x + (ct + 4) * (l + 2))
    (s' := fun x => sc x + (ct + 4) * (l + 2)) (fun x => by have := hb x; omega)
    (fun x => by have := hb x; omega)
  obtain ⟨k₁, S₁, _, tm₁, htm₁⟩ := hf
  obtain ⟨k₂, S₂, _, tm₂, htm₂⟩ := hg
  refine ⟨(ct + 4) * (l + 2) + 15 + 5 * max k₀ (max k₁ k₂), _, _, inferInstance,
    iteTM tmc tm₁ tm₂, fun x => ?_⟩
  have h := (htmc x).ite (tm₁ := tm₁) (tm₂ := tm₂) (y := encOut (if c x then f x else g x))
    (t₁ := tf x) (s₁ := sf x) (t₂ := tg x) (s₂ := sg x)
    (fun hw => by
      have hcx : c x = true := by cases hcx : c x <;> simp_all [encTest_true, encTest_false]
      simpa [hcx] using htm₁ ⟨x, hcx⟩)
    (fun hw => by
      have hcx : c x = false := by cases hcx : c x <;> simp_all [encTest_true, encTest_false]
      simpa [hcx] using htm₂ ⟨x, hcx⟩)
  refine TransformsTapes.mono h ?_ ?_ <;> cases hcx : c x <;>
    simp [hcx, encTest_true, encTest_false] <;> omega

end Turing.MultiTapeTM


