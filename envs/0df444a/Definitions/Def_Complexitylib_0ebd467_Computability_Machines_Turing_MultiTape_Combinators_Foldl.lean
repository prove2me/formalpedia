-- Prove2me | Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Combinators_Foldl
-- name    : Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Combinators_Foldl
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:43:46.283784+00:00
-- url     : https://prove2.me/theorems/48f1522d-71b9-438b-8404-15c57a8e64ae
-- title:
--   Complexity.Computability.Machines.Turing.MultiTape.Combinators.Foldl — Legacy fold certificate facade
-- statement:
--   This is module `Complexity.Computability.Machines.Turing.MultiTape.Combinators.Foldl` of [complexitylib](https://github.com/cslib-community/complexitylib), the complexity-theory library of the CSLib community (machine models, polynomial time, and the `polytime` tactic; Apache-2.0), at commit `0ebd467`. It is published here because the formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) states and proves its running-time bounds with it.
--
--   The machine construction lives in the Internal fold compiler. This compatibility theorem retains
--   its original statement for callers still using the staged existential tidy interface.
--
--   **Contents.** The module is published as a whole: 1 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Combinators_Foldl`.
-- source:
--   https://github.com/cslib-community/complexitylib/blob/0ebd4671c2e7278a91f5671c11109bb254ae413c/Complexity/Computability/Machines/Turing/MultiTape/Combinators/Foldl.lean

/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: vendored crei:crei/tidy-universal @7f7c0696 (unsubmitted)

public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_FoldCompiler
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Combinators_Comp
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Combinators_Encoding
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Combinators_IterateWhile

/- Prove2me definition bundle for `Complexity.Computability.Machines.Turing.MultiTape.Combinators.Foldl` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-! # Legacy fold certificate facade

The machine construction lives in the Internal fold compiler. This compatibility theorem retains
its original statement for callers still using the staged existential tidy interface.
-/
namespace Turing.MultiTapeTM
universe u
public theorem ComputableTidilyInTimeAndSpace.foldl {γ α β : Type u} {encIn : γ ↪ List Bool}
    {encA : α ↪ List Bool} {encB : β ↪ List Bool} {encL : List α ↪ List Bool}
    {encBA : β × α ↪ List Bool} {encS : List α × β ↪ List Bool}
    {encO : Option (List α × β) ↪ List Bool}
    [hLE : ListEncoding encA encL] [hBA : PairEncoding encB encA encBA]
    [hSE : PairEncoding encL encB encS] [hOE : OptionEncoding encS encO]
    {list : γ → List α} {init : γ → β} {step : β → α → β}
    {t s : γ → ℕ} {tStep sStep : β × α → ℕ} {tMax sMax lMax : γ → ℕ}
    (hlist : ComputableTidilyInTimeAndSpace list encIn encL t s)
    (hinit : ComputableTidilyInTimeAndSpace init encIn encB t s)
    (hstep : ComputableTidilyInTimeAndSpace (fun p : β × α => step p.1 p.2) encBA encB tStep sStep)
    (htMax : ∀ x i (hi : i < (list x).length),
      tStep (((list x).take i).foldl step (init x), (list x)[i]) ≤ tMax x)
    (hsMax : ∀ x i (hi : i < (list x).length),
      sStep (((list x).take i).foldl step (init x), (list x)[i]) ≤ sMax x)
    (hlMax : ∀ x, ∀ i ≤ (list x).length,
      (encS ((list x).drop i, ((list x).take i).foldl step (init x))).length ≤ lMax x) :
    ∃ c, ComputableTidilyInTimeAndSpace (fun x => (list x).foldl step (init x)) encIn encB
      (fun x => c * (t x + ((list x).length + 1) * (tMax x + lMax x + 1)))
      (fun x => c * (s x + sMax x + lMax x + 1)) := by
  obtain ⟨kl, Ql, _, tml, hl⟩ := hlist
  obtain ⟨ki, Qi, _, tmi, hi⟩ := hinit
  obtain ⟨ks, Qs, _, tms, hs⟩ := hstep
  exact Internal.FoldCompiler.foldl (encA := encA) (encL := encL)
    (encS := encS) (encO := encO) hl hi hs htMax hsMax hlMax
end Turing.MultiTapeTM


