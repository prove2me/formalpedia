-- Prove2me | Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_Capabilities
-- name    : Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_Capabilities
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:35:28.334476+00:00
-- url     : https://prove2.me/theorems/8503dabc-157b-4aab-8f5c-ed3c0885f3eb
-- title:
--   Complexity.Computability.Machines.Turing.MultiTape.Encodings.Capabilities — Computational capabilities of pair, option and list encodings
-- statement:
--   This is module `Complexity.Computability.Machines.Turing.MultiTape.Encodings.Capabilities` of [complexitylib](https://github.com/cslib-community/complexitylib), the complexity-theory library of the CSLib community (machine models, polynomial time, and the `polytime` tactic; Apache-2.0), at commit `0ebd467`. It is published here because the formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) states and proves its running-time bounds with it.
--
--   The classes contain proofs of plain computational capabilities, not selected machines or clocks.
--   Pairing retains independent time and workspace bounds and explicitly charges the output pair.
--
--   **Contents.** The module is published as a whole: 4 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_Capabilities`.
-- source:
--   https://github.com/cslib-community/complexitylib/blob/0ebd4671c2e7278a91f5671c11109bb254ae413c/Complexity/Computability/Machines/Turing/MultiTape/Encodings/Capabilities.lean

/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: vendored crei:crei/tidy-universal @7f7c0696 (unsubmitted)

public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_Bool
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_ResourceBounds

/- Prove2me definition bundle for `Complexity.Computability.Machines.Turing.MultiTape.Encodings.Capabilities` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-! # Computational capabilities of pair, option and list encodings

The classes contain proofs of plain computational capabilities, not selected machines or clocks.
Pairing retains independent time and workspace bounds and explicitly charges the output pair.
-/

namespace Turing.MultiTapeTM

universe u

/-! ### Encodings of pairs, options and lists -/

section Classes

variable {α β : Type u}

/-- `enc` encodes pairs compatibly with `enc₁` and `enc₂`. -/
public class PairEncoding (enc₁ : α ↪ List Bool) (enc₂ : β ↪ List Bool)
    (enc : α × β ↪ List Bool) : Prop where
  /-- Pairing is a combinator: functions `f` and `g` computable from a common input within
  common bounds combine into `fun x => (f x, g x)`, within a constant factor of those bounds, plus
  space for the encoded pair. Different bounds are covered by
  `Turing.MultiTapeTM.PairEncoding.pair_mono`. -/
  pair {γ : Type u} {encIn : γ ↪ List Bool} {f : γ → α} {g : γ → β} {t s : γ → ℕ} :
    ComputableInTimeAndSpace f encIn enc₁ t s →
    ComputableInTimeAndSpace g encIn enc₂ t s →
    ∃ c, ComputableInTimeAndSpace (fun x => (f x, g x)) encIn enc
      (fun x => c * (t x + 1)) (fun x => c * (s x + (enc (f x, g x)).length + 1))
  /-- The first projection is computable in linear time and space. -/
  fst : ComputableInDegree Prod.fst enc enc₁ 1 1
  /-- The second projection is computable in linear time and space. -/
  snd : ComputableInDegree Prod.snd enc enc₂ 1 1

/-- `enc` encodes options compatibly with `enc₁`: `none` is encoded by the empty word. -/
public class OptionEncoding (enc₁ : α ↪ List Bool) (enc : Option α ↪ List Bool) : Prop where
  /-- `none` is encoded by the empty word. -/
  none_eq : enc none = []
  /-- `some` is computable in linear time and space. -/
  some : ComputableInDegree some enc₁ enc 1 1
  /-- `Option.getD` is computable in linear time and space. -/
  getD (d : α) : ComputableInDegree (fun o => o.getD d) enc enc₁ 1 1

/-- `enc` encodes lists compatibly with `enc₁`. -/
public class ListEncoding (enc₁ : α ↪ List Bool) (enc : List α ↪ List Bool) : Prop where
  /-- `List.headD` is computable in linear time and space. -/
  headD (d : α) : ComputableInDegree (fun l => l.headD d) enc enc₁ 1 1
  /-- `List.tail` is computable in linear time and space. -/
  tail : ComputableInDegree List.tail enc enc 1 1
  /-- Testing a list for emptiness is computable in linear time and space. -/
  isEmpty : ComputableInDegree List.isEmpty enc encBool 1 1

/-- Pairing functions computable within different bounds. -/
public theorem PairEncoding.pair_mono {enc₁ : α ↪ List Bool} {enc₂ : β ↪ List Bool}
    {enc : α × β ↪ List Bool} [h : PairEncoding enc₁ enc₂ enc] {γ : Type u}
    {encIn : γ ↪ List Bool} {f : γ → α} {g : γ → β} {t₁ s₁ t₂ s₂ : γ → ℕ}
    (hf : ComputableInTimeAndSpace f encIn enc₁ t₁ s₁)
    (hg : ComputableInTimeAndSpace g encIn enc₂ t₂ s₂) :
    ∃ c, ComputableInTimeAndSpace (fun x => (f x, g x)) encIn enc
      (fun x => c * (t₁ x + t₂ x + 1))
      (fun x => c * (s₁ x + s₂ x + (enc (f x, g x)).length + 1)) :=
  h.pair (hf.mono (fun _ => Nat.le_add_right _ _) (fun _ => Nat.le_add_right _ _))
    (hg.mono (fun _ => Nat.le_add_left _ _) (fun _ => Nat.le_add_left _ _))

end Classes

end Turing.MultiTapeTM


