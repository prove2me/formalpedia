-- Prove2me | Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Universal_Bit
-- name    : Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Universal_Bit
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:32:40.72718+00:00
-- url     : https://prove2.me/theorems/653bd085-4012-4bb8-93fb-002af576c6e4
-- title:
--   Complexity.Computability.Machines.Turing.MultiTape.Universal.Bit — Bits as symbols
-- statement:
--   This is module `Complexity.Computability.Machines.Turing.MultiTape.Universal.Bit` of [complexitylib](https://github.com/cslib-community/complexitylib), the complexity-theory library of the CSLib community (machine models, polynomial time, and the `polytime` tactic; Apache-2.0), at commit `0ebd467`. It is published here because the formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) states and proves its running-time bounds with it.
--
--   Machines over bits are described for the universal machine, whose symbols are natural numbers,
--   through `Turing.MultiTapeTM.Universal.eBit`.
--
--   ### Main definitions
--
--   * `Turing.MultiTapeTM.Universal.eBit`: bits as symbols.
--
--   **Contents.** The module is published as a whole: 1 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Universal_Bit`.
-- source:
--   https://github.com/cslib-community/complexitylib/blob/0ebd4671c2e7278a91f5671c11109bb254ae413c/Complexity/Computability/Machines/Turing/MultiTape/Universal/Bit.lean

/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: vendored crei:crei/tidy-universal @7f7c0696 (unsubmitted)
-- vendored: `eBit` sits in `Universal/Compose.lean` on that branch; it is kept apart here so that
-- `Universal` does not depend on composition, which moved out of it (#2179)

public import Batteries.Tactic.Lint.Basic
public import Mathlib.Init
public import Mathlib.Tactic.Common
public import Definitions.Def_Cslib_254e30e_Tactic_GrindAttrs
public import Mathlib.Logic.Embedding.Basic

/- Prove2me definition bundle for `Complexity.Computability.Machines.Turing.MultiTape.Universal.Bit` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# Bits as symbols

Machines over bits are described for the universal machine, whose symbols are natural numbers,
through `Turing.MultiTapeTM.Universal.eBit`.

## Main definitions

* `Turing.MultiTapeTM.Universal.eBit`: bits as symbols.
-/

namespace Turing.MultiTapeTM.Universal

/-- Bits as symbols. -/
@[expose] public def eBit : Bool ↪ ℕ :=
  ⟨Bool.toNat, fun a b h => by cases a <;> cases b <;> simp_all⟩

end Turing.MultiTapeTM.Universal


