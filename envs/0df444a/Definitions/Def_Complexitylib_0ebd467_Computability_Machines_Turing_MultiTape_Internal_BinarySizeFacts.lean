-- Prove2me | Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_BinarySizeFacts
-- name    : Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_BinarySizeFacts
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:44:50.160643+00:00
-- url     : https://prove2.me/theorems/09b6a6a9-22ea-4b3e-a472-570a8317448a
-- title:
--   Complexity.Computability.Machines.Turing.MultiTape.Internal.BinarySizeFacts — Pure binary-size facts
-- statement:
--   This is module `Complexity.Computability.Machines.Turing.MultiTape.Internal.BinarySizeFacts` of [complexitylib](https://github.com/cslib-community/complexitylib), the complexity-theory library of the CSLib community (machine models, polynomial time, and the `polytime` tactic; Apache-2.0), at commit `0ebd467`. It is published here because the formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) states and proves its running-time bounds with it.
--
--   Moved unchanged from the legacy binary calculus, retaining its existing qualified names. No
--   computability predicate is imported or introduced here; the names remain a staged cleanup item.
--
--   **Contents.** The module is published as a whole: 2 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Internal_BinarySizeFacts`.
-- source:
--   https://github.com/cslib-community/complexitylib/blob/0ebd4671c2e7278a91f5671c11109bb254ae413c/Complexity/Computability/Machines/Turing/MultiTape/Internal/BinarySizeFacts.lean

/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/
module
-- upstream: candidate

public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_Nat_Bits
import Mathlib.Data.Nat.Size
import Mathlib.Tactic.Linarith

/- Prove2me definition bundle for `Complexity.Computability.Machines.Turing.MultiTape.Internal.BinarySizeFacts` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-! # Pure binary-size facts

Moved unchanged from the legacy binary calculus, retaining its existing qualified names. No
computability predicate is imported or introduced here; the names remain a staged cleanup item.
-/

namespace Turing.MultiTapeTM.ComputableTidilyInO

/-- The length of `encNat` is monotone. -/
public lemma length_encNat_mono {m n : ℕ} (h : m ≤ n) : (encNat m).length ≤ (encNat n).length := by
  simpa [Nat.size_eq_bits_len] using Nat.size_le_size h

-- upstream: vendored crei:crei/tidy-universal @9cce4cc7 (unsubmitted)
-- vendored: `length_encNat_add_le` below, from that revision's `Complexity/Binary`

/-- Adding `i` adds at most `i` bits. -/
public lemma length_encNat_add_le (n i : ℕ) : (encNat (n + i)).length ≤ (encNat n).length + i := by
  induction i with
  | zero => rfl
  | succ i ih =>
    refine le_trans ?_ (Nat.add_le_add_right ih 1)
    simp only [encNat_apply, Nat.size_eq_bits_len, ← Nat.add_assoc]
    refine Nat.size_le.mpr ((Nat.succ_le_of_lt (Nat.lt_size_self _)).trans_lt ?_)
    rw [pow_succ]
    have := Nat.one_le_two_pow (n := (n + i).size)
    omega

end Turing.MultiTapeTM.ComputableTidilyInO


