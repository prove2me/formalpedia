-- Prove2me | Definitions.Def_Cslib_254e30e_Foundations_Data_BitString
-- name    : Cslib_254e30e_Foundations_Data_BitString
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:33:02.235614+00:00
-- url     : https://prove2.me/theorems/90e6294c-462b-41a7-b3ca-24fc5ad504bc
-- title:
--   Cslib.Foundations.Data.BitString — Fixed-length bit strings and Boolean functions
-- statement:
--   This is module `Cslib.Foundations.Data.BitString` of [CSLib](https://github.com/leanprover/cslib) (Apache-2.0), at commit `254e30e`: part of its development of multi-tape Turing machines. It is published here because the formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) states its running-time bounds on these machines.
--
--   A bit string is indexed by its coordinates, so selecting or updating one bit uses the usual
--   functions on `Fin n → Bool`.
--
--   **Contents.** The module is published as a whole: 2 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_Cslib_254e30e_Foundations_Data_BitString`.
-- source:
--   https://github.com/leanprover/cslib/blob/254e30e6d4299c51323aaeaf5f51a4763b375d4a/Cslib/Foundations/Data/BitString.lean

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module

public import Batteries.Tactic.Lint.Basic
public import Mathlib.Init
public import Mathlib.Tactic.Common
public import Definitions.Def_Cslib_254e30e_Tactic_GrindAttrs

set_option autoImplicit true
set_option relaxedAutoImplicit true

/- Prove2me definition bundle for `Cslib.Foundations.Data.BitString` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# Fixed-length bit strings and Boolean functions

A bit string is indexed by its coordinates, so selecting or updating one bit uses the usual
functions on `Fin n → Bool`.
-/

@[expose] public section

namespace Cslib

/-- A string of `n` bits, indexed by its coordinates. -/
abbrev BitString (n : ℕ) : Type := Fin n → Bool

/-- A Boolean function of `n` input bits. -/
abbrev BooleanFunction (n : ℕ) : Type := BitString n → Bool

end Cslib


