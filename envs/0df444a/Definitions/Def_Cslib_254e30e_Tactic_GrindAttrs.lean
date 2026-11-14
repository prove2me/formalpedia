-- Prove2me | Definitions.Def_Cslib_254e30e_Tactic_GrindAttrs
-- name    : Cslib_254e30e_Tactic_GrindAttrs
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:22:06.046565+00:00
-- url     : https://prove2.me/theorems/59c980a5-fb0c-4bbd-a504-f7ed3b365804
-- title:
--   Cslib.Tactic.GrindAttrs — CSLib grind sets
-- statement:
--   This is module `Cslib.Tactic.GrindAttrs` of [CSLib](https://github.com/leanprover/cslib) (Apache-2.0), at commit `254e30e`: part of its development of multi-tape Turing machines. It is published here because the formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) states its running-time bounds on these machines.
--
--   This module registers custom grind sets in CSLib.
--
--   **Contents.** The module is published as a whole: 0 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_Cslib_254e30e_Tactic_GrindAttrs`.
-- source:
--   https://github.com/leanprover/cslib/blob/254e30e6d4299c51323aaeaf5f51a4763b375d4a/Cslib/Tactic/GrindAttrs.lean

/-
Copyright (c) 2026 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

module

public import Lean.Meta.Tactic.Grind.RegisterCommand

set_option autoImplicit true
set_option relaxedAutoImplicit true

/- Prove2me definition bundle for `Cslib.Tactic.GrindAttrs` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-! # CSLib grind sets

This module registers custom grind sets in CSLib.
-/

@[expose] public section

namespace Cslib.Logic.Modal

/--
The `modal` grind set is designed to quickly resolve goals that can be derived from modal reasoning
without unfolding the underlying Lean semantics of satisfaction for modalities. Use this in
combination with modal axioms for more powerful proof search. -/
register_grind_attr modal

end Cslib.Logic.Modal


