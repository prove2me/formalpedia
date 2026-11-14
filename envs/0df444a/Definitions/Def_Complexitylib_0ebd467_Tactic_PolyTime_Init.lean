-- Prove2me | Definitions.Def_Complexitylib_0ebd467_Tactic_PolyTime_Init
-- name    : Complexitylib_0ebd467_Tactic_PolyTime_Init
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:33:16.027216+00:00
-- url     : https://prove2.me/theorems/ab0ad811-e8d7-438a-bccc-2cb75c62dd03
-- title:
--   Complexity.Tactic.PolyTime.Init — Shared rule sets and named efficiency certificates
-- statement:
--   This is module `Complexity.Tactic.PolyTime.Init` of [complexitylib](https://github.com/cslib-community/complexitylib), the complexity-theory library of the CSLib community (machine models, polynomial time, and the `polytime` tactic; Apache-2.0), at commit `0ebd467`. It is published here because the formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) states and proves its running-time bounds with it.
--
--   `polytime` searches the Aesop rule set `PolyTime`. A certificate for a named program is registered
--   with `@[program_certificate]`. Certificates are indexed by their efficiency predicate and by the
--   constant at the head of the program, looking through an output encoding. A goal's certificates
--   are looked up using its own program head, so similarly implemented algorithms do not unfold into
--   each other's rules.
--   Certificates are also registered with `fun_prop`, reusing any existing global registration, so the
--   same annotation supports calls inside larger functional programs without duplicating search rules.
--   Parameterized `IsPPT` certificates are uncurried to the definitionally equal `IsPPTOn` statement
--   before registration, keeping both tactic interfaces on the same encoded-input contract.
--
--   The certificate index is adapted from the cslib `crypto` branch. The computation predicates use
--   separate input and output encodings. `Tactic.PPT` combines the `PPT` and `PolyTime`
--   rule sets for closed probabilistic programs; machine witnesses remain behind their certificates.
--
--   ### Main definitions
--
--   * `program_certificate`: register a named efficiency theorem before its implementation unfolds.
--
--   Aesop's index cannot see inside the program, which is a function, so the lookup is a single tactic
--   rule for each efficiency predicate rather than one `apply` rule for each certificate.
--
--   ### References
--
--   Adapted from Cslib/Tactic/PolyTime/Init.lean on the cslib `crypto` branch at
--   `5ff69ca93402e7c947208dc56396d6d86203ccd8`, sharing routine-call matching between both tactics.
--
--   **Contents.** The module is published as a whole: 0 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with library lemmas renamed back to their names in this Mathlib and a few proof steps adjusted; no statement is changed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_Complexitylib_0ebd467_Tactic_PolyTime_Init`.
-- source:
--   https://github.com/cslib-community/complexitylib/blob/0ebd4671c2e7278a91f5671c11109bb254ae413c/Complexity/Tactic/PolyTime/Init.lean

/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Batteries.Tactic.Lint.Basic
public import Mathlib.Init
public import Mathlib.Tactic.Common
public import Definitions.Def_Cslib_254e30e_Tactic_GrindAttrs
public import Definitions.Def_Complexitylib_0ebd467_Tactic_LogSpace_Init
public import Aesop
public import Mathlib.Tactic.FunProp

/- Prove2me definition bundle for `Complexity.Tactic.PolyTime.Init` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# Shared rule sets and named efficiency certificates

`polytime` searches the Aesop rule set `PolyTime`. A certificate for a named program is registered
with `@[program_certificate]`. Certificates are indexed by their efficiency predicate and by the
constant at the head of the program, looking through an output encoding. A goal's certificates
are looked up using its own program head, so similarly implemented algorithms do not unfold into
each other's rules.
Certificates are also registered with `fun_prop`, reusing any existing global registration, so the
same annotation supports calls inside larger functional programs without duplicating search rules.
Parameterized `IsPPT` certificates are uncurried to the definitionally equal `IsPPTOn` statement
before registration, keeping both tactic interfaces on the same encoded-input contract.

The certificate index is adapted from the cslib `crypto` branch. The computation predicates use
separate input and output encodings. `Tactic.PPT` combines the `PPT` and `PolyTime`
rule sets for closed probabilistic programs; machine witnesses remain behind their certificates.

## Main definitions

* `program_certificate`: register a named efficiency theorem before its implementation unfolds.

Aesop's index cannot see inside the program, which is a function, so the lookup is a single tactic
rule for each efficiency predicate rather than one `apply` rule for each certificate.

## References

Adapted from Cslib/Tactic/PolyTime/Init.lean on the cslib `crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8`, sharing routine-call matching between both tactics.
-/

public section

declare_aesop_rule_sets [PolyTime, PPT]

end

-- Prove2me backport: the `program_certificate` attribute and the support code of the `polytime`
-- tactic (metaprogramming, not accepted in platform submissions and not used by the proofs
-- published here) are omitted; only the rule sets remain.


