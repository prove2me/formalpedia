-- Prove2me | Definitions.Def_ValiantBorder_completeNetwork
-- name    : ValiantBorder_completeNetwork
-- status  : Definition
-- author  : @Abhishek Anand
-- created : 2026-11-24T00:26:45.256539+00:00
-- url     : https://prove2.me/theorems/4ddb9132-423b-488e-ac18-78ae1f454b53
-- title:
--   The polynomial of the complete network
-- statement:
--   Put a table of variables at each of $k$ vertices of a complete graph. Assign an $ℓ$-bit string to each edge. At a vertex, the incident strings select one table entry. The complete-network polynomial is the sum, over all edge assignments, of the product of the selected entries.
--
--   See [Claude (Anthropic), *VP ≠ VNP over every field*](https://hexagonmath.org/2611.00954v1) and the [corresponding Lean source](https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/vp-vnp/Nc/CaseI/Fkl.lean).
-- source:
--   Claude (Anthropic), VP ≠ VNP over every field, https://hexagonmath.org/2611.00954v1. Lean source: https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/vp-vnp/Nc/CaseI/Fkl.lean.

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import Mathlib

/-! Adapted from Claude (Anthropic), *VP ≠ VNP over every field*, the complete-network
polynomial, the flat-case bound, and Appendix N. Sources at commit
11b6c7e3c927df2658f513b6b68ea7f8929c62c5 of `anthropics/formal-math` include
`vp-vnp/Nc/CaseI/Fkl.lean`, `Nc/{LowDegree,PermValiant,Rate/Circuit}.lean` and
`Paper/{Grids,Flat,Rate,Approximate}.lean`. Apache-2.0. -/
namespace Nc.CaseI
open Finset MvPolynomial
/-- The pairs. -/
abbrev Pr (k : ℕ) := {e : Fin k × Fin k // e.1 < e.2}

/-- The strings at a table. -/
abbrev Ix (k ℓ : ℕ) := Fin k → Fin ℓ → Bool

variable {k ℓ : ℕ}

/-- Every end of a pair has a string; the strings at the tables. -/
def asm (x : Pr k → Fin 2 → Fin ℓ → Bool) (a : Fin k) : Ix k ℓ := fun b =>
  if h : a < b then x ⟨(a, b), h⟩ 0 else if h : b < a then x ⟨(b, a), h⟩ 1 else fun _ => false

variable (F : Type*) [CommSemiring F] (k ℓ : ℕ)

/-- **The polynomial of the complete network** of k tables with strings of ℓ bits. -/
noncomputable def fkl : MvPolynomial (Fin k × Ix k ℓ) F :=
  ∑ σ : Pr k → Fin ℓ → Bool, ∏ a, X (a, asm (fun e _ => σ e) a)


end Nc.CaseI


