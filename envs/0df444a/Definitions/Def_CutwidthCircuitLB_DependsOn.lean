-- Prove2me | Definitions.Def_CutwidthCircuitLB_DependsOn
-- name    : CutwidthCircuitLB_DependsOn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:24:28.697743+00:00
-- url     : https://prove2.me/theorems/40080637-6ac9-458a-983c-b06e9adb59c1
-- title:
--   A Boolean function depends on $x_j$
-- statement:
--   A function $f : \{0,1\}^n \to \{0,1\}$ **depends on** the variable $x_j$ if flipping $x_j$ changes its value on some input: $f(x \oplus e_j) \ne f(x)$ for some $x$.
-- source:
--   McGuire–Schlesinger–Williams, Explicit functions requiring larger than 4.5n size circuits, STOC 2027 submission (manuscript sha256 ed87148f…cfa3), Section 4.1, p.11

import Mathlib

namespace CutwidthCircuitLB

/-- `f : {0,1}ⁿ → {0,1}` **depends on** the variable `x_j` if flipping `x_j` changes its value on
some input (McGuire–Schlesinger–Williams, *Explicit functions requiring larger than 4.5n size circuits*, STOC 2027 submission manuscript (sha256 ed87148f…cfa3), §4.1, p.11). -/
def DependsOn {n : ℕ} (f : (Fin n → Bool) → Bool) (j : Fin n) : Prop :=
  ∃ x : Fin n → Bool, f (Function.update x j (!x j)) ≠ f x

end CutwidthCircuitLB


