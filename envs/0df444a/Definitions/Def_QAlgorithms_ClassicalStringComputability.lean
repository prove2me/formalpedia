-- Prove2me | Definitions.Def_QAlgorithms_ClassicalStringComputability
-- name    : QAlgorithms_ClassicalStringComputability
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-13T17:23:47.698854+00:00
-- url     : https://prove2.me/theorems/3e33af85-fc2c-41a4-8572-61f6fea2e5a7
-- title:
--   Classical binary strings and polynomial-time computability
-- statement:
--   Classical binary strings and polynomial-time computability
--
--   ### QAlgorithms.Complexity.Str
--
--   The type of finite binary strings: finite lists of Booleans, including the empty string.
--
--   ### QAlgorithms.Complexity.PolyTimeComputable
--
--   For a function $f$ from finite binary strings to finite binary strings, the proposition "$f$ is polynomial-time computable" asserts that there exists at least one witness of polynomial-time computability of $f$. This uses Mathlib's multi-stack Turing-machine model ("TM2"), with the identity map supplied as both the input and the output encoding of strings.
--
--   Such a witness consists of:
--   - a TM2 machine;
--   - a polynomial $q$ with natural-number coefficients;
--   - the property that on every input string $w$, the machine halts with output $f(w)$ within $q(|w|)$ steps.
--
--   The proposition is the mere existence of such data.
--
--   ### QAlgorithms.Complexity.encNat
--
--   For $k \in \mathbb{N}$, this is the bit string (list of Booleans, true written $1$ and false $0$)
--   $$\mathrm{encNat}(k) = 1^k 0.$$
--   It consists of $k$ ones followed by a single zero, so it has length $k+1$; for example, $\mathrm{encNat}(0) = 0$.
-- source:
--   https://github.com/shiy1022/lean-quantum-complexity/blob/main/algorithms/QAlgorithms/Defs/Complexity.lean . Exact primary-source page locators are preserved in the declaration docstrings.

import Mathlib

namespace QAlgorithms.Complexity
open Computability Turing

/-- Copied from `PvsNP.Str` (Cook, p.2): a binary string `w ∈ Σ*` with `Σ = {0,1}`. Used by de
Wolf p.122 (§13.2) for languages and reductions. -/
abbrev Str := List Bool

/-- Copied from `PvsNP.PolyTimeComputable` (Cook, Definition 3); de Wolf p.122 (§13.2), p.187
(§20.3): a function `f : Σ* → Σ*` is polynomial-time computable: a multi-stack machine started
with `w` on its input stack halts within `p(|w|)` steps with `f w` on its output stack, for some
polynomial `p`. -/
def PolyTimeComputable (f : Str → Str) : Prop :=
  Nonempty (TM2ComputableInPolyTime (id : Str → Str) (id : Str → Str) f)

/-! ### From `Def_ShiShallow_Core.lean` (verbatim) -/

/-- Copied from `ShiBQP.encNat`: a natural number in unary, terminated by `false`. -/
def encNat (k : ℕ) : Str := List.replicate k true ++ [false]

end QAlgorithms.Complexity


