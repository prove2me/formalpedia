-- Prove2me | Definitions.Def_TargetedSamplers_TimeConstructible
-- name    : TargetedSamplers_TimeConstructible
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T04:04:49.457446+00:00
-- url     : https://prove2.me/theorems/6c7c5f45-05bb-4a5b-afa9-205b3a80aa17
-- title:
--   Time-constructible functions
-- statement:
--   A function $T:\mathbb N\to\mathbb N$ is **time-constructible** if one program, given $1^n$, outputs the binary expansion of $T(n)$ within time $T(n)$, read as $\mathrm{budget}$ (up to constant and polylogarithmic factors).
--
--   **Formalization Note** The paper uses the term without defining it; this is the standard definition on the paper's RAM.
-- source:
--   Chen, Doron, Ebtehaj, Tell, Targeted Samplers, STOC 2027 submission (manuscript sha256 599d0a59…), Definition 4.1, p.20 (pdf p.22); Proposition 4.26, p.35; Theorem 4.29, p.41

import Mathlib
import Definitions.Def_TargetedSamplers_Machine

namespace TargetedSamplers

/-- `T : ℕ → ℕ` is time-constructible: one program, on input `1ⁿ`, outputs the binary expansion of
`T(n)` (little-endian, `Nat.bits`) within time `T(n)` (Chen, Doron, Ebtehaj, Tell, Targeted
Samplers, STOC 2027 submission, manuscript sha256 599d0a59…, used throughout §4, e.g. Definition 4.1,
p.20, "For every time-constructible functions Q, T, C").

**Formalization Note** The paper does not define the term; this is the standard definition on the
paper's RAM, with "time `T(n)`" read as `budget` (up to constant and polylogarithmic factors). -/
def TimeConstructible (T : ℕ → ℕ) : Prop :=
  ∃ (p : Program) (K k : ℕ), ∀ n : ℕ,
    p.RunsIn (Tapes.ofInput (List.replicate n true)) (budget K k (T n) n) (some (Nat.bits (T n)))

end TargetedSamplers


