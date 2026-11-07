-- Prove2me | Definitions.Def_NSWBetter_largeCount
-- name    : NSWBetter_largeCount
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:52:36.779561+00:00
-- url     : https://prove2.me/theorems/dc7ab014-0d1a-4f97-8df9-f3069c33f050
-- title:
--   Number $\ell$ of large goods
-- statement:
--   $\ell=|L|$, the number of large goods of the instance (Definition 3.2). Observation 3.3 shows that the set of large goods exists and is unique, so $\ell$ is well defined.
--
--   **Formalization Note** The least $\ell$ satisfying Definition 3.2 is taken; the fallback $0$ applies only when no such $\ell$ exists, which Observation 3.3 excludes for $\Delta\ge1$ and nonnegative values.
-- source:
--   Viswanathan, A Better-than-e^{1/e} Approximation Algorithm for Nash Social Welfare under Additive Valuations, arXiv:2607.13340 (held version, sha256 08811cb468c2df39231dca4222c5af94163587c7c83e205e50bbf0b91fc1deb3), Definition 3.2 and Observation 3.3, p.11

import Mathlib
import Definitions.Def_NSWBetter_IsLargeCount

namespace NSWBetter

open Classical in
/-- **The number ℓ of large goods.**
Viswanathan, *A Better-than-e^{1/e} Approximation Algorithm for Nash Social Welfare under Additive Valuations*, arXiv:2607.13340 (held version, sha256 08811cb4…), Definition 3.2, p.11; Observation 3.3, p.11: "there exists a unique set of large goods L satisfying the properties of Definition 3.2."

`largeCount Δ s` is the `ℓ` with `IsLargeCount Δ s ℓ`.

**Formalization Note.** By Observation 3.3 (for `Δ ≥ 1` and nonnegative values) such an `ℓ` exists and is unique; `Nat.find` picks it. The fallback value `0` is never reached in the instances the statements use. -/
noncomputable def largeCount (Δ : ℕ) (s : Multiset ℝ) : ℕ :=
  if h : ∃ ℓ, IsLargeCount Δ s ℓ then Nat.find h else 0

end NSWBetter


