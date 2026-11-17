-- Prove2me | Definitions.Def_AGProxGap_Supplement_codeDist
-- name    : AGProxGap_Supplement_codeDist
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:14:01.019777+00:00
-- url     : https://prove2.me/theorems/7081a666-5a2e-4769-af9c-9ca026ff6c96
-- title:
--   Distance $d(u,C)$ from a word to a code
-- statement:
--   For a code $C\subseteq K^n$ and a word $u\in K^n$, the **distance from $u$ to $C$** is
--   $$d(u,C)=\min_{c\in C} d(u,c),$$
--   where $d(u,c)=|\{i\in[n]:u_i\neq c_i\}|$ is the Hamming distance.
--
--   It is the quantity in the statements "$d(r(z),C)=e$" of the paper's counterexamples, which assert an exact distance, not only an upper bound.
--
--   **Formalization Note** The minimum is the infimum in $\mathbb N$ of the set of Hamming distances; for a nonempty code it is attained. On the empty code it would be $0$; every code it is applied to here contains the zero word.
-- source:
--   Li, Xing, Yuan, Zhu, On Proximity Gaps for One-Point Algebraic Geometric Codes, arXiv:2610.39256 (held version, sha256 d2017986…3b3f), §2.1, p.13

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Classical

namespace AGProxGap.Supplement

/-- **Distance from a word to a code** `d(u, C) = min_{c ∈ C} d(u, c)` (Li, Xing, Yuan, Zhu, *On Proximity Gaps for One-Point Algebraic Geometric Codes*, arXiv:2610.39256 (held version, sha256 d2017986…), §2.1, p.13: "For a
nonempty code C, let d(u, C) = min_{c∈C} d(u, c)").

**Formalization Note** The minimum is `sInf` of the set of Hamming distances
`{d(u, c) : c ∈ C}` in `ℕ` (Mathlib's `hammingDist`); for a nonempty code it is attained, so it
is the paper's minimum. On the empty code it is the junk value `0`; every code it is applied to
is a one-point AG code, which contains `0`. Decidability of equality is classical. -/
noncomputable def codeDist {K : Type*} {n : ℕ} (C : Set (Fin n → K)) (w : Fin n → K) : ℕ :=
  sInf {d : ℕ | ∃ c ∈ C, hammingDist w c = d}

end AGProxGap.Supplement


