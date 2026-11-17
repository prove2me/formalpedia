-- Prove2me | Definitions.Def_AGProxGap_Supplement_minDist
-- name    : AGProxGap_Supplement_minDist
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:14:16.340757+00:00
-- url     : https://prove2.me/theorems/59e71afa-4f0f-4aa2-9bee-66202e69ea79
-- title:
--   Minimum distance $d(C)$ of a code
-- statement:
--   For a code $C\subseteq K^n$, the **minimum distance** is
--   $$d(C)=\min_{c\neq c'\in C} d(c,c'),$$
--   the least Hamming distance between two distinct codewords. For a one-point AG code it is at least the designed distance $n-m$, and the paper's counterexamples compare their radii with $d(C)/2$, half the *actual* minimum distance.
--
--   **Formalization Note** The minimum is the infimum in $\mathbb N$ over pairs of distinct codewords; it would be $0$ for a code with fewer than two words, which never occurs for the codes it is applied to ($m\ge1$).
-- source:
--   Li, Xing, Yuan, Zhu, On Proximity Gaps for One-Point Algebraic Geometric Codes, arXiv:2610.39256 (held version, sha256 d2017986…3b3f), §2.1, p.13

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Classical

namespace AGProxGap.Supplement

/-- **Minimum distance of a code** `d(C) = min_{c ≠ c' ∈ C} d(c, c')` (Li, Xing, Yuan, Zhu, *On Proximity Gaps for One-Point Algebraic Geometric Codes*, arXiv:2610.39256 (held version, sha256 d2017986…), §2.1, p.13: "Its
minimum distance is d(C) = min_{c≠c′∈C} d(c, c′)").

**Formalization Note** The minimum over pairs of distinct codewords is `sInf` in `ℕ` of the set
of their Hamming distances. It is the actual minimum distance, not the designed distance
`n − m`. On a code with fewer than two words the set is empty and the value is the junk `0`;
every code it is applied to here (a one-point AG code on a Garcia–Stichtenoth level with
`m ≥ 1`) has at least two codewords. -/
noncomputable def minDist {K : Type*} {n : ℕ} (C : Set (Fin n → K)) : ℕ :=
  sInf {d : ℕ | ∃ c ∈ C, ∃ c' ∈ C, c ≠ c' ∧ hammingDist c c' = d}

end AGProxGap.Supplement


