-- Prove2me | Definitions.Def_AGProxGap_IsClose
-- name    : AGProxGap_IsClose
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:35:19.023946+00:00
-- url     : https://prove2.me/theorems/33c0f94f-b2e3-463b-8bb9-5bfb5052c109
-- title:
--   Closeness $d(w,C)\le e$
-- statement:
--   For a code $C\subseteq\mathbb F_q^n$, a word $w\in\mathbb F_q^n$ and an integer $e\ge 0$, the word is **within distance $e$ of $C$**, written $d(w,C)\le e$, if some codeword $c\in C$ has Hamming distance
--   $$
--   d(w,c)=|\{i\in[n]: w_i\ne c_i\}|\le e .
--   $$
--   For a nonempty code this is the same as $\min_{c\in C}d(w,c)\le e$.
--
--   **Formalization Note** The minimum over $C$ is not formed; the predicate is the existential form (false for the empty code). Distance is Mathlib's `hammingDist`, with classical decidability of equality.
-- source:
--   Li, Xing, Yuan, Zhu, On Proximity Gaps for One-Point Algebraic Geometric Codes, arXiv:2610.39256 (held version, sha256 d2017986…3b3f), §2.1, p.13

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Classical

namespace AGProxGap

/-- **Closeness to a code**: `d(w, C) ≤ e` (Li, Xing, Yuan, Zhu, *On Proximity Gaps for One-Point Algebraic Geometric Codes*, arXiv:2610.39256 (held version, sha256 d2017986…), §2.1, p.13: "the Hamming distance is defined as
d(u, v) = |{i ∈ [n] : u_i ≠ v_i}|. For a nonempty code C, let d(u, C) = min_{c∈C} d(u, c)").

**Formalization Note** The minimum over `C` is not formed: `d(w, C) ≤ e` is stated as "some
codeword is within Hamming distance `e`" (Mathlib's `hammingDist`), which is the same for a
nonempty code (and is false for the empty code). Decidability of equality is classical. -/
def IsClose {K : Type*} {n : ℕ} (C : Set (Fin n → K)) (w : Fin n → K) (e : ℕ) : Prop :=
  ∃ c ∈ C, hammingDist w c ≤ e

end AGProxGap


