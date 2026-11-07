-- Prove2me | Definitions.Def_AGProxGap_closeSet
-- name    : AGProxGap_closeSet
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:37:11.350744+00:00
-- url     : https://prove2.me/theorems/51bba12b-2b63-4b6a-97a3-5f33ef6dd360
-- title:
--   The set $S=\{z\in\mathbb F_q: d(r(z),C)\le e\}$
-- statement:
--   For a code $C\subseteq\mathbb F_q^n$, words $u_0,\dots,u_\ell$ and an integer $e\ge 0$, the **set of close parameters** is
--   $$
--   S=\{\,z\in\mathbb F_q : d(r(z),C)\le e\,\},\qquad r(z)=\sum_{j=0}^{\ell}u_jz^j .
--   $$
--   Since probabilities over $z$ are uniform on $\mathbb F_q$, $\Pr_z[d(r(z),C)\le e]=|S|/q$.
--
--   **Formalization Note** A `Finset` of the finite field; membership is decided classically.
-- source:
--   Li, Xing, Yuan, Zhu, On Proximity Gaps for One-Point Algebraic Geometric Codes, arXiv:2610.39256 (held version, sha256 d2017986…3b3f), Theorem 3.1, p.17; §2.2, p.13

import Mathlib
import Definitions.Def_AGProxGap_curve
import Definitions.Def_AGProxGap_IsClose

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Classical

namespace AGProxGap

/-- **The set of close parameters** `S = {z ∈ F_q : d(r(z), C) ≤ e}` (Li, Xing, Yuan, Zhu, *On Proximity Gaps for One-Point Algebraic Geometric Codes*, arXiv:2610.39256 (held version, sha256 d2017986…), Theorem 3.1, p.17:
"let S = {z ∈ F_q : d(r(z), C) ≤ e}"). Its size over `q = |F_q|` is the probability
`Pr_z[d(r(z), C) ≤ e]` for `z` uniform on `F_q` (§2.2, p.13).

**Formalization Note** A `Finset` of the finite field `K` (all of `K`, not a subset of
parameters); membership is decided classically. -/
noncomputable def closeSet {K : Type*} [Field K] [Fintype K] {n ℓ : ℕ} (C : Set (Fin n → K))
    (u : Fin (ℓ + 1) → Fin n → K) (e : ℕ) : Finset K :=
  Finset.univ.filter (fun z => IsClose C (curve u z) e)

end AGProxGap


