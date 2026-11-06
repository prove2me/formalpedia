-- Prove2me | Definitions.Def_AnytimeAdaVR_Tape
-- name    : AnytimeAdaVR_Tape
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:27:40.717686+00:00
-- url     : https://prove2.me/theorems/26eb6f1a-e7ad-4a35-8322-3f026fa45028
-- title:
--   Random tape of Algorithm 4
-- statement:
--   The randomness of Algorithm 4 is a **tape** with three independent parts:
--
--   1. the optimization samples $\xi_{i,t}$ of each path $i\in\{S,M,D\}$, used in order;
--   2. the reservoir coins $U_{i,r}\in[0,1]$ of each path;
--   3. the validation samples $\xi^{\mathrm{val}}_{i,k,j}$ for the frozen report of path $i$ at checkpoint $n=2^k$, $j<n$.
-- source:
--   Jiang–Wang–Yang–Zhang–Li, Adaptive Variance Reduction across Smoothness and Noise Conditions (preprint, 2026; held artifact sha256 6f3caf41…74006), §5.3, p.10

import Mathlib
import Definitions.Def_AnytimeAdaVR_Path

namespace AnytimeAdaVR

/-- **The random tape of Algorithm 4.** Jiang–Wang–Yang–Zhang–Li, *Adaptive Variance Reduction across Smoothness and Noise Conditions*
(preprint, 2026), §5.3, p.10: "Each path, its reservoir, and
validation use independent random streams."

An element `ω = (ξ, U, ζ)` holds: the optimization samples `ξ (i, t)` of each path `i` (in order of
use); the reservoir coins `U (i, r) ∈ [0,1]` of each path (`r` = local query number); and the
validation samples `ζ (i, k, j)` for the frozen report of path `i` at checkpoint `n = 2^k`, index
`j < n`.

**Formalization Note.** The tape is drawn from `AnytimeAdaVR.tapeMeasure`, under which all
coordinates are independent, the samples have the oracle's law and the coins are uniform. Unused
coordinates are harmless. -/
abbrev Tape (Ξ : Type*) : Type _ :=
  (Path × ℕ → Ξ) × (Path × ℕ → unitInterval) × (Path × ℕ × ℕ → Ξ)

end AnytimeAdaVR


