-- Prove2me | Definitions.Def_FixpReciprocal_clip
-- name    : FixpReciprocal_clip
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:45:05.020672+00:00
-- url     : https://prove2.me/theorems/08a5bb28-f3c1-4755-88ca-a4d01aabe6c6
-- title:
--   Clipping $[\![t]\!]$ and the reciprocal function $R_\tau$
-- statement:
--   For a real number $t$, its **clipping** to the unit interval is
--   $$[\![t]\!]=\min\{1,\max\{t,0\}\}.$$
--   For a rational $\tau$, the **reciprocal function** is
--   $$R_\tau(u)=\frac{1}{1+\tau u}.$$
--
--   These are the two functions of the gates of the mission. On $u\in[0,1]$ with $\tau>0$ the denominator is at least $1$, and $R_\tau(u)\in[0,1]$.
--
--   **Formalization Note** Lean's division is total, so $R_\tau$ is a total function; every statement that uses it carries $\tau>0$ and evaluates it on $[0,1]$.
-- source:
--   Shimizu, FIXP-Completeness via Reciprocal Gates: Applications to Second-Price Auctions (STOC 2027 submission, sha256 ffcad4a7…), §3, p.10 (PDF p.12); display (4), p.11 (PDF p.13)

import Mathlib

namespace FixpReciprocal

/-- **The clipping map** `⟦t⟧ = min{1, [t]₊}`, with `[t]₊ = max{t, 0}`.

Shimizu, *FIXP-Completeness via Reciprocal Gates: Applications to Second-Price Auctions*, STOC 2027 submission (sha256 ffcad4a7…), §3, p.10. -/
noncomputable def clip (t : ℝ) : ℝ := min 1 (max t 0)

/-- **The reciprocal gate function** `R_τ(u) = 1 / (1 + τ u)`.

Shimizu, *FIXP-Completeness via Reciprocal Gates: Applications to Second-Price Auctions*, STOC 2027 submission (sha256 ffcad4a7…), display (4), p.11 (and display (1), p.2).

**Formalization Note.** Lean's division is total, so this is a total function of `(τ, u)`. Every
statement using it carries `0 < τ` and evaluates it on `[0, 1]`, where the denominator is at least 1. -/
noncomputable def reciprocal (τ : ℚ) (u : ℝ) : ℝ := 1 / (1 + (τ : ℝ) * u)

end FixpReciprocal


