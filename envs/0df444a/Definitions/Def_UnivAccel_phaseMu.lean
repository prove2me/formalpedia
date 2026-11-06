-- Prove2me | Definitions.Def_UnivAccel_phaseMu
-- name    : UnivAccel_phaseMu
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:18:09.739337+00:00
-- url     : https://prove2.me/theorems/c30abe13-0467-4687-ba93-dca2a4357334
-- title:
--   Restart schedule: $\mu_k = (\Delta/2^k)/R^2$ and $K = \lceil \log_2(\Delta/\varepsilon)\rceil$ phases
-- statement:
--   The restart scheme of §5.4 runs phases $k = 0, 1, \dots$. Phase $k$ regularizes with
--   $$
--   \mu_k = \frac{\Delta_k}{R^2}, \qquad \Delta_k = \frac{\Delta}{2^k},
--   $$
--   where $\Delta \ge f(x_0) - f(x^*)$ is the given gap bound and $R \ge \|x_0 - x^*\|$ the given distance bound. The method runs
--   $$
--   K = \lceil \log_2(\Delta/\varepsilon) \rceil
--   $$
--   phases (`numPhases`), after which the gap bound $\Delta/2^K$ is at most $\varepsilon$.
--
--   The page sets $\mu = f(a)/R^2$ at a phase anchor $a$ under the normalization $f(x^*) = 0$; that is $\mu = (f(a) - f(x^*))/R^2$, which a method cannot compute without knowing $f(x^*)$. The schedule uses the known bound $\Delta_k$ on the gap at the $k$-th anchor instead; it halves in every phase, as the gap does on p.24.
--
--   **Formalization Note** $\lceil\cdot\rceil$ is the natural-number ceiling; $\Delta/\varepsilon > 1$ in every use, so $K \ge 1$.
-- source:
--   Adil, Kyng, Universal Acceleration: New Approaches to Heavy Ball Discretization, STOC 2027 submission (manuscript sha256 c7b64bc2…), §5.4 "One phase" and "Total cost", pp.24–25

import Mathlib

namespace UnivAccel

/-- The regularization parameter of restart phase `k` (Adil–Kyng, *Universal Acceleration: New
Approaches to Heavy Ball Discretization*, STOC 2027 submission manuscript (sha256
c7b64bc2…980250), §5.4 "One phase", p.24): `μ_k = Δ_k / R²` with `Δ_k = Δ / 2^k`.

**Formalization Note** The page sets `μ = f(a)/R²` under the normalization `f(x*) = 0`, i.e.
`μ = (f(a) − f(x*))/R²`, which a method cannot evaluate without `f(x*)`. The restart uses the
known gap bound `Δ_k ≥ f(a_k) − f(x*)` in its place: the gap bound halves in every phase, as the
gap does on p.24. -/
noncomputable def phaseMu (Δ R : ℝ) (k : ℕ) : ℝ :=
  Δ / 2 ^ k / R ^ 2

/-- The number of restart phases `K = ⌈log₂(Δ/ε)⌉`, after which the gap bound `Δ/2^K` is at most
`ε` (same source, §5.4 "Total cost", p.25).

**Formalization Note** `⌈·⌉₊` is the natural-number ceiling; `Δ/ε > 1` in every use, so
`K ≥ 1`. -/
noncomputable def numPhases (Δ ε : ℝ) : ℕ :=
  ⌈Real.logb 2 (Δ / ε)⌉₊

end UnivAccel


