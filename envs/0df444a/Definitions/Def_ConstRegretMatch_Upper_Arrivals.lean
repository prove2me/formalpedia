-- Prove2me | Definitions.Def_ConstRegretMatch_Upper_Arrivals
-- name    : ConstRegretMatch_Upper_Arrivals
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T02:31:14.050886+00:00
-- url     : https://prove2.me/theorems/3e7298d2-013a-4ee3-b2c7-f2b898f69136
-- title:
--   §2, pp. 7–8 — i.i.d. arrival paths, the arrival counts Aᵗ and the expectation at horizon t
-- statement:
--   Arrivals happen in discrete time, one per period at times $t=1,2,\dots$; the type of each arrival is drawn independently, equal to $i$ with probability $\lambda_i$. An **arrival path** is a sequence $\omega=(\omega_0,\omega_1,\dots)$ of types, where $\omega_s$ is the type of the arrival at time $s+1$.
--
--   The number of type-$i$ arrivals at times $a+1,\dots,b$ is
--   $$A_i(a,b]=\#\{s\in[a,b): \omega_s=i\},$$
--   and $A^t_i=A_i(0,t]$ is the number of type-$i$ arrivals by time $t$. No agent arrives at time $0$, so all queues are empty then.
--
--   The **expectation at horizon $t$** of a quantity $F(\omega)$ that depends only on the first $t$ arrivals is the finite sum
--   $$\mathbb E[F]=\sum_{w\in\mathcal A^t}\Big(\prod_{s<t}\lambda_{w_s}\Big)F(w).$$
--   Every expectation in the mission (of the static optimum, of the collected value, of a queue length, of $h^*$ at an epoch) is of this form.
--
--   **Formalization Note** Paths are `ℕ → Fin n`. The expectation evaluates `F` on the prefix `w` extended by a fixed type after time `t`; for quantities that depend only on the first `t` arrivals (all those used here, by non-anticipativity) the extension is irrelevant. Using a finite sum avoids measure-theoretic expectations and their junk values on non-integrable functions. For `n = 0` the expectation is defined as `0`; no statement uses this case because $\sum_i\lambda_i=1$ forces $n\ge1$.
-- source:
--   Kerimov, Ashlagi, Gurvich, Dynamic Matching: Characterizing and Achieving Constant Regret, SSRN 3824407 (Sep 14, 2022), pp. 7–8, §2 (arrivals and the counts Aᵗ)

import Mathlib

namespace ConstRegretMatch.Upper

variable {n : ℕ}

/-- The number of `s ∈ [a, b)` with `ω s = i`. For an arrival path `ω : ℕ → Fin n` (the arrival at
time `s + 1` is of type `ω s`), this is the number of type-`i` arrivals at times `a + 1, …, b`. -/
def arrivalsBetween (ω : ℕ → Fin n) (a b : ℕ) (i : Fin n) : ℕ :=
  ((Finset.Ico a b).filter (fun s => ω s = i)).card

/-- `A^t_i`, the number of type-`i` arrivals by time `t` (§2, p. 8). Exactly one agent arrives at
each time `1, 2, …`; the arrival at time `s + 1` is `ω s` (0-based path), and there is no arrival at
time `0` (all queues are empty at `t = 0`). -/
def arrivals (ω : ℕ → Fin n) (t : ℕ) (i : Fin n) : ℕ :=
  arrivalsBetween ω 0 t i

/-- Extend a finite arrival prefix `w : Fin t → Fin n` to a whole path, with the constant type `i0`
after time `t`. -/
def extendPath {t : ℕ} (w : Fin t → Fin n) (i0 : Fin n) : ℕ → Fin n :=
  fun s => if h : s < t then w ⟨s, h⟩ else i0

/-- Expectation at horizon `t` under i.i.d. arrivals with law `lam` (§2, p. 7: at each time an arrival
is of type `i` with probability `λ_i`): the finite sum
`∑_{w ∈ (Fin n)^t} (∏_{s < t} λ_{w_s}) F(w)`.
It is the expectation of `F` for every `F : (ℕ → Fin n) → ℝ` whose value depends only on the first
`t` arrivals `ω 0, …, ω (t-1)`; every quantity it is applied to in this development has that
property. (For `n = 0` there is no path and the value is `0`; no statement uses that case, since
`∑ λ_i = 1` forces `n ≥ 1`.) -/
noncomputable def expect (lam : Fin n → ℝ) (t : ℕ) (F : (ℕ → Fin n) → ℝ) : ℝ :=
  if h : 0 < n then
    ∑ w : Fin t → Fin n, (∏ s, lam (w s)) * F (extendPath w ⟨0, h⟩)
  else 0

end ConstRegretMatch.Upper


