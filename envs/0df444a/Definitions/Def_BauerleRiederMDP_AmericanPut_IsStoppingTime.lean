-- Prove2me | Definitions.Def_BauerleRiederMDP_AmericanPut_IsStoppingTime
-- name    : BauerleRiederMDP_AmericanPut_IsStoppingTime
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:29:50.829892+00:00
-- url     : https://prove2.me/theorems/c539a43d-6a9a-40ad-8f18-35692648ca0a
-- title:
--   Exercise times with values in $\mathbb N_0\cup\{\infty\}$
-- statement:
--   A random time $\tau$ with values in $\mathbb N_0\cup\{\infty\}$ is a **stopping time** if, for every $n\in\mathbb N_0$, whether $\tau=n$ is decided by the first $n$ moves of the stock. The perpetual put allows every such $\tau$, including $\tau=\infty$ (never exercise).
--
--   **Formalization Note** On the path space of moves, an event is in $\sigma(\tilde R_1,\dots,\tilde R_n)$ exactly when it depends only on the first $n$ coordinates; the predicate says this for $\{\tau=n\}$. For an initial price $x>0$ this is the natural filtration of $(S_n)$ (Definition 10.1.1). At the absorbing price $x=0$ it is larger than the trivial filtration of $S\equiv0$, which does not change any value.
-- source:
--   N. Bäuerle and U. Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, Definition 10.1.1, p.304, PDF 312; §11.1, p.337, PDF 345 ($\tau\le\infty$)

import Mathlib

namespace BauerleRiederMDP.AmericanPut

/-- A **stopping time** (exercise time) of the binomial model, with values in `ℕ₀ ∪ {∞}` (Bäuerle & Rieder,
Markov Decision Processes with Applications to Finance (2011), §11.1, p.337, PDF 345, where the perpetual put
allows `τ ≤ ∞`; stopping times as in §10.1, p.303, PDF 311): for every `n ∈ ℕ₀` the event `{τ = n}` is
determined by the first `n` moves of the stock.

**Formalization Note.** On the path space `ℕ → Bool` of the moves, an event belongs to
`σ(R̃_1, …, R̃_n)` exactly when it is determined by the coordinates `ω 0, …, ω (n-1)`; this is the predicate
below. For an initial price `x > 0` (and `u ≠ d`) this filtration is the natural filtration of `(S_n)`; at the
absorbing price `x = 0` it is larger than the (trivial) filtration of `S`, which does not change the value of
the problem since `S ≡ 0` there. Values are in `ℕ∞`, `⊤` meaning that the option is never exercised. -/
def IsStoppingTime (τ : (ℕ → Bool) → ℕ∞) : Prop :=
  ∀ (n : ℕ) (ω ω' : ℕ → Bool), (∀ k < n, ω k = ω' k) → τ ω = (n : ℕ∞) → τ ω' = (n : ℕ∞)

end BauerleRiederMDP.AmericanPut


