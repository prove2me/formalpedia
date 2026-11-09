-- Prove2me | Definitions.Def_HDXHitting_cMax
-- name    : HDXHitting_cMax
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:58:20.075822+00:00
-- url     : https://prove2.me/theorems/8774cec3-127e-48c9-aafb-ee6f2a2f9250
-- title:
--   $c_d(\mu)$: largest expected product at mean $\mu$
-- statement:
--   For a $d$-dimensional complex with top distribution $p$ and $\mu\in[0,1]$, let
--   $$
--   c_d(\mu) = \sup\Big\{\ \mathbb E_{\tau\sim\pi_d}\Big[\prod_{v\in\tau}f(v)\Big]\ :\ f:V\to[0,1],\ \mathbb E_\pi f = \mu\Big\},
--   $$
--   the least upper bound of the expected product over all $[0,1]$-valued functions with mean $\mu$. This is the function $c_d$ of the proof of the one-sided bound of Lemma 3.2.
--
--   **Formalization Note** Lean's real supremum: for $\mu\in[0,1]$ (and $d\ge1$) the set is nonempty (the constant function $\mu$) and bounded by $1$; outside $[0,1]$ the set is empty and the value is $0$, which is never used.
-- source:
--   Bafna–Tjowasi, A Hitting Set Lemma for HDX & Applications, STOC 2027 submission (manuscript sha256 60d23b0d…), proof of Lemma 3.2, p.15 (c_d(µ) the least upper bound)

import Mathlib
import Definitions.Def_HDXHitting_vertexMeasure
import Definitions.Def_HDXHitting_mean
import Definitions.Def_HDXHitting_hit

namespace HDXHitting

/-- `c_d(µ)` of the proof of the one-sided bound (Bafna–Tjowasi, *A Hitting Set Lemma for HDX & Applications*, STOC 2027 submission manuscript (sha256 60d23b0d…e56d3), proof of Lemma 3.2, p.15: "the
least upper bound for the quantity `E_{τ∈X(d)}[∏_{v∈τ} f(v)]`"), for a fixed complex: the
supremum of `E_{τ∼π_d}[∏_{v∈τ} f(v)]` over all `f` with values in `[0, 1]` and mean `µ`.

**Formalization Note** Real `sSup`: the set is nonempty and bounded (by `1`) for `µ ∈ [0, 1]`
(when `1 ≤ d`), and is used only there; outside it is `0`. -/
noncomputable def cMax {V : Type*} [Fintype V] [DecidableEq V] (d : ℕ) (p : Finset V → ℝ)
    (μ : ℝ) : ℝ :=
  sSup ((fun f => hit p f) '' {f : V → ℝ | (∀ v, 0 ≤ f v ∧ f v ≤ 1) ∧ mean d p f = μ})

end HDXHitting


