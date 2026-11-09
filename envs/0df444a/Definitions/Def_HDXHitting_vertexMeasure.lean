-- Prove2me | Definitions.Def_HDXHitting_vertexMeasure
-- name    : HDXHitting_vertexMeasure
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:56:28.999209+00:00
-- url     : https://prove2.me/theorems/79331c6a-16f0-4507-964d-106c90a99d1c
-- title:
--   Vertex distribution $\pi_1(v)=\frac1d\Pr_{\sigma\sim\pi_d}[v\in\sigma]$
-- statement:
--   For a $d$-dimensional complex with top distribution $p$, the **vertex distribution** is
--   $$
--   \pi_1(v) = \frac1d\,\Pr_{\sigma\sim p}[v\in\sigma] = \frac1d\sum_{\sigma\ni v} p(\sigma).
--   $$
--   Since every top face has $d$ vertices, $\sum_v \Pr[v\in\sigma] = d$, so $\pi_1$ is a probability distribution on the vertices (for $d\ge1$). It is the stationary measure of the induced graph and the measure under which the mean $\mu = \mathbb E_\pi f$ of Lemma 3.2 is taken.
--
--   **Formalization Note** At $d=0$ the factor $1/d$ is $0$ in Lean; every result of the mission assumes $d\ge1$.
-- source:
--   Bafna–Tjowasi, A Hitting Set Lemma for HDX & Applications, STOC 2027 submission (manuscript sha256 60d23b0d…), Section 2.2.1, p.12 (π_k(τ) ∝ Pr_{σ∼π_d}[τ ⊂ σ])

import Mathlib

namespace HDXHitting

/-- The vertex distribution `π_1` of a `d`-dimensional complex with top distribution `p`
(Bafna–Tjowasi, *A Hitting Set Lemma for HDX & Applications*, STOC 2027 submission manuscript (sha256 60d23b0d…e56d3), §2.2.1, p.12: `π_k(τ) ∝ Pr_{σ∼π_d}[τ ⊂ σ]`): `π_1(v) = (1/d) · Pr_{σ∼p}[v ∈ σ]`.
On a distribution supported on `d`-sets, `∑_v Pr[v ∈ σ] = d`, so `1/d` is the normalizing
constant.

**Formalization Note** At `d = 0` the factor `1/d` is `0` in Lean; every result of the mission
assumes `1 ≤ d`. -/
noncomputable def vertexMeasure {V : Type*} [Fintype V] [DecidableEq V] (d : ℕ)
    (p : Finset V → ℝ) (v : V) : ℝ :=
  (1 / (d : ℝ)) * ∑ σ ∈ Finset.univ.filter (fun σ : Finset V => v ∈ σ), p σ

end HDXHitting


