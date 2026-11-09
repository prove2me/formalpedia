-- Prove2me | Definitions.Def_HDXHitting_hit
-- name    : HDXHitting_hit
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:56:28.848094+00:00
-- url     : https://prove2.me/theorems/2bb604e6-bdfd-4291-a5f6-f072551bb88e
-- title:
--   Expected product over a random top face $\mathbb E_{\tau\sim\pi_d}\prod_{v\in\tau}f(v)$
-- statement:
--   For a top distribution $p$ and a function $f$ on the vertices,
--   $$
--   \mathbb E_{\tau\sim\pi_d}\Big[\prod_{v\in\tau} f(v)\Big] = \sum_{\sigma\subseteq V} p(\sigma)\prod_{v\in\sigma} f(v).
--   $$
--   For an indicator $f = 1_S$ this is the probability that a random top face lies entirely inside $S$; Lemma 3.2 bounds it in terms of the mean of $f$.
-- source:
--   Bafna–Tjowasi, A Hitting Set Lemma for HDX & Applications, STOC 2027 submission (manuscript sha256 60d23b0d…), Lemma 3.2, p.15

import Mathlib

namespace HDXHitting

/-- The expected product of `f` over a random top face, `E_{τ∼π_d}[∏_{v∈τ} f(v)] =
∑_σ p(σ) ∏_{v∈σ} f(v)` (Bafna–Tjowasi, *A Hitting Set Lemma for HDX & Applications*, STOC 2027 submission manuscript (sha256 60d23b0d…e56d3), Lemma 3.2, p.15). For `f = 1_S` this is the probability
that a random top face lies inside `S` (the hitting quantity of the paper's title). -/
noncomputable def hit {V : Type*} [Fintype V] (p : Finset V → ℝ) (f : V → ℝ) : ℝ :=
  ∑ σ : Finset V, p σ * ∏ v ∈ σ, f v

end HDXHitting


