-- Prove2me | Definitions.Def_HDXHitting_colourMean
-- name    : HDXHitting_colourMean
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:56:33.665408+00:00
-- url     : https://prove2.me/theorems/0191a480-039e-4850-91fd-04da8f09a534
-- title:
--   Colour-class means $\mu_i=\mathbb E_{\pi_{1|\{i\}}}f$
-- statement:
--   For a top distribution $p$, a colouring $c$ and a function $f$ on the vertices, the **mean of $f$ on colour $i$** is
--   $$
--   \mu_i = \mathbb E_{\pi_{1|\{i\}}} f = \sum_{v:\,c(v)=i} \Pr_{\sigma\sim p}[v\in\sigma]\, f(v).
--   $$
--   On a $d$-partite complex, $\pi_{1|\{i\}}(v) = d\,\pi_1(v)\,1(c(v)=i) = \Pr[v\in\sigma]$ is the vertex distribution conditioned on colour $i$ (the paper's $\pi_{k|C}(\tau)=\binom dk\pi(\tau)1(c(\tau)=C)$ with $k=1$): each top face has exactly one vertex of colour $i$, so these weights sum to $1$.
--
--   These are the means $\mu_i$ of the partite bound (3).
-- source:
--   Bafna–Tjowasi, A Hitting Set Lemma for HDX & Applications, STOC 2027 submission (manuscript sha256 60d23b0d…), Lemma 3.2, p.15; Section 2.2.1, p.12 (π_{k|C})

import Mathlib

namespace HDXHitting

/-- The colour-class means `µ_i = E_{π_{1|{i}}} f` (Bafna–Tjowasi, *A Hitting Set Lemma for HDX & Applications*, STOC 2027 submission manuscript (sha256 60d23b0d…e56d3), Lemma 3.2, p.15; §2.2.1, p.12:
`π_{k|C}(τ) = (d choose k) π(τ) 1(c(τ) = C)`, so `π_{1|{i}}(v) = Pr_{σ∼π_d}[v ∈ σ]` for a vertex
of colour `i`): `µ_i = ∑_{v : c(v) = i} Pr_{σ∼p}[v ∈ σ] f(v)`.

**Formalization Note** On a `d`-partite complex each top face has exactly one vertex of colour
`i`, so these weights sum to `1` over the colour class. -/
noncomputable def colourMean {V ι : Type*} [Fintype V] [DecidableEq V] [DecidableEq ι]
    (p : Finset V → ℝ) (c : V → ι) (f : V → ℝ) (i : ι) : ℝ :=
  ∑ v ∈ Finset.univ.filter (fun v => c v = i),
    (∑ σ ∈ Finset.univ.filter (fun σ : Finset V => v ∈ σ), p σ) * f v

end HDXHitting


