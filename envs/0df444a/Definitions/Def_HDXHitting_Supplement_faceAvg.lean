-- Prove2me | Definitions.Def_HDXHitting_Supplement_faceAvg
-- name    : HDXHitting_Supplement_faceAvg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T23:50:36.276694+00:00
-- url     : https://prove2.me/theorems/6f65997f-7c6e-4b81-a93d-7409e010e156
-- title:
--   Uniform average $\bar f(\sigma)$ of $f$ over the $k$-subsets of $\sigma$
-- statement:
--   Let $f$ be a real function on the $k$-element vertex sets. For a face $\sigma$, its **$k$-face average** is the uniform average of $f$ over the $k$-subsets of $\sigma$:
--   $$
--   \bar f(\sigma)=\mathbb E_{\tau\in\binom{\sigma}{k}}f(\tau)=\frac{1}{\binom{|\sigma|}{k}}\sum_{\tau\subseteq\sigma,\ |\tau|=k}f(\tau).
--   $$
--   On a top face $|\sigma|=d$, so the denominator is $\binom dk$.
--
--   This is the empirical mean of $f$ over the $k$-faces of a random top face; Section 4 of the paper bounds its upper tail (Theorem 4.1).
--
--   **Formalization Note** $f$ is defined on all finite vertex sets; only its values on the $k$-subsets of $\sigma$ are read. For $|\sigma|<k$ the Lean value is $0$ (division by zero), a case that never occurs on a top face since $k<d$.
-- source:
--   Bafna–Tjowasi, A Hitting Set Lemma for HDX & Applications, STOC 2027 submission (manuscript sha256 60d23b0d9400dc6e1b6e21e0efe05488a4e247d1be3b89a9c202e92f1e3e56d3), §4, p.20 (definition of f̄)

import Mathlib

namespace HDXHitting.Supplement

/-- The uniform average of a function on `k`-faces over the `k`-subsets of a face
(Bafna–Tjowasi, *A Hitting Set Lemma for HDX & Applications*, STOC 2027 submission manuscript
(sha256 60d23b0d…e56d3), §4, p.20: "for `f : X(k) → [0, 1]`, let
`f̄(σ) := E_{τ ∈ (σ choose k)} f(τ)` be the uniform average of `f` on the `k`-faces of `σ`"):
`f̄(σ) = (∑_{τ ⊆ σ, |τ| = k} f(τ)) / C(|σ|, k)`.

**Formalization Note** `f` is a function on all finite vertex sets; only its values on the
`k`-subsets of `σ` matter. On a top face `|σ| = d ≥ k`, so the denominator is `C(d, k) > 0`;
the Lean value `0` for `|σ| < k` (division by `0`) is never used on a top face. -/
noncomputable def faceAvg {V : Type*} (k : ℕ) (f : Finset V → ℝ) (σ : Finset V) : ℝ :=
  (∑ τ ∈ σ.powersetCard k, f τ) / (σ.card.choose k : ℝ)

end HDXHitting.Supplement


