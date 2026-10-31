-- Prove2me | Definitions.Def_TransitoryQueue_quantile
-- name    : TransitoryQueue_quantile
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:00:26.470457+00:00
-- url     : https://prove2.me/theorems/2d5fee7f-85b1-4fcf-9656-330e40e5fbb7
-- title:
--   Generalized inverse $F^{\leftarrow}(u)=\inf\{t:F(t)\ge u\}$
-- statement:
--   For a distribution function $F$, the **generalized inverse** is
--
--   $$F^{\leftarrow}(u)=\inf\{t\in\mathbb R: F(t)\ge u\}.$$
--
--   For $u\in(0,1)$ and right-continuous $F$, $F^{\leftarrow}(u)\le t$ if and only if $u\le F(t)$; hence $F^{\leftarrow}(U)$ has distribution function $F$ when $U$ is uniform on $[0,1]$. The paper writes $G^{-1}$ in the proof of Proposition 5.2.
--
--   **Formalization Note** A real infimum; at $u\in\{0,1\}$ the value is a junk value, attained by a uniform variable with probability $0$.
-- source:
--   Chakraborty and Honnappa, Strong Embeddings for Transitory Queueing Models, arXiv:1906.06740v1, proof of Proposition 5.2, pp.24–26

import Mathlib

namespace TransitoryQueue

/-- The generalized inverse (quantile function) `F^←(u) = inf{t : F(t) ≥ u}` of a distribution
function `F`. Chakraborty and Honnappa, *Strong Embeddings for Transitory Queueing Models*, arXiv:1906.06740v1, proof of Proposition 5.2, pp.24–26 (the paper writes `G^{-1}`).

**Formalization Note** A real `sInf`. For a distribution function `F` and `u ∈ (0, 1)` the set
is nonempty and bounded below, and `F^←(u) ≤ t ↔ u ≤ F(t)` by right-continuity. At `u = 0` and
`u = 1` the value is a junk value; uniform variables take these values with probability `0`. -/
noncomputable def quantile (F : ℝ → ℝ) (u : ℝ) : ℝ :=
  sInf {t : ℝ | u ≤ F t}

end TransitoryQueue


