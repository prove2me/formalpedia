-- Prove2me | Definitions.Def_GraphNNSphere_W
-- name    : GraphNNSphere_W
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:43:01.306192+00:00
-- url     : https://prove2.me/theorems/cef168d3-8849-485c-ae51-5332e05d2615
-- title:
--   Evaluation count $W_G(q;x_0)$
-- statement:
--   $W_G(q;x_0)$ is the number of distinct points evaluated through the first completed expansion after which a target has been evaluated, including the entry itself, and $W_G(q;x_0)=\infty$ if the run stops without evaluating a target. The graph $G$ succeeds from every entry for $q$ if $W_G(q;x_0)<\infty$ for every $x_0\in D_n$. A failing entry is one with $W_G(q;x_0)=\infty$.
--
--   **Formalization Note** The value lies in the extended natural numbers.
-- source:
--   Lu, Sharp Limits of Graph-Based Nearest Neighbor Search on the Sphere, STOC 2027 submission (manuscript sha256 93565bc5…), §1.2, p.3

import Mathlib
import Definitions.Def_GraphNNSphere_greedyRun

namespace GraphNNSphere

/-- `W_G(q; x₀)`: the number of distinct points evaluated through the first completed expansion
after which a target has been evaluated, including the entry itself, and `∞` if the run stops
without evaluating a target (Lu, *Sharp Limits of Graph-Based Nearest Neighbor Search on the
Sphere*, STOC 2027 submission (manuscript sha256 93565bc5…), §1.2, p.3).

**Formalization Note** The value lies in `ℕ∞`, and a failing entry is one with `W = ⊤`. -/
noncomputable def W {n d : ℕ} (G : NavGraph n) (X : Fin n → Sph d) (q : Sph d) (k : ℕ)
    (x₀ : Fin n) : ℕ∞ :=
  match greedyRun G X q k x₀ with
  | .success _ _ evals => (evals : ℕ∞)
  | .fail => ⊤

end GraphNNSphere


