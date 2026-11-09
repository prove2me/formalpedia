-- Prove2me | Definitions.Def_DerandSq_LambdaH
-- name    : DerandSq_LambdaH
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T06:06:08.832602+00:00
-- url     : https://prove2.me/theorems/15f75c84-9447-4760-ab96-11de27369e94
-- title:
--   $\Lambda_H$, the Cohen–Cohen–Maor–Peled bound
-- statement:
--   For $d \geq 3$ and a graph $H$ on $[d]$ with characteristic polynomial $\chi_x(H)$ and $x_0$ the largest root of (4.4),
--   $$
--   \Lambda_H = d \cdot \Bigl( x_0 - (d - 1)\,\frac{\chi_{x_0}(H)}{\chi'_{x_0}(H)} \Bigr).
--   $$
--   Cohen, Cohen, Maor and Peled show $\lambda(G \circledS H) \geq \Lambda_H - o(1)$ for vertex-transitive $H$; Theorem 4.1 shows that random matching-model graphs attain it. For example $\Lambda_{K_3} = 5$, and $\Lambda_H = 2\sqrt 3$ for the perfect matching $H$ on $[4]$.
--
--   **Formalization Note** Real arithmetic throughout; $\chi'(x_0) > 0$ for $d \geq 3$, so the division is a genuine one.
-- source:
--   Alev–Rao, Rotating Walks, Derandomized Squares, and Permutation Conjugated Walks, STOC 2027 submission (manuscript sha256 2549f907…376941e0), (4.3), p.19

import Mathlib
import Definitions.Def_DerandSq_chi
import Definitions.Def_DerandSq_x0

namespace DerandSq

/-- `Λ_H = d·(x₀ − (d − 1)·χ_{x₀}(H) / χ'_{x₀}(H))` (Alev–Rao, *Rotating Walks, Derandomized Squares, and Permutation Conjugated Walks*, STOC 2027 submission manuscript (sha256 2549f907…376941e0), (4.3), p.19), the
Cohen–Cohen–Maor–Peled lower bound for `λ(G Ⓢ H)`.

**Formalization Note** `d − 1` is computed in `ℝ`. The division is real division; for `d ≥ 3`
the derivative `χ'` is positive at `x₀` (which exceeds every eigenvalue of `H`), so no junk value
`x / 0 = 0` occurs. -/
noncomputable def LambdaH (d : ℕ) (H : SimpleGraph (Fin d)) : ℝ :=
  d * (x0 d H - ((d : ℝ) - 1) * (chi H).eval (x0 d H) /
    (Polynomial.derivative (chi H)).eval (x0 d H))

end DerandSq


