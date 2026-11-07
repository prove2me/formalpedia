-- Prove2me | Definitions.Def_HalfIndMatch_Lval
-- name    : HalfIndMatch_Lval
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:09:59.902482+00:00
-- url     : https://prove2.me/theorems/6f1bd37e-1cb5-4330-8c44-b020336af25f
-- title:
--   The parameter $L=\log_b(np)$, $b=1/(1-p)$
-- statement:
--   For $n\ge1$ and $p\in(0,1)$ set $b=1/(1-p)$ and
--
--   $$L=\log_b(np)=\frac{\log(np)}{-\log(1-p)}.$$
--
--   In the regime $C/n\le p\le1-\kappa$ the largest induced matching of $G(n,p)$ has size $(1+o(1))L$; the mission's thresholds $(1/2\pm\varepsilon)L$ are expressed through it.
--
--   **Formalization Note** Natural logarithms (`Real.log`), so that $L\log b=\log(np)$ as in the paper. Lean's logarithm and division are total; the mission only uses $L$ for $0<p<1$ and $np>1$, where the formula is the paper's.
-- source:
--   Dhawan, Kızıldağ, Maitra, Mao, Wee, Half-Optimal Induced Matchings in Random Graphs: Online and Low-Degree Algorithms, arXiv:2610.40369 (held version, sha256 a1b329a1…), eq. (1), p.1 (PDF p.3); restated at the start of §3, p.12 (PDF p.14)

import Mathlib

namespace HalfIndMatch

/-- The parameter `L = log_b(np) = log(np) / (−log(1 − p))` of (1), where `b = 1/(1 − p)`. For
`p ∈ (0, 1)` and `np > 1` it is, up to lower-order terms, the size of a maximum induced matching
of `G(n, p)`.

Source: Dhawan, Kızıldağ, Maitra, Mao, Wee, *Half-Optimal Induced Matchings in Random Graphs:
Online and Low-Degree Algorithms*, arXiv:2610.40369 (held version, sha256 a1b329a1…), eq. (1),
p.1 (PDF p.3); restated at the start of §3, p.12 (PDF p.14).

**Formalization Note** Natural logarithms (`Real.log`), as in the paper (`L log b = log(np)`).
Lean's `Real.log` and division are total; every statement of the mission uses `Lval n p` only for
`0 < p < 1` and `np ≥ C > 1`, where the formula is the paper's. -/
noncomputable def Lval (n : ℕ) (p : ℝ) : ℝ :=
  Real.log ((n : ℝ) * p) / (-Real.log (1 - p))

end HalfIndMatch


