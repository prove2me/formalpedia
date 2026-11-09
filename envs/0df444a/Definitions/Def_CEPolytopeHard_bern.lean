-- Prove2me | Definitions.Def_CEPolytopeHard_bern
-- name    : CEPolytopeHard_bern
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:15:23.47275+00:00
-- url     : https://prove2.me/theorems/9946f176-1ee4-4a39-957c-ea9811a51a9d
-- title:
--   Bivariate Bernstein approximation
-- statement:
--   For an integer $p$ and a map $h$ on $[0,1]^2$, the **Bernstein approximation** is
--   $$
--   f(a, b) = \mathbb E_{\xi_a \sim \mathrm{Bin}(p,a),\ \xi_b \sim \mathrm{Bin}(p,b)}\, h(\xi_a/p, \xi_b/p) = \sum_{u=0}^p \sum_{v=0}^p \binom pu a^u (1-a)^{p-u} \binom pv b^v (1-b)^{p-v}\, h\big(\tfrac up, \tfrac vp\big),
--   $$
--   with independent binomial variables. Claim 4.1 lists its properties.
--
--   **Formalization Note** The binomial probabilities are written out, so the formula is a polynomial defined for all real $a, b$.
-- source:
--   Anagnostides–Daskalakis–Farina–Golowich–Sandholm–Zhang, The Complexity of Correlated Equilibria Beyond Normal-Form Games, arXiv:2605.17665 (held version of November 2, 2026, sha256 6aec500a…7820), proof of Theorem 4(i), p.20

import Mathlib

set_option autoImplicit false

namespace CEPolytopeHard

/-- The **bivariate Bernstein approximation** of a map `h` (Anagnostides–Daskalakis–Farina–Golowich–Sandholm–Zhang, *The Complexity of Correlated Equilibria Beyond Normal-Form Games*, arXiv:2605.17665, held version of November 2, 2026, sha256 6aec500a…7820, proof of Theorem 4(i), p.20:
"f_i(a, b) = E_{ξ_a∼Bin(p,a), ξ_b∼Bin(p,b)} h_i(ξ_a/p, ξ_b/p), where the binomial variables above
are independent"), written as the finite sum
`∑_{u, v = 0}^{p} C(p,u) a^u (1 − a)^{p−u} · C(p,v) b^v (1 − b)^{p−v} · h(u/p, v/p)`.

**Formalization Note** The binomial probabilities are written out, so the formula is defined (as a
polynomial) for all real `a, b`; for `a, b ∈ [0, 1]` it is the printed expectation. -/
noncomputable def bern (p : ℕ) (h : ℝ → ℝ → ℝ) (a b : ℝ) : ℝ :=
  ∑ u ∈ Finset.range (p + 1), ∑ v ∈ Finset.range (p + 1),
    ((p.choose u : ℝ) * a ^ u * (1 - a) ^ (p - u)) * ((p.choose v : ℝ) * b ^ v * (1 - b) ^ (p - v)) *
      h ((u : ℝ) / p) ((v : ℝ) / p)

end CEPolytopeHard


