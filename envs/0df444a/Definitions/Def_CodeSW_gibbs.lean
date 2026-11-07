-- Prove2me | Definitions.Def_CodeSW_gibbs
-- name    : CodeSW_gibbs
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:24:43.021716+00:00
-- url     : https://prove2.me/theorems/dfb9188c-1c6b-4a4f-841c-7e3104a5d895
-- title:
--   The Gibbs distribution $\pi(x)\propto e^{-2\beta|hx|}$ and the bond probability $p=1-e^{-2\beta}$
-- statement:
--   The energy of a configuration $x\in\{0,1\}^n$ for the code with parity check matrix $h$ is $H(x)=2|hx|$, twice the number of violated checks. The corresponding **Gibbs distribution** at inverse temperature $\beta$ is
--   $$\pi(x)=\frac{e^{-2\beta|hx|}}{\sum_{y}e^{-2\beta|hy|}}.$$
--   The **bond probability** of the Code Swendsen-Wang algorithm is $p=1-e^{-2\beta}$.
--
--   The Gibbs distribution is the target of the sampling chain, and $p$ is the probability with which the chain keeps a satisfied check.
--
--   **Formalization Note** The normalizer is a finite sum of positive terms, so $\pi$ is a probability distribution for every real $\beta$.
-- source:
--   Hangleiter, Ju, Vazirani, Code Swendsen-Wang Dynamics, arXiv:2510.08446 (manuscript sha256 4e4abb5e…), §2.1.2, eqs. (4)–(5), p.11; §3.2, p.16; Algorithm 2, p.16

import Definitions.Def_CodeSW_kerA
open Matrix
noncomputable section

namespace CodeSW

/-- The **Gibbs distribution** of the code with parity check matrix `h ∈ {0,1}^{c×n}` at inverse
temperature `β`: `π(x) ∝ e^{−βH(x)}` with energy `H(x) = 2|hx|`, i.e.
`π(x) = e^{−2β|hx|} / ∑_y e^{−2β|hy|}` on `X = {0,1}^n`
(Hangleiter, Ju, Vazirani, *Code Swendsen-Wang Dynamics*, arXiv:2510.08446, manuscript sha256
4e4abb5e…, §2.1.2, eqs. (4)–(5), p.11; §3.2, p.16).

**Formalization Note** States are `Fin n → ZMod 2`; the normalizer is a finite sum of positive
terms, so `π` is a probability distribution for every real `β`. -/
def gibbs {c n : ℕ} (h : Matrix (Fin c) (Fin n) (ZMod 2)) (β : ℝ) (x : Fin n → ZMod 2) : ℝ :=
  Real.exp (-2 * β * hammingWeight (h *ᵥ x)) /
    ∑ y : Fin n → ZMod 2, Real.exp (-2 * β * hammingWeight (h *ᵥ y))

/-- The bond probability `p = 1 − e^{−2β}` of the Code SW algorithm
(arXiv:2510.08446, manuscript sha256 4e4abb5e…, Algorithm 2, p.16). -/
def bondProb (β : ℝ) : ℝ := 1 - Real.exp (-2 * β)

end CodeSW


