-- Prove2me | Definitions.Def_PolyEvalDS_LargeChar_Params
-- name    : PolyEvalDS_LargeChar_Params
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:48:43.433645+00:00
-- url     : https://prove2.me/theorems/0cba2797-2048-416c-949e-2958b62cc9ef
-- title:
--   The parameter ranges of Propositions 3.1, 3.2 and Theorems 1.1, 1.2
-- statement:
--   The index sets of the four datastructure statements, each exactly the hypotheses of its statement.
--
--   1. **Proposition 3.1** (p. 7): $p$ prime, $n,d,B$ positive integers, $p>d$.
--   2. **Proposition 3.2** (p. 7): $p$ prime, $n,d,B,r$ positive integers, $p>rd\ge2$.
--   3. **Theorem 1.1** (p. 8), for a threshold $d_0$: $p>2$ prime, $n,d$ positive integers, $d\ge d_0$.
--   4. **Theorem 1.2** (p. 9), for a threshold $d_0$: $p>2$ prime, $n,d$ positive integers, $d\ge d_0$, and a real $\varepsilon$ with $0<\varepsilon\le\frac12$.
--
--   **Formalization Note** $p$ is prime by the standing convention of §2, p. 5.
-- source:
--   Hiroki Okada, Rachel Player, Simon Pohmann, An Algebraic Polynomial Evaluation Datastructure for Fields of Large Characteristic, STOC 2027 submission #463 (October 2026), source.pdf SHA-256 33e2ace7597795eb2f5be3a68d2beb3fd8c69139336faf4559faf1452360646b, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/463.pdf, Propositions 3.1, 3.2, p. 7; Theorem 1.1, p. 8; Theorem 1.2, p. 9; §2, p. 5

import Mathlib

namespace PolyEvalDS.LargeChar

/-- The parameters of Proposition 3.1, p. 7: `p` prime, `n, d, B` positive, `p > d`. -/
structure Prop31Params where
  p : ℕ
  n : ℕ
  d : ℕ
  B : ℕ
  hp : p.Prime
  hn : 1 ≤ n
  hd : 1 ≤ d
  hB : 1 ≤ B
  hpd : d < p

/-- The parameters of Proposition 3.2, p. 7: `p` prime, `n, d, B, r` positive, `p > rd ≥ 2`. -/
structure Prop32Params where
  p : ℕ
  n : ℕ
  d : ℕ
  B : ℕ
  r : ℕ
  hp : p.Prime
  hn : 1 ≤ n
  hd : 1 ≤ d
  hB : 1 ≤ B
  hr : 1 ≤ r
  hrd : r * d < p
  hrd2 : 2 ≤ r * d

/-- The parameters of Theorem 1.1, p. 8: `p > 2` prime, `n, d` positive, `d` at least the
threshold `d₀`. -/
structure Thm11Params (d₀ : ℕ) where
  p : ℕ
  n : ℕ
  d : ℕ
  hp : p.Prime
  hp2 : 2 < p
  hn : 1 ≤ n
  hd : 1 ≤ d
  hd₀ : d₀ ≤ d

/-- The parameters of Theorem 1.2, p. 9: `p > 2` prime, `n, d` positive, `d` at least the
threshold `d₀`, and a real `ε` with `0 < ε ≤ 1/2`. -/
structure Thm12Params (d₀ : ℕ) where
  p : ℕ
  n : ℕ
  d : ℕ
  ε : ℝ
  hp : p.Prime
  hp2 : 2 < p
  hn : 1 ≤ n
  hd : 1 ≤ d
  hd₀ : d₀ ≤ d
  hε : 0 < ε
  hε2 : ε ≤ 1 / 2

end PolyEvalDS.LargeChar


