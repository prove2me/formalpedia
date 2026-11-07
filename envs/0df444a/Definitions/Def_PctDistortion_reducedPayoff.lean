-- Prove2me | Definitions.Def_PctDistortion_reducedPayoff
-- name    : PctDistortion_reducedPayoff
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:40:58.656396+00:00
-- url     : https://prove2.me/theorems/b673154c-f0d0-43e2-9113-9ddeb6e26264
-- title:
--   The reduced game on $C$, payoff (3)
-- statement:
--   With $\ell=sr+1$, arithmetic modulo $\ell$, and $\hat\nu=\nu(\mathcal G^{ABC}_H)$, the **reduced game** on $C$ lets Alice and Bob choose blocks $i,j\in\{0,\dots,\ell-1\}$, and Alice receives
--   $$p^{ABC}_A(i,j)=\begin{cases}1&\text{if } i=j=0,\\ \hat\nu&\text{if } i=j,\ i\ne 0,\\ -1&\text{if } i\in\{j+1,\dots,j+r\},\\ 1&\text{otherwise.}\end{cases}\tag{3}$$
--   Corollary 1 shows that these are Alice's block-level payoffs at an equilibrium of the ABC game on $G=C[P,H,\dots,H]$.
--
--   **Formalization Note** $\hat\nu$ is a real parameter; $i\in\{j+1,\dots,j+r\}$ is $1\le(i-j)\bmod\ell\le r$.
-- source:
--   Kizilkaya, Kalayci, Kempe, Micha, The Caccetta-Häggkvist Conjecture and Percentile Distortion: An Equivalence via Asymmetric Maximal Lotteries, STOC 2027 submission (held version, sha256 fd779dd0…), Corollary 1, eq. (3), p.14

import Mathlib

set_option autoImplicit false

namespace PctDistortion

/-- Alice's payoff (3) in the **reduced game on `C`**, `ℓ = s r + 1`, when Alice plays block `i`
and Bob plays block `j` (`ν̂ = νH`): `1` if `i = j = 0`; `ν̂` if `i = j ≠ 0`; `-1` if
`i ∈ {j + 1, …, j + r}` (mod `ℓ`); `1` otherwise.

Kizilkaya, Kalayci, Kempe, Micha, *The Caccetta-Häggkvist Conjecture and Percentile Distortion: An Equivalence via Asymmetric Maximal Lotteries*, STOC 2027 submission (held version, sha256 fd779dd0…), Corollary 1, eq. (3), p.14, and p.14: "We therefore define the reduced game on C, in which both
Alice and Bob play mixed strategies over {0, . . . , ℓ−1}, and Alice's payoff for the pair (i, j) of
pure strategies is given by Eq. (3)."

**Formalization Note.** `i ∈ {j + 1, …, j + r}` modulo `ℓ` is `1 ≤ (i − j) mod ℓ ≤ r`, with
subtraction in `Fin ℓ`. -/
def reducedPayoff (νH : ℝ) (s r : ℕ) (i j : Fin (s * r + 1)) : ℝ :=
  if i = j then (if i = 0 then 1 else νH)
  else if 1 ≤ (i - j).val ∧ (i - j).val ≤ r then -1 else 1

end PctDistortion


