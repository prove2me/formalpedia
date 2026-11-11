-- Prove2me | Definitions.Def_CorrBoundsPoly_ExactDegree_RandomWalk
-- name    : CorrBoundsPoly_ExactDegree_RandomWalk
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T15:57:17.312988+00:00
-- url     : https://prove2.me/theorems/f8f55568-7a54-4a71-90e2-2557e3954756
-- title:
--   Lemma 3.8 — simple symmetric random walk and the survival probability $\mathbb P(\tau_D>m)$
-- statement:
--   Let $S_0=0$ and $S_t=\varepsilon_1+\dots+\varepsilon_t$ with independent uniform steps $\varepsilon_i\in\{\pm1\}$ (the **simple symmetric random walk** on $\mathbb Z$ from $0$), and let $\tau_D=\inf\{t\ge0:|S_t|=D\}$. The event $\{\tau_D>m\}$ is $\{|S_t|\ne D\text{ for all }0\le t\le m\}$ and depends only on the first $m$ steps, whose law is uniform on $\{\pm1\}^m$. Hence
--   $$\mathbb P(\tau_D>m)=2^{-m}\,\#\big\{\varepsilon\in\{\pm1\}^m:\ |S_t|\ne D\ \text{for all }0\le t\le m\big\}.$$
--
--   This survival probability is the random-walk form of the exact correlation $\eta(m,D)$ (Lemma 3.8).
--
--   **Formalization Note** A step sequence is `ε : Fin m → Bool` (`true` is $+1$, `false` is $-1$); `walk ε t = ∑_{i < t} ε_i` in `ℤ` (so `walk ε 0 = 0`). `survival D m` is the number of `ε` with `|walk ε t| ≠ D` for all `t ≤ m`, divided by `2^m`: the law of the first `m` steps of the walk.
-- source:
--   Xin Li, More on Correlation Bounds for Polynomials, STOC 2027 submission (manuscript sha256 aa4ef6f7…), Lemma 3.8, p. 29 (PDF 31)

import Mathlib

namespace CorrBoundsPoly.ExactDegree

/-! Xin Li, *More on Correlation Bounds for Polynomials*, STOC 2027 submission (manuscript sha256
aa4ef6f7…), Lemma 3.8, p. 29 (PDF 31).

The simple symmetric random walk `S_0 = 0`, `S_t = ε_1 + ⋯ + ε_t` with independent uniform
steps `ε_i ∈ {±1}`, its exit time `τ_D = inf{t ≥ 0 : |S_t| = D}`, and the survival probability
`P(τ_D > m)`. -/

/-- The walk after `t` of the steps `ε ∈ {±1}^m` (step `i` is `+1` when `ε i = true`, `−1`
otherwise): `S_t = ∑_{i < t} ε_i`; `S_0 = 0`. -/
def walk {m : ℕ} (ε : Fin m → Bool) (t : ℕ) : ℤ :=
  ∑ i : Fin m, if i.val < t then (if ε i then (1 : ℤ) else -1) else 0

/-- `P(τ_D > m)`. The event `τ_D > m` is `|S_t| ≠ D` for every `0 ≤ t ≤ m`; it depends only on the
first `m` steps, whose law is uniform on `{±1}^m`. So
`P(τ_D > m) = 2^{−m} · #{ε ∈ {±1}^m : |S_t| ≠ D for all t ≤ m}`. -/
noncomputable def survival (D m : ℕ) : ℝ :=
  ((Finset.univ.filter fun ε : Fin m → Bool => ∀ t : ℕ, t ≤ m → |walk ε t| ≠ (D : ℤ)).card : ℝ) /
    2 ^ m

end CorrBoundsPoly.ExactDegree


