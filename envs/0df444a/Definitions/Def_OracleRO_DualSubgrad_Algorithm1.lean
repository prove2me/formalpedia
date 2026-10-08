-- Prove2me | Definitions.Def_OracleRO_DualSubgrad_Algorithm1
-- name    : OracleRO_DualSubgrad_Algorithm1
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T08:46:48.31563+00:00
-- url     : https://prove2.me/theorems/331e5b50-3ebd-4a2a-b41a-48ecc83971f9
-- title:
--   Algorithm 1 — Dual-Subgradient Robust Optimization: iterates, output and number of oracle calls
-- statement:
--   Fix a projection $P$ onto $\mathcal U$, a gradient map $\nabla_u f_i(x,u)$ (written $\mathrm{grad}_i(x,u)$), an oracle $\mathcal O$, parameters $\epsilon, D, G$, an initial dual point $(u^0_1,\dots,u^0_m)$ and an initial primal point $x^0$. Algorithm 1 sets
--
--   $$
--   T=\left\lceil \frac{G^2D^2}{\epsilon^2}\right\rceil,\qquad \eta=\frac{D}{G\sqrt T},
--   $$
--
--   and for $t=1,\dots,T$ performs the dual update and the oracle call
--
--   $$
--   u^t_i=P\bigl(u^{t-1}_i+\eta\,\nabla_u f_i(x^{t-1},u^{t-1}_i)\bigr)\ (i=1,\dots,m),\qquad x^t=\mathcal O(u^t_1,\dots,u^t_m).
--   $$
--
--   If the oracle declares infeasibility in some round $t\le T$, the algorithm stops and returns "infeasible"; otherwise it returns the average $\bar x=\frac1T\sum_{t=1}^T x^t$. The number of oracle calls is the first round in which the oracle declares infeasibility, or $T$ if it never does.
--
--   These objects make Theorem 3 a statement about one explicitly defined run of the algorithm.
--
--   **Formalization Note** Rounds are indexed by natural numbers, index $0$ being the initialisation. The algorithm never defines $x^0$ (it is used by the first update); it is an input. The state recursion is total: after a round in which the oracle answers `none`, it continues with $x^t:=x^0$; those rounds are never executed by the algorithm and affect neither the output nor the call count. The output is `none` for "infeasible" and `some` $\bar x$ otherwise.
-- source:
--   Ben-Tal, Hazan, Koren, Mannor, Oracle-Based Robust Optimization via Online Learning, arXiv:1402.6361v1, p. 7, Algorithm 1

import Mathlib

namespace OracleRO.DualSubgrad

/-- The number of rounds of Algorithm 1 (p. 7): `T = ⌈G²D²/ε²⌉`. -/
noncomputable def alg1T (G D ε : ℝ) : ℕ :=
  ⌈G ^ 2 * D ^ 2 / ε ^ 2⌉₊

/-- The step size of Algorithm 1 (p. 7): `η = D / (G √T)` with `T = ⌈G²D²/ε²⌉`. -/
noncomputable def alg1Eta (G D ε : ℝ) : ℝ :=
  D / (G * Real.sqrt (alg1T G D ε))

/-- The state `(u^t, x^t)` of Algorithm 1 (p. 7) after round `t` (index 0 is the initialisation
`(u⁰, x⁰)`). Round `t + 1` makes the dual update
`u^{t+1}_i = P(u^t_i + η ∇_u f_i(x^t, u^t_i))` for every `i` and then calls the oracle:
`x^{t+1} = O(u^{t+1})`. When the oracle answers "infeasible" (`none`) the algorithm stops; the
recursion then carries `x⁰` along so that it stays total, and those later rounds are never used. -/
noncomputable def alg1State {m n d : ℕ}
    (gradU : Fin m → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin d) →
      EuclideanSpace ℝ (Fin d))
    (P : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (O : (Fin m → EuclideanSpace ℝ (Fin d)) → Option (EuclideanSpace ℝ (Fin n)))
    (η : ℝ) (u0 : Fin m → EuclideanSpace ℝ (Fin d)) (x0 : EuclideanSpace ℝ (Fin n)) :
    ℕ → (Fin m → EuclideanSpace ℝ (Fin d)) × EuclideanSpace ℝ (Fin n)
  | 0 => (u0, x0)
  | t + 1 =>
    let s := alg1State gradU P O η u0 x0 t
    let u' : Fin m → EuclideanSpace ℝ (Fin d) := fun i => P (s.1 i + η • gradU i s.2 (s.1 i))
    (u', (O u').getD x0)

/-- The dual iterate `u^t = (u^t_1, …, u^t_m)` of Algorithm 1 with its own parameters
`T = ⌈G²D²/ε²⌉` and `η = D/(G√T)`. -/
noncomputable def alg1U {m n d : ℕ}
    (gradU : Fin m → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin d) →
      EuclideanSpace ℝ (Fin d))
    (P : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (O : (Fin m → EuclideanSpace ℝ (Fin d)) → Option (EuclideanSpace ℝ (Fin n)))
    (G D ε : ℝ) (u0 : Fin m → EuclideanSpace ℝ (Fin d)) (x0 : EuclideanSpace ℝ (Fin n))
    (t : ℕ) : Fin m → EuclideanSpace ℝ (Fin d) :=
  (alg1State gradU P O (alg1Eta G D ε) u0 x0 t).1

/-- The primal iterate `x^t` of Algorithm 1 (the oracle's answer in round `t ≥ 1`; `x⁰` at
`t = 0`) with its own parameters `T = ⌈G²D²/ε²⌉` and `η = D/(G√T)`. -/
noncomputable def alg1X {m n d : ℕ}
    (gradU : Fin m → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin d) →
      EuclideanSpace ℝ (Fin d))
    (P : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (O : (Fin m → EuclideanSpace ℝ (Fin d)) → Option (EuclideanSpace ℝ (Fin n)))
    (G D ε : ℝ) (u0 : Fin m → EuclideanSpace ℝ (Fin d)) (x0 : EuclideanSpace ℝ (Fin n))
    (t : ℕ) : EuclideanSpace ℝ (Fin n) :=
  (alg1State gradU P O (alg1Eta G D ε) u0 x0 t).2

open Classical in
/-- The output of Algorithm 1 (p. 7): `none` ("infeasible") if the oracle declares
infeasibility in some round `t ∈ {1, …, T}`, and otherwise `some x̄` with
`x̄ = (1/T) ∑_{t=1}^T x^t`. -/
noncomputable def alg1Output {m n d : ℕ}
    (gradU : Fin m → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin d) →
      EuclideanSpace ℝ (Fin d))
    (P : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (O : (Fin m → EuclideanSpace ℝ (Fin d)) → Option (EuclideanSpace ℝ (Fin n)))
    (G D ε : ℝ) (u0 : Fin m → EuclideanSpace ℝ (Fin d)) (x0 : EuclideanSpace ℝ (Fin n)) :
    Option (EuclideanSpace ℝ (Fin n)) :=
  if ∃ t ∈ Finset.Icc 1 (alg1T G D ε), O (alg1U gradU P O G D ε u0 x0 t) = none then none
  else some ((1 / (alg1T G D ε : ℝ)) •
    ∑ t ∈ Finset.Icc 1 (alg1T G D ε), alg1X gradU P O G D ε u0 x0 t)

open Classical in
/-- The number of oracle calls Algorithm 1 makes (one per executed round): the first round
`t ∈ {1, …, T}` in which the oracle declares infeasibility, or `T` if it never does. -/
noncomputable def alg1Calls {m n d : ℕ}
    (gradU : Fin m → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin d) →
      EuclideanSpace ℝ (Fin d))
    (P : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (O : (Fin m → EuclideanSpace ℝ (Fin d)) → Option (EuclideanSpace ℝ (Fin n)))
    (G D ε : ℝ) (u0 : Fin m → EuclideanSpace ℝ (Fin d)) (x0 : EuclideanSpace ℝ (Fin n)) : ℕ :=
  if h : ∃ t, 1 ≤ t ∧ t ≤ alg1T G D ε ∧ O (alg1U gradU P O G D ε u0 x0 t) = none then
    Nat.find h
  else alg1T G D ε

end OracleRO.DualSubgrad


