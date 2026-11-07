-- Prove2me | Definitions.Def_LaconicBarrier_TwoMsg
-- name    : LaconicBarrier_TwoMsg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:39:21.027378+00:00
-- url     : https://prove2.me/theorems/1f543360-1a6f-4409-84fe-3f10477f2cf3
-- title:
--   Families of two-message games and the advantage of a response oracle
-- statement:
--   A **family of two-message games** $\{(\mathcal D_x, c_0)\}_x$, indexed by strings $x$, has a common baseline $c_0 \in [0,1)$. On index $x$ and parameter $\lambda$ the challenger draws coins $\rho$, sends a challenge, receives one response $a$ and wins according to a predicate of $(\lambda, x, \rho, a)$. Source challengers may be inefficient.
--
--   A source adversary is a possibly unbounded randomized **response oracle** $O$: for each challenge a distribution on responses. Its advantage at $(\lambda, x)$ is
--   $$
--   \mathrm{Adv}_{(\mathcal D_x, c_0)}(O;\lambda) = \max\bigl\{0,\ \Pr[O \text{ wins } \mathcal D_x(1^\lambda)] - c_0\bigr\}.
--   $$
--   For the soundness game of an argument this is the non-adaptive soundness advantage at $(\lambda, x)$.
-- source:
--   Jain, Mathialagan, Roy, From Succinct Arguments to Proofs: Lower Bounds for Obfuscation and SNARGs, STOC 2027 submission (manuscript sha256 1af78662…), Definition 4.5, p.15; §4.1.6, p.20

import Mathlib

namespace LaconicBarrier

/-- An indexed family `{(D_x, c₀)}_x` of **two-message games** (Jain, Mathialagan, Roy, STOC 2027
submission (manuscript sha256 1af78662…), Definition 4.5, p.15 and §4.1.6, p.20: "the challenger
sends one challenge and receives one response"): on index `x` and parameter `λ` the challenger
samples coins `ρ`, sends the challenge `chal λ x ρ`, receives a response `a`, and wins iff
`wins λ x ρ a`; the common baseline is `c₀ ∈ [0, 1)`. Source challengers may be inefficient: no
running time is imposed. -/
structure TwoMsg where
  /-- the number of challenger coins at `(λ, x)` -/
  coins : ℕ → List Bool → ℕ
  /-- the challenge -/
  chal : (lam : ℕ) → (x : List Bool) → (Fin (coins lam x) → Bool) → List Bool
  /-- whether a response wins -/
  wins : (lam : ℕ) → (x : List Bool) → (Fin (coins lam x) → Bool) → List Bool → Bool
  /-- the baseline -/
  c₀ : ℝ
  c₀_nonneg : 0 ≤ c₀
  c₀_lt_one : c₀ < 1

/-- The **advantage** of a possibly unbounded randomized response oracle `O` (challenge ↦
distribution of the response) in the game `(D_x, c₀)` at `λ` (Jain, Mathialagan, Roy, STOC 2027
submission (manuscript sha256 1af78662…), Definitions 4.1, 4.5, p.15; §4.1.2, p.16: "its advantage
in the game `(C_x, c₀)` is its non-adaptive soundness advantage at `(λ, x)`"):
`max{0, Pr[O wins D_x(1^λ)] − c₀}`. -/
noncomputable def TwoMsg.adv (S : TwoMsg) (lam : ℕ) (x : List Bool)
    (O : List Bool → PMF (List Bool)) : ℝ :=
  max 0 ((((PMF.uniformOfFintype (Fin (S.coins lam x) → Bool)).bind fun ρ =>
    (O (S.chal lam x ρ)).map fun a => S.wins lam x ρ a) true).toReal - S.c₀)

end LaconicBarrier


