-- Prove2me | Definitions.Def_MultitaskContracts_separable
-- name    : MultitaskContracts_separable
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T22:30:47.313625+00:00
-- url     : https://prove2.me/theorems/f84877e8-ff94-4e75-ab2d-e1d44752dcf9
-- title:
--   Separable contracts $t(Y)=t_0+\sum_{k\in Y}t_k$
-- statement:
--   A contract $t:2^K\to\mathbb R$ is **separable** if it pays a fixed amount $t_0\ge0$ plus an additive payment $t_k\ge0$ for success on every task $k$, regardless of the outcomes of the other tasks:
--   $$t(Y)=t_0+\sum_{k\in Y}t_k. \tag{8}$$
--   Separable contracts correspond to contracting each task separately; they are the benchmark that quantifies the value of bundling.
--
--   **Formalization Note** A function `Finset K → ℝ` is separable when some $t_0\ge0$ and $(t_k)_{k\in K}\ge0$ represent it as in (8); the representation is unique ($t_0=t(\emptyset)$, $t_k=t(\{k\})-t_0$).
-- source:
--   Saig, Talgam-Cohen, Tolkowsky, Multitask Contracts: Realizing the Value of Bundling, STOC 2027 submission (held version, sha256 e991a51a…), §2, eq. (8), p.8 (PDF p.10)

import Mathlib

set_option autoImplicit false

namespace MultitaskContracts

open scoped ENNReal

/-- The class of **separable contracts** (eq. (8), §2, p.8, PDF 10): `t` pays a fixed amount
`t₀ ≥ 0` plus an additive payment `t_k ≥ 0` for success on every task `k`,
`t(Y) = t₀ + ∑_{k ∈ Y} t_k`. E. Saig, I. Talgam-Cohen, Y. Tolkowsky, *Multitask Contracts: Realizing the Value of Bundling*,
STOC 2027 submission (held version, sha256 e991a51a…), §2, p.8, eq. (8).

**Formalization Note.** A contract is a function `Finset K → ℝ`; it is separable when some
`t₀ ≥ 0` and `t_k ≥ 0` represent it (the representation is unique: `t₀ = t(∅)`). -/
def separable (K : Type*) [Fintype K] [DecidableEq K] : Set (Finset K → ℝ) :=
  {t | ∃ (t₀ : ℝ) (tk : K → ℝ), 0 ≤ t₀ ∧ (∀ k, 0 ≤ tk k) ∧ ∀ Y, t Y = t₀ + ∑ k ∈ Y, tk k}

end MultitaskContracts


