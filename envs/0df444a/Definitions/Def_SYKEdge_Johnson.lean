-- Prove2me | Definitions.Def_SYKEdge_Johnson
-- name    : SYKEdge_Johnson
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T13:05:40.909198+00:00
-- url     : https://prove2.me/theorems/459aa79a-de7f-4bd6-845a-85d105f05317
-- title:
--   Johnson scheme matrices $M_t(S,T)=\binom{|S\cap T|}t$, eigenvalues $\mu_{t,j}$ and $\lambda_j$, multiplicities $d_j$
-- statement:
--   On $\binom{[n]}k$ the **Johnson matrices** are $M_t(S,T)=\binom{|S\cap T|}{t}$, $0\le t\le k$. The following numbers describe their spectra and that of the dense sign matrix:
--   $$\mu_{t,j}=\begin{cases}\binom{k-j}{t-j}\binom{n-t-j}{k-t}&j\le t,\\0&j>t,\end{cases}\qquad \lambda_j=\binom nk^{-1}\sum_{t=j}^k(-2)^t\binom{k-j}{t-j}\binom{n-t-j}{k-t},$$
--   $$d_j=\binom nj-\binom n{j-1}\quad\Big(\binom n{-1}:=0\Big).$$
--   A permutation $\sigma$ of $[n]$ acts on $\psi\in\mathbb C^{\binom{[n]}k}$ by $(\sigma\cdot\psi)(S)=\psi(\sigma^{-1}(S))$.
--
--   These are the eigenvalue data of the Bose–Mesner algebra of the Johnson scheme, to which the dense sign matrix belongs.
--
--   **Formalization Note** Binomial coefficients vanish when the lower index exceeds the upper one (the paper's convention). The natural-number subtractions occur only for $j\le t\le k$ and $2k\le n$, where they are exact; $d_j$ is written with an explicit case at $j=0$, and its subtraction is exact for $j\le n/2$, which covers every use. For $j>k$ the sum defining $\lambda_j$ is empty and $\lambda_j=0$.
-- source:
--   Basu, Kothari, Midha, Sharp Bounds on Ground State Energy of the SYK Model, arXiv:2607.27185v2, 'The Johnson Scheme' and Fact 3.1, p.16; eq. (27), p.33; d_j, p.34

import Mathlib
import Definitions.Def_SYKEdge_Majorana

namespace SYKEdge

/-!
# The Johnson scheme matrices `M_t`, the eigenvalues `μ_{t,j}`, `λ_j` and multiplicities `d_j`

A. Basu, P. K. Kothari, S. Midha, *Sharp Bounds on Ground State Energy of the SYK Model*,
arXiv:2607.27185v2, "The Johnson Scheme" and Fact 3.1, p.16; (27), p.33; `d_j`, p.34.

**Formalization Note.**
* `johnsonM n k t = M_t ∈ ℂ^{([n] choose k)×([n] choose k)}`, `M_t(S,T) = (|S∩T| choose t)`.
* `muTJ n k t j = μ_{t,j} = (k−j choose t−j)(n−t−j choose k−t)` for `j ⩽ t`, `0` for `j > t`.
* `lamJ n k j = λ_j = (n choose k)^{−1} Σ_{t=j}^{k} (−2)^t (k−j choose t−j)(n−t−j choose k−t)`, (27);
  for `j > k` the sum is empty and `λ_j = 0`.
* `dJ n j = d_j = (n choose j) − (n choose j−1)` with `(n choose −1) := 0`, written with an explicit
  case at `j = 0` so that `n choose (j−1)` is never read at `j = 0`.
* Binomials are `Nat.choose`, which is `0` when the lower index exceeds the upper one, matching the
  page's convention (p.15). The `ℕ` subtractions `k−j`, `t−j`, `k−t`, `n−t−j` occur only for
  `j ⩽ t ⩽ k`; in every statement of the mission `2k ⩽ n`, so `n−t−j` is exact. `dJ`'s truncated
  subtraction is exact for `j ⩽ n/2`, where `(n choose j)` is nondecreasing in `j`, which covers every
  use (`j ⩽ k ⩽ n/2`).
* `permAct σ ψ` is the action `(σ·ψ)(S) := ψ(σ^{−1}(S))` of `σ ∈ S_n` on `ℂ^{([n] choose k)}`
  (Fact 3.1 (3)).
-/

/-- The Johnson matrix `M_t(S,T) := (|S∩T| choose t)` on `([n] choose k)` (p.16). -/
def johnsonM (n k t : ℕ) : Matrix (KSet n k) (KSet n k) ℂ :=
  fun S T => (((S.1 ∩ T.1).card.choose t : ℕ) : ℂ)

/-- `μ_{t,j} := (k−j choose t−j)(n−t−j choose k−t)` for `j ⩽ t`, `0` for `j > t` (Fact 3.1). -/
def muTJ (n k t j : ℕ) : ℕ :=
  if j ≤ t then (k - j).choose (t - j) * (n - t - j).choose (k - t) else 0

/-- `λ_j := (n choose k)^{−1} Σ_{t=j}^{k} (−2)^t (k−j choose t−j)(n−t−j choose k−t)`, (27). -/
noncomputable def lamJ (n k j : ℕ) : ℝ :=
  ((n.choose k : ℕ) : ℝ)⁻¹ *
    ∑ t ∈ Finset.Icc j k,
      (-2 : ℝ) ^ t * (((k - j).choose (t - j) : ℕ) : ℝ) * (((n - t - j).choose (k - t) : ℕ) : ℝ)

/-- `d_j := (n choose j) − (n choose j−1)`, with `(n choose −1) := 0` (Fact 3.1 (1), p.34). -/
def dJ (n j : ℕ) : ℕ :=
  n.choose j - (if j = 0 then 0 else n.choose (j - 1))

/-- The action `(σ·ψ)(S) := ψ(σ^{−1}(S))` of a permutation of the modes on `ℂ^{([n] choose k)}`. -/
def permAct {n k : ℕ} (σ : Equiv.Perm (Fin n)) (ψ : KSet n k → ℂ) : KSet n k → ℂ :=
  fun S => ψ ⟨S.1.map σ.symm.toEmbedding, by rw [Finset.card_map]; exact S.2⟩

end SYKEdge


