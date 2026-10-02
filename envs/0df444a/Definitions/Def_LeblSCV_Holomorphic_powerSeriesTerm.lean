-- Prove2me | Definitions.Def_LeblSCV_Holomorphic_powerSeriesTerm
-- name    : LeblSCV_Holomorphic_powerSeriesTerm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T02:01:57.563976+00:00
-- url     : https://prove2.me/theorems/4617e347-f3ae-4033-b0d3-557da2c4d885
-- title:
--   Power series terms $c_\alpha (z-a)^\alpha$ and uniform absolute convergence
-- statement:
--   A power series in $n$ variables centered at $a \in \mathbb{C}^n$ has coefficients $c_\alpha \in \mathbb{C}$ indexed by multi-indices $\alpha \in \mathbb{N}_0^n$, and terms
--   $$c_\alpha (z - a)^\alpha = c_\alpha (z_1 - a_1)^{\alpha_1} (z_2 - a_2)^{\alpha_2} \cdots (z_n - a_n)^{\alpha_n}.$$
--   Since $\mathbb{N}_0^n$ has no natural ordering, the series $\sum_\alpha c_\alpha (z-a)^\alpha$ is understood as an absolutely convergent (order-independent) sum. The series **converges uniformly absolutely** for $z \in X$ when $\sum_\alpha |c_\alpha (z-a)^\alpha|$ converges uniformly for $z \in X$.
--
--   **Formalization Note.** `powerSeriesTerm c a α z` is the term $c_\alpha (z-a)^\alpha$, with `c : (Fin n → ℕ) → ℂ`. `ConvergesUniformlyAbsolutelyOn c a X` states that the partial sums $\sum_{\alpha \in s} |c_\alpha (z-a)^\alpha|$ over finite sets $s$ of multi-indices, directed by inclusion, converge uniformly on $X$ to some limit function. For series of nonnegative terms this is equivalent to uniform convergence of the partial sums along any enumeration of $\mathbb{N}_0^n$. The sum itself is expressed in the theorems with `HasSum` (unconditional convergence), never with a default-valued `tsum`.
-- source:
--   Lebl, Tasty Bits of Several Complex Variables, version 4.4 (2026), pp. 18–20 (multi-index notation; power series; definition of uniform absolute convergence, p. 20)

import Mathlib

open Filter

namespace LeblSCV.Holomorphic

/-- The term `c_α (z - a)^α = c_α (z_1 - a_1)^{α_1} ⋯ (z_n - a_n)^{α_n}` of a power series in `n`
variables centered at `a` (Lebl, pp. 18–20), for a multi-index `α ∈ ℕ₀ⁿ` (here `Fin n → ℕ`). -/
def powerSeriesTerm {n : ℕ} (c : (Fin n → ℕ) → ℂ) (a : Fin n → ℂ) (α : Fin n → ℕ)
    (z : Fin n → ℂ) : ℂ :=
  c α * ∏ k : Fin n, (z k - a k) ^ α k

/-- Uniform absolute convergence (Lebl, p. 20): the power series `∑_α c_α (z - a)^α` converges
uniformly absolutely for `z ∈ X` when `∑_α |c_α (z - a)^α|` converges uniformly for `z ∈ X`.
The sum over `α ∈ ℕ₀ⁿ` has no natural order, so its partial sums are the sums over finite sets
of multi-indices, directed by inclusion; "converges uniformly on `X`" means these partial sums
converge uniformly on `X` to some limit function. -/
def ConvergesUniformlyAbsolutelyOn {n : ℕ} (c : (Fin n → ℕ) → ℂ) (a : Fin n → ℂ)
    (X : Set (Fin n → ℂ)) : Prop :=
  ∃ S : (Fin n → ℂ) → ℝ,
    TendstoUniformlyOn (fun (s : Finset (Fin n → ℕ)) (z : Fin n → ℂ) =>
      ∑ α ∈ s, ‖powerSeriesTerm c a α z‖) S atTop X

end LeblSCV.Holomorphic


