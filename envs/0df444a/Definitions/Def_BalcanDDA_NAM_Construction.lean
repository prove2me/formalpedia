-- Prove2me | Definitions.Def_BalcanDDA_NAM_Construction
-- name    : BalcanDDA_NAM_Construction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T06:17:33.580989+00:00
-- url     : https://prove2.me/theorems/54a53c5b-2d53-4b88-bf47-d386cf4aac14
-- title:
--   The shattered valuation profiles $v^{(\ell)}$ and the parameter vectors $\rho$ of the proof of Theorem 5.2
-- statement:
--   These are the two objects built in the proof of Theorem 5.2 (pp. 23–24). Let $n$ be the number of agents and $N=\lfloor n/2\rfloor$.
--
--   1. **The profiles $v^{(\ell)}$.** For $\varepsilon\in\mathbb R$ and $\ell\in[N]$, the profile $v^{(\ell)}$ assigns
--   $$v_i^{(\ell)}(1)=\begin{cases}1 & \text{if } i=\ell,\\ 0 & \text{otherwise,}\end{cases}\qquad v_i^{(\ell)}(2)=\begin{cases}\varepsilon & \text{if } i=N+\ell,\\ 0 & \text{otherwise,}\end{cases}$$
--   and value $0$ to every alternative beyond the second. So under $v^{(\ell)}$ agent $\ell$ values alternative 1 at $1$, agent $N+\ell$ values alternative 2 at $\varepsilon$, and all other values are $0$.
--   2. **The parameter vector of a bit vector.** For $b\in\{0,1\}^N$, the vector $\rho\in\{0,1\}^n$ is defined by: for every $\ell\in[N]$, if $b_\ell=0$ then $\rho[\ell]=0$ and $\rho[N+\ell]=1$, and if $b_\ell=1$ then $\rho[\ell]=1$ and $\rho[N+\ell]=0$. All other entries of $\rho$ (the last agent when $n$ is odd) are $0$.
--
--   The paper prints the condition for $v_i^{(\ell)}(2)=\varepsilon$ as "$\ell = n/2 + i$", which no $\ell\le n/2$ satisfies; its own $n=6$ example on p. 24 places $\varepsilon$ at $v^{(1)}_4(2)$, $v^{(2)}_5(2)$, $v^{(3)}_6(2)$, i.e. at $i=n/2+\ell$, which is the reading used here. The paper takes $n$ even ("without loss of generality"); with $N=\lfloor n/2\rfloor$ the same construction applies to odd $n$.
--
--   **Formalization Note** Indices are 0-based: `ℓ : Fin (n / 2)`, agents `Fin n`, alternatives `Fin m`; the paper's first and second alternatives are `0` and `1`. `profile n m ε ℓ` is $v^{(\ell)}$ and `paramOf n b` is $\rho$ for `b : Fin (n / 2) → Bool`, with `true` for the bit $1$. `n / 2` is natural-number division, $\lfloor n/2\rfloor$. Entries are defined by comparing index values (`(i : ℕ) = n / 2 + ℓ`), so no casts between `Fin` types are involved.
-- source:
--   Balcan et al., How Much Data Is Sufficient to Learn High-Performing Algorithms?, arXiv:1908.02894v4, pp. 23–24, proof of Theorem 5.2 (definition of v^(ℓ), the n = 6 example, and the definition of ρ ∈ {0,1}^n)

import Mathlib

namespace BalcanDDA.NAM

/-- The `ℓ`-th valuation profile `v^(ℓ)` of the proof of Theorem 5.2 (Balcan et al.,
arXiv:1908.02894v4, pp. 23–24), with `N = n / 2` and 0-based indices (`ℓ : Fin (n / 2)`,
agents `0, …, n-1`, alternatives `0, …, m-1`; the paper's first and second alternatives are
`0` and `1`). Agent `ℓ` values alternative `0` at `1`, agent `n / 2 + ℓ` values alternative
`1` at `ε`, and every other value is `0`. This reads the paper's condition "ℓ = n/2 + i" as
`i = n/2 + ℓ`, as the paper's own `n = 6` example on p. 24 does. -/
def profile (n m : ℕ) (ε : ℝ) (ℓ : Fin (n / 2)) : Fin n → Fin m → ℝ :=
  fun i j =>
    if (i : ℕ) = (ℓ : ℕ) ∧ (j : ℕ) = 0 then 1
    else if (i : ℕ) = n / 2 + (ℓ : ℕ) ∧ (j : ℕ) = 1 then ε
    else 0

/-- The NAM parameter vector `ρ ∈ {0,1}^n` built from a bit vector `b` in the proof of
Theorem 5.2 (p. 24), with `N = n / 2` and 0-based indices: for `ℓ < N`, if `b ℓ` then
`ρ[ℓ] = 1` and `ρ[N + ℓ] = 0`, otherwise `ρ[ℓ] = 0` and `ρ[N + ℓ] = 1`; every other entry
(the last agent when `n` is odd) is `0`. -/
def paramOf (n : ℕ) (b : Fin (n / 2) → Bool) : Fin n → ℝ :=
  fun i =>
    if h : (i : ℕ) < n / 2 then (if b ⟨i, h⟩ then 1 else 0)
    else if h' : (i : ℕ) < n / 2 + n / 2 then
      (if b ⟨(i : ℕ) - n / 2, by omega⟩ then 0 else 1)
    else 0

end BalcanDDA.NAM


