-- Prove2me | Definitions.Def_SeqLoss_FixedFraction_Examples
-- name    : SeqLoss_FixedFraction_Examples
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T06:45:18.838396+00:00
-- url     : https://prove2.me/theorems/68a668f6-e2ec-46da-b8f5-080dccaef218
-- title:
--   Appendix B, p. 26 — the rules $\varphi^A$ (serial), $\varphi^B$, $\varphi^C$, $\varphi^D$ used to show the axioms independent
-- statement:
--   Four rules from Appendix B (p. 26), each of which is not a fixed-fraction rule; agents are indexed $1,\dots,n$ and $L=\ell_1+\dots+\ell_n$.
--
--   1. **The serial rule $\varphi^A$:** $\displaystyle \varphi^A_i(\ell)=\sum_{j\ge i}\frac{\ell_j}{j}$. Each loss $\ell_j$ is shared equally among the agents $1,\dots,j$; on elementary problems $\varphi^A_i(e_n)=1/n$.
--   2. **The rule $\varphi^B$:** it coincides with the serial rule on every elementary problem except $\varphi^B(e_3)=(\tfrac12,0,\tfrac12)$, and is extended to every problem by Proposition 1's formula $\varphi^B_i(\ell)=\sum_{j\ge i}\ell_j\,\varphi^B_i(e_j)$.
--   3. **The rule $\varphi^C$:** $\varphi^C(\ell)=(\ell_1+\ell_n,\ell_2,\dots,\ell_{n-1},0)$ for $n\ge 2$, and $\varphi^C(\ell_1)=(\ell_1)$ for $n=1$.
--   4. **The rule $\varphi^D$:** the fixed-fraction formula with a loss-dependent parameter,
--   $$\varphi^D(\ell)=(\lambda\ell_1+(1-\lambda)L,\lambda\ell_2,\dots,\lambda\ell_n),\qquad \lambda=\frac{L-\ell_1}{L},$$
--   and $\varphi^D(\ell)=0$ when $L=0$.
--
--   Each of them violates exactly one of the four axioms of Theorem 1, which shows that no axiom can be dropped.
--
--   **Formalization Note.** 0-based indices: in $\varphi^A$ the 0-based agent $j$ contributes $\ell_j/(j+1)$. The manuscript leaves $\varphi^C$ undefined for $n=1$ (its formula would need $\ell_1+\ell_1$ and a trailing $0$ at once) and $\varphi^D$ undefined at $L=0$; the readings $\varphi^C(\ell_1)=(\ell_1)$ and $\varphi^D(0)=0$ are the only allocations of those problems, so they are forced.
-- source:
--   Gudmundsson, Hougaard & Ko, Sharing Sequentially Triggered Losses: Automated Conflict Resolution Through Smart Contracts, accepted manuscript (2023), Management Science 70(3) 1773–1786, doi:10.1287/mnsc.2023.4772, Appendix B, p. 26

import Mathlib
import Definitions.Def_SeqLoss_FixedFraction_Setting

namespace SeqLoss.FixedFraction

/-- The serial rule `φ^A` (Appendix B, p. 26): `φ^A_i(ℓ) = ∑_{j ≥ i} ℓ_j / j` (1-based `j`;
0-based, agent `j` contributes `ℓ j / (j + 1)`). -/
noncomputable def serialRule (n : ℕ) (ℓ : Fin n → ℝ) : Fin n → ℝ :=
  fun i => ∑ j ∈ Finset.univ.filter (fun j : Fin n => i ≤ j), ℓ j / ((j.val : ℝ) + 1)

/-- The rule `φ^B` (Appendix B, p. 26): it agrees with the serial rule on every elementary problem
except `φ^B(e_3) = (1/2, 0, 1/2)`, and is extended to every problem by Proposition 1's formula
`φ^B_i(ℓ) = ∑_{j ≥ i} ℓ_j · φ^B_i(e_j)`. 0-based: the share of agent `i` in `e_{j+1}` is
`1 / (j + 1)`, except for `j = 2`, where it is `1/2, 0, 1/2` for `i = 0, 1, 2`. -/
noncomputable def serialRuleB (n : ℕ) (ℓ : Fin n → ℝ) : Fin n → ℝ :=
  fun i => ∑ j ∈ Finset.univ.filter (fun j : Fin n => i ≤ j),
    ℓ j * (if j.val = 2 then (if i.val = 1 then 0 else 1 / 2) else 1 / ((j.val : ℝ) + 1))

/-- The rule `φ^C` (Appendix B, p. 26): `φ^C(ℓ) = (ℓ_1 + ℓ_n, ℓ_2, …, ℓ_{n-1}, 0)` for `n ≥ 2`,
and `φ^C(ℓ_1) = (ℓ_1)` for `n = 1` (where the printed formula is undefined). -/
def ruleC (n : ℕ) (ℓ : Fin n → ℝ) : Fin n → ℝ :=
  fun i =>
    if n = 1 then ℓ i
    else if i.val = 0 then ℓ i + ℓ ⟨n - 1, by have := i.isLt; omega⟩
    else if i.val + 1 = n then 0
    else ℓ i

/-- The rule `φ^D` (Appendix B, p. 26): the fixed-fraction formula with the loss-dependent
parameter `λ = (L - ℓ_1) / L`, i.e. `φ^D(ℓ) = φ^{(L - ℓ_1)/L}(ℓ)`; for `L = 0` (where the
printed `λ` is undefined) `φ^D(ℓ) = 0`. -/
noncomputable def ruleD (n : ℕ) (ℓ : Fin n → ℝ) : Fin n → ℝ :=
  if h : 0 < n ∧ total ℓ ≠ 0 then
    fixedFraction ((total ℓ - ℓ ⟨0, h.1⟩) / total ℓ) n ℓ
  else 0

end SeqLoss.FixedFraction


