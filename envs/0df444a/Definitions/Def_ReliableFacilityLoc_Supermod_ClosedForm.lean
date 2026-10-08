-- Prove2me | Definitions.Def_ReliableFacilityLoc_Supermod_ClosedForm
-- name    : ReliableFacilityLoc_Supermod_ClosedForm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T01:14:19.107869+00:00
-- url     : https://prove2.me/theorems/b92c1223-d0f3-4094-b16c-28b744c99418
-- title:
--   A.3: the quantities $\bar n$, $s$, $t$, $P_k$ and $C_k$ of the proof of Proposition 3
-- statement:
--   Let $S = \{j_1, j_2, \dots, j_n\}$ be a set of regular facilities listed in nondecreasing order of distance to customer $i$, $d_{ij_1} \le d_{ij_2} \le \dots \le d_{ij_n}$. The proof of Proposition 3 uses the following quantities.
--
--   1. For a threshold $x$, the number of listed facilities with $d_{ij_k} \le x$. With $x = \varphi_i$ this is $\bar n$, the number of facilities of $S$ no farther than the penalty; with $x = d_{iu}$ it is $s$, and with $x = d_{iv}$ it is $t$.
--   2. The products of failure probabilities $P_0 = 1$ and $P_k = \prod_{\ell=1}^{k} q_{j_\ell}$.
--   3. The cost terms
--   $$
--   C_k = \begin{cases} P_{k-1}(1-q_{j_k})\, d_{ij_k}, & 1 \le k \le \bar n,\\ P_{\bar n}\, \varphi_i, & k = \bar n + 1.\end{cases}
--   $$
--
--   $C_k$ is the expected cost contributed by the $k$-th closest facility when the customer is assigned level by level to $j_1, \dots, j_{\bar n}$ and then to the emergency facility, and $\sum_{k=1}^{\bar n+1} C_k$ is the expected transportation-plus-penalty cost of that assignment.
--
--   **Formalization Note** The list is a Lean `List (Fin J)`, and $j_k$ is its $(k-1)$-th entry. The paper prints $\bar n = \inf\{1 \le k \le n : d_{ij_k} \le \varphi_i\}$ (and likewise $s$, $t$); the proof uses these as counts (the largest such $k$, or $0$), which is what is defined. $P_k$ is defined for every $k$ and $C_k = 0$ outside $1 \le k \le \bar n + 1$; statements use them only in the paper's range.
-- source:
--   Cui, Ouyang, Shen, Reliable Facility Location Design under the Risk of Disruptions, UCTC-FR-2010-02 (Feb. 2010), p. 35 (PDF 37), Appendix A.3, definitions of n̄, s, t, P_k, C_k

import Mathlib

namespace ReliableFacilityLoc.Supermod

/-- The number of entries `j` of the list `L` with `d j ≤ x`.

This is the paper's `n̄` (with `x = φ_i`), `s` (with `x = d_iu`) and `t` (with `x = d_iv`) of the
proof of Proposition 3 (Cui, Ouyang & Shen, UCTC-FR-2010-02 (Feb. 2010), Appendix A.3, p. 35,
PDF 37), where `L = [j_1, …, j_n]` lists `S` in nondecreasing order of distance.

Formalization Note: the paper prints `n̄ = inf{1 ≤ k ≤ n : d_{ij_k} ≤ φ_i}` (and likewise `s`, `t`).
Read literally, this is `1` whenever some element qualifies; the proof uses `n̄` as the number of
elements of `S` within `φ_i` (the largest such `k`, or `0` if there is none), which, for a sorted
list, is the count formalized here. -/
noncomputable def countLE {J : ℕ} (d : Fin J → ℝ) (x : ℝ) (L : List (Fin J)) : ℕ :=
  L.countP (fun j => d j ≤ x)

/-- `P_k = Π_{ℓ=1}^{k} q_{j_ℓ}`, with `P_0 = 1` (UCTC-FR-2010-02, A.3, p. 35, PDF 37), the product
of the failure probabilities of the first `k` entries of `L = [j_1, …, j_n]`.

Formalization Note: the paper defines `P_k` only for `0 ≤ k ≤ n̄`; the formula here is total, and
every statement uses it only at indices `≤ n̄`. -/
def prodQ {J : ℕ} (q : Fin J → ℝ) (L : List (Fin J)) (k : ℕ) : ℝ :=
  ((L.take k).map q).prod

/-- `C_k` of the proof of Proposition 3 (UCTC-FR-2010-02, A.3, p. 35, PDF 37), for the list
`L = [j_1, …, j_n]` (1-based in the paper):
`C_k = P_{k−1}(1 − q_{j_k}) d_{ij_k}` for `1 ≤ k ≤ n̄`, and `C_{n̄+1} = P_{n̄} φ_i`,
where `n̄ = countLE d φ_i L`.

Formalization Note: `j_k` is the `(k−1)`-th entry of `L` (0-based Lean indexing). The paper leaves
`C_k` undefined for `k = 0` and `k > n̄ + 1`; the value `0` is used there, and every statement sums
`C_k` only over `k ∈ {1, …, n̄ + 1}`. -/
noncomputable def Ck {J : ℕ} (d : Fin J → ℝ) (phi : ℝ) (q : Fin J → ℝ) (L : List (Fin J))
    (k : ℕ) : ℝ :=
  if k = countLE d phi L + 1 then prodQ q L (countLE d phi L) * phi
  else if 1 ≤ k ∧ k ≤ countLE d phi L then
    prodQ q L (k - 1) * (L.map (fun j => (1 - q j) * d j)).getD (k - 1) 0
  else 0

end ReliableFacilityLoc.Supermod


