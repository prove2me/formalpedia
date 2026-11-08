-- Prove2me | Definitions.Def_QWildMatch_dpCell
-- name    : QWildMatch_dpCell
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T10:18:04.157865+00:00
-- url     : https://prove2.me/theorems/7c6ccfb5-e6b6-445e-8656-31271c24a90f
-- title:
--   The truncated dynamic-programming table $F[i,u]$, its band, and the acceptance rule
-- statement:
--   Fix a start $s$ and let $w=T[s:\min(n,s+\ell))$ be the text suffix clipped at $n$. The table is given by $F[0,0]=0$ and
--
--   $$F[i,u]=\min\{F[i-1,u-1]+\mu(P[i-1],w[u-1]),\;F[i-1,u]+c_{\mathrm{del}}(P[i-1]),\;F[i,u-1]+c_{\mathrm{ins}}(w[u-1])\},$$
--
--   where out-of-range neighbours are $+\infty$ and every value is truncated at $k+1$. The table accepts when $F[m,u]\le k$ for at least one $0\le u\le\min(\ell,n-s)$. The banded table sets every cell outside $-r_-\le u-i\le r_+$ to $+\infty$ and accepts by the same rule.
--
--   **Formalization Note** The parameter `keep` selects the evaluated states: `keep = True` is the full table (`dpAccept`) and `keep = inBand` is the banded one (`bandAccept`). Truncation is a `min` with $k+1$ at each evaluated cell, so an out-of-range cell in the full table holds $k+1$ rather than $+\infty$, which still rejects. Band arithmetic is in $\mathbb Z$.
-- source:
--   Zhao, Chen, Li, Kong, Peng, Yu, Yue, Quantum Approximate Pattern Matching with Wildcards and Weighted Edits, STOC 2027 submission (file sha256 9e87a9dd…), §4, p.5; Theorem 4.1, p.5

import Mathlib
import Definitions.Def_QWildMatch_Match

namespace QWildMatch

/-- The diagonal edge cost `μ(P[i], w[u])`; `+∞` for an out-of-range neighbour (Zhao et al., STOC 2027
submission (file sha256 9e87a9dd…), §4, p.5). -/
noncomputable def diagCost {Sym : Type} (cm : CostModel Sym) (P : List (Option Sym)) (w : List Sym)
    (i u : ℕ) : WithTop ℝ :=
  match P[i]?, w[u]? with
  | some a, some b => ((cm.μ a b : ℝ) : WithTop ℝ)
  | _, _ => ⊤

/-- The vertical edge cost `c_del(P[i])`; `+∞` when out of range (§4, p.5). -/
noncomputable def delCost {Sym : Type} (cm : CostModel Sym) (P : List (Option Sym)) (i : ℕ) :
    WithTop ℝ :=
  match P[i]? with
  | some a => ((cm.cdel a : ℝ) : WithTop ℝ)
  | none => ⊤

/-- The horizontal edge cost `c_ins(w[u])`; `+∞` when out of range (§4, p.5). -/
noncomputable def insCost {Sym : Type} (cm : CostModel Sym) (w : List Sym) (u : ℕ) : WithTop ℝ :=
  match w[u]? with
  | some b => ((cm.cins b : ℝ) : WithTop ℝ)
  | none => ⊤

open Classical in
/-- The table `F[i, u]` of §4, p.5 (Zhao et al., STOC 2027 submission): `F[0, 0] = 0` and
`F[i, u] = min{F[i−1, u−1] + μ(P[i−1], T[s+u−1]), F[i−1, u] + c_del(P[i−1]), F[i, u−1] + c_ins(T[s+u−1])}`,
with out-of-range neighbours `+∞` and every value truncated at `k + 1`, on the read word
`w = T[s : s + u_max)`.

**Formalization Note** The parameter `keep` selects the evaluated states: a cell with `¬ keep i u` is
`+∞`. `keep = True` is the full table and `keep = inBand` the banded one. Truncation is a `min` with
`k + 1` at every evaluated cell, as on the page; it can turn `+∞` into `k + 1`, which still rejects. -/
noncomputable def dpCell {Sym : Type} (cm : CostModel Sym) (P : List (Option Sym)) (w : List Sym)
    (k : ℝ) (keep : ℕ → ℕ → Prop) : ℕ → ℕ → WithTop ℝ
  | 0, 0 => if keep 0 0 then min (((k + 1 : ℝ)) : WithTop ℝ) 0 else ⊤
  | 0, u + 1 =>
    if keep 0 (u + 1) then
      min (((k + 1 : ℝ)) : WithTop ℝ) (dpCell cm P w k keep 0 u + insCost cm w u)
    else ⊤
  | i + 1, 0 =>
    if keep (i + 1) 0 then
      min (((k + 1 : ℝ)) : WithTop ℝ) (dpCell cm P w k keep i 0 + delCost cm P i)
    else ⊤
  | i + 1, u + 1 =>
    if keep (i + 1) (u + 1) then
      min (((k + 1 : ℝ)) : WithTop ℝ)
        (min (min (dpCell cm P w k keep i u + diagCost cm P w i u)
            (dpCell cm P w k keep i (u + 1) + delCost cm P i))
          (dpCell cm P w k keep (i + 1) u + insCost cm w u))
    else ⊤
termination_by i u => i + u

/-- The band of Theorem 4.1, `−r₋ ≤ u − i ≤ r₊` (Zhao et al., STOC 2027 submission, p.5), in integer
arithmetic. -/
def inBand {Sym : Type} [Fintype Sym] [Nonempty Sym] (cm : CostModel Sym) (k : ℝ) (i u : ℕ) : Prop :=
  -(rMinus cm k : ℤ) ≤ (u : ℤ) - (i : ℤ) ∧ (u : ℤ) - (i : ℤ) ≤ (rPlus cm k : ℤ)

noncomputable instance {Sym : Type} [Fintype Sym] [Nonempty Sym] (cm : CostModel Sym) (k : ℝ) (i u : ℕ) :
    Decidable (inBand cm k i u) := by
  unfold inBand
  infer_instance

/-- The acceptance rule of §4, p.5 (Zhao et al., STOC 2027 submission), for the table with state
selection `keep`: `F[m, u] ≤ k` for at least one `0 ≤ u ≤ min(ℓ, n − s)`, on the word
`T[s : min(n, s + ℓ))` (the text suffix clipped at `n`). -/
def dpAcceptWith {Sym : Type} [Fintype Sym] [Nonempty Sym] {n : ℕ} (cm : CostModel Sym)
    (P : List (Option Sym)) (T : Fin n → Sym) (k : ℝ) (s : ℕ) (keep : ℕ → ℕ → Prop) : Prop :=
  ∃ u : ℕ, u ≤ min (ell cm P k) (n - s) ∧
    dpCell cm P (sub T s (min n (s + ell cm P k))) k keep P.length u ≤ ((k : ℝ) : WithTop ℝ)

/-- Acceptance of the full table of §4, p.5. -/
def dpAccept {Sym : Type} [Fintype Sym] [Nonempty Sym] {n : ℕ} (cm : CostModel Sym)
    (P : List (Option Sym)) (T : Fin n → Sym) (k : ℝ) (s : ℕ) : Prop :=
  dpAcceptWith cm P T k s (fun _ _ => True)

/-- Acceptance of the banded table of Theorem 4.1, p.5: cells outside `−r₋ ≤ u − i ≤ r₊` are `+∞`. -/
def bandAccept {Sym : Type} [Fintype Sym] [Nonempty Sym] {n : ℕ} (cm : CostModel Sym)
    (P : List (Option Sym)) (T : Fin n → Sym) (k : ℝ) (s : ℕ) : Prop :=
  dpAcceptWith cm P T k s (inBand cm k)

end QWildMatch


