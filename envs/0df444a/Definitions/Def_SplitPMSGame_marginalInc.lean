-- Prove2me | Definitions.Def_SplitPMSGame_marginalInc
-- name    : SplitPMSGame_marginalInc
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:13:00.810784+00:00
-- url     : https://prove2.me/theorems/6adb04b7-b952-4168-a9c0-fba29416c6b5
-- title:
--   Marginal increments $\Delta_j$, the counts $K_{J(S)}(j)$, and the CB requirement vectors
-- statement:
--   With the jobs indexed $1,\dots,\psi(N)$ in nondecreasing order of requirement and $p_0=0$, the **marginal increment** of job $j$ is $\Delta_j=p_j-p_{j-1}$. For a coalition $S$, $K_{J(S)}(j)$ is the number of jobs of $J(S)$ whose index is at least $j$. The $j$-th **constrained basic (CB) PMS game** $F^{(j)}$ has the same players, jobs and speeds and the $0$–$1$ requirement vector whose first $j-1$ entries are $0$ and the others $1$:
--   $$
--   F^{(j)}(J(S))=P_{(0,\dots,0,1,\dots,1)}(S).
--   $$
--
--   The PMS game is a nonnegative combination of the CB games (Lemma 1, Theorem 1).
--
--   **Formalization Note** Lean indices are 0-based: Lean job $j$ is the paper's $j+1$. $K$ counts indices $\ge j$, as the sentence after (4) and the proof of Lemma 1 do; the printed set $\ell^S(j)=\{\ell : j^S_{\ell-1}\le j<j^S_\ell\}$ would count indices $>j$, under which Lemma 1 fails (one player, one job, $p=1$, $v=1$).
-- source:
--   Alon, Anily, The Basic Core of a Parallel Machines Scheduling Game, MSOM 25(6) (2023), doi:10.1287/msom.2021.0337, §5, eq. (2), (4), p.2240 (PDF p.9); §5.1.1, pp.2241–2242 (PDF pp.10–11)

import Mathlib
import Definitions.Def_SplitPMSGame_pmsCost

namespace SplitPMSGame

/-- **Marginal increment** `Δⱼ = pⱼ − pⱼ₋₁` with `p₀ = 0` (Alon, Anily, *The Basic Core of a
Parallel Machines Scheduling Game*, MSOM 25(6) (2023), §5, p.2240).

**Formalization Note** Jobs are `Fin ψ`: the paper's job `j ∈ {1, …, ψ(N)}` is the index
`j − 1`, so `marginalInc p 0 = p 0 − 0` and `marginalInc p j = p j − p (j − 1)` for `j ≥ 1`. -/
def marginalInc {ψ : ℕ} (p : Fin ψ → ℝ) (j : Fin ψ) : ℝ :=
  p j - (if h : (j : ℕ) = 0 then 0 else p ⟨(j : ℕ) - 1, by omega⟩)

/-- **`K_{J(S)}(j)`** (MSOM 2023, eq. (4), p.2240): "the number of job players of `J(S)` whose
index in `J(N)` is at least as large as `j`".

**Formalization Note** This follows the sentence after (4) and the proof of Lemma 1. The
printed set `ℓ^S(j) = {ℓ : j^S_{ℓ−1} ≤ j < j^S_ℓ}` would count indices `> j`, which makes Lemma 1
false (one player, one job with `p = 1`, `v = 1`). Index `j` is the paper's `j + 1`. -/
def countFrom {N : Type*} [DecidableEq N] {ψ : ℕ} (f : Fin ψ → N) (S : Finset N) (j : Fin ψ) : ℕ :=
  ((jobsOf f S).filter (fun k => j ≤ k)).card

/-- **The requirement vector of the `j`-th CB game** (MSOM 2023, §5.1.1, pp.2241–2242): the
nondecreasing `0`–`1` vector whose first `j − 1` entries are `0` (paper index), i.e. job `k`
gets requirement `1` iff `k ≥ j`. The `j`-th constrained basic (CB) PMS game
`(J(N), 𝒞, F^(j))` is the PMS game with this requirement vector:
`F^(j)(J(S)) = pmsCost (basicReq j) f v S`.

**Formalization Note** Lean index `j` is the paper's `j + 1`. -/
def basicReq {ψ : ℕ} (j : Fin ψ) : Fin ψ → ℝ :=
  fun k => if j ≤ k then 1 else 0

end SplitPMSGame


