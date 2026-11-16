-- Prove2me | Definitions.Def_MultiSelectPandora_Supplement_stValue
-- name    : MultiSelectPandora_Supplement_stValue
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:29:18.328348+00:00
-- url     : https://prove2.me/theorems/f7bd249b-3fc1-4d09-9bd7-a5792ab8a4df
-- title:
--   Expected utility of a state policy from a state
-- statement:
--   For a state policy $\pi$ and a state $(U,\alpha)$, the **expected utility** $u_\pi(U,\alpha)$ is computed recursively:
--
--   1. if $\pi$ stops, it is $\sum_{j=1}^k\alpha_j$;
--   2. if $\pi$ stops with box $i$ claimed closed, it is $\alpha_1+\dots+\alpha_{k-1}+\mathbb E[v_i]$;
--   3. if $\pi$ opens box $i$, it is
--   $$-c_i+\sum_{v}\Pr[v_i=v]\;u_\pi\big(U\setminus\{i\},\ \mathrm{top}_k(\alpha\cup\{v\})\big).$$
--
--   Costs paid before reaching $(U,\alpha)$ are not counted, as in §2.2. This is the objective that defines optimal policies of the subproblem $P(U,\alpha)$ with one closed claim.
--
--   **Formalization Note** The recursion runs on a fuel equal to $|U|$; expectations are finite sums over the support positions of each box; $\mathrm{top}_k(\alpha\cup\{v\})$ is the published `insertTop`, and $\alpha_1+\dots+\alpha_{k-1}$ is $\sum_j\alpha_j-\alpha_k$ with $\alpha_k$ the published `stFloor` (used with $k\ge1$). Invalid actions (a box outside $U$) get junk values; they are excluded at reachable states by admissibility, and unreachable states enter with weight $0$.
-- source:
--   Beyhaghi–Han–Luqman, Multi-Selection Pandora's Box with Nonobligatory Inspection: A PTAS and a Structural Separation, manuscript (STOC 2027 submission; preprint basis, sha256 0c3a8a501c28a4d26cc0a9898ecfcee9283823c4b2a6aaa221463bce48e9cea8), §2.1, p.5 (PDF p.6); §2.2, p.6 (PDF p.7)

import Mathlib
import Definitions.Def_MultiSelectPandora_Inst
import Definitions.Def_MultiSelectPandora_Inst_mean
import Definitions.Def_MultiSelectPandora_insertTop
import Definitions.Def_MultiSelectPandora_stFloor
import Definitions.Def_MultiSelectPandora_Supplement_StPolicy

namespace MultiSelectPandora.Supplement

/-- **Expected utility of a state policy from a state `(U, α)`.** Beyhaghi–Han–Luqman, *Multi-Selection Pandora's Box with Nonobligatory Inspection*, manuscript (STOC 2027 submission), §2.1–§2.2, pp.5–6 (PDF pp.6–7):
stopping yields `Σ_j α_j`; stopping with box `i` claimed closed yields `α_1 + ⋯ + α_{k−1} + E[v_i]` (the claimed box is
selected, together with the `k − 1` best observed values); opening `i` costs `c_i` and leads to
`(U \ {i}, top_k(α ∪ {v_i}))`.

**Formalization Note.** The utility counts costs paid from `(U, α)` on (costs paid earlier are accounted for in `α`'s
problem, §2.2). `go` recurses on a fuel equal to `|U|`; expectations are finite sums over support positions.
`α_1 + ⋯ + α_{k−1}` is written `Σ_j α_j − α_k` with `α_k = stFloor α` (sorted `α`, `k ≥ 1` in every use). Invalid
actions (a box not in `U`, opening with fuel 0) get junk values; they are excluded by `Admissible` at every reachable
state, and unreachable states enter with probability weight 0. -/
noncomputable def stValue (I : Inst) {k : ℕ} (π : StPolicy I k) (U : Finset (Fin I.n)) (α : Fin k → ℝ) : ℝ :=
  go U.card U α
where
  /-- the recursion, with fuel `|U|` -/
  go : ℕ → Finset (Fin I.n) → (Fin k → ℝ) → ℝ
    | 0, U, α =>
      match π U α with
      | .claimStop i => ∑ j, α j - stFloor α + I.mean i
      | _ => ∑ j, α j
    | m + 1, U, α =>
      match π U α with
      | .stop => ∑ j, α j
      | .claimStop i => ∑ j, α j - stFloor α + I.mean i
      | .openBox i => -I.c i + ∑ j, I.prob i j * go m (U.erase i) (insertTop α (I.val i j))

end MultiSelectPandora.Supplement


