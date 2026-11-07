-- Prove2me | Definitions.Def_MultiSelectPandora_optState
-- name    : MultiSelectPandora_optState
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:04:25.414684+00:00
-- url     : https://prove2.me/theorems/8bb43c49-78c3-4a80-915d-249c8fe29ead
-- title:
--   The Bellman value $\mathrm{OPT}(U,\alpha,\hat k)$
-- statement:
--   $\mathrm{OPT}(U,\alpha,\hat k)$ is the optimal expected utility of the problem from the state $(U,\alpha,\hat k)$, where $U$ is the set of boxes neither opened nor claimed closed, $\alpha$ the $k$ best values secured so far, and $\hat k$ the number of closed claims still permitted. It is the maximum of $\sum_j\alpha_j$ (stopping), of
--   $$-c_i+\sum_j\mathrm{prob}_{ij}\,\mathrm{OPT}\big(U\setminus\{i\},\mathrm{top}_k(\alpha\cup\{\mathrm{val}_{ij}\}),\hat k\big)\qquad(i\in U),$$
--   and, if $\hat k\ge1$, of
--   $$\mathrm{OPT}\big(U\setminus\{i\},\mathrm{top}_k(\alpha\cup\{E[v_i]\}),\hat k-1\big)\qquad(i\in U).$$
--   This value counts the entries of $\alpha$.
-- source:
--   Beyhaghi–Han–Luqman, Multi-Selection Pandora's Box with Nonobligatory Inspection: A PTAS and a Structural Separation, manuscript (STOC 2027 submission; held artifact sha256 0c3a8a501c28a4d26cc0a9898ecfcee9283823c4b2a6aaa221463bce48e9cea8), §2.2, p.6 (PDF p.7)

import Mathlib
import Definitions.Def_MultiSelectPandora_Inst
import Definitions.Def_MultiSelectPandora_Inst_mean
import Definitions.Def_MultiSelectPandora_insertTop

namespace MultiSelectPandora

/-- **`OPT(U, α, k̂)`, the Bellman value of the problem `P(U, α, k̂)`.** Beyhaghi–Han–Luqman manuscript, §2.2, p.6 (PDF p.7):
opening `i ∈ U` leads to `(U \ {i}, top_k(α ∪ {v_i}), k̂)`, claiming `i` closed leads to
`(U \ {i}, top_k(α ∪ {E[v_i]}), k̂ − 1)`, and stopping yields `Σ_j α_j`.

**Formalization Note.** The value counts the entries of `α`. `go` recurses on a fuel equal to `|U|`. The `max` over a finite
set is `Finset.fold max` with the stopping value as its base, so `U = ∅` gives `Σ_j α_j`. Opening charges `c_i`. -/
noncomputable def optState (I : Inst) {k : ℕ} (U : Finset (Fin I.n)) (α : Fin k → ℝ) (hatk : ℕ) : ℝ :=
  go U.card U α hatk
where
  /-- the recursion, with fuel `|U|` -/
  go : ℕ → Finset (Fin I.n) → (Fin k → ℝ) → ℕ → ℝ
    | 0, _, α, _ => ∑ j, α j
    | m + 1, U, α, hatk =>
      U.fold max (∑ j, α j) fun i =>
        let o := -I.c i + ∑ j, I.prob i j * go m (U.erase i) (insertTop α (I.val i j)) hatk
        if 1 ≤ hatk then max o (go m (U.erase i) (insertTop α (I.mean i)) (hatk - 1)) else o

end MultiSelectPandora


