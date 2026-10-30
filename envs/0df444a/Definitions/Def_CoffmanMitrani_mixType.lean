-- Prove2me | Definitions.Def_CoffmanMitrani_mixType
-- name    : CoffmanMitrani_mixType
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:21:19.13369+00:00
-- url     : https://prove2.me/theorems/29b2e05b-e3ed-4883-bacf-db5b9f1d00de
-- title:
--   Type of a busy period in a mixing strategy
-- statement:
--   For a probability vector $(\alpha_1,\dots,\alpha_k)$ and a uniform seed $u$, the type is the least $j$ with $u < \alpha_1 + \dots + \alpha_j$. Type $j$ is chosen with probability $\alpha_j$.
--
--   **Formalization Note** The $k$ strategies are indexed $0,\dots,K$ with $k = K+1$; the paper's free parameters $\alpha_1,\dots,\alpha_{k-1}$, with $\alpha_k = 1-\alpha_1-\dots-\alpha_{k-1}$, form the probability vector.
-- source:
--   Coffman and Mitrani, A Characterization of Waiting Time Performance Realizable by Single-Server Queues, Operations Research 28 (1980), doi:10.1287/opre.28.3.810, §2, pp. 813–814

import Mathlib

namespace CoffmanMitrani

open Classical in
/-- **Type of a busy period in a mixing strategy.**
Coffman and Mitrani, *A Characterization of Waiting Time Performance Realizable by Single-Server
Queues*, Operations Research 28 (1980), doi:10.1287/opre.28.3.810, §2, pp. 813–814: "a new strategy which, at the beginning of each busy period, decides with
probability α that sequencing decisions during that busy period are to be made according to S1, and
with probability 1 − α these decisions are to be made according to S2. … These strategies are
generalized in the obvious way to mixing strategies for S1, S2, ···, Sk with parameters
α1, α2, ···, αk−1."

For weights `α : Fin (K + 1) → ℝ` and a uniform seed `u`, `mixType α u` is the least `j` with
`u < α 0 + ··· + α j` (and the last index if there is none). When `α` is a probability vector,
type `j` has probability `α j`.

**Formalization Note.** The paper's `k` strategies are indexed by `Fin (K + 1)`, `k = K + 1`, and its
parameters `α1, …, αk−1` with `αk = 1 − α1 − ··· − αk−1` are the probability vector `α`. -/
noncomputable def mixType {K : ℕ} (α : Fin (K + 1) → ℝ) (u : unitInterval) : Fin (K + 1) :=
  if h : ∃ j : Fin (K + 1), (u : ℝ) < ∑ l ∈ Finset.Iic j, α l then
    (Finset.univ.filter (fun j : Fin (K + 1) => (u : ℝ) < ∑ l ∈ Finset.Iic j, α l)).min'
      (let ⟨j, hj⟩ := h; ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩⟩)
  else Fin.last K

end CoffmanMitrani


