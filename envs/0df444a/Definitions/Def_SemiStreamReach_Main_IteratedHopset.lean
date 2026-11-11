-- Prove2me | Definitions.Def_SemiStreamReach_Main_IteratedHopset
-- name    : SemiStreamReach_Main_IteratedHopset
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T21:51:37.501863+00:00
-- url     : https://prove2.me/theorems/afc61ea1-860a-402f-adac-dfd35e133c04
-- title:
--   Building the hopset in stages (Algorithm 4) with abstract trials; $w_{\min}$, $w_{\max}$
-- statement:
--   **Algorithm 4** (IteratedHopset$(G,\varepsilon)$) sets $T=\lceil\log_2 n\rceil$ and $H_1=\emptyset$; for $i=1,\dots,T$ it forms $K_i=G\cup H_i$, runs $C_2\log n$ independent trials on $K_i$, and sets $H_{i+1}=H_i\cup(\text{the edges output by these trials})$; it returns $H_{T+1}$. The trials are abstract: the trial of stage $i$, run when the earlier stages have produced $H_i$, outputs a random set $H'$ of weighted edges. $w_{\min}$ and $w_{\max}$ are the smallest and largest edge weights of $G$.
--
--   **Formalization Note.** The law of one trial of stage $i$ given $H_i=H$ is a discrete distribution `κ i H : PMF (WGraph V)`; the $N$ trials of a stage are independent draws from it, and `histLaw κ N k` is the law of $H_{k+1}$ ($H_1$ is the empty edge set, every pair `⊤`). Unions keep the lightest edge of each pair. `edgeMinWeight G` is `⊤` and `edgeMaxWeight G` is `0` for a graph without edges.
-- source:
--   Hoppenworth, Li, Mahabadi, Tarnawski, Semi-Streaming Reachability and Shortest Paths in n^{1/3+o(1)} Passes, arXiv:2611.05061 (PDF sha256 c1b64474…), p. 37 (PDF 39), §5.6 and Algorithm 4

import Mathlib
import Definitions.Def_SemiStreamReach_Main_Distances

open scoped ENNReal

namespace SemiStreamReach.Main

/-! # Building the hopset in stages (Algorithm 4, IteratedHopset) with abstract trials

Hoppenworth, Li, Mahabadi, Tarnawski, arXiv:2611.05061 (PDF sha256 c1b64474…), §5.6 p. 37 (PDF 39):
"Algorithm 4 runs T = ⌈log₂ n⌉ stages of C2 log n independent trials each, for a sufficiently large
constant C2, on the graphs K_i = G ∪ H_i, where H_i contains the edges of the earlier stages. …
We leave the trials abstract here." Algorithm 4: "T ← ⌈log₂ n⌉ and H_1 ← ∅; for i = 1, …, T do
K_i ← G ∪ H_i; Run C2 log n independent trials on K_i with accuracy ε; H_{i+1} ← H_i ∪ (the edges
output by these trials); return H_{T+1}."

**Formalization Note.** A trial is abstract: the trial of stage `i` run when the earlier stages have
produced `H_i = H` outputs a random weighted edge set with law `κ i H`, a discrete distribution
(`PMF`) — a randomized procedure has countably many outcomes. The `N` trials of a stage are
independent draws from `κ i H`; the stage adds all their edges to `H` (unions keep the lightest
edge of each pair). `histLaw κ N k` is the law of `H_{k+1}`: `histLaw κ N 0` is the point mass at
the empty edge set (`⊤`, every pair absent) and stage `i` maps the law of `H_i` to that of
`H_{i+1}`. The number of trials `N = ⌈C2 log n⌉` and the number of stages are arguments of the
statements. `edgeMinWeight G` and `edgeMaxWeight G` are `w_min` and `w_max`. -/

variable {V : Type*}

/-- `w_min`: the smallest edge weight of `G` (`⊤` if `G` has no edge). -/
noncomputable def edgeMinWeight (G : WGraph V) : ℝ≥0∞ := ⨅ u, ⨅ v, G u v

/-- `w_max`: the largest edge weight of `G` (`0` if `G` has no edge). -/
noncomputable def edgeMaxWeight (G : WGraph V) : ℝ≥0∞ := ⨆ (u : V) (v : V) (_ : G u v ≠ ⊤), G u v

/-- The union of the outputs of `k` independent trials, each with law `trial`. -/
noncomputable def trialsUnion (trial : PMF (WGraph V)) : ℕ → PMF (WGraph V)
  | 0 => PMF.pure ⊤
  | k + 1 => (trialsUnion trial k).bind (fun A => trial.map (fun H' => A ⊓ H'))

/-- One stage: from `H_i = H`, run `N` independent trials with law `trial H` and return
`H_{i+1} = H ∪ (their outputs)`. -/
noncomputable def stageStep (trial : WGraph V → PMF (WGraph V)) (N : ℕ) (H : WGraph V) :
    PMF (WGraph V) :=
  (trialsUnion (trial H) N).map (fun A => H ⊓ A)

/-- The law of `H_{k+1}` in Algorithm 4: `H_1 = ∅`, and stage `i` (`i = 1, 2, …`) runs `N` trials
with law `κ i H_i`. -/
noncomputable def histLaw (κ : ℕ → WGraph V → PMF (WGraph V)) (N : ℕ) : ℕ → PMF (WGraph V)
  | 0 => PMF.pure ⊤
  | k + 1 => (histLaw κ N k).bind (stageStep (κ (k + 1)) N)

end SemiStreamReach.Main


