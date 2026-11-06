-- Prove2me | Definitions.Def_NearLinIsing_isingSampler
-- name    : NearLinIsing_isingSampler
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:44:29.952206+00:00
-- url     : https://prove2.me/theorems/3fbc6cbc-377e-4f2e-95f4-ee27b2d342fa
-- title:
--   The Ising sampler
-- statement:
--   With chain-length constant $c_T$ the sampler sets $r=(\beta-1)/(\beta+1)$ and builds the port graph $H$ of the 2-core. If $H$ has no edges it recovers spins from $F=\emptyset$. Otherwise it runs the chain on cycle polymers from the empty family for $T=\lceil c_T\,N\log^2(N/\varepsilon)\rceil$ steps with $N=10m$, projects the final family to the original edges of $G$, and recovers spins with $t_e=r$ on every edge.
--
--   **Formalization Note** $c_T$ is the unnamed constant of the horizon $O(N\log^2(N/\varepsilon))$. Isolated and pruned vertices get their spins from recovery; the isolated-vertex preprocessing of §2.6 is the special case of a singleton component.
-- source:
--   Miao, Near-linear-Time Sampling of the Ferromagnetic Ising Model at the Tree Uniqueness Threshold, arXiv:2611.04786, proof of Theorem 1.1, p. 22

import Mathlib
import Definitions.Def_NearLinIsing_chain
import Definitions.Def_NearLinIsing_recover

namespace NearLinIsing

/-- Projection of a cycle family of `H` to the original edges of `G` (proof of Theorem 1.1, p. 22):
the flags of the `G`-edges carried by original edges of the stored cycles. -/
noncomputable def projectFam (H : PortGraph) (m : ℕ) (fam : Array (List ℕ)) : Prog (Array Bool) := do
  let mut inF ← alloc m false
  for C in fam do
    tick 1 -- dispatch
    for e in C do
      tick 3 -- dispatch, read flag, branch
      if H.isOrig[e]! then
        tick 2 -- read index, write
        inF := inF.set! H.gEdge[e]! true
  return inF

/-- **The Ising sampler** of the proof of Theorem 1.1 (p. 22), with chain-length constant `cT`.
Put `r = (β − 1)/(β + 1)` and build the port graph `H` of the 2-core (Proposition 4.1). If `H` has
no edges (the 2-core is empty, `G` is a forest), recover spins from `F = ∅`. Otherwise run the
insertion–deletion chain on cycle polymers of `H` from `∅` for `T = ⌈cT · N · log²(N/ε)⌉` steps
with `N = 10 m` (Theorem 1.5, Proposition 4.6), project the family to the original edges, and
recover spins (Lemma 4.5) with `t_e = r` on every edge of `G`.

Miao, *Near-linear-Time Sampling of the Ferromagnetic Ising Model at the Tree Uniqueness
Threshold*, arXiv:2611.04786, proof of Theorem 1.1, p. 22.

**Formalization Note.** Reading R1: the paper's "has an ε-approximate sampler" is stated for this
concrete program; `cT` is the unnamed constant of the horizon `O(N log²(N/ε))`. Every vertex of `G`,
including isolated and pruned ones, gets its spin from `recoverSpins` (the isolated-vertex
preprocessing of §2.6 is the special case of a singleton component). -/
noncomputable def isingSampler (cT : ℝ) (G : IncGraph) (β ε : ℝ) : Prog (Array Bool) := do
  let m ← qM G
  let r ← op 3 ((β - 1) / (β + 1)) -- subtraction, addition, division
  let H ← buildPort G r
  tick 2 -- read, comparison
  if H.ne = 0 then
    let inF ← alloc m false
    recoverSpins G (fun _ => r) inF
  else
    let N ← op 1 (10 * m)
    let T ← op 6 (⌈cT * N * Real.log (N / ε) ^ 2⌉₊) -- two multiplications, division, log, square, ceiling
    let st ← runSteps H N T
    let inF ← projectFam H m st.fam
    recoverSpins G (fun _ => r) inF

/-- The spins output by `isingSampler` on the tape `τ`. -/
noncomputable def samplerOut (cT : ℝ) (G : IncGraph) (β ε : ℝ) (τ : Tape) : Fin G.n → Bool :=
  spinsOf G (runVal (isingSampler cT G β ε) τ)

end NearLinIsing


