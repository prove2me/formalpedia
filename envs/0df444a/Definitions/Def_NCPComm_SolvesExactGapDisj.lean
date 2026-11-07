-- Prove2me | Definitions.Def_NCPComm_SolvesExactGapDisj
-- name    : NCPComm_SolvesExactGapDisj
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T20:59:11.196005+00:00
-- url     : https://prove2.me/theorems/6c01dd9f-30e3-4056-a4bf-49179a87e33b
-- title:
--   Exact gap disjointness $\mathrm{GapDisj}_{N,g,k_a,k_b}$ in the public-coin model
-- statement:
--   Alice holds $x\in\{0,1\}^N$ and Bob holds $y\in\{0,1\}^N$, with $|x|=k_a$ and $|y|=k_b$. Write $\langle x,y\rangle$ for the number of common ones. A public-coin protocol run for $k$ bits **solves exact gap disjointness with error $\varepsilon$** if, on promise inputs,
--
--   1. Alice outputs $1$ with probability at least $1-\varepsilon$ when $\langle x,y\rangle=0$, and
--   2. Alice outputs $0$ with probability at least $1-\varepsilon$ when $\langle x,y\rangle=g$.
--
--   This is the source problem of the paper's reduction, and its communication lower bound is the source of the NCP lower bound.
--
--   **Formalization Note** The protocol is the published `DistVerif.Simulation.PubProtocol`. Only Alice's output must be correct (p.10: "Alice's decision at the end of the protocol will solve GapDisj"), so a lower bound here is stronger than one for protocols where both parties must be correct. The published `ComputesWithin` concerns total functions with both outputs correct and is not used.
-- source:
--   Herman, The Communication Complexity of Verifying Distribution Properties, STOC 2027 submission (manuscript sha256 714c0353…), Definition 3.13, p.17

import Mathlib
import Definitions.Def_DistVerif_Simulation_Protocol

open scoped ENNReal

namespace NCPComm

/-- `|x|`: the number of ones of a vector `x ∈ {0,1}^N`. -/
def weight {N : ℕ} (x : Fin N → Bool) : ℕ := (Finset.univ.filter fun i => x i = true).card

/-- `⟨x, y⟩ = |A ∩ B|`: the number of common ones of two vectors. -/
def innerCount {N : ℕ} (x y : Fin N → Bool) : ℕ :=
  (Finset.univ.filter fun i => x i = true ∧ y i = true).card

/-- The public-coin protocol `P`, run for exactly `k` bits, solves exact gap disjointness
`GapDisj_{N,g,k_a,k_b}` with error at most `ε` (Definition 3.13, p.17, of Herman, The Communication
Complexity of Verifying Distribution Properties, STOC 2027 submission, manuscript sha256 714c0353…):
on inputs with `|x| = k_a` and `|y| = k_b`, Alice outputs `1` with probability at least `1 - ε` when
the sets are disjoint and `0` with probability at least `1 - ε` when `⟨x, y⟩ = g`. Other inputs are
outside the promise.

**Formalization Note** `P` is the published `DistVerif.Simulation.PubProtocol`. Only Alice's output
has to be correct, as on p.10 ("Alice's decision at the end of the protocol will solve GapDisj");
this makes a communication lower bound stronger than one for protocols where both parties must be
correct. Sets are `Fin N → Bool` indicators. The fixed length `k` is the padding convention of the
published protocol model. -/
def SolvesExactGapDisj {N : ℕ} (P : DistVerif.Simulation.PubProtocol N) (k g ka kb : ℕ) (ε : ℝ) :
    Prop :=
  ∀ x y : Fin N → Bool, weight x = ka → weight y = kb →
    (innerCount x y = 0 → 1 - ε ≤ (P.μ.toOuterMeasure
      {ω | (P.prot ω).outA x ((P.prot ω).transcript x y k) = true}).toReal) ∧
    (innerCount x y = g → 1 - ε ≤ (P.μ.toOuterMeasure
      {ω | (P.prot ω).outA x ((P.prot ω).transcript x y k) = false}).toReal)

end NCPComm


