-- Prove2me | Definitions.Def_ReplParity_multistageCover
-- name    : ReplParity_multistageCover
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:43:00.772901+00:00
-- url     : https://prove2.me/theorems/c2a4d53e-0f1d-4551-9df2-46e18c4a5936
-- title:
--   The multistage covering subspace (proof of Proposition 3.4)
-- statement:
--   The algorithm starts with $V_0=\{0\}$ and, at stage $j=1,\dots,L$, runs the gate of Lemma 3.3 on $V_{j-1}$ with parameters $q_j,\eta_j$ and its own block. On "skip" it sets $V_j=V_{j-1}$. On "continue" it takes the stage's collection block of $R_j$ samples and collects the first $K_j$ of them that lie outside $V_{j-1}$. If fewer than $K_j$ lie outside, it sets $V_j=V_{j-1}$; otherwise it runs the token min-hash of Lemma 3.2 with parameter $\eta_j$ on the collected vectors and sets $V_j=V_{j-1}+W_j$. The output is $U=V_L$. Every stage has its own seed: the gate's $J$ and the hash coefficients.
--
--   **Formalization Note** Each stage uses an admissible implementation of the token min-hash; the construction is defined for every such family of choices.
-- source:
--   Shen, Zhong, Replicable Parity Learning: Cubic Sample Complexity and a Geometric Characterization, STOC 2027 submission (manuscript sha256 40424491d00eef39c790dd41b7557e0ffdf9de2d14d95ddcd611aeacb0f77a50), proof of Proposition 3.4, p.17 (PDF p.19); Figure 2, p.14

import Mathlib
import Definitions.Def_ReplParity_coverM

namespace ReplParity

/-- The seed of the multistage cover: for each stage `j = 1, …, L` (index `j − 1 : Fin L`), the
gate's `J ∈ {0, …, B_j − 1}` and the `K_j/2` hash coefficients of Lemma 3.2's construction in the
stage's field. "every stage has its own seed" (p.17). -/
abbrev CoverSeed (n : ℕ) (ε ρ : ℝ)
    (impl : (j : ℕ) → TokenHashImpl n (stageK n ε ρ j) (stageEta ε ρ j)) : Type :=
  (j : Fin (coverL ε)) →
    Fin (gateB (stageEta ε ρ ((j : ℕ) + 1))) × (Fin (stageK n ε ρ ((j : ℕ) + 1) / 2) → (impl ((j : ℕ) + 1)).F)

open Classical in
/-- Stage `j + 1` of the multistage cover, applied to the current subspace `V = V_j`. -/
noncomputable def stageStep {n : ℕ} {ε ρ : ℝ}
    (impl : (j : ℕ) → TokenHashImpl n (stageK n ε ρ j) (stageEta ε ρ j))
    (S : Fin (coverM n ε ρ) → Vec n) (seed : CoverSeed n ε ρ impl) (j : Fin (coverL ε))
    (V : Subsp n) : Subsp n :=
  let off := stageOff n ε ρ ((j : ℕ) + 1)
  let Ng := gateN (stageQ ((j : ℕ) + 1)) (stageEta ε ρ ((j : ℕ) + 1))
  if gate (stageQ ((j : ℕ) + 1)) (stageEta ε ρ ((j : ℕ) + 1)) V (fun i => sampleAt S (off + i))
      (seed j).1 = false then V
  else
    let out := (List.ofFn (fun i : Fin (stageR n ε ρ ((j : ℕ) + 1)) =>
      sampleAt S (off + Ng + i))).filter (fun v => decide (v ∉ V))
    if out.length < stageK n ε ρ ((j : ℕ) + 1) then V
    else V ⊔ tokenMinHash (impl ((j : ℕ) + 1)) (fun i => out.getD i 0) (seed j).2

/-- **The multistage covering subspace (proof of Proposition 3.4).** Shen, Zhong, *Replicable Parity
Learning: Cubic Sample Complexity and a Geometric Characterization*, STOC 2027 submission (manuscript
sha256 40424491…), proof of Proposition 3.4, p.17 (PDF p.19): "The algorithm starts with V_0 = {0}
and, at stage j, runs Lemma 3.3 on V_{j−1} with parameters q_j and η_j. On “skip” it sets
V_j = V_{j−1}. On “continue” it lets K_j = 4⌈128n³/η_j²⌉, takes a fresh block of R_j = ⌈8K_j/q_j⌉
samples, and collects the first K_j of them that lie outside V_{j−1}. If fewer than K_j samples lie
outside, it sets V_j = V_{j−1}, and otherwise it runs Lemma 3.2 with parameter η_j on the collected
vectors and lets V_j = V_{j−1} + W_j. The output is U = V_L. All blocks are reserved in advance, and
every stage has its own seed."

The sample `S` is the concatenation of the stage blocks (gate block, then collection block), used
whether or not a stage skips; stage `j` runs the gate construction (`gate`) and the token min-hash
construction (`tokenMinHash`) with the implementation `impl j`.

**Formalization Note.** `impl` fixes, for every stage, the admissible field, integer reading, token
encoding and subspace order of Lemma 3.2's construction. -/
noncomputable def multistageCover {n : ℕ} {ε ρ : ℝ}
    (impl : (j : ℕ) → TokenHashImpl n (stageK n ε ρ j) (stageEta ε ρ j))
    (S : Fin (coverM n ε ρ) → Vec n) (seed : CoverSeed n ε ρ impl) : Subsp n :=
  (List.finRange (coverL ε)).foldl (fun V j => stageStep impl S seed j V) ⊥

end ReplParity


