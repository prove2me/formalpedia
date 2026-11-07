-- Prove2me | Definitions.Def_LowTempGlauber_SamplerInput
-- name    : LowTempGlauber_SamplerInput
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:26:12.704473+00:00
-- url     : https://prove2.me/theorems/066699fd-c95c-4ac4-900b-e0def50cc390
-- title:
--   Input encoding and output law of a full sampler on the unit-cost real RAM with fair coins
-- statement:
--   This file makes "an algorithm that outputs in time $T$ a sample" of Theorem 1 precise on the published unit-cost real RAM with fair coins (`SubsetConvFPRAS` machine; its two value oracles are set to $0$).
--
--   1. **Vertex numbering.** The $2n$ vertices are numbered $0,\dots,2n-1$, $V^+$ first.
--   2. **Input.** Integer cell $0$ holds $n$, cell $1$ holds $d$, and cell $2+d\cdot\mathrm{num}(v)+j$ ($0\le j<d$) holds the number of the $j$-th neighbour of $v$ in increasing order; all other integer cells hold $0$. Real cell $0$ holds $\lambda$. All bitmaps start empty.
--   3. **Output law.** The program is run for $B$ steps on $B$ fair coin flips; $\mathrm{outLaw}(S)$ is the fraction of the $2^B$ coin sequences on which the run has halted with bitmap $0$ equal to $S$, a set of vertex numbers.
--   4. The configuration $\mathrm{cfg}(S)$ occupies exactly the vertices numbered in $S$.
--
--   **Formalization Note** The machine has unit-cost exact real arithmetic $+,-,\times,\div$, integer memory and pointers, rational literals in admissible programs, and one fair coin per `coin` instruction; it has no exponential, floor, or uniform-real primitive.
-- source:
--   Galanis–Štefankovič, Low-Temperature Sampling via Equilibrium Disagreements, STOC 2027 submission (manuscript sha256 c41a38ff…7533d), Theorem 1, part 2, p.4; §3.3.2, pp.18–19

import Mathlib
import Definitions.Def_ExpanderBIS_RandomHardCore_Setting
import Definitions.Def_SubsetConvFPRAS_Machine

open Classical

namespace LowTempGlauber

/-!
# The full sampler of Theorem 1(2) on the published unit-cost real RAM with fair coins

A. Galanis, D. Štefankovič, *Low-Temperature Sampling via Equilibrium Disagreements*, STOC 2027
submission manuscript dated 3 November 2026 (held version, sha256 c41a38ff…7533d), Theorem 1, part 2,
p.4 ("There is an algorithm that outputs in time `Õ(n²)` an `ε`-sample from the full distribution
`μ_G`"), and its proof, §3.3.2, pp.18–19.

The machine is the published `SubsetConvFPRAS` real RAM (unit cost per instruction, rational literals
in `Admissible` programs, fair coins, integer memory, bitmaps over a ground set `Fin N`), used with its
two value oracles set to `0`, so `query` only loads `0`. The ground set is `Fin (n + n)`, the vertices
of `G` numbered by `vIdx = finSumFinEquiv` (`V⁺ = inl` first).

**Formalization Note.**
* Input: integer cell `0` holds `n`, cell `1` holds `d`, and cell `2 + d·vIdx(v) + j` (`j < d`) holds the
  number of the `j`-th neighbour of `v` in increasing order (a `d`-regular graph has exactly `d`); all
  other integer cells hold `0`. Real cell `0` holds `λ`; bitmaps are empty.
* Output: the program halts (`output.isSome`) and the sampled independent set is bitmap `0`.
  `outLaw P n d G λ B S` is the fraction of the `2^B` coin tapes of length `B` on which the run of `B`
  steps has halted with bitmap `0` equal to `S`.
* `cfgOfSet S` is the configuration occupied exactly on the vertices numbered in `S`.
-/

open ExpanderBIS.RandomHardCore

/-- The numbering of the `2n` vertices: `V⁺ = inl` gets `0, …, n − 1`, `V⁻ = inr` gets `n, …, 2n − 1`. -/
def vIdx (n : ℕ) : Vertex n ≃ Fin (n + n) := finSumFinEquiv

/-- The neighbours of `v`, numbered by `vIdx`, in increasing order. -/
noncomputable def nbrList {n : ℕ} (G : SimpleGraph (Vertex n)) (v : Vertex n) : List (Fin (n + n)) :=
  ((Finset.univ.filter (G.Adj v)).image (vIdx n)).sort (· ≤ ·)

/-- The integer input of the sampler: `n`, `d`, then the sorted adjacency lists. -/
noncomputable def graphInts (n d : ℕ) (G : SimpleGraph (Vertex n)) : ℤ → ℤ := fun i =>
  if i = 0 then (n : ℤ)
  else if i = 1 then (d : ℤ)
  else if h : 2 ≤ i ∧ (i - 2).toNat < d * (n + n) then
    (((nbrList G ((vIdx n).symm ⟨(i - 2).toNat / d, Nat.div_lt_of_lt_mul h.2⟩))[(i - 2).toNat % d]?
      |>.map (fun x : Fin (n + n) => ((x : ℕ) : ℤ))).getD 0)
  else 0

/-- The initial state of the sampler on input `(n, d, G, λ)`. -/
noncomputable def initSampler (n d : ℕ) (G : SimpleGraph (Vertex n)) (lam : ℝ) :
    SubsetConvFPRAS.State (n + n) :=
  SubsetConvFPRAS.mkInit (graphInts n d G) (fun _ => ∅) (fun i => if i = 0 then lam else 0)

/-- The output law of program `P` run for `B` steps: the probability, over `B` fair coins, that it has
halted with bitmap `0` equal to `S`. -/
noncomputable def outLaw (P : SubsetConvFPRAS.Program) (n d : ℕ) (G : SimpleGraph (Vertex n))
    (lam : ℝ) (B : ℕ) (S : Finset (Fin (n + n))) : ℝ :=
  (SubsetConvFPRAS.tapeCount P (fun _ => 0) (fun _ => 0) (initSampler n d G lam) B
      (fun st => st.output.isSome ∧ st.bitmap 0 = S) : ℝ) / 2 ^ B

/-- The configuration occupied exactly on the vertices numbered in `S`. -/
def cfgOfSet {n : ℕ} (S : Finset (Fin (n + n))) : Vertex n → Bool :=
  fun v => decide (vIdx n v ∈ S)

end LowTempGlauber


