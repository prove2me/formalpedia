-- Prove2me | Definitions.Def_CNFEncComplexity_teutschNbr
-- name    : CNFEncComplexity_teutschNbr
-- status  : Definition
-- author  : @bersubs
-- created : 2026-11-14T18:18:01.101704+00:00
-- url     : https://prove2.me/theorems/0c7f1ced-ae54-474c-b551-22dea1cdb30f
-- title:
--   Teutsch expander neighbor function from a disperser RAM
-- statement:
--   These functions specify the neighbor evaluator used in the reduction from dispersers to Teutsch’s expander. The folded layer takes a finite log-cost RAM program that lists raw neighbors, runs it with a fixed polynomial step budget, and uses a residue and a copy index to generate its output label. The merged evaluator assigns the layers consecutive disjoint right intervals and decodes a neighbor index into its layer and local slot.
--
--   The folding implements the degree and right-size normalization in Section 4. It needs only the RAM’s neighbor list and can run without the original right-side size.
--
--   **Formalization Note** The evaluator uses a layer bound and a left-vertex bound before simulating the RAM. A query outside the available slots returns `none`.
-- source:
--   Jason Teutsch, Short lists for shortest descriptions in short time, https://arxiv.org/pdf/1212.6104, Section 4, pp. 6–8, Theorem 4 and Expander Lemma.

import Mathlib.Data.Nat.Log
import Definitions.Def_TimeSpaceMA_RAM

namespace CNFEncComplexity

/-- Encode the disjoint union of the layers by successive intervals. An invalid layer
index is rejected before forming the offset. -/
def mergeNbr (degree : ℕ → ℕ) (layer : ℕ × ℕ × ℕ × ℕ → Option ℕ) :
    ℕ × ℕ × ℕ × ℕ → Option ℕ
  | (N, k, l, i) =>
    let j := i / degree N
    if j ≤ k ∧ j ≤ Nat.log 2 N then
      (layer (N, j, l, i % degree N)).map ((2 ^ (j + 2) - 4) + ·)
    else none

/-- One layer of Teutsch's expander from a log-cost RAM that lists disperser neighbors.
The parameters e and C fix the fuel and the maximum number of copies, respectively.
The right endpoint of the underlying disperser is not needed by the computation. -/
def ramFoldedLayer (P : TimeSpaceMA.Program) (e C : ℕ) :
    ℕ × ℕ × ℕ × ℕ → Option ℕ
  | (N, j, l, i) =>
    if j ≤ Nat.log 2 N ∧ l < N then
      let n := Nat.log 2 N + 1
      let B := C + 3 * (Nat.log 2 n + 1)
      let M := (2 : ℕ)^((j+2)-B)
      let u := (2 : ℕ)^(min (j+2) B)
      let st := (P.step TimeSpaceMA.zeroTape)^[n^e+e]
        (TimeSpaceMA.State.init (TimeSpaceMA.memOf [n,j,l]))
      if st.halted = true ∧ i / u < st.mem 0 then
        some (i % u * M + st.mem (1 + i / u) % M)
      else none
    else none

end CNFEncComplexity


