-- Prove2me | Definitions.Def_TetrisHard_Rows_ThreePartition
-- name    : TetrisHard_Rows_ThreePartition
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T22:50:12.82937+00:00
-- url     : https://prove2.me/theorems/970e7997-dc12-478d-a01c-9a850bd0989c
-- title:
--   Indexed 3-Partition and unary encoding
-- statement:
--   An instance consists of a nonnegative number s of parts, a nonnegative target T, and 3s indexed nonnegative entries. Validity requires their sum to be sT and T < 4aᵢ and 2aᵢ < T for each index. A solution assigns each index to one of s parts, each of sum T. Equal entries remain separate indices. The binary alphabet encodes each natural number as a run of ones followed by zero; the list of numbers is s, T, then the entries in order. The yes-language contains precisely the codes of valid solvable instances. The separate normalization predicate requires every subset summing to T to contain three indices, T even, and every unequal subset sum to differ from T by at least 3s. Empty instances are retained.
-- source:
--   Demaine, Hohenberger and Liben-Nowell, Tetris is Hard, Even to Approximate, arXiv:cs/0210020v1, §3, p. 7, https://arxiv.org/abs/cs/0210020v1

import Definitions.Def_CookPvsNP_defs

namespace TetrisHard.Rows

/-- The indexed, nonnegative source problem (Section 3, p. 7). -/
structure ThreePartition where
  s : ℕ
  target : ℕ
  entry : Fin (3 * s) → ℕ

def ThreePartition.Valid (P : ThreePartition) : Prop :=
  (∑ i, P.entry i) = P.s * P.target ∧
  ∀ i, P.target < 4 * P.entry i ∧ 2 * P.entry i < P.target

def ThreePartition.HasSolution (P : ThreePartition) : Prop :=
  ∃ assign : Fin (3 * P.s) → Fin P.s,
    ∀ j, ∑ i ∈ Finset.univ.filter (fun i => assign i = j), P.entry i = P.target

/-- Self-delimiting unary codes over two symbols; repeated entries remain distinct. -/
def unaryCode (ns : List ℕ) : List Bool :=
  ns.flatMap (fun n => List.replicate n true ++ [false])

def ThreePartition.code (P : ThreePartition) : List Bool :=
  unaryCode ([P.s, P.target] ++ List.ofFn P.entry)

def threePartitionLanguage : CookPvsNP.Lang Bool :=
  {w | ∃ P : ThreePartition, P.Valid ∧ P.HasSolution ∧ w = P.code}

/-- The three normalization conditions, separate from source validity. -/
def ThreePartition.Normalized (P : ThreePartition) : Prop :=
  (∀ A : Finset (Fin (3 * P.s)), (∑ i ∈ A, P.entry i) = P.target → A.card = 3) ∧
  Even P.target ∧
  ∀ A : Finset (Fin (3 * P.s)), (∑ i ∈ A, P.entry i) ≠ P.target →
    (3 * P.s : ℤ) ≤ |(P.target : ℤ) - ∑ i ∈ A, (P.entry i : ℤ)|

end TetrisHard.Rows


