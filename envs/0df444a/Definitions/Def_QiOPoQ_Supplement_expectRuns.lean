-- Prove2me | Definitions.Def_QiOPoQ_Supplement_expectRuns
-- name    : QiOPoQ_Supplement_expectRuns
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:06:20.271975+00:00
-- url     : https://prove2.me/theorems/bb0842fa-448c-4472-9927-3cd0cee464db
-- title:
--   Independent runs of classical algorithms, concatenation of decoded circuits, block splitting
-- statement:
--   Helpers for Definition 6.4: the expectation over independent runs of several classical PPT algorithms with fresh coins; the description of the concatenation $D_1\|\cdots\|D_k$ of the circuits described by their outputs (empty if some output describes no ancilla-free $n$-qubit circuit); and the splitting of a gate list into the blocks of lengths $N(\lambda,n,2s+1),N(\lambda,n,2s),\dots,N(\lambda,n,2s+1)$.
-- source:
--   Gheorghiu, Gupte, Havlíček, Liu, Verifiable Quantum Advantage and Computation via Quantum Circuit Obfuscation, arXiv:2609.40289 (sha256 fe2f9210…), Definition 6.4, p.31; proof of Theorem 6.6, p.32

import Mathlib
import Definitions.Def_QiOPoQ_UPPT
import Definitions.Def_QiOPoQ_encCirc
import Definitions.Def_QiOPoQ_Supplement_Placement

set_option autoImplicit false

namespace QiOPoQ.Supplement

open QAlgorithms.Complexity

/-- `E[g(M_1(x_1), …, M_k(x_k))]` for classical PPT algorithms run on their inputs with fresh,
independent coins (Gheorghiu, Gupte, Havlíček, Liu, arXiv:2609.40289, sha256 fe2f9210…, proof of
Theorem 6.6, p.32: "All samples and calls to RIO use fresh, independent randomness"). -/
noncomputable def expectRuns : List (UPPT × Str) → (List Str → ℝ) → ℝ
  | [], g => g []
  | (M, x) :: rest, g => M.expect x fun o => expectRuns rest fun os => g (o :: os)

variable {G : GateSet}

/-- The concatenation `D_1∥⋯∥D_k` of the circuits described by the strings `outs`, each read as an
ancilla-free `n`-qubit circuit, as a description; the empty string if some piece describes no
such circuit. -/
noncomputable def concatDecoded (G : GateSet) (n : ℕ) (outs : List Str) : Str :=
  match outs.mapM (decAC (G := G) n) with
  | some ls => encCirc (afCirc n ls.flatten)
  | none => []

/-- Split a list into consecutive blocks of the given lengths. -/
def splitLens {α : Type*} : List ℕ → List α → List (List α)
  | [], _ => []
  | k :: ks, xs => xs.take k :: splitLens ks (xs.drop k)

/-- The block lengths of Definition 6.4: `2m − 1` blocks, alternately `N₁` (odd positions
`D_1, D_3, …`) and `N₂` (even positions `D_2, D_4, …`). -/
def blockLens (m N₁ N₂ : ℕ) : List ℕ :=
  (List.range (2 * m - 1)).map fun i => if i % 2 = 0 then N₁ else N₂

end QiOPoQ.Supplement


