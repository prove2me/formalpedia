-- Prove2me | Definitions.Def_SubexpPermanent_Main_Machines
-- name    : SubexpPermanent_Main_Machines
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T22:00:28.282241+00:00
-- url     : https://prove2.me/theorems/f3130be2-19b3-4ed9-b62f-0abca751ef2f
-- title:
--   Machines and codes: step-bounded runs of a Boolean Turing machine, the binary code of a rational matrix, and the weighted graph of a rational weight matrix
-- statement:
--   **Computational model.** Inputs and outputs are bit strings. `OutputsWithin M input output t` says that the bundled multi-stack Turing machine $M$ (Mathlib's `Turing.FinTM2`, with input and output alphabets identified with $\{0,1\}$) started on `input` halts within $t$ steps with `output` on its output stack and every other stack empty. A rational $N\times N$ matrix is encoded by `encMat`: the list of its rows, each the list of its entries, every entry a rational in lowest terms, using the published self-delimiting binary codes `encList` and `encRat` of `ContinualHardness_Linear_Encoding`.
--
--   **Weighted graphs from a weight matrix.** A symmetric rational matrix $W$ with zero diagonal and nonnegative entries describes the finite simple graph on vertices $\{0,\dots,N-1\}$ whose edges are the pairs $i\ne j$ with $W_{ij}>0$, with edge weight $w_{ij}=W_{ij}$ (`adjGraph`, `adjWeight`; the weight is written $(W_{ij}+W_{ji})/2$, which equals $W_{ij}$ for symmetric $W$). `MaxDegreeLE W Δ` says that every vertex has at most $\Delta$ neighbours.
--
--   **Formalization Note.** Mathlib's `TM2OutputsInTime` also requires the final configuration to carry the initial internal state. A machine can reset its finite state before halting, so this changes no time bound beyond a constant.
-- source:
--   Kudria, Luo, Majid, Subexponential Approximation of the Permanent in Deterministic Polynomial Time, arXiv:2609.10516 (held PDF, sha256 e752b6f0…), pp. 1–2 (Computational model); p. 11 (bits); p. 25 (Theorem 7.1)

import Mathlib
import Definitions.Def_ContinualHardness_Linear_Encoding

namespace SubexpPermanent.Main

/-! # Machines, binary codes, and weighted graphs given by a rational matrix
(Kudria–Luo–Majid, "Computational model", pp. 1–2; Theorem 7.1, p. 25) -/

open Classical
open ContinualHardness.Linear

/-- `M` started on the bit string `input` halts with `output` on its output stack (all other
stacks empty) after at most `t` steps: Mathlib's `Turing.TM2OutputsInTime` for a bundled
multi-stack Turing machine `Turing.TM2ComputableAux Bool Bool` with Boolean input and output
alphabets. -/
def OutputsWithin (M : Turing.TM2ComputableAux Bool Bool) (input output : List Bool) (t : ℕ) :
    Prop :=
  Nonempty (Turing.TM2OutputsInTime M.tm (input.map M.inputAlphabet.symm)
    (some (output.map M.outputAlphabet.symm)) t)

/-- Binary code of a rational `N × N` matrix: the list of its rows, each the list of its entries,
every entry a rational in lowest terms (`encRat`). -/
def encMat {N : ℕ} (A : Matrix (Fin N) (Fin N) ℚ) : List Bool :=
  encList (encList encRat) (List.ofFn fun i => List.ofFn fun j => A i j)

/-- The finite simple graph on `Fin N` whose edges are the off-diagonal pairs with positive
weight in the (symmetric) weight matrix `W`. -/
def adjGraph {N : ℕ} (W : Matrix (Fin N) (Fin N) ℚ) : SimpleGraph (Fin N) where
  Adj i j := i ≠ j ∧ 0 < W i j ∧ 0 < W j i
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- The edge weights `w_{ij}` of `adjGraph W`, read from `W` (symmetrized; equal to `W i j`
when `W` is symmetric). -/
noncomputable def adjWeight {N : ℕ} (W : Matrix (Fin N) (Fin N) ℚ) : Sym2 (Fin N) → ℝ :=
  Sym2.lift ⟨fun i j => ((W i j : ℝ) + (W j i : ℝ)) / 2, fun i j => by ring⟩

/-- Every vertex of `adjGraph W` has at most `Δ` neighbours. -/
def MaxDegreeLE {N : ℕ} (W : Matrix (Fin N) (Fin N) ℚ) (Δ : ℕ) : Prop :=
  ∀ i : Fin N, (Finset.univ.filter (fun j => (adjGraph W).Adj i j)).card ≤ Δ

end SubexpPermanent.Main


