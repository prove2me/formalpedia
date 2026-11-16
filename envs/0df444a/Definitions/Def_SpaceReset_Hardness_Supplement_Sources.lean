-- Prove2me | Definitions.Def_SpaceReset_Hardness_Supplement_Sources
-- name    : SpaceReset_Hardness_Supplement_Sources
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T13:42:23.229334+00:00
-- url     : https://prove2.me/theorems/e06e4bb0-e1ff-46e2-9a47-2244f8ad2a53
-- title:
--   Repeated-bit sources and local Clifford equivalence across a cut
-- statement:
--   A **repeated-bit source** (App. A, p. 36) is a binary specification $G\in\mathbb F_2^{k\times n}$ of full row rank in which every column is a unit vector and every row has weight exactly two. Each independent fair bit (row) is emitted on exactly two output qubits, and each output qubit carries exactly one bit.
--
--   A **Clifford unitary** on $P$ qubits is a finite product of the gate matrices of $H$, $S$ and controlled-$X$, $Y$, $Z$ gates. A global phase is immaterial under conjugation, so these give the whole Clifford group acting on states.
--
--   For a cut $t\in\{0,\dots,n\}$, two $n$-qubit operators $\rho_A,\rho_B$ are **locally Clifford equivalent across $t$** if some Clifford unitary $U$ on the first $t$ qubits and some Clifford unitary $W$ on the last $n-t$ qubits satisfy
--   $$(U\otimes W)\,\rho_A\,(U\otimes W)^\dagger=\rho_B .$$
--   This is an equivalence of the entire bipartite operators, not only of their reduced spectra.
--
--   **Formalization Note.** Qubits are 0-based. $U\otimes W$ is written entrywise through the first-$t$ and last-$(n-t)$ parts of a basis string.
-- source:
--   Rinka Miura, STOC 2027 submission #1715 (October 2026), The Complexity of Space–Reset Tradeoffs in Online Quantum Computation (held submission, no arXiv version; SHA-256 c2a340e2195da0d130bf10d936d56d4f1d4da805e644efb7fe1c36d9c904f3e5), App. A, p. 36 (Theorem 23 and its proof)

import Mathlib
import Definitions.Def_SpaceReset_Hardness_Native

set_option autoImplicit false

noncomputable section

namespace SpaceReset.Hardness.Supplement

/-!
Rinka Miura, STOC 2027 submission #1715 (October 2026), App. A, p. 36: repeated-bit sources and
local Clifford equivalence of output states across a cut.

Conventions. Output qubits are `Fin n` (0-based: qubit `j` is the paper's qubit `j + 1`), with
computational basis `Fin n → Bool`. The cut `t` (`0 ≤ t ≤ n`) separates the first `t` qubits from
the last `n − t`. A Clifford unitary on `P` qubits is a product of the gate matrices of `H`, `S`
and controlled-`X/Y/Z` gates (the base gate matrices); a global phase is immaterial under
conjugation, so this is the Clifford group as it acts on states.
-/

open Matrix
open SpaceReset.Hardness

variable {κ : Type} [Fintype κ] [DecidableEq κ]

/-- A repeated-bit source (p. 36): a binary specification of full row rank in which every column
is a unit vector and every row has weight exactly two, i.e. each independent fair bit (row) is
emitted on exactly two output qubits and each output qubit carries exactly one bit. -/
def IsRepeatedBitSource {n : ℕ} (G : Matrix κ (Fin n) F2) : Prop :=
  FullRowRank G ∧
  (∀ j : Fin n, ∃! i : κ, G i j = 1) ∧
  (∀ i : κ, (Finset.univ.filter (fun j : Fin n => G i j = 1)).card = 2)

/-- The gate matrix of a named Clifford gate (`RESET` and `D_Z` are not unitary gates; they are
excluded by `IsCliffordGate`). -/
def cliffordGateMat {P : ℕ} : CGate P → Matrix (Fin P → Bool) (Fin P → Bool) ℂ
  | .h w => hadamardMat w
  | .s w => phaseMat w
  | .cx a b => cxMat a b
  | .cy a b => cyMat a b
  | .cz a b => czMat a b
  | .reset _ => 1
  | .dz _ => 1

/-- `H`, `S`, controlled-`X`, controlled-`Y`, controlled-`Z`. -/
def IsCliffordGate {P : ℕ} : CGate P → Prop
  | .reset _ => False
  | .dz _ => False
  | _ => True

/-- A Clifford unitary on `P` qubits: a finite product of Clifford gate matrices. -/
def IsCliffordUnitary {P : ℕ} (U : Matrix (Fin P → Bool) (Fin P → Bool) ℂ) : Prop :=
  ∃ gs : List (CGate P), (∀ gt ∈ gs, IsCliffordGate gt) ∧ U = (gs.map cliffordGateMat).prod

/-- The first `t` qubits of an `n`-qubit basis string (for `t ≤ n`). -/
def leftPart {n : ℕ} (t : ℕ) (x : Fin n → Bool) : Fin t → Bool :=
  fun i => if h : i.val < n then x ⟨i.val, h⟩ else false

/-- The last `n − t` qubits of an `n`-qubit basis string. -/
def rightPart {n : ℕ} (t : ℕ) (x : Fin n → Bool) : Fin (n - t) → Bool :=
  fun i => if h : t + i.val < n then x ⟨t + i.val, h⟩ else false

/-- `U ⊗ W` on `n` qubits, with `U` acting on the first `t` and `W` on the last `n − t`. -/
def cutKron {n : ℕ} (t : ℕ) (U : Matrix (Fin t → Bool) (Fin t → Bool) ℂ)
    (W : Matrix (Fin (n - t) → Bool) (Fin (n - t) → Bool) ℂ) :
    Matrix (Fin n → Bool) (Fin n → Bool) ℂ :=
  fun x x' => U (leftPart t x) (leftPart t x') * W (rightPart t x) (rightPart t x')

/-- Local Clifford equivalence across the cut `t` (p. 36): some Clifford unitary `U` on the first
`t` qubits and some Clifford unitary `W` on the remaining `n − t` qubits satisfy
`(U ⊗ W) ρ_A (U ⊗ W)† = ρ_B`. -/
def LocallyCliffordEquiv {n : ℕ} (t : ℕ) (ρA ρB : Matrix (Fin n → Bool) (Fin n → Bool) ℂ) :
    Prop :=
  ∃ (U : Matrix (Fin t → Bool) (Fin t → Bool) ℂ) (W : Matrix (Fin (n - t) → Bool) (Fin (n - t) → Bool) ℂ),
    IsCliffordUnitary U ∧ IsCliffordUnitary W ∧ cutKron t U W * ρA * (cutKron t U W)ᴴ = ρB

end SpaceReset.Hardness.Supplement


