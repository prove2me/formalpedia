-- Prove2me | Definitions.Def_AutoQMem_Lindblad_Supplement_Registers
-- name    : AutoQMem_Lindblad_Supplement_Registers
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:44:24.564999+00:00
-- url     : https://prove2.me/theorems/199860d2-b053-4313-9230-51fea0bbee79
-- title:
--   Local classical registers and the extended stabilizer algebras
-- statement:
--   The data qubits are augmented by a finite set of **register qubits** $\mathrm{Reg}=\mathrm{Reg}_X\sqcup\mathrm{Reg}_Z$, each located at a site (a data qubit), so that $\mathcal H^{\mathrm{ext}}=\mathcal H\otimes(\mathbb C^2)^{\otimes\mathrm{Reg}}$. Data operators act as $A\otimes I_{\mathrm{reg}}$; register Pauli strings are $X^v$, $Z^w$ with $v,w\in\mathbb F_2^{\mathrm{Reg}}$, and $Y_j=iX_jZ_j$. The registers are read in the computational basis, so their $Z$ operators are adjoined to the stabilizer algebras:
--   $$\mathcal A^{\mathrm{ext}}=\mathrm{Alg}\big(\mathcal A\cup\{Z_j:j\in\mathrm{Reg}\}\big),\qquad \mathcal A^{\mathrm{ext}}_\sigma=\mathrm{Alg}\big(\mathcal A_\sigma\cup\{Z_j:j\in\mathrm{Reg}_\sigma\}\big).$$
--   The module also fixes the dissipator $\mathcal D[J](\rho)=J\rho J^\dagger-\tfrac12\{J^\dagger J,\rho\}$ on any finite-dimensional space.
--
--   These are the ingredients of the register-extended Lindbladians of Theorem 4.
-- source:
--   Drechsler, Oreg, Aharonov, Autonomous Quantum Memories from Classical Stochastic Processes, arXiv:2610.05589 (PDF of 2026-11-03), §7.1, eqs. (176)–(177), pp. 51–52 (PDF pp. 53–54); Definition 2.23, p. 20 (PDF p. 22); eq. (30), p. 19 (PDF p. 21)

import Mathlib
import Definitions.Def_AutoQMem_Lindblad_CSSCode
import Definitions.Def_AutoQMem_Lindblad_pauliAt
open Matrix

namespace AutoQMem.Lindblad.Supplement

open AutoQMem.Lindblad

/-- **Local classical registers attached to the data qubits.** Drechsler, Oreg, Aharonov, *Autonomous
Quantum Memories from Classical Stochastic Processes*, arXiv:2610.05589 (PDF of 2026-11-03), §7.1,
p. 51–52 (PDF 53–54): "For each sector σ ∈ {X, Z}, let Reg_σ be a finite set of register qubits,
with Reg_X ∩ Reg_Z = ∅, and let H^ext := H ⊗ (ℂ²)^{⊗(Reg_X ⊔ Reg_Z)}"; and Definition 2.23, p. 20:
"the registers attached to a site i are counted as located at i".

**Formalization Note.** `Reg` is the finite set `Reg_X ⊔ Reg_Z`, `isX j` says `j ∈ Reg_X`, and
`loc j` is the data qubit (site) at which register `j` is located. -/
structure Registers (n : ℕ) : Type 1 where
  /-- The register qubits `Reg_X ⊔ Reg_Z`. -/
  Reg : Type
  [fintype : Fintype Reg]
  [decEq : DecidableEq Reg]
  /-- The site at which each register is located. -/
  loc : Reg → Fin n
  /-- `true` for the registers of `Reg_X`, `false` for those of `Reg_Z`. -/
  isX : Reg → Bool

attribute [instance] Registers.fintype Registers.decEq

namespace Registers

variable {n : ℕ} (R : Registers n)

/-- Basis labels of `H^ext = H ⊗ (ℂ²)^{⊗Reg}`: a data string and a register configuration. -/
abbrev Idx : Type := (Fin n → ZMod 2) × (R.Reg → ZMod 2)

/-- Operators on `H^ext`. -/
abbrev Op : Type := Matrix R.Idx R.Idx ℂ

/-- A data operator extended by the identity on the registers, `A ⊗ I_reg` (§7.1, eq. (183):
"operators on H are extended by the identity on the registers"). -/
def extData (A : AutoQMem.Lindblad.Op n) : R.Op := Matrix.kronecker A 1

/-- The register Pauli string `X^v` (flips the registers `j` with `v_j = 1`), `I ⊗ X^v`. -/
def regXstr (v : R.Reg → ZMod 2) : R.Op :=
  Matrix.kronecker 1 (Matrix.of fun c d => if c = d + v then 1 else 0)

/-- The register Pauli string `Z^w`, `I ⊗ Z^w`, `Z^w |c⟩ = (−1)^{w·c} |c⟩`. -/
def regZstr (w : R.Reg → ZMod 2) : R.Op :=
  Matrix.kronecker 1 (Matrix.diagonal fun c => (-1 : ℂ) ^ (w ⬝ᵥ c).val)

/-- The single-register Pauli `P_j`, `P ∈ {I, X, Y, Z}`, with `Y_j = i X_j Z_j` (the paper's
convention, Appendix B, p. 65). -/
noncomputable def regPauli : Pauli1 → R.Reg → R.Op
  | .I, _ => 1
  | .X, j => R.regXstr (Pi.single j 1)
  | .Y, j => Complex.I • (R.regXstr (Pi.single j 1) * R.regZstr (Pi.single j 1))
  | .Z, j => R.regZstr (Pi.single j 1)

/-- **Extended stabilizer algebra** `A^ext := Alg(A ∪ {Z_j : j ∈ Reg_X ⊔ Reg_Z})` (§7.1, eq. (176),
p. 52, PDF 54). -/
noncomputable def algExt {mX mZ : ℕ} (C : CSSCode n mX mZ) : Subalgebra ℂ R.Op :=
  Algebra.adjoin ℂ (R.extData '' (C.alg : Set (AutoQMem.Lindblad.Op n)) ∪
    Set.range fun j => R.regPauli .Z j)

/-- **Extended sector algebras** `A^ext_σ := Alg(A_σ ∪ {Z_j : j ∈ Reg_σ})` (eq. (176)); `σ = true`
is the X sector, `σ = false` the Z sector. -/
noncomputable def algExtSec {mX mZ : ℕ} (C : CSSCode n mX mZ) (σ : Bool) : Subalgebra ℂ R.Op :=
  Algebra.adjoin ℂ (R.extData '' ((if σ then C.algX else C.algZ : Subalgebra ℂ _) :
      Set (AutoQMem.Lindblad.Op n)) ∪
    {O | ∃ j, R.isX j = σ ∧ O = R.regPauli .Z j})

end Registers

/-- **Lindblad dissipator** `D[J](ρ) = J ρ J† − ½{J†J, ρ}` on any finite-dimensional space (§2.2.1,
eq. (30), p. 19, PDF 21). -/
noncomputable def dissG {κ : Type} [Fintype κ] [DecidableEq κ] (J ρ : Matrix κ κ ℂ) :
    Matrix κ κ ℂ :=
  J * ρ * Jᴴ - (1 / 2 : ℂ) • (Jᴴ * J * ρ + ρ * (Jᴴ * J))

end AutoQMem.Lindblad.Supplement


