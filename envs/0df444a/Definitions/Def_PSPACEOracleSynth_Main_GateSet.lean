-- Prove2me | Definitions.Def_PSPACEOracleSynth_Main_GateSet
-- name    : PSPACEOracleSynth_Main_GateSet
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T03:20:52.842559+00:00
-- url     : https://prove2.me/theorems/d606ebd5-279b-415d-88fb-d7d8892034e9
-- title:
--   The gate set $G=\{H,T,T^\dagger,\mathrm{CNOT}\}$, circuits over $G$, the gates of Lemma 4.3, and words over $\{H,T,T^\dagger\}$
-- statement:
--   The constructed circuits are over the gate set
--   $$G=\{H,T,T^\dagger,\mathrm{CNOT}\},\qquad H=\frac1{\sqrt2}\begin{pmatrix}1&1\\1&-1\end{pmatrix},\qquad T=\begin{pmatrix}1&0\\0&e^{i\pi/4}\end{pmatrix},$$
--   that is, they use only these gates and oracle gates. In the circuit model of Kretschmer and Tang a gate is given by encodings of its matrix entries; a gate is a $G$-gate when the matrix it describes is exactly $H$, $T$ or $T^\dagger$ on one wire or CNOT (control first) on two wires.
--
--   The definition also fixes three gates used in Lemma 4.3:
--   1. NOT: $|b\rangle\mapsto|b\oplus1\rangle$;
--   2. Toffoli: $|a,b,c\rangle\mapsto|a,b,c\oplus ab\rangle$;
--   3. the uniformly controlled gate $\sum_{y}|y\rangle\langle y|\otimes W_y$ with a two-bit control $y=y_0y_1$ and $W_{00}=I$, $W_{01}=H$, $W_{10}=T$, $W_{11}=T^\dagger$.
--
--   Finally, a **word** over $\{H,T,T^\dagger\}$ is a finite list of these letters, multiplied in application order (the first letter acts first).
--
--   **Formalization Note.** Circuits are the published `KTUnitary.Synth.UCircuit`; `OverG f C` says every explicit gate decodes under $f$ to exactly $H$, $T$, $T^\dagger$ or CNOT and every oracle gate is an uncontrolled $O_m$; `OracleFree C` says there are no oracle gates. Basis states of $k$ qubits are `Bits k`, wire $0$ first.
-- source:
--   Sichen Wang, Unitary Synthesis with a PSPACE Oracle, STOC 2027 submission #1740 (October 2026), §2.1, p. 9 (gate set G); §2.4, p. 13 (words); Lemma 4.3, p. 26

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Complexity
import Definitions.Def_KTUnitary_Synth_UCircuit

open QAlgorithms.Complexity KTUnitary.Synth

namespace PSPACEOracleSynth.Main

/-!
# The gate set `G = {H, T, T†, CNOT}`, circuits over `G`, and the gates of Lemma 4.3

Sichen Wang, *Unitary Synthesis with a PSPACE Oracle*, STOC 2027 submission #1740 (October 2026),
§2.1, p. 9; §2.4, p. 13 (words); Lemma 4.3, p. 26.

`H = (1/√2)[[1, 1], [1, −1]]` and `T = diag(1, e^{iπ/4})` are the published `hMat`, `tMat`
(`Bool`-indexed, `false = |0⟩`). A circuit is **over `G`** if it uses only these gates and oracle
gates (p. 9: "that is, they use only these gates and oracle gates"). In the published circuit model
`KTUnitary.Synth.UCircuit` an explicit gate is given by encodings of its entries; a gate is a `G`
gate when the matrix it describes is exactly `H`, `T` or `T†` on one wire, or `CNOT` on two wires.
-/

/-- `H` as a one-qubit matrix indexed by `Bits 1`. -/
noncomputable def h1 : Matrix (Bits 1) (Bits 1) ℂ := Matrix.of fun i j => hMat (i 0) (j 0)

/-- `T` as a one-qubit matrix indexed by `Bits 1`. -/
noncomputable def t1 : Matrix (Bits 1) (Bits 1) ℂ := Matrix.of fun i j => tMat (i 0) (j 0)

/-- `T†` as a one-qubit matrix indexed by `Bits 1`. -/
noncomputable def tdg1 : Matrix (Bits 1) (Bits 1) ℂ :=
  Matrix.of fun i j => (tMat.conjTranspose) (i 0) (j 0)

/-- `CNOT` on two wires, the first (wire `0` of the gate) the control and the second the target:
`|a, b⟩ ↦ |a, b ⊕ a⟩`. -/
def cnot2 : Matrix (Bits 2) (Bits 2) ℂ :=
  Matrix.of fun i j => if i 0 = j 0 ∧ i 1 = xor (j 1) (j 0) then 1 else 0

/-- A gate of the published circuit model is a gate over `G` (under the encoding `f`): an explicit
one-qubit gate describing exactly `H`, `T` or `T†`, an explicit two-qubit gate describing exactly
`CNOT`, or an uncontrolled oracle gate `O_m`. -/
def IsGGate (f : Str → ℝ) {N : ℕ} : UGate N → Prop
  | .expl 1 _ ent => decodeU f ent = h1 ∨ decodeU f ent = t1 ∨ decodeU f ent = tdg1
  | .expl 2 _ ent => decodeU f ent = cnot2
  | .expl _ _ _ => False
  | .orac κ _ _ => κ = .plain
  | .corac _ _ _ => False

/-- A circuit is **over `G`** (p. 9) under the encoding `f`: every gate is a gate over `G`. -/
def OverG (f : Str → ℝ) (C : UCircuit) : Prop := ∀ g ∈ C.gates, IsGGate f g

/-- A circuit has no oracle gates: every gate is explicit. -/
def OracleFree (C : UCircuit) : Prop :=
  ∀ g ∈ C.gates, ∃ (k : ℕ) (w : Fin k ↪ Fin C.N) (ent : Bits k → Bits k → Str × Str),
    g = .expl k w ent

/-- The NOT gate `|b⟩ ↦ |b ⊕ 1⟩`. -/
def notGate : Matrix (Bits 1) (Bits 1) ℂ := Matrix.of fun i j => if i 0 = !(j 0) then 1 else 0

/-- The Toffoli gate on three wires, controls on wires `0, 1` and target on wire `2`:
`|a, b, c⟩ ↦ |a, b, c ⊕ ab⟩`. -/
def toffoliGate : Matrix (Bits 3) (Bits 3) ℂ :=
  Matrix.of fun i j => if i 0 = j 0 ∧ i 1 = j 1 ∧ i 2 = xor (j 2) (j 0 && j 1) then 1 else 0

/-- The one-qubit unitary that the gate of Lemma 4.3 applies for the control string `y₀y₁`:
`I, H, T, T†` for `00, 01, 10, 11`. -/
noncomputable def selIHTT : Bool → Bool → Matrix Bool Bool ℂ
  | false, false => 1
  | false, true => hMat
  | true, false => tMat
  | true, true => tMat.conjTranspose

/-- The uniformly controlled gate of Lemma 4.3 on three wires: two control wires `0, 1` holding
`y₀y₁` and the target wire `2`, applying `I, H, T, T†` for `y₀y₁ = 00, 01, 10, 11`:
`Σ_y |y⟩⟨y| ⊗ W_y`. -/
noncomputable def ucIHTTGate : Matrix (Bits 3) (Bits 3) ℂ :=
  Matrix.of fun i j => if i 0 = j 0 ∧ i 1 = j 1 then selIHTT (j 0) (j 1) (i 2) (j 2) else 0

/-- `W` is (the matrix of) a **word over `{H, T, T†}`** (p. 13): a finite list of letters from
`{H, T, T†}`, multiplied in application order (the first letter rightmost). -/
def IsHTWord (W : Matrix Bool Bool ℂ) : Prop :=
  ∃ l : List (Matrix Bool Bool ℂ),
    (∀ x ∈ l, x = hMat ∨ x = tMat ∨ x = tMat.conjTranspose) ∧ W = l.reverse.prod

end PSPACEOracleSynth.Main


