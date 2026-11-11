-- Prove2me | Definitions.Def_TightPQRepetition_Main_Oracle
-- name    : TightPQRepetition_Main_Oracle
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T23:40:06.68736+00:00
-- url     : https://prove2.me/theorems/6826e3d9-b5ba-4909-afea-809191e25997
-- title:
--   Coherent sampler states, the oracle $U_b$ and oracle circuits without access to $R$
-- statement:
--   Let a sampler map $c$ uniform coins to $L$ output bits. Its **coherent state** on registers $R$ ($c$ qubits) and $E$ ($L$ qubits) is
--   $$|D\rangle_{RE}=2^{-c/2}\sum_r|r\rangle_R|D(r)\rangle_E.$$
--   With a single-qubit register $O$, Equation (1) defines
--   $$U=X_O\otimes|D\rangle\langle D|_{RE}+I_O\otimes(I-|D\rangle\langle D|)_{RE}.$$
--   An **oracle circuit** on $O,R,E,I$ alternates gates that act as the identity on $R$ with calls of $U$ on $ORE$; these are the only operations touching $R$.
--
--   For such a circuit $V^U$ and pure advice $|\phi\rangle_I$, put $|\psi\rangle=V^U|0\rangle_O|D\rangle_{RE}|\phi\rangle_I$, let $\rho=\mathrm{Tr}_{RE}(|D\rangle\langle D|\,|\psi\rangle\langle\psi|\,|D\rangle\langle D|)$, a subnormalized state on $OI$, and let the **flagged state** be
--   $$\|(I-|D\rangle\langle D|)_{RE}|\psi\rangle\|^2\,|0\rangle\langle0|\otimes|\bot\rangle\langle\bot|+|1\rangle\langle1|\otimes\rho.$$
--   These objects express that a distinguisher can test whether $RE$ is still in its state without reading the coins.
--
--   **Formalization Note** Registers are consecutive wires in the order $O,R,E,I$. The flagged state lives on `Option` of the basis of $OI$, the value `none` being the failure branch: the flag and $\bot$ are orthogonal to the support of $\rho$. The reused `QAlgorithms.OracleCircuit` provides the oracle circuits, restricted by `IsRespectful`.
-- source:
--   Zvika Brakerski, Andrew Huang, Yael Tauman Kalai, Nicholas Spooner, STOC 2027 submission #158 (October 2026), SHA-256 269f233ccbc44af16ba1b9aceb41299c2242cca048f65729c5fd3451cb6cd0b8, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/158.pdf, Definition 4 and footnotes 10–12, printed pp. 14–15 / PDF pp. 16–17

import Mathlib
import Definitions.Def_TightPQRepetition_Main_Encryption

namespace TightPQRepetition.Main

/-!
Brakerski, Huang, Kalai, Spooner, STOC 2027 submission #158, §4 (PDF pp. 16–17, Definition 4 and
footnotes 11–12): coherent purifications of samplers, the reflection oracle `U_b`, and oracle
circuits with no direct access to the purifying register `R`.

The register layout, at one security parameter, is `O R E I` on `1 + c + L + i` wires, in this
order: the single qubit `O`, the coins `R` of the sampler, its output `E`, and a workspace `I`.
-/

open QAlgorithms Matrix
open scoped ComplexConjugate

/-- The wires of a register `O R E I`. -/
abbrev OREIWires (c L i : ℕ) := 1 + c + L + i

/-- The qubit `O` of a basis string. -/
def sliceO {c L i : ℕ} (y : Qubits (OREIWires c L i)) : Qubits 1 :=
  fun a => y (Fin.castAdd i (Fin.castAdd L (Fin.castAdd c a)))

/-- The coins `R` of a basis string. -/
def sliceR {c L i : ℕ} (y : Qubits (OREIWires c L i)) : Qubits c :=
  fun a => y (Fin.castAdd i (Fin.castAdd L (Fin.natAdd 1 a)))

/-- The sample register `E` of a basis string. -/
def sliceE {c L i : ℕ} (y : Qubits (OREIWires c L i)) : Qubits L :=
  fun a => y (Fin.castAdd i (Fin.natAdd (1 + c) a))

/-- The workspace `I` of a basis string. -/
def sliceI {c L i : ℕ} (y : Qubits (OREIWires c L i)) : Qubits i :=
  fun a => y (Fin.natAdd (1 + c + L) a)

/-- The basis string with the given parts. -/
def assemble {c L i : ℕ} (o : Qubits 1) (r : Qubits c) (e : Qubits L) (x : Qubits i) :
    Qubits (OREIWires c L i) :=
  Fin.append (Fin.append (Fin.append o r) e) x

/-- The state `|D⟩_{RE} ∝ ∑_r |r⟩_R |D(r)⟩_E` of a sampler `f` with `c` coins and `L` output bits
(Definition 4), as a function of the basis labels of `R` and `E`. -/
noncomputable def sampleAmp (c L : ℕ) (f : Bits → Bits) (r : Qubits c) (e : Qubits L) : ℂ :=
  if toBits e = f (toBits r) then (((Real.sqrt 2) ^ c)⁻¹ : ℝ) else 0

/-- `|D⟩⟨D|` on `RE`, tensored with the identity on `O` and `I`. -/
noncomputable def sampleProj (c L i : ℕ) (f : Bits → Bits) :
    Matrix (Qubits (OREIWires c L i)) (Qubits (OREIWires c L i)) ℂ :=
  Matrix.of fun y z =>
    if sliceO y = sliceO z ∧ sliceI y = sliceI z then
      sampleAmp c L f (sliceR y) (sliceE y) * conj (sampleAmp c L f (sliceR z) (sliceE z))
    else 0

/-- The qubit `O` of a basis string of `ORE`. -/
def oreFlag {c L : ℕ} (y : Qubits (1 + c + L)) : Bool := y (Fin.castAdd L (Fin.castAdd c 0))

/-- The coins `R` of a basis string of `ORE`. -/
def oreCoins {c L : ℕ} (y : Qubits (1 + c + L)) : Qubits c :=
  fun a => y (Fin.castAdd L (Fin.natAdd 1 a))

/-- The sample `E` of a basis string of `ORE`. -/
def oreSample {c L : ℕ} (y : Qubits (1 + c + L)) : Qubits L := fun a => y (Fin.natAdd (1 + c) a)

/-- The unitary `U_{b,λ} = X_O ⊗ |D⟩⟨D|_{RE} + I_O ⊗ (I - |D⟩⟨D|)_{RE}` of Equation (1), on the
`1 + c + L` wires of `ORE`. -/
noncomputable def reflectionOracle (c L : ℕ) (f : Bits → Bits) :
    Matrix (Qubits (1 + c + L)) (Qubits (1 + c + L)) ℂ :=
  Matrix.of fun y z =>
    let P : ℂ := sampleAmp c L f (oreCoins y) (oreSample y) *
      conj (sampleAmp c L f (oreCoins z) (oreSample z))
    if oreFlag y = oreFlag z then
      (1 : Matrix (Qubits (1 + c + L)) (Qubits (1 + c + L)) ℂ) y z - P
    else P

/-- An oracle circuit on `O R E I` with one oracle on `ORE`. -/
abbrev OREICircuit (c L i : ℕ) :=
  OracleCircuit smallGates (fun _ : Fin 1 => 1 + c + L) (OREIWires c L i)

/-- The wires `ORE`, in order, inside `O R E I`. -/
def oreWires (c L i : ℕ) : Fin (1 + c + L) ↪ Fin (OREIWires c L i) :=
  ⟨Fin.castAdd i, Fin.castAdd_injective _ _⟩

/-- Footnotes 11 and 12: every gate acts as the identity on `R`, and every oracle call is a plain
application of `U_{b,λ}` on `ORE`. -/
def IsRespectful {c L i : ℕ} (C : OREICircuit c L i) : Prop :=
  ∀ st ∈ C, match st with
    | .gate g => ∀ a, ∀ b : Fin c,
        g.wires a ≠ Fin.castAdd i (Fin.castAdd L (Fin.natAdd 1 b))
    | .query _ adj ctrl w _ => adj = false ∧ ctrl = none ∧ HEq w (oreWires c L i)

/-- The unitary `V^{U}` of an oracle circuit given the oracle `U`. -/
noncomputable def OREICircuit.op {c L i : ℕ} (C : OREICircuit c L i)
    (U : Matrix (Qubits (1 + c + L)) (Qubits (1 + c + L)) ℂ) :
    Matrix (Qubits (OREIWires c L i)) (Qubits (OREIWires c L i)) ℂ :=
  OracleCircuit.unitary C (fun _ => U)

/-- The input `|0⟩_O |D⟩_{RE} |ϕ⟩_I`. -/
noncomputable def oreiInput (c L i : ℕ) (f : Bits → Bits) (φ : EuclideanSpace ℂ (Qubits i)) :
    EuclideanSpace ℂ (Qubits (OREIWires c L i)) :=
  WithLp.toLp 2 fun y =>
    if sliceO y = (fun _ => false) then sampleAmp c L f (sliceR y) (sliceE y) * φ (sliceI y) else 0

/-- `|ψ_{b,V}⟩ = V^{U_b} |0⟩_O |D_b⟩_{RE} |ϕ⟩_I`. -/
noncomputable def oracleOutput (c L i : ℕ) (f : Bits → Bits) (C : OREICircuit c L i)
    (φ : EuclideanSpace ℂ (Qubits i)) : EuclideanSpace ℂ (Qubits (OREIWires c L i)) :=
  act (C.op (reflectionOracle c L f)) (oreiInput c L i f φ)

/-- `TrRE(|D⟩⟨D| · |ψ⟩⟨ψ| · |D⟩⟨D|)`, a subnormalized state on `O I`. -/
noncomputable def returnedState (c L i : ℕ) (f : Bits → Bits)
    (ψ : EuclideanSpace ℂ (Qubits (OREIWires c L i))) :
    Matrix (Qubits 1 × Qubits i) (Qubits 1 × Qubits i) ℂ :=
  Matrix.of fun p q => ∑ r : Qubits c, ∑ e : Qubits L,
    (act (sampleProj c L i f) ψ) (assemble p.1 r e p.2) *
      conj ((act (sampleProj c L i f) ψ) (assemble q.1 r e q.2))

/-- `w · |0⟩⟨0| ⊗ |⊥⟩⟨⊥| + |1⟩⟨1| ⊗ ρ`. The flag and `⊥` are orthogonal to the support of `ρ`, so
the state lives on `Option` of the index of `ρ`, with `none` the failure branch. -/
def flagged {β : Type} (w : ℝ) (ρ : Matrix β β ℂ) : Matrix (Option β) (Option β) ℂ :=
  Matrix.of fun p q => match p, q with
    | none, none => (w : ℂ)
    | some x, some y => ρ x y
    | _, _ => 0

/-- `∥(I - |D⟩⟨D|)_{RE} |ψ⟩∥² · |0⟩⟨0| ⊗ |⊥⟩⟨⊥| + |1⟩⟨1| ⊗ ρ`, the flagged state of Lemma 4.3. -/
noncomputable def flaggedReturn (c L i : ℕ) (f : Bits → Bits)
    (ψ : EuclideanSpace ℂ (Qubits (OREIWires c L i))) :
    Matrix (Option (Qubits 1 × Qubits i)) (Option (Qubits 1 × Qubits i)) ℂ :=
  flagged (‖act (1 - sampleProj c L i f) ψ‖ ^ 2) (returnedState c L i f ψ)

/-- Two samplers on common registers: `D b lam` maps `c lam` coins to a string of `L lam` bits,
by polynomial-size circuits (Definition 4). -/
def IsSamplerPair (c L : ℕ → ℕ) (D : Bool → ℕ → Bits → Bits) : Prop :=
  PolyBound c ∧ PolyBound L ∧
    ∀ b, Efficient (D b) ∧ ∀ lam r, r.length = c lam → (D b lam r).length = L lam

/-- A polynomial-size family of oracle circuits (footnote 12) acting on `I` of `i lam` qubits. -/
def IsOracleFamily (c L i : ℕ → ℕ) (C : (lam : ℕ) → OREICircuit (c lam) (L lam) (i lam)) : Prop :=
  PolyBound i ∧ PolyBound (fun lam => (C lam).length) ∧ ∀ lam, IsRespectful (C lam)

/-- The probability that the distinguisher `S^{U}` on `|0⟩_O |D⟩_{RE} |ϕ⟩_I`, with `out` a wire
outside `R`, outputs `1`. -/
noncomputable def oracleAccept (c L i : ℕ) (f : Bits → Bits) (C : OREICircuit c L i)
    (out : Fin (OREIWires c L i)) (φ : EuclideanSpace ℂ (Qubits i)) : ℝ :=
  ‖act (outcomeProj [out] [true]) (oracleOutput c L i f C φ)‖ ^ 2

end TightPQRepetition.Main


