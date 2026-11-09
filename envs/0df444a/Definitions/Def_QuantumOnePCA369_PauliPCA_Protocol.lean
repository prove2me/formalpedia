-- Prove2me | Definitions.Def_QuantumOnePCA369_PauliPCA_Protocol
-- name    : QuantumOnePCA369_PauliPCA_Protocol
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:34:48.848564+00:00
-- url     : https://prove2.me/theorems/f2a77d9f-44f1-4b63-9b3b-e053443d2f33
-- title:
--   Non-adaptive Pauli basis measurement protocols and their outcome law
-- statement:
--   The measurement model of Theorem 1.1.
--
--   A **non-adaptive Pauli protocol** on $n$ qubits consists of a finite randomness set $\mathcal R$, drawn uniformly; a finite set of copy indices $\mathcal C$, one fresh copy of the unknown state per index; a setting map assigning to each $r\in\mathcal R$ and $c\in\mathcal C$ a product Pauli basis; and a costed classical decoder from $r$ and the outcome tuple $(y_c)_{c\in\mathcal C}\in(\mathbb F_2^n)^{\mathcal C}$ to an output. The setting map takes neither the state nor any outcome, so the measurements are non-adaptive Pauli basis measurements by construction. The number of copies is $N=|\mathcal C|$.
--
--   For a state $\rho$ the probability of $(r,y)$ is
--   $$w_\rho(r,y)=\frac1{|\mathcal R|}\prod_{c\in\mathcal C}\Pr_\rho[y_c\mid\text{setting}(r,c)],$$
--   the copies being independent. Probabilities of events and expectations of matrix-valued functions of a run are finite sums against $w_\rho$. The running time of a run is $n$ ticks per measured copy plus the cost of the decoder.
--
--   **Algorithm 3's measurement.** A copy measured for the Pauli $\sigma_{x,z}$ on the last $m$ qubits uses $Z$ on the first $\ell$ qubits and, on qubit $\ell+j$, the basis $X$, $Y$, $Z$ for the label $(x_j,z_j)=(1,0),(1,1),(0,1)$; at an identity site $(0,0)$ it measures $Z$ and ignores the bit. Its $\pm1$ value is $O=\prod(-1)^{y_{\ell+j}}$ over the non-identity sites ($O=1$ for $\sigma_{0,0}$).
--
--   **Output descriptions.** An output vector of $\mathbb C^{2^n}$ is described either by a computational-basis string or by a dense array of $2^n$ complex amplitudes.
-- source:
--   Dutch Hansen, Jerry Li, Quantum 1-PCA with Pauli Measurements in Nearly Linear Time, STOC 2027 submission #369 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/369.pdf, pp. 1–2 (non-adaptive single-qubit Pauli basis measurements, Theorem 1.1), p. 6 (Pauli eigenstate projections), p. 10, Algorithm 3 lines 10–12

import Mathlib
import Definitions.Def_MITMSynthesis_Timed
import Definitions.Def_QuantumOnePCA369_PauliPCA_Basic

namespace QuantumOnePCA369.PauliPCA

open MITMSynthesis

/-! Non-adaptive single-copy Pauli-basis measurement protocols (§1–2) and their outcome law. -/

/-- A **non-adaptive Pauli basis measurement protocol** on `n` qubits with output type `Out`.
Internal randomness `r ∈ Rand` is drawn uniformly; for every copy index `c ∈ Copy` one fresh copy
of the unknown state is measured in the product Pauli basis `setting r c`; the classical decoder
maps `r` and all outcomes to a costed output. The settings depend on neither the state nor any
outcome, so non-adaptivity and the restriction to Pauli bases hold by the type. -/
structure PauliProtocol (n : ℕ) (Out : Type) where
  /-- internal randomness, drawn uniformly -/
  Rand : Type
  [randFintype : Fintype Rand]
  [randDecEq : DecidableEq Rand]
  /-- one index per measured copy -/
  Copy : Type
  [copyFintype : Fintype Copy]
  [copyDecEq : DecidableEq Copy]
  /-- the Pauli basis in which each copy is measured -/
  setting : Rand → Copy → PauliSetting n
  /-- the classical post-processing, with its unit-cost running time -/
  decode : Rand → (Copy → Bits n) → Timed Out

attribute [instance] PauliProtocol.randFintype PauliProtocol.randDecEq
  PauliProtocol.copyFintype PauliProtocol.copyDecEq

namespace PauliProtocol

variable {n : ℕ} {Out : Type}

/-- The number `N` of copies of the state the protocol consumes. -/
def copies (P : PauliProtocol n Out) : ℕ := Fintype.card P.Copy

/-- Probability of internal randomness `r` and outcome tuple `y` when the copies are independent
copies of `ρ`: `|Rand|⁻¹ ∏_c Pr_ρ[y_c | setting r c]` (Born rule, p. 6). -/
noncomputable def weight (P : PauliProtocol n Out) (ρ : Matrix (Bits n) (Bits n) ℂ)
    (r : P.Rand) (y : P.Copy → Bits n) : ℝ :=
  (Fintype.card P.Rand : ℝ)⁻¹ * ∏ c, bornProb ρ (P.setting r c) (y c)

/-- Probability of an event of the run. -/
noncomputable def prob (P : PauliProtocol n Out) (ρ : Matrix (Bits n) (Bits n) ℂ)
    (E : P.Rand → (P.Copy → Bits n) → Prop) : ℝ := by
  classical
  exact ∑ r, ∑ y, if E r y then P.weight ρ r y else 0

/-- Expectation of a matrix-valued function of the run. -/
noncomputable def expect {κ : Type} (P : PauliProtocol n Out) (ρ : Matrix (Bits n) (Bits n) ℂ)
    (f : P.Rand → (P.Copy → Bits n) → Matrix κ κ ℂ) : Matrix κ κ ℂ :=
  ∑ r, ∑ y, ((P.weight ρ r y : ℝ) : ℂ) • f r y

/-- Output of the run with randomness `r` and outcomes `y`. -/
def output (P : PauliProtocol n Out) (r : P.Rand) (y : P.Copy → Bits n) : Out :=
  (P.decode r y).val

/-- Running time of a run: `n` ticks per measured copy plus the decoder's cost. -/
def runTime (P : PauliProtocol n Out) (r : P.Rand) (y : P.Copy → Bits n) : ℕ :=
  n * P.copies + (P.decode r y).cost

end PauliProtocol

/-- Measurement basis at a qubit carrying the Pauli label `(a, b) = (x_j, z_j)`: `(1,0) ↦ X`,
`(1,1) ↦ Y`, `(0,1) ↦ Z`; at an identity site `(0,0)` the qubit is measured in `Z` and the bit
ignored. -/
def siteBasis (a b : ZMod 2) : PauliBasis :=
  if a = 1 then (if b = 1 then PauliBasis.Y else PauliBasis.X) else PauliBasis.Z

/-- The setting of Algorithm 3 for one copy: `Z` on the first `ℓ` qubits and the basis of
`σ_{x,z}` on the last `m` qubits (`ℓ + m = n`). -/
def alg3Setting (n ℓ m : ℕ) (x z : Bits m) : PauliSetting n :=
  fun i => if i.val < ℓ then PauliBasis.Z else
    if h : i.val - ℓ < m then siteBasis (x ⟨i.val - ℓ, h⟩) (z ⟨i.val - ℓ, h⟩) else PauliBasis.Z

/-- The `±1` outcome `O` of measuring `σ_{x,z}` on the last `m` qubits, from the outcome bits `y`:
the product of `(-1)^{y_j}` over the non-identity sites (`1` for `σ_{0,0}`). -/
def pauliOutcome {n : ℕ} (ℓ m : ℕ) (x z : Bits m) (y : Bits n) : ℂ :=
  ∏ t : Fin m, if x t = 0 ∧ z t = 0 then 1 else sgn (suffixBits ℓ m y t)

/-- A classical description of a vector of `ℂ^{2^n}`: a computational basis vector, or a dense
complex array. -/
inductive VecDesc (n : ℕ)
  | basis (x : Bits n)
  | dense (v : Bits n → ℂ)

/-- The vector described. -/
def VecDesc.toVec {n : ℕ} : VecDesc n → Bits n → ℂ
  | .basis x => fun y => if y = x then 1 else 0
  | .dense v => v

end QuantumOnePCA369.PauliPCA


