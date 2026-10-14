-- Prove2me | Definitions.Def_ShorWiki_Defs
-- name    : ShorWiki_Defs
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-13T02:57:47.325541+00:00
-- url     : https://prove2.me/theorems/f8f061fd-22b3-4b50-a3bc-7648cdeae452
-- title:
--   Shor's algorithm: order, the modular-multiplication gate and the order-finding circuit
-- statement:
--   This file fixes the objects in terms of which all statements of the mission are phrased.
--
--   1. **Order.** For integers $N$ and $a$, $\operatorname{ord}_N(a)$ is the multiplicative order of $a$ modulo $N$: when $\gcd(a,N)=1$ it is the smallest positive integer $r$ with $a^r \equiv 1 \pmod N$.
--   2. **Register size.** $n = \lceil \log_2 N \rceil$ is the smallest integer with $N \le 2^n$; the second register has $n$ qubits and the first register has $2n$ qubits. Write $Q = 2^{2n}$.
--   3. **Basis states and tensor products.** A state of a $d$-dimensional register is a vector in $\mathbb C^d$; $|m\rangle$ is the $m$-th standard basis vector, and $|u\rangle \otimes |v\rangle$ is the product state on the two-register space $\mathbb C^{d_1} \otimes \mathbb C^{d_2}$.
--   4. **The modular-multiplication gate.** The $n$-qubit gate $U$ acts on basis states by
--   $$U|k\rangle = \begin{cases} |ak \bmod N\rangle & 0 \le k < N,\\ |k\rangle & N \le k < 2^n.\end{cases}$$
--   5. **Roots of unity and the states $|\psi_j\rangle$.** $\omega_r = e^{2\pi i/r}$, and with $r = \operatorname{ord}_N(a)$,
--   $$|\psi_j\rangle = \frac{1}{\sqrt r}\sum_{k=0}^{r-1} \omega_r^{-kj}\,|a^k \bmod N\rangle .$$
--   6. **Gates of the phase estimation circuit.** $H^{\otimes m}$ is the $m$-fold tensor power of the Hadamard gate, $\langle x|H^{\otimes m}|y\rangle = 2^{-m/2}(-1)^{x\cdot y}$ with $x\cdot y$ the number of bit positions where both $x$ and $y$ have a $1$. $\mathrm{QFT}_{2^m}$ is the quantum Fourier transform, $\langle y|\mathrm{QFT}_{2^m}|x\rangle = 2^{-m/2} e^{2\pi i xy/2^m}$, and $\mathrm{QFT}_{2^m}^{-1}$ is its conjugate transpose. The controlled gate $C\text{-}U^{2^j}$ applies $U^{2^j}$ to the second register exactly when bit $j$ of the first register is $1$.
--   7. **Phase estimation circuit.** With an $m$-qubit first register, the circuit is: $H^{\otimes m}$ on the first register, then $C\text{-}U^{2^0}, C\text{-}U^{2^1}, \dots, C\text{-}U^{2^{m-1}}$, then $\mathrm{QFT}_{2^m}^{-1}$ on the first register.
--   8. **Order-finding output.** The output state of Shor's order-finding subroutine is the phase estimation circuit with $m = 2n$ applied to $|0\rangle^{\otimes 2n} \otimes |1\rangle$.
--   9. **Measurement.** For a two-register state $|\Psi\rangle$, the probability of outcome $k$ when the first register is measured in the computational basis is $\sum_i |\langle k, i|\Psi\rangle|^2$.
--
--   These are the objects of the article's description of the order-finding subroutine; every theorem of the mission is stated in terms of them.
--
--   **Formalization Note** States are plain coordinate vectors `Fin d → ℂ` (not normalized by fiat) and gates are matrices acting by `Matrix.mulVec`; the order is `orderOf (a : ZMod N)`, and $\lceil\log_2 N\rceil$ is `Nat.clog 2 N`. The controlled-power stage is the product of the individual controlled gates, exactly as drawn in the article's circuit diagram, rather than a single block-diagonal operator.
-- source:
--   Wikipedia, "Shor's algorithm", revision oldid=1378862216, https://en.wikipedia.org/w/index.php?title=Shor%27s_algorithm&oldid=1378862216, sections "Classical reduction", "Quantum order-finding subroutine" and "Quantum phase estimation" (PDF pp. 2–5)

import Mathlib

open Matrix Kronecker

namespace ShorWiki

/-- The multiplicative order of `a` modulo `N`: the smallest positive integer `r` with
`a ^ r ≡ 1 (mod N)` (when `a` is coprime to `N`). -/
noncomputable def ord (N a : ℕ) : ℕ := orderOf (a : ZMod N)

/-- The number of qubits `n` of the second register: the smallest `n` with `N ≤ 2 ^ n`,
i.e. `n = ⌈log₂ N⌉`. -/
def regBits (N : ℕ) : ℕ := Nat.clog 2 N

/-- The computational basis state `|m⟩` in a register of dimension `d`
(the zero vector if `m ≥ d`). -/
def ket (d m : ℕ) : Fin d → ℂ := fun i => if (i : ℕ) = m then 1 else 0

/-- The tensor product `|u⟩ ⊗ |v⟩` of two register states. -/
def tensorState {d₁ d₂ : ℕ} (u : Fin d₁ → ℂ) (v : Fin d₂ → ℂ) : Fin d₁ × Fin d₂ → ℂ :=
  fun p => u p.1 * v p.2

/-- The `n`-qubit gate `U` of multiplication by `a` modulo `N`:
`U|k⟩ = |a k mod N⟩` for `0 ≤ k < N` and `U|k⟩ = |k⟩` for `N ≤ k < 2 ^ n`.
The entry `U i k` is the amplitude `⟨i|U|k⟩`. -/
noncomputable def mulModGate (N a n : ℕ) : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ :=
  fun i k =>
    if (k : ℕ) < N then (if (i : ℕ) = a * k % N then 1 else 0)
    else (if i = k then 1 else 0)

/-- The primitive `r`-th root of unity `ω_r = e^{2πi/r}`. -/
noncomputable def omega (r : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / r)

/-- The state `|ψ_j⟩ = r^{-1/2} ∑_{k=0}^{r-1} ω_r^{-kj} |a^k mod N⟩` of the `n`-qubit
second register, where `r = ord N a`. -/
noncomputable def eigState (N a n j : ℕ) : Fin (2 ^ n) → ℂ :=
  fun i => (1 / Real.sqrt (ord N a) : ℂ) *
    ∑ k ∈ Finset.range (ord N a),
      (omega (ord N a) ^ (k * j))⁻¹ * (if (i : ℕ) = a ^ k % N then 1 else 0)

/-- The `m`-fold tensor power `H^{⊗m}` of the Hadamard gate:
`⟨x|H^{⊗m}|y⟩ = 2^{-m/2} (-1)^{x·y}`, where `x·y` is the number of bit positions
`b < m` at which both `x` and `y` have a `1`. -/
noncomputable def hadamardTensor (m : ℕ) : Matrix (Fin (2 ^ m)) (Fin (2 ^ m)) ℂ :=
  fun x y => (1 / Real.sqrt (2 ^ m) : ℂ) *
    (-1) ^ ((Finset.range m).filter (fun b => (x : ℕ).testBit b ∧ (y : ℕ).testBit b)).card

/-- The quantum Fourier transform on `m` qubits:
`⟨y|QFT_{2^m}|x⟩ = 2^{-m/2} e^{2πi x y / 2^m}`. -/
noncomputable def qft (m : ℕ) : Matrix (Fin (2 ^ m)) (Fin (2 ^ m)) ℂ :=
  fun y x => (1 / Real.sqrt (2 ^ m) : ℂ) *
    Complex.exp (2 * Real.pi * Complex.I * (x : ℕ) * (y : ℕ) / 2 ^ m)

/-- The inverse quantum Fourier transform `QFT_{2^m}^{-1} = QFT_{2^m}^†`. -/
noncomputable def qftInv (m : ℕ) : Matrix (Fin (2 ^ m)) (Fin (2 ^ m)) ℂ := (qft m)ᴴ

/-- The controlled gate `C-U^{2^j}`: qubit `j` of the first (`m`-qubit) register controls
the application of `U^{2^j}` to the second (`n`-qubit) register, where `U = mulModGate N a n`.
On `|x⟩|k⟩` it applies `U^{2^j}` to `|k⟩` if bit `j` of `x` is `1`, and does nothing otherwise. -/
noncomputable def controlledPowGate (N a n m j : ℕ) :
    Matrix (Fin (2 ^ m) × Fin (2 ^ n)) (Fin (2 ^ m) × Fin (2 ^ n)) ℂ :=
  fun p q =>
    if p.1 = q.1 then
      (if (q.1 : ℕ).testBit j then (mulModGate N a n ^ (2 ^ j)) p.2 q.2
       else (1 : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) p.2 q.2)
    else 0

/-- The modular-exponentiation stage of the circuit: the product of the controlled gates
`C-U^{2^0}, C-U^{2^1}, …, C-U^{2^{m-1}}`. -/
noncomputable def controlledPowers (N a n m : ℕ) :
    Matrix (Fin (2 ^ m) × Fin (2 ^ n)) (Fin (2 ^ m) × Fin (2 ^ n)) ℂ :=
  ((List.range m).map (fun j => controlledPowGate N a n m j)).prod

/-- The quantum phase estimation circuit for `U = mulModGate N a n` with an `m`-qubit first
register: Hadamard gates on the first register, then the controlled powers of `U`, then the
inverse quantum Fourier transform on the first register. -/
noncomputable def phaseEstimationCircuit (N a n m : ℕ) :
    Matrix (Fin (2 ^ m) × Fin (2 ^ n)) (Fin (2 ^ m) × Fin (2 ^ n)) ℂ :=
  (qftInv m ⊗ₖ (1 : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ)) * controlledPowers N a n m *
    (hadamardTensor m ⊗ₖ (1 : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ))

/-- The output state of Shor's order-finding circuit: phase estimation with a `2n`-qubit
first register, `n = regBits N`, applied to the input `|0⟩^{⊗2n} ⊗ |1⟩`. -/
noncomputable def orderFindingOutput (N a : ℕ) :
    Fin (2 ^ (2 * regBits N)) × Fin (2 ^ regBits N) → ℂ :=
  (phaseEstimationCircuit N a (regBits N) (2 * regBits N)) *ᵥ
    tensorState (ket (2 ^ (2 * regBits N)) 0) (ket (2 ^ regBits N) 1)

/-- The probability of obtaining outcome `k` when measuring the first register of a
two-register state `Ψ` in the computational basis: `∑_i |⟨k, i|Ψ⟩|²`. -/
noncomputable def measureFirst {d₁ d₂ : ℕ} (Ψ : Fin d₁ × Fin d₂ → ℂ) (k : Fin d₁) : ℝ :=
  ∑ i : Fin d₂, ‖Ψ (k, i)‖ ^ 2

end ShorWiki


