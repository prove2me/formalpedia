-- Prove2me | Definitions.Def_PRUMicrocrypt_phaseHadamardU
-- name    : PRUMicrocrypt_phaseHadamardU
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T22:26:54.339179+00:00
-- url     : https://prove2.me/theorems/a85c5634-a2dd-4b0d-9e3f-f594b7d2c3a3
-- title:
--   Five-phase construction $U(S)=F_5HF_4HF_3HF_2HF_1$ and the interface $\mathrm{Select}(U)$
-- statement:
--   Let $N=2^n$ and identify $\{0,1\}^n$ with $\{0,\dots,N-1\}$ by reading a bit string as a big-endian binary number. The $n$-qubit **Hadamard transform** is $\langle y|H|x\rangle=(-1)^{x\cdot y}/\sqrt N$, with $x\cdot y=\sum_i x_iy_i \bmod 2$. A **phase table** is a function $h:\mathbb F_2^n\to\mathbb Z_N$, and its **phase layer** is the diagonal unitary $F|x\rangle=e^{2\pi i h(x)/N}|x\rangle$.
--
--   For a sample $S=(h_1,\dots,h_5)$ of five phase tables, the **five-phase construction** is
--
--   $$U(S)=F_5\,H\,F_4\,H\,F_3\,H\,F_2\,H\,F_1 .$$
--
--   Access to a unitary $U$ means coherent access to the five-branch interface
--
--   $$\mathrm{Select}(U)=P_0\otimes I+P_1\otimes U+P_2\otimes U^\dagger+P_3\otimes U^T+P_4\otimes \overline U,$$
--
--   where $P_0,\dots,P_4$ are the projections of a selector register and transpose and conjugation are taken in the computational basis. All five branches use the same matrix.
--
--   This is the object of the whole mission: Theorem 4.1 compares $U(S)$ for uniform $S$ with a Haar-random unitary, and the keyed construction of Section 5 is $U(S_k)$ for tables read from a random oracle.
--
--   **Formalization Note** $\mathbb Z_N$ is represented by $\{0,\dots,N-1\}$ (`Fin N`); `S j` is the table $h_{j+1}$. The selector is $\mathbb C^5$ with $P_a=|a\rangle\langle a|$; an arbitrary selector space with projections summing to $I$ embeds isometrically into $\mathbb C^5\otimes(\text{reference})$, and every algorithm in the mission carries a reference register.
-- source:
--   Gulati–Khurana–Tomer, How to Build Pseudorandom Unitaries in Microcrypt, arXiv:2610.03711 (version of 2026-11-03, sha256 b591a3e5…), §3, p.20; §3.1, p.21

import Mathlib

set_option autoImplicit false

namespace PRUMicrocrypt

open Matrix

/-- The computational basis of `n` qubits, `{0,1}ⁿ ≅ {0, …, N − 1}` with `N = 2ⁿ` (§3, p.20).
A. Gulati, D. Khurana, K. Tomer, *How to Build Pseudorandom Unitaries in Microcrypt*,
arXiv:2610.03711 (version of 2026-11-03, sha256 b591a3e5…), §3, p.20.

**Formalization Note.** A basis label `x : Idx n` is the integer whose big-endian binary expansion
is the bit string `x ∈ {0,1}ⁿ`: bit `i` (for `i = 0, …, n − 1`, read left to right) is the
coefficient of `2^(n−1−i)`. `Idx n` is `Fin (2 ^ n)`, the index type of the published Haar
measure `QAlgorithms.Schur.unitaryHaar (2 ^ n)`. -/
abbrev Idx (n : ℕ) := Fin (2 ^ n)

/-- Bit `i` (left to right, big-endian) of the basis label `x ∈ {0,1}ⁿ`. -/
def bitOf {n : ℕ} (x : Idx n) (i : Fin n) : Bool :=
  x.val.testBit (n - 1 - i.val)

/-- The basis label with big-endian bit string `b ∈ {0,1}ⁿ`: `∑ᵢ bᵢ 2^(n−1−i)`.

**Formalization Note.** The sum is always `< 2ⁿ`; the reduction modulo `2ⁿ` only supplies the
bound for the `Fin` type and never changes the value. -/
def idxOfBits (n : ℕ) (b : Fin n → Bool) : Idx n :=
  ⟨(∑ i : Fin n, if b i then 2 ^ (n - 1 - i.val) else 0) % 2 ^ n,
    Nat.mod_lt _ (Nat.two_pow_pos n)⟩

/-- The bit string `x ∈ {0,1}ⁿ` of a basis label, as a word of length `n` (left to right). -/
def bitList {n : ℕ} (x : Idx n) : List Bool :=
  List.ofFn (bitOf x)

/-- The inner product `x · y = ∑ᵢ xᵢ yᵢ mod 2` of two bit strings in `𝔽₂ⁿ`. -/
def dot {n : ℕ} (x y : Idx n) : Bool :=
  decide ((Finset.univ.filter fun i : Fin n => bitOf x i && bitOf y i).card % 2 = 1)

/-- The `n`-qubit Hadamard transform `H`, `⟨y|H|x⟩ = (−1)^{x·y}/√N`, `N = 2ⁿ` (§3, p.20). -/
noncomputable def hadamard (n : ℕ) : Matrix (Idx n) (Idx n) ℂ :=
  fun y x => (if dot y x then -1 else 1) / (Real.sqrt (2 ^ n) : ℂ)

/-- The diagonal phase layer `F|x⟩ = e^{2πi h(x)/N}|x⟩` of a table `h : 𝔽₂ⁿ → ℤ_N`, `N = 2ⁿ`
(§3, p.20).

**Formalization Note.** `ℤ_N` is represented by `Fin N`; the phase uses the representative
`h(x) ∈ {0, …, N − 1}`, so `e^{2πi h(x)/N}` is the same for every representative. -/
noncomputable def phaseLayer (n : ℕ) (h : Idx n → Fin (2 ^ n)) : Matrix (Idx n) (Idx n) ℂ :=
  Matrix.diagonal fun x =>
    Complex.exp (2 * Real.pi * Complex.I * ((h x).val : ℂ) / ((2 : ℂ) ^ n))

/-- A sample `S = (h₁, …, h₅)` of the five phase tables `hⱼ : 𝔽₂ⁿ → ℤ_N` (§3, p.20).

**Formalization Note.** `S j` is the table `h_{j+1}` (`j : Fin 5`, so `S 0 = h₁`, …, `S 4 = h₅`).
A uniform `S` (five independent functions with independent uniform values) is the uniform
distribution on this finite type. -/
abbrev Tables (n : ℕ) := Fin 5 → Idx n → Fin (2 ^ n)

/-- **The five-phase construction** (§3, p.20): for `S = (h₁, …, h₅)`,
`U(S) = F₅ H F₄ H F₃ H F₂ H F₁` with `Fⱼ|x⟩ = e^{2πi hⱼ(x)/N}|x⟩` and `H` the `n`-qubit Hadamard
transform, `N = 2ⁿ`.
A. Gulati, D. Khurana, K. Tomer, *How to Build Pseudorandom Unitaries in Microcrypt*,
arXiv:2610.03711 (version of 2026-11-03, sha256 b591a3e5…), §3, p.20.

**Formalization Note.** `U(S)` is a matrix in the computational basis `Idx n` (big-endian labels);
it is unitary because each factor is. -/
noncomputable def phaseHadamardU {n : ℕ} (S : Tables n) : Matrix (Idx n) (Idx n) ℂ :=
  phaseLayer n (S 4) * hadamard n * phaseLayer n (S 3) * hadamard n * phaseLayer n (S 2) *
    hadamard n * phaseLayer n (S 1) * hadamard n * phaseLayer n (S 0)

/-- The five branches `(U₀, U₁, U₂, U₃, U₄) = (I, U, U†, Uᵀ, Ū)` of the oracle interface (§3.1,
p.21). Transpose and conjugation are taken in the fixed computational basis. -/
noncomputable def branchOp {n : ℕ} (U : Matrix (Idx n) (Idx n) ℂ) :
    Fin 5 → Matrix (Idx n) (Idx n) ℂ
  | 0 => 1
  | 1 => U
  | 2 => Uᴴ
  | 3 => Uᵀ
  | 4 => U.map star

/-- **The coherent oracle interface** (§3.1, p.21):
`Select(U) = P₀ ⊗ I + P₁ ⊗ U + P₂ ⊗ U† + P₃ ⊗ Uᵀ + P₄ ⊗ Ū` on selector ⊗ query register.
A. Gulati, D. Khurana, K. Tomer, *How to Build Pseudorandom Unitaries in Microcrypt*,
arXiv:2610.03711 (version of 2026-11-03, sha256 b591a3e5…), §3.1, p.21.

**Formalization Note.** The selector register is `ℂ⁵` with `P_a = |a⟩⟨a|`; an arbitrary selector
space with projections `P₀ + ⋯ + P₄ = I` embeds isometrically into `ℂ⁵ ⊗ (reference)` so that
`Select(U)` is intertwined, and every algorithm below carries an arbitrary reference register.
All five branches use the same matrix `U` (one fixed global phase). -/
noncomputable def selectOp {n : ℕ} (U : Matrix (Idx n) (Idx n) ℂ) :
    Matrix (Fin 5 × Idx n) (Fin 5 × Idx n) ℂ :=
  fun p q => if p.1 = q.1 then branchOp U p.1 p.2 q.2 else 0

end PRUMicrocrypt


