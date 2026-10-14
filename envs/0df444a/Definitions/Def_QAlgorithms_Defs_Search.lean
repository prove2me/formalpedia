-- Prove2me | Definitions.Def_QAlgorithms_Defs_Search
-- name    : QAlgorithms_Defs_Search
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-13T17:29:16.167969+00:00
-- url     : https://prove2.me/theorems/d59d2728-95d0-4c0f-b373-d209977c9fe0
-- title:
--   Grover search and amplitude amplification (shared definition layer)
-- statement:
--   Grover search and amplitude amplification (shared definition layer)
--
--   ### QAlgorithms.groverIterate
--
--   For $n \in \mathbb{N}$ and a Boolean function $x : \{0,1\}^n \to \{\text{true},\text{false}\}$ on $n$-bit strings, this defines the $2^n\times 2^n$ complex matrix
--
--   $$
--   G_x = H_n \, R_0 \, H_n \, O_x ,
--   $$
--
--   indexed by $n$-bit strings. The right-most factor is applied first. The factors are:
--
--   - **Hadamard matrix.** $H_n$ has entries $(H_n)_{j,i} = (-1)^{i\cdot j}\,(1/\sqrt2)^n$. Here $i\cdot j$ is the parity (XOR-sum) of the bitwise ANDs $i_k \wedge j_k$.
--   - **Reflection about $0^n$.** $R_0$ is diagonal, with entry $+1$ at the all-zeros string $0^n$ and $-1$ at every other string.
--   - **Phase oracle.** $O_x$ is diagonal, with entry $-1$ at strings $i$ where $x(i)$ is true and $+1$ where $x(i)$ is false.
--
--   For $n = 0$ all matrices are $1\times 1$:
--   - $H_0 = (1)$;
--   - $R_0 = (1)$;
--   - $O_x = (\pm 1)$, depending on $x$ at the empty string.
--
--   ### QAlgorithms.groverSuccessProb
--
--   For $n\in\mathbb{N}$, a Boolean function $x$ on $n$-bit strings, and $k \in \mathbb{N}$, this defines the real number
--
--   $$
--   \sum_{i \in \{0,1\}^n,\ x(i)=\text{true}} \big|\langle i \,|\, G_x^{\,k}\, H_n\, |0^n\rangle\big|^2 .
--   $$
--
--   - **Grover iterate.** $G_x = H_n R_0 H_n O_x$ is the matrix of `groverIterate`: the Hadamard matrix, the reflection with $+1$ at $0^n$ and $-1$ elsewhere, and the phase oracle with $-1$ on marked strings.
--   - **Power.** $G_x^{\,k}$ is the $k$-th matrix power, with $G_x^0 = I$.
--   - **Initial state.** $H_n|0^n\rangle$ is the Hadamard matrix applied to the basis vector of the all-zeros string.
--   - **Probabilities.** $|\langle i|\psi\rangle|^2$ is the squared modulus of the $i$-th coordinate.
--
--   So this is the total computational-basis probability, after $k$ Grover iterations from $H_n|0^n\rangle$, of strings marked by $x$. If no string is marked, the sum is empty and the value is $0$.
--
--   ### QAlgorithms.groverAngle
--
--   For natural numbers $t$ and $N$, this defines the real number
--
--   $$
--   \theta(t,N) = \arcsin\!\sqrt{t/N},
--   $$
--
--   computed in the reals. Two edge cases arise from total-function conventions:
--
--   - **$N = 0$.** Division by zero gives $t/0 = 0$, so the angle is $0$.
--   - **$t > N$.** Then $\sqrt{t/N} > 1$, and the real $\arcsin$ is clamped there, giving $\pi/2$.
--
--   For $0 \le t \le N$ with $N > 0$, the value lies in $[0,\pi/2]$ and is the usual angle with $\sin\theta = \sqrt{t/N}$.
--
--   ### QAlgorithms.ampAmpIterate
--
--   For a finite index type $\iota$ with decidable equality, two arbitrary complex $\iota\times\iota$ matrices $A$ and $R_G$, and a distinguished index $z \in \iota$, this defines the matrix
--
--   $$
--   A\, R_z\, A^{*}\, R_G .
--   $$
--
--   - **Conjugate transpose.** $A^{*}$ is the conjugate transpose of $A$.
--   - **Reflection.** $R_z$ is the diagonal matrix with entry $+1$ at $z$ and $-1$ at every other index.
--   - **No conditions.** Neither $A$ nor $R_G$ is required to be unitary, a reflection, or anything else; they are arbitrary matrices.
-- source:
--   https://github.com/shiy1022/lean-quantum-complexity/blob/main/algorithms/QAlgorithms/Defs/Search.lean . Exact primary-source page locators are preserved in the declaration docstrings.

import Definitions.Def_QAlgorithms_Defs_Fourier
/-!
# Grover search and amplitude amplification (shared definition layer)

The uniform superposition `uniformState` used here is defined in `QAlgorithms.Defs.Fourier`
(it is first needed by the Abelian HSP algorithm).
-/

namespace QAlgorithms

/-- de Wolf p.65 (§7.2, (7.1)): the Grover iterate `G = H^{⊗n} R_0 H^{⊗n} O_{x,±}` (one phase
query per iterate), with `R_0 = reflAt 0` leaving `|0ⁿ⟩` fixed and negating every other basis
state. -/
noncomputable def groverIterate {n : ℕ} (x : Qubits n → Bool) : Matrix (Qubits n) (Qubits n) ℂ :=
  hadamardN n * reflAt (0 : Qubits n) * hadamardN n * phaseOracle x

/-- de Wolf p.65–66 (§7.2): `P_k`, the probability that measuring `G^k H^{⊗n} |0ⁿ⟩` gives a
solution (an `i` with `x_i = 1`). -/
noncomputable def groverSuccessProb {n : ℕ} (x : Qubits n → Bool) (k : ℕ) : ℝ :=
  probEvent (act (groverIterate x ^ k) (act (hadamardN n) (zeroKet n))) fun i => x i = true

/-- de Wolf p.66 (§7.2: "`θ = arcsin √(t/N)`"), p.69 (§7.3, with `p` in place of `t/N`): Grover's
angle. The quotient is real division; statements take `N ≥ 1` (here `N = 2ⁿ`) and require
`1 ≤ t` before dividing by `θ`. -/
noncomputable def groverAngle (t N : ℕ) : ℝ :=
  Real.arcsin (Real.sqrt ((t : ℝ) / (N : ℝ)))

/-- de Wolf p.69 (§7.3): the amplitude-amplification iterate `A R_0 A^{−1} R_G` (first the
reflection `R_G` through the bad state, then the reflection `A R_0 A^{−1}` through `A|0^m⟩`),
with `A` unitary so that `A^{−1} = A†`, and `R_0 = reflAt z` for `z = 0^m`. -/
def ampAmpIterate {ι : Type*} [Fintype ι] [DecidableEq ι] (A RG : Matrix ι ι ℂ) (z : ι) :
    Matrix ι ι ℂ :=
  A * reflAt z * star A * RG

/-! ### Sanity tests -/

/-- With no iterates, `P_0` is the probability of a solution in the uniform superposition. -/
example {n : ℕ} (x : Qubits n → Bool) :
    groverSuccessProb x 0 = probEvent (act (hadamardN n) (zeroKet n)) fun i => x i = true := by
  simp [groverSuccessProb, act]

/-- de Wolf p.67: for `t = N/4`, `θ = π/6`. -/
example : groverAngle 1 4 = Real.pi / 6 := by
  rw [groverAngle, show ((1 : ℕ) : ℝ) / ((4 : ℕ) : ℝ) = (1 / 2) ^ 2 by norm_num,
    Real.sqrt_sq (by norm_num), show (1 / 2 : ℝ) = Real.sin (Real.pi / 6) by
      rw [Real.sin_pi_div_six]]
  exact Real.arcsin_sin (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])

/-- Grover is amplitude amplification with `A = H^{⊗n}` and `R_G = O_{x,±}` (de Wolf p.69), as
`H^{⊗n}` is self-adjoint. -/
example {n : ℕ} (x : Qubits n → Bool) :
    ampAmpIterate (hadamardN n) (phaseOracle x) 0 = groverIterate x := by
  simp [ampAmpIterate, groverIterate, hadamardN_star]

end QAlgorithms


