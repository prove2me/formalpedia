-- Prove2me | Definitions.Def_ConstOverheadCompile_Main_Supplement_PhaseGradient
-- name    : ConstOverheadCompile_Main_Supplement_PhaseGradient
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T18:28:55.800204+00:00
-- url     : https://prove2.me/theorems/47d7c5b0-1c28-421e-b377-6c3d91ecaba0
-- title:
--   The dyadic gate set $\mathcal D$, the phase gradient state $|\mathrm{grad}_n\rangle$ in the forms of Eqs. (6) and (36), and ancilla padding/projection
-- statement:
--   Write $R(\theta)=\mathrm{diag}(1,e^{i\theta})$ and $\mathcal G=\{H,T,\mathrm{CNOT}\}$ (both from the published gate-set definitions of this mission). This file fixes the objects of Theorems 2, 3 and 10.
--
--   1. **The dyadic gate set** (Eq. (4)):
--   $$\mathcal D=\mathcal G\cup\{R(\pi/2^j): j\ge 1\}.$$
--   The index starts at $j=1$, so the largest dyadic rotation is $R(\pi/2)=S$.
--
--   2. **The phase gradient state** (Eq. (6)): on $n$ qubits,
--   $$|\mathrm{grad}_n\rangle=\bigotimes_{j=0}^{n-1}R(\pi/2^j)|+\rangle,\qquad R(\theta)|+\rangle=\tfrac{1}{\sqrt2}\big(|0\rangle+e^{i\theta}|1\rangle\big),$$
--   with the factor $j$ on wire $j$ (so wire $0$ holds $|-\rangle$).
--
--   3. **The same state in the form of Eq. (36)** (= Eq. (7)): with $Z_j$ the Pauli $Z$ on the $j$-th qubit,
--   $$e^{-iH}|+^n\rangle,\qquad H=\pi\sum_{j=1}^n 2^{-j}Z_j .$$
--   Since $H$ is diagonal, its amplitude at a basis string $x$ is $2^{-n/2}e^{-i\lambda(x)}$, where $\lambda(x)=\pi\sum_{j=1}^n 2^{-j}(-1)^{x_j}$. The paper notes that it agrees with Eq. (6) up to a global phase (the phase is $e^{-i\pi(1-2^{-n})}$).
--
--   4. **Ancillas.** For a vector $\psi$ on $n$ qubits, $\psi\otimes|0^a\rangle$ is the vector on $n+a$ qubits with the data on the first $n$ wires and the ancillas, all in $|0\rangle$, on the last $a$ wires. For a vector $\psi$ on $n+a$ qubits, $(I\otimes\langle 0^a|)\psi$ is the (unnormalized) vector on the $n$ data qubits obtained by keeping the component in which every ancilla is $|0\rangle$.
--
--   These objects are the targets of the phase gradient preparation results (Theorems 3 and 10) and the input gate set of Theorem 2.
--
--   **Formalization Note** Qubit $j$ of the paper ($1$-based) is wire $j-1$. Vectors are elements of `EuclideanSpace ℂ (Qubits n)`. The phase gradient state of Eq. (36) is defined by its amplitudes (the exponential of a diagonal operator), not through a matrix exponential.
-- source:
--   Chenyi Zhang, Xinyu Tan, Robin Kothari, David Gosset, Craig Gidney, Quantum circuit compilation with constant overhead, STOC 2027 submission #397 (October 2026), source.pdf SHA-256 b848604016de1821f5f693c59f328e0b2a9e535bca0b37bb664e6f40dbe3681f, p.2 Eq. (4); p.3 Eq. (6); p.4 Eq. (7); p.11 Eqs. (36)–(37)

import Mathlib
import Definitions.Def_ConstOverheadCompile_Main_GateSets
import Definitions.Def_ConstOverheadCompile_Main_Gadgets

namespace ConstOverheadCompile.Main.Supplement

open QAlgorithms ConstOverheadCompile.Main

/-- Eq. (4), p.2: the dyadic gate set `𝒟 = 𝒢 ∪ {R(π/2^j) : j ⩾ 1}`, where
`𝒢 = {H, T, CNOT}` (`CliffordT`) and `R(θ) = diag(1, e^{iθ})` (`rot`). The index `j` starts at
`1`, so the largest dyadic rotation is `R(π/2) = S`. -/
def dyadicGates : Set Gate :=
  CliffordT ∪ {g | ∃ j : ℕ, 1 ≤ j ∧ g = Gate.ofMatrix1 (rot (Real.pi / 2 ^ j))}

/-- Eq. (6), p.3: the phase gradient state `|grad_n⟩ = ⊗_{j=0}^{n-1} R(π/2^j)|+⟩` on `n` qubits.
Wire `j` (`0 ≤ j ≤ n - 1`) carries `R(π/2^j)|+⟩ = (|0⟩ + e^{iπ/2^j}|1⟩)/√2` (`resourceVec`), so
the amplitude at the basis string `x` is `∏_j resourceVec (π/2^j) (x j)`. -/
noncomputable def gradState (n : ℕ) : EuclideanSpace ℂ (Qubits n) :=
  WithLp.toLp 2 fun x => ∏ j : Fin n, resourceVec (Real.pi / 2 ^ (j : ℕ)) (x j)

/-- Eq. (36), p.11: the eigenvalue of the diagonal Hamiltonian `H = π Σ_{j=1}^n 2^{-j} Z_j` on
the computational basis string `x`. The paper's qubit `j` is wire `j - 1`, and `Z_j` has
eigenvalue `+1` on bit `0` and `-1` on bit `1`. -/
noncomputable def gradHamEig (n : ℕ) (x : Qubits n) : ℝ :=
  Real.pi * ∑ j : Fin n, ((1 : ℝ) / 2) ^ ((j : ℕ) + 1) * (if x j then -1 else 1)

/-- Eq. (36), p.11 (= Eq. (7), p.4): the phase gradient state in the form `e^{-iH}|+^n⟩` with
`H = π Σ_{j=1}^n 2^{-j} Z_j`. Since `H` is diagonal, the amplitude at `x` is
`2^{-n/2} e^{-i λ(x)}` with `λ(x)` its eigenvalue (`gradHamEig`). It equals `gradState n` up to
the global phase `e^{-iπ(1 - 2^{-n})}`. -/
noncomputable def gradExp (n : ℕ) : EuclideanSpace ℂ (Qubits n) :=
  WithLp.toLp 2 fun x =>
    Complex.exp (-((gradHamEig n x : ℝ) : ℂ) * Complex.I) * ((((Real.sqrt 2)⁻¹) ^ n : ℝ) : ℂ)

/-- The vector `ψ ⊗ |0^a⟩` on `n + a` wires: the data `ψ` on wires `0, …, n - 1`, the `a`
ancillas (wires `n, …, n + a - 1`) in `|0⟩`. -/
noncomputable def padZero {n : ℕ} (a : ℕ) (ψ : EuclideanSpace ℂ (Qubits n)) :
    EuclideanSpace ℂ (Qubits (n + a)) :=
  WithLp.toLp 2 fun z =>
    ψ (fun i : Fin n => z (Fin.castAdd a i)) *
      (if ∀ i : Fin a, z (Fin.natAdd n i) = false then 1 else 0)

/-- The vector `(I ⊗ ⟨0^a|)ψ` on the `n` data wires: the component of `ψ` (on `n + a` wires,
data first) whose `a` ancillas are all in `|0⟩`, without renormalization. -/
noncomputable def projZero {n a : ℕ} (ψ : EuclideanSpace ℂ (Qubits (n + a))) :
    EuclideanSpace ℂ (Qubits n) :=
  WithLp.toLp 2 fun x => ψ (Fin.append x (fun _ : Fin a => false))

end ConstOverheadCompile.Main.Supplement


