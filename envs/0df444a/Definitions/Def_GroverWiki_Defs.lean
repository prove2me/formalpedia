-- Prove2me | Definitions.Def_GroverWiki_Defs
-- name    : GroverWiki_Defs
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-13T14:32:20.382609+00:00
-- url     : https://prove2.me/theorems/3bca456e-4afe-4170-8f3b-72d1154f27d2
-- title:
--   Grover's algorithm: basis states, oracles, diffusion operator, Grover iteration and measurement
-- statement:
--   This file fixes the objects in terms of which every statement of the mission is phrased. Throughout, $N \ge 1$ is the size of the search space $\{0,1,\dots,N-1\}$ and the state space is $\mathcal H = \mathbb C^N$ with the standard inner product $\langle u|v\rangle = \sum_x \overline{u_x}\,v_x$.
--
--   1. **Basis states.** $|x\rangle \in \mathbb C^N$ is the $x$-th standard basis vector.
--   2. **Uniform superposition.** $|s\rangle = \frac{1}{\sqrt N}\sum_{x=0}^{N-1}|x\rangle$.
--   3. **The perpendicular ket.** For a marked index $\omega$, $|s'\rangle = \frac{1}{\sqrt{N-1}}\sum_{x\ne\omega}|x\rangle$ (meaningful for $N \ge 2$).
--   4. **Phase oracle.** For $f\colon\{0,\dots,N-1\}\to\{0,1\}$, $U_\omega|x\rangle = (-1)^{f(x)}|x\rangle$.
--   5. **Standard oracle and $|-\rangle$.** On $\mathbb C^N\otimes\mathbb C^2$ (main register plus one ancillary qubit), $U_f|x\rangle|y\rangle = |x\rangle|y\oplus f(x)\rangle$, where $\oplus$ is addition modulo $2$; $|u\rangle\otimes|v\rangle$ is the product state; and $|-\rangle = \frac{1}{\sqrt2}(|0\rangle - |1\rangle)$.
--   6. **Grover diffusion operator.** $U_s = 2|s\rangle\langle s| - I$.
--   7. **Grover iteration and the algorithm's state.** One Grover iteration applies $U_\omega$ and then $U_s$, i.e. the operator $U_sU_\omega$; after $r$ iterations the state is $(U_sU_\omega)^r|s\rangle$.
--   8. **Measurement.** Measuring a normalized state $|\psi\rangle$ in the computational basis yields $x$ with probability $|\langle x|\psi\rangle|^2$ (Born rule).
--
--   **Formalization Note** Vectors are functions `Fin N → ℂ` and operators are matrices `Matrix (Fin N) (Fin N) ℂ` acting by `mulVec`; the two-register space is indexed by `Fin N × Fin 2`, and `Fin 2` is used for the bit values $\{0,1\}$ (so `+` on `Fin 2` is XOR). Scalars $1/\sqrt N$, $1/\sqrt{N-1}$, $1/\sqrt2$ are real numbers cast to $\mathbb C$.
-- source:
--   Wikipedia, "Grover's algorithm", revision oldid=1373498442, https://en.wikipedia.org/w/index.php?title=Grover%27s_algorithm&oldid=1373498442, sections "Problem description", "Alternative oracle definition", "Algorithm", "Geometric proof" (PDF pp. 2–5)

import Mathlib

open Matrix

namespace GroverWiki

/-- The computational basis state `|x⟩ ∈ ℂ^N` of an `N`-dimensional state space,
indexed by `x ∈ {0, …, N-1}`. -/
def ket {N : ℕ} (x : Fin N) : Fin N → ℂ := Pi.single x 1

/-- The tensor product `|u⟩ ⊗ |v⟩ ∈ ℂ^N ⊗ ℂ^2` of a state of the main register and a state of
one ancillary qubit, as a vector indexed by pairs `(x, y)`. -/
def tensorKet {N : ℕ} (u : Fin N → ℂ) (v : Fin 2 → ℂ) : Fin N × Fin 2 → ℂ :=
  fun p => u p.1 * v p.2

/-- The uniform superposition `|s⟩ = (1/√N) ∑_{x=0}^{N-1} |x⟩`. -/
noncomputable def uniformState (N : ℕ) : Fin N → ℂ :=
  fun _ => (((Real.sqrt N)⁻¹ : ℝ) : ℂ)

/-- The ket `|s'⟩ = (1/√(N-1)) ∑_{x ≠ ω} |x⟩`, perpendicular to `|ω⟩`. -/
noncomputable def perpState {N : ℕ} (ω : Fin N) : Fin N → ℂ :=
  fun x => if x = ω then 0 else (((Real.sqrt ((N : ℝ) - 1))⁻¹ : ℝ) : ℂ)

/-- The single-qubit state `|−⟩ = (|0⟩ - |1⟩)/√2`. -/
noncomputable def minusState : Fin 2 → ℂ :=
  ![(((Real.sqrt 2)⁻¹ : ℝ) : ℂ), -(((Real.sqrt 2)⁻¹ : ℝ) : ℂ)]

/-- The phase oracle `U_ω` of a function `f : {0, …, N-1} → {0, 1}`:
`U_ω |x⟩ = (-1)^{f(x)} |x⟩`. -/
def phaseOracle {N : ℕ} (f : Fin N → Fin 2) : Matrix (Fin N) (Fin N) ℂ :=
  diagonal fun x => (-1) ^ (f x : ℕ)

/-- The standard quantum oracle `U_f` on `ℂ^N ⊗ ℂ^2` (main register plus one ancillary qubit):
`U_f |x⟩|y⟩ = |x⟩|y ⊕ f(x)⟩`. Addition in `Fin 2` is addition modulo 2 (XOR). -/
def standardOracle {N : ℕ} (f : Fin N → Fin 2) :
    Matrix (Fin N × Fin 2) (Fin N × Fin 2) ℂ :=
  fun p q => if p.1 = q.1 ∧ p.2 = q.2 + f q.1 then 1 else 0

/-- The Grover diffusion operator `U_s = 2|s⟩⟨s| - I`. -/
noncomputable def diffusion (N : ℕ) : Matrix (Fin N) (Fin N) ℂ :=
  (2 : ℂ) • vecMulVec (uniformState N) (star (uniformState N)) - 1

/-- One Grover iteration: apply `U_ω`, then `U_s`, i.e. the operator `U_s U_ω`. -/
noncomputable def groverIteration {N : ℕ} (f : Fin N → Fin 2) : Matrix (Fin N) (Fin N) ℂ :=
  diffusion N * phaseOracle f

/-- The state of Grover's algorithm after `r` Grover iterations:
`(U_s U_ω)^r |s⟩`. -/
noncomputable def groverState {N : ℕ} (f : Fin N → Fin 2) (r : ℕ) : Fin N → ℂ :=
  (groverIteration f ^ r) *ᵥ uniformState N

/-- Born rule: the probability of obtaining outcome `x` when a (normalized) state `ψ ∈ ℂ^N` is
measured in the computational basis, `|⟨x|ψ⟩|^2`. -/
noncomputable def measureProb {N : ℕ} (ψ : Fin N → ℂ) (x : Fin N) : ℝ :=
  ‖ψ x‖ ^ 2

end GroverWiki


