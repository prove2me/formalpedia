-- Prove2me | Definitions.Def_QubitFreqSensing_Supplement_PurifiedProtocol
-- name    : QubitFreqSensing_Supplement_PurifiedProtocol
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T03:59:22.097199+00:00
-- url     : https://prove2.me/theorems/c24f995d-5986-48d7-9ecd-6ea716c5539e
-- title:
--   Purified sensing protocols on $\mathbb C^2\otimes\mathbb C^{\alpha}$, the frame operator $M(t)=U_c(t)^\dagger(Z\otimes I)U_c(t)$, coefficient vectors and the detection probability
-- statement:
--   The general sensing protocols of the lower bound live on the Hilbert space $\mathcal H=\mathbb C^2\otimes\mathbb C^{\alpha}$: the sensing qubit together with an arbitrary finite auxiliary register $\alpha$. The signal acts on the sensing qubit only, through $Z\otimes I$ with $Z=\mathrm{diag}(1,-1)$ the Pauli $Z$ matrix.
--
--   A **purified protocol** consists of
--
--   1. an initial unit vector $v\in\mathcal H$;
--   2. a control-only evolution $t\mapsto U_c(t)$, a unitary operator on $\mathcal H$ for every absolute time $t$, with $U_c(0)=I$ and measurable entries;
--   3. the "signal present" effect $E$ of the final two-outcome measurement, an operator with $0\le E\le I$.
--
--   In the control-following basis the signal operator is $M(t)=U_c(t)^\dagger(Z\otimes I)U_c(t)$. Under a signal Hamiltonian $h(t)\,(Z\otimes I)$ on $[0,T]$ the **coefficient vector** $c:[0,T]\to\mathcal H$ is the continuous solution of
--
--   $$
--   i\,\dot c(t)=h(t)\,M(t)\,c(t),\qquad c(0)=v,\qquad\text{i.e.}\qquad c(t)=v-i\int_0^t h(s)\,M(s)\,c(s)\,ds\quad(t\in[0,T]),
--   $$
--
--   and the physical state at time $t$ is $U_c(t)c(t)$. With no signal, $c\equiv v$. The probability that the protocol reports "signal" on a final state $\psi$ is $\langle\psi,E\psi\rangle$.
--
--   Mid-protocol measurements, classical randomness, random waits, adaptivity and fresh qubits can all be purified into a larger register and a control-only unitary evolution followed by one final measurement, so this class contains every protocol to which the discrete Grover–Heisenberg lower bound applies.
--
--   **Formalization Note** Vectors are functions $\mathrm{Fin}\,2\times\alpha\to\mathbb C$ and operators are matrices; the inner product is $\overline{x}\cdot y$, conjugate-linear in the first argument. The control path is only required to be measurable entrywise: no continuity and no bounded control Hamiltonian, so instantaneous gates are jumps of $U_c$. For continuous $c$ and $h$ the integrand is bounded and measurable, so the integral equation is a genuine Bochner integral and its solution exists and is unique.
-- source:
--   Chen, Coladangelo, Li, Zhang, Sensing frequencies at the discrete Grover-Heisenberg limit using a single qubit, manuscript (STOC 2027 submission; held version sha256 fd015276…c95c9a2), §4, eqs. (4)–(6), pp.13–14; proof of Theorem 8.1, eq. (29), p.31

import Mathlib
import Definitions.Def_MIPRE_LCS_Pauli

open Matrix
open scoped ComplexOrder

namespace QubitFreqSensing.Supplement

/-- The signal operator `Z ⊗ I` on `ℂ² ⊗ ℂ^α` (sensing qubit ⊗ auxiliary register), with
`Z = diag(1, -1)` the Pauli matrix `MIPRE.LCS.Pauli.Z` (Chen, Coladangelo, Li, Zhang, *Sensing
frequencies at the discrete Grover-Heisenberg limit using a single qubit*, manuscript (STOC 2027
submission), proof of Theorem 8.1, p.31: "with `Z ⊗ I` in place of `Z`"). The signal acts on the
sensing qubit only. -/
def sigOp (α : Type) [Fintype α] [DecidableEq α] : Matrix (Fin 2 × α) (Fin 2 × α) ℂ :=
  Matrix.kroneckerMap (· * ·) MIPRE.LCS.Pauli.Z (1 : Matrix α α ℂ)

/-- **Purified sensing protocol with auxiliary register** (Chen, Coladangelo, Li, Zhang, manuscript
(STOC 2027 submission), §4, eqs. (4)–(6), pp.13–14; proof of Theorem 8.1, p.31: "We can purify the
entire protocol, and represent it as a unitary evolution on a larger Hilbert space followed by one
final measurement"). The Hilbert space is `ℂ² ⊗ ℂ^α`, the sensing qubit times an arbitrary finite
auxiliary register `α`. A protocol consists of

1. an initial unit vector `init` (the coefficient vector `v = |c(0)⟩`);
2. the control-only evolution `control t = U_c(t)`, a unitary for every absolute time `t`, with
   `U_c(0) = I`, required only to be measurable entrywise;
3. the "signal present" outcome `effect = E` of the final two-outcome measurement, `0 ≤ E ≤ I`.

**Formalization Note** Mid-protocol measurements, classical randomness, random waits, adaptivity and
fresh qubits are absorbed by purification into a larger register and a control-only unitary
evolution, as on p.31; so this class contains every protocol of Theorem 8.1. No continuity of `U_c`
and no bound on a control Hamiltonian is assumed: instantaneous gates are jumps of `U_c`. Vectors are
`Fin 2 × α → ℂ`, the inner product is `star x ⬝ᵥ y` (conjugate-linear in `x`). -/
structure PurifiedProtocol (α : Type) [Fintype α] [DecidableEq α] where
  /-- The initial coefficient vector `v`. -/
  init : Fin 2 × α → ℂ
  /-- `v` is a unit vector. -/
  init_unit : star init ⬝ᵥ init = 1
  /-- The control-only evolution `U_c(t)` at absolute time `t`. -/
  control : ℝ → Matrix.unitaryGroup (Fin 2 × α) ℂ
  /-- `U_c(0) = I`. -/
  control_zero : control 0 = 1
  /-- Every entry of `t ↦ U_c(t)` is measurable. -/
  control_measurable :
    ∀ a b, Measurable fun t => (control t : Matrix (Fin 2 × α) (Fin 2 × α) ℂ) a b
  /-- The "signal present" effect `E` of the final measurement. -/
  effect : Matrix (Fin 2 × α) (Fin 2 × α) ℂ
  /-- `0 ≤ E`. -/
  effect_nonneg : effect.PosSemidef
  /-- `E ≤ I`. -/
  effect_le_one : (1 - effect).PosSemidef

namespace PurifiedProtocol

variable {α : Type} [Fintype α] [DecidableEq α]

/-- The signal operator in the control-following basis, `M(t) = U_c(t)† (Z ⊗ I) U_c(t)`
(manuscript, eq. (6), p.14, and eq. (29), p.31). -/
noncomputable def frameOp (P : PurifiedProtocol α) (t : ℝ) : Matrix (Fin 2 × α) (Fin 2 × α) ℂ :=
  star (P.control t : Matrix (Fin 2 × α) (Fin 2 × α) ℂ) * sigOp α *
    (P.control t : Matrix (Fin 2 × α) (Fin 2 × α) ℂ)

/-- `c` is the coefficient vector of the protocol `P` under the signal Hamiltonian `h(t) (Z ⊗ I)` on
`[0, T]` (manuscript, eqs. (4)–(6), pp.13–14; eq. (29), p.31): `c` is continuous on `[0, T]` and
solves `i ċ(t) = h(t) M(t) c(t)`, `c(0) = v`, in integral form
`c(t) = v - i ∫₀ᵗ h(s) M(s) c(s) ds` for `t ∈ [0, T]`. The physical state is `U_c(t) c(t)`.

**Formalization Note** For measurable `U_c`, continuous `c` and continuous `h` the integrand is
bounded and measurable on `[0, t]`, so the integral is a genuine Bochner integral (no junk value);
the solution exists and is unique, so `c` is the true evolution, not a free function. For `h ≡ 0` the
solution is the constant `v`. -/
def IsCoeffSolution (P : PurifiedProtocol α) (h : ℝ → ℝ) (T : ℝ) (c : ℝ → Fin 2 × α → ℂ) :
    Prop :=
  ContinuousOn c (Set.Icc 0 T) ∧
    ∀ t ∈ Set.Icc 0 T,
      c t = P.init - Complex.I • ∫ s in (0 : ℝ)..t, ((h s : ℝ) : ℂ) • (P.frameOp s *ᵥ c s)

/-- The probability that the final measurement of `P` reports "signal" on the final state `ψ`:
`⟨ψ, E ψ⟩` (real, in `[0, 1]` for a unit `ψ`). For the final state under a signal with coefficient
vector `c` and total time `T`, `ψ = U_c(T) c(T)`; with no signal, `ψ = U_c(T) v`. -/
noncomputable def probSignal (P : PurifiedProtocol α) (ψ : Fin 2 × α → ℂ) : ℝ :=
  (star ψ ⬝ᵥ (P.effect *ᵥ ψ)).re

end PurifiedProtocol

end QubitFreqSensing.Supplement


