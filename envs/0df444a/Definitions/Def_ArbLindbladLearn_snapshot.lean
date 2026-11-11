-- Prove2me | Definitions.Def_ArbLindbladLearn_snapshot
-- name    : ArbLindbladLearn_snapshot
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:26:39.511987+00:00
-- url     : https://prove2.me/theorems/c1443d55-f531-4940-8f7c-2276a41e2777
-- title:
--   Two-sided process shadow: snapshot $\hat J_t$, estimator $X_A$, and the law of $(\psi,\phi)$
-- statement:
--   In the random Clifford probing experiment at time $t\ge0$, a uniformly random $\psi\in\mathrm{Stab}_n$ is evolved under $e^{t\mathcal L}$, a uniformly random Clifford $C$ is applied, the outcome $b$ is measured, and $\phi=C^\dagger|b\rangle\langle b|C$. The module defines:
--   1. $S(\xi)=(d+1)\xi-I$ and the snapshot $\hat J_t=S(\psi^\top)\otimes S(\phi)=((d+1)\psi^\top-I)\otimes((d+1)\phi-I)$ (eq. (28));
--   2. the single-snapshot estimator $X_A=\mathrm{tr}(\Pi_A\hat J_t)=\langle\Phi_A|\hat J_t|\Phi_A\rangle$;
--   3. the law of the recorded pair: $\psi$ uniform on $\mathrm{Stab}_n$, then $\phi\in\mathrm{Stab}_n$ with probability $d\,\mathrm{tr}(e^{t\mathcal L}(\psi)\phi)/|\mathrm{Stab}_n|$ (eq. (29)), and the expectation under it.
--
--   **Formalization Note** Eq. (29) is the law the paper derives from the uniform Clifford measurement; it is used directly because a uniform measure on the Clifford group is defined only up to global phases. Traces are real here; real parts are taken.
-- source:
--   Chen, Yu, Learning Arbitrary Lindbladians from Time Evolution, arXiv:2607.28610 (sha256 46c27db5…), eqs. (28)–(29), p.28; Lemma 4.5, p.29

import Mathlib
import Definitions.Def_ArbLindbladLearn_Stab
import Definitions.Def_ArbLindbladLearn_gen
import Definitions.Def_ArbLindbladLearn_bellVec

set_option autoImplicit false
open scoped ComplexOrder BigOperators Matrix ENNReal NNReal Kronecker
noncomputable section

namespace ArbLindbladLearn

open LindbladTolerant.Testing

/-- `S(ξ) = (d + 1)ξ − I` with `d = 2ⁿ` (proof of Lemma 4.5, Chen–Yu, *Learning Arbitrary Lindbladians from Time Evolution*, arXiv:2607.28610 (sha256 46c27db5…), p.29). -/
def shadowS {n : ℕ} (ξ : Op (Qubits n)) : Op (Qubits n) := ((2 : ℂ) ^ n + 1) • ξ - 1

/-- The two-sided snapshot `Ĵ_t = ((d+1)ψ^⊤ − I) ⊗ ((d+1)φ − I)` of a recorded pair `(ψ, φ)`
(eq. (28), p.28), reference factor first as in `J_t`. -/
def snapshot {n : ℕ} (ψ φ : Op (Qubits n)) : Op (Qubits n × Qubits n) :=
  shadowS ψᵀ ⊗ₖ shadowS φ

/-- The single-snapshot estimator `X_A = tr(Π_A Ĵ_t) = ⟨Φ_A|Ĵ_t|Φ_A⟩` (Lemma 4.5, p.29).

**Formalization Note** `X_A` is real (`Ĵ_t` is Hermitian for stabilizer `ψ, φ`); the real part is
taken. -/
def snapEst {n : ℕ} (A : Op (Qubits n)) (ψ φ : Op (Qubits n)) : ℝ :=
  (bellForm (snapshot ψ φ) (bellVec A) (bellVec A)).re

/-- The probability of the recorded pair `(ψ, φ) ∈ Stab_n × Stab_n` in the random-Clifford-probing
experiment at time `t` (p.28, steps 1–3 and eq. (29)): `ψ` is uniform on `Stab_n`, and given `ψ`
the outcome `φ` has probability `d·tr(e^{tℒ}(ψ) φ)/|Stab_n|`.

**Formalization Note** Eq. (29) is the law the paper derives from "apply a uniformly random
Clifford `C`, measure `b` in the computational basis, set `φ = C†|b⟩⟨b|C`"; it is used here directly,
because a uniform measure on the Clifford group itself is defined only up to global phases. The
trace is real for a state `ψ`; its real part is taken. -/
def shadowWeight {n : ℕ} (c : Coeffs n) (t : ℝ) (ψ φ : Op (Qubits n)) : ℝ :=
  ((Stab n).ncard : ℝ)⁻¹ *
    ((2 : ℝ) ^ n * (applySuper (evolution (gen c) t) ψ * φ).trace.re / (Stab n).ncard)

/-- The expectation `E[F(ψ, φ)]` under the law `shadowWeight` of the recorded pair (Lemmas 4.4–4.5,
pp.28–29). -/
def shadowExpect {n : ℕ} {M : Type*} [AddCommMonoid M] [Module ℝ M] (c : Coeffs n) (t : ℝ)
    (F : Op (Qubits n) → Op (Qubits n) → M) : M :=
  ∑ᶠ ψ ∈ Stab n, ∑ᶠ φ ∈ Stab n, shadowWeight c t ψ φ • F ψ φ

end ArbLindbladLearn


