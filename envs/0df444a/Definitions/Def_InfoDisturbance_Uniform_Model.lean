-- Prove2me | Definitions.Def_InfoDisturbance_Uniform_Model
-- name    : InfoDisturbance_Uniform_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T02:23:35.045988+00:00
-- url     : https://prove2.me/theorems/e12417d7-8c0a-4416-a72c-d9849bd8d7c7
-- title:
--   Eqs. (2)–(5), (9), (26), pp. 3–6, 11–12 — instrument compatible with a POVM, square-root operation, disturbance on the uniform ensemble
-- statement:
--   Fix a dimension $d\ge 1$ and work on $\mathbb C^d$. A **POVM** $\{F_b\}_{b\in B}$ is a finite family of positive semidefinite operators with $\sum_b F_b=I$; the probability of outcome $b$ on a state $\rho$ is $\operatorname{tr}\rho F_b$.
--
--   1. **Compatible instrument (Eqs. (2)–(3), pp. 3–4).** A family of operators $\{A_{bi}\}_{b\in B,\,i\in I}$ (the *HK operators*) is compatible with the POVM $\{F_b\}$ when
--   $$\sum_i A_{bi}^\dagger A_{bi}=F_b\qquad\text{for every outcome } b.$$
--   The unnormalized post-measurement state for outcome $b$ is $\mathcal A_b(\rho)=\sum_i A_{bi}\rho A_{bi}^\dagger$, and the **overall operation** is $\mathcal A(\rho)=\sum_b\mathcal A_b(\rho)=\sum_{b,i}A_{bi}\rho A_{bi}^\dagger$.
--   2. **Square-root operation (Eq. (5), pp. 4–5).** The operation with one HK operator $F_b^{1/2}$ per outcome,
--   $$\rho\;\longmapsto\;\sum_b F_b^{1/2}\rho F_b^{1/2},$$
--   where $F_b^{1/2}$ is the positive square root.
--   3. **Disturbance on the uniform ensemble (Eq. (9), p. 6).** Let $\Omega$ be the unitarily invariant probability measure on unit vectors of $\mathbb C^d$ (the law of $U|0\rangle$ for Haar-random unitary $U$). The average disturbance of an operation $\mathcal E$ is
--   $$D(\mathcal E)=1-\int d\Omega_\psi\,\langle\psi|\mathcal E(|\psi\rangle\langle\psi|)|\psi\rangle .$$
--   For $\mathcal E=\mathcal A$ this is $1-\int d\Omega_\psi\sum_{b,i}|\langle\psi|A_{bi}|\psi\rangle|^2$, the paper's Eq. (9).
--   4. **Second moment (Eq. (26), p. 12).** $\Pi=\int d\Omega_\psi\,|\psi\rangle\langle\psi|\otimes|\psi\rangle\langle\psi|$, an operator on $\mathbb C^d\otimes\mathbb C^d$.
--   5. **Real matrix powers (Theorem 7, p. 11).** $X^s$ for a positive operator $X$ and real $s$, by the functional calculus.
--
--   These are the objects of every statement in the mission: the goal compares $D$ of the square-root operation with $D$ of an arbitrary compatible instrument.
--
--   **Formalization Note** Operators are `Matrix (Fin d) (Fin d) ℂ`, vectors `EuclideanSpace ℂ (Fin d)`. The measure $\Omega$ and the average fidelity are the published `haarPureStateLaw` and `averageFidelity` (the integrand is $\operatorname{Re}\operatorname{tr}(|\psi\rangle\langle\psi|\,\mathcal E(|\psi\rangle\langle\psi|))$, which for pure states is the paper's fidelity $\langle\psi|\sigma|\psi\rangle$ with $\sigma$ unnormalized). One finite Kraus index type $I$ serves every outcome; outcomes with fewer HK operators are padded with zero operators, which changes neither (3) nor $\mathcal A$. The square root is `cfc Real.sqrt`, and $X^s$ is `cfc (fun x => x ^ s)` with `Real.rpow`, so $X^0=I$. $\Pi$ is taken entrywise: its $((a,b),(c,e))$ entry is $\int d\Omega_\psi\,\psi_a\bar\psi_c\psi_b\bar\psi_e$.
-- source:
--   Barnum, Information-disturbance tradeoff in quantum measurement on the uniform ensemble, arXiv:quant-ph/0205155v1, pp. 3–6, Eqs. (2)–(5), (9); p. 11, Theorem 7; p. 12, Eq. (26)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_QuditChannelFidelities
noncomputable section
open scoped Matrix ComplexOrder Kronecker
open QAlgorithms QAlgorithms.QuditFidelity MeasureTheory

namespace InfoDisturbance.Uniform

/-- Barnum, arXiv:quant-ph/0205155v1, p. 3, Eq. (3) and p. 4: the HK operators `A b i` form an
instrument compatible with the POVM `F`, i.e. `Σ_i A_bi† A_bi = F_b` for every outcome `b`.
One finite Kraus index type `I` serves every outcome (zero operators pad shorter lists). -/
def IsCompatible {d : ℕ} {B I : Type*} [Fintype I]
    (F : B → Matrix (Fin d) (Fin d) ℂ) (A : B → I → Matrix (Fin d) (Fin d) ℂ) : Prop :=
  ∀ b, ∑ i, (A b i)ᴴ * A b i = F b

/-- p. 4: the overall operation `𝒜 = Σ_b 𝒜_b`, `ρ ↦ Σ_{b,i} A_bi ρ A_bi†`. -/
def instrumentOperation {d : ℕ} {B I : Type*} [Fintype B] [Fintype I]
    (A : B → I → Matrix (Fin d) (Fin d) ℂ) : Superop (Fin d) (Fin d) :=
  krausApply (fun p : B × I => A p.1 p.2)

/-- pp. 4–5, Eq. (5): the square-root operation `ρ ↦ Σ_b F_b^{1/2} ρ F_b^{1/2}`. -/
def sqrtOperation {d : ℕ} {B : Type*} [Fintype B] (F : B → Matrix (Fin d) (Fin d) ℂ) :
    Superop (Fin d) (Fin d) :=
  krausApply (fun b => cfc Real.sqrt (F b))

/-- p. 6, Eq. (9): the average disturbance of the operation `E` on the uniform (unitarily
invariant, normalized) ensemble `Ω` of pure states, `1 − ∫ dΩ_ψ ⟨ψ|E(|ψ⟩⟨ψ|)|ψ⟩`. -/
def disturbance (d : ℕ) (hd : 0 < d) (E : Superop (Fin d) (Fin d)) : ℝ :=
  1 - averageFidelity d hd E

/-- p. 12, Eq. (26): the second moment `Π := ∫ dΩ_ψ |ψ⟩⟨ψ| ⊗ |ψ⟩⟨ψ|` of the uniform ensemble,
taken entrywise; entry `((a,b),(c,e))` is `∫ dΩ_ψ ψ_a ψ̄_c ψ_b ψ̄_e`. -/
def secondMoment (d : ℕ) (hd : 0 < d) : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  Matrix.of fun p q => ∫ ψ, (pureDensity ψ ⊗ₖ pureDensity ψ) p q ∂haarPureStateLaw d hd

/-- p. 11, Theorem 7: the real power `X^s` of a positive operator through the continuous
functional calculus (`Real.rpow`, so `0^0 = 1` and `X^0 = I`). -/
def matrixRpow {ι : Type*} [Fintype ι] [DecidableEq ι] (X : Matrix ι ι ℂ) (s : ℝ) :
    Matrix ι ι ℂ :=
  cfc (fun x : ℝ => x ^ s) X

end InfoDisturbance.Uniform


