-- Prove2me | Definitions.Def_ClassicalShadow_Linear_Setting
-- name    : ClassicalShadow_Linear_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-18T20:11:08.260801+00:00
-- url     : https://prove2.me/theorems/05a666ce-2c09-4b00-b5f1-dcd9eab41dc8
-- title:
--   Definition 1, (S1)–(S3), (S7), (S12), pp. 11–12 — measurement primitive, channel M and M⁻¹, classical shadow, shadow norm, median of means
-- statement:
--   This file sets up the randomized-measurement framework of Huang, Kueng and Preskill for $n$ qubits.
--
--   **Operators.** Computational-basis labels are bit strings $b \in \{0,1\}^n$, and operators are $2^n \times 2^n$ complex matrices indexed by them. $|b\rangle\langle b|$ is the projector onto the basis vector $|b\rangle$, and $\langle b|X|b\rangle$ is the diagonal entry $X_{bb}$.
--
--   **Measurement primitive (Definition 1).** A primitive $\mathcal U$ is a finite ensemble of unitaries $U_i$, $i \in \iota$, drawn with probabilities $w_i \ge 0$, $\sum_i w_i = 1$. One applies $\rho \mapsto U_i \rho U_i^\dagger$ and measures in the computational basis. The primitive is **tomographically complete** if for any two density operators $\sigma \neq \rho$ there are an index $i$ with $w_i > 0$ and a label $b$ with
--   $$\langle b|U_i\sigma U_i^\dagger|b\rangle \neq \langle b|U_i\rho U_i^\dagger|b\rangle .$$
--
--   **Snapshots (S1).** One snapshot of a state $\rho$ draws $i$ with probability $w_i$ and then $b$ with probability $\langle b|U_i\rho U_i^\dagger|b\rangle$ (Born's rule); the outcome $\omega = (i,b)$ thus has probability $w_i \langle b|U_i\rho U_i^\dagger|b\rangle$.
--
--   **Measurement channel (S2) and classical shadow (S3).** The channel is the linear map
--   $$\mathcal M(X) = \sum_i w_i \sum_{b \in \{0,1\}^n} \langle b|U_i X U_i^\dagger|b\rangle\, U_i^\dagger|b\rangle\langle b|U_i ,$$
--   $\mathcal M^{-1}$ is its inverse, and the classical shadow of the outcome $(i,b)$ is $\hat\rho = \mathcal M^{-1}(U_i^\dagger|b\rangle\langle b|U_i)$. For an observable $O$ the single-shadow prediction is $\hat o = \operatorname{tr}(O\hat\rho)$; its mean $\mathbb E[\hat o]$ and variance $\operatorname{Var}[\hat o] = \mathbb E[(\hat o - \mathbb E[\hat o])^2]$ are taken under the snapshot law.
--
--   **Traceless part and shadow norm (S7).** $O_0 = O - \frac{\operatorname{tr}(O)}{2^n}\mathbb I$, and
--   $$\|O\|_{\mathrm{shadow}} = \max_{\sigma:\ \text{state}} \Big( \sum_i w_i \sum_{b} \langle b|U_i\sigma U_i^\dagger|b\rangle\, \langle b|U_i\mathcal M^{-1}(O)U_i^\dagger|b\rangle^2 \Big)^{1/2}.$$
--
--   **Median of means (S12).** From $NK$ snapshots arranged in $K$ batches of $N$, the $k$-th empirical mean is $\hat o^{(k)} = \frac1N\sum_{j} \operatorname{tr}(O\hat\rho_{k,j})$ and the estimate is $\hat o(N,K) = \operatorname{median}\{\hat o^{(1)},\dots,\hat o^{(K)}\}$. The probability of an event about the $NK$ snapshots is computed under the product law (independent snapshots).
--
--   These objects are the vocabulary of Lemma 1 and Theorem 1 of the paper: the classical-shadow estimator of linear properties and its sample complexity.
--
--   **Formalization Note.** The ensemble is finite (a `WildeQIT.FinDist` of weights and a family in `Matrix.unitaryGroup`); the paper's ensemble is general, and both of its examples (global and local Clifford measurements with uniform weights) are finite. "$U \in \mathcal U$" in tomographic completeness is read as "positive weight". $\mathcal M$ is a genuine $\mathbb C$-linear endomorphism of the matrix space, and $\mathcal M^{-1}$ is `Ring.inverse` of it, which is the inverse when $\mathcal M$ is a unit and $0$ otherwise; every theorem that uses $\mathcal M^{-1}$ assumes tomographic completeness, under which $\mathcal M$ is invertible. The predictions $\hat o$ and the target $\operatorname{tr}(O\rho)$ are taken as real parts; for Hermitian $O$ they are real, so the real part is only a type cast. In (S7) the square of the complex entry is taken and then its real part; for Hermitian $O$ the entry is real. The maximum over states is a real supremum (`⨆`) over the nonempty set of density operators of a function that is bounded above (the state set is compact and the expression is affine in $\sigma$), so it is the paper's maximum. The median is the lower median, the $\lfloor (K-1)/2\rfloor$-th entry (0-based) of the sorted list, which is the median for odd $K$; the paper does not fix the even-$K$ convention. Batch $k$ consists of the snapshots indexed $(k, 0), \dots, (k, N-1)$, the paper's $j = N(k-1)+1, \dots, Nk$.
-- source:
--   Huang, Kueng, Preskill, Predicting many properties of a quantum system from very few measurements, arXiv:2002.08953v2, pp. 11–12, Definition 1, (S1)–(S3), (S5)–(S7), (S11)–(S12)

import Mathlib
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_WildeQIT_FinDist

open scoped ComplexOrder Matrix
open Classical

namespace ClassicalShadow.Linear

/-- Computational-basis labels `b ∈ {0,1}ⁿ`. -/
abbrev Bits (n : ℕ) := Fin n → Fin 2

/-- Operators on `n` qubits: `2ⁿ × 2ⁿ` complex matrices indexed by `{0,1}ⁿ`. -/
abbrev Op (n : ℕ) := Matrix (Bits n) (Bits n) ℂ

/-- Definition 1 (measurement primitive): a finite ensemble `𝒰` of unitaries `U i`, drawn with
probability `w.prob i`. -/
structure Primitive (n : ℕ) (ι : Type) [Fintype ι] where
  /-- the sampling weights of the ensemble -/
  w : WildeQIT.FinDist ι
  /-- the unitaries of the ensemble -/
  U : ι → Matrix.unitaryGroup (Bits n) ℂ

variable {n : ℕ} {ι : Type} [Fintype ι]

/-- The matrix of the `i`-th unitary. -/
def Primitive.mat (E : Primitive n ι) (i : ι) : Op n := (E.U i : Op n)

/-- The projector `|b⟩⟨b|`. -/
def proj (b : Bits n) : Op n := Matrix.single b b 1

/-- The diagonal entry `⟨b|U_i X U_i†|b⟩`. -/
def diagEntry (E : Primitive n ι) (i : ι) (X : Op n) (b : Bits n) : ℂ :=
  (E.mat i * X * star (E.mat i)) b b

/-- The rotated projector `U_i†|b⟩⟨b|U_i`. -/
def rotProj (E : Primitive n ι) (i : ι) (b : Bits n) : Op n :=
  star (E.mat i) * proj b * E.mat i

/-- Definition 1, tomographic completeness: for any two distinct states `σ ≠ ρ` there are a
unitary of the ensemble (a positive-weight index `i`) and a label `b` with
`⟨b|U_i σ U_i†|b⟩ ≠ ⟨b|U_i ρ U_i†|b⟩`. -/
def TomographicallyComplete (E : Primitive n ι) : Prop :=
  ∀ σ ρ : Op n, WildeQIT.IsDensityOperator σ → WildeQIT.IsDensityOperator ρ → σ ≠ ρ →
    ∃ i, 0 < E.w.prob i ∧ ∃ b, diagEntry E i σ b ≠ diagEntry E i ρ b

/-- The linear functional `X ↦ ⟨b|U_i X U_i†|b⟩`. -/
noncomputable def diagFunctional (E : Primitive n ι) (i : ι) (b : Bits n) : Op n →ₗ[ℂ] ℂ :=
  (Matrix.entryLinearMap ℂ ℂ b b).comp
    ((LinearMap.mulRight ℂ (star (E.mat i))).comp (LinearMap.mulLeft ℂ (E.mat i)))

/-- (S2): the measurement channel
`M(X) = E_{U∼𝒰} Σ_b ⟨b|U X U†|b⟩ U†|b⟩⟨b|U = Σ_i w_i Σ_b ⟨b|U_i X U_i†|b⟩ U_i†|b⟩⟨b|U_i`,
as a `ℂ`-linear endomorphism of the operator space. -/
noncomputable def measChannel (E : Primitive n ι) : Module.End ℂ (Op n) :=
  ∑ i, ∑ b, ((E.w.prob i : ℂ) • (diagFunctional E i b).smulRight (rotProj E i b))

/-- `M⁻¹`. This is `Ring.inverse`, which is the inverse of `M` when `M` is a unit (the case under
tomographic completeness) and `0` otherwise. -/
noncomputable def measChannelInv (E : Primitive n ι) : Module.End ℂ (Op n) :=
  Ring.inverse (measChannel E)

/-- (S3): the classical shadow `ρ̂ = M⁻¹(U_i†|b⟩⟨b|U_i)` of the outcome `ω = (i, b)`. -/
noncomputable def shadow (E : Primitive n ι) (ω : ι × Bits n) : Op n :=
  measChannelInv E (rotProj E ω.1 ω.2)

/-- (S1) with `U ∼ 𝒰`: the probability `w_i ⟨b|U_i ρ U_i†|b⟩` of the outcome `ω = (i, b)`. -/
def snapProb (E : Primitive n ι) (ρ : Op n) (ω : ι × Bits n) : ℝ :=
  E.w.prob ω.1 * (diagEntry E ω.1 ρ ω.2).re

/-- The single-shadow prediction `ô = tr(O ρ̂)` of outcome `ω` (real part; real for Hermitian
`O`). -/
noncomputable def snapEstimate (E : Primitive n ι) (O : Op n) (ω : ι × Bits n) : ℝ :=
  (O * shadow E ω).trace.re

/-- `E[ô]` under the snapshot law of `ρ`. -/
noncomputable def snapMean (E : Primitive n ι) (ρ O : Op n) : ℝ :=
  ∑ ω, snapProb E ρ ω * snapEstimate E O ω

/-- `Var[ô] = E[(ô − E[ô])²]` under the snapshot law of `ρ`. -/
noncomputable def snapVar (E : Primitive n ι) (ρ O : Op n) : ℝ :=
  ∑ ω, snapProb E ρ ω * (snapEstimate E O ω - snapMean E ρ O) ^ 2

/-- The traceless part `O − (tr(O)/2ⁿ) 𝕀`. -/
noncomputable def traceless (O : Op n) : Op n :=
  O - (O.trace / (2 : ℂ) ^ n) • (1 : Op n)

/-- (S7): the shadow norm
`‖O‖_shadow = max_σ (E_{U∼𝒰} Σ_b ⟨b|UσU†|b⟩ ⟨b|U M⁻¹(O) U†|b⟩²)^{1/2}`, the maximum over
density operators `σ`. -/
noncomputable def shadowNorm (E : Primitive n ι) (O : Op n) : ℝ :=
  Real.sqrt (⨆ σ : {σ : Op n // WildeQIT.IsDensityOperator σ},
    ∑ i, E.w.prob i * ∑ b, (diagEntry E i σ.1 b).re * ((diagEntry E i (measChannelInv E O) b) ^ 2).re)

/-- The (lower) median of `K` reals: the `⌊(K−1)/2⌋`-th entry (0-based) of the sorted list. -/
noncomputable def median {K : ℕ} (x : Fin K → ℝ) : ℝ :=
  ((List.ofFn x).mergeSort (fun a b => decide (a ≤ b))).getD ((K - 1) / 2) 0

/-- (S12): the `k`-th empirical mean `ô^{(k)} = (1/N) Σ_j tr(O ρ̂_{k,j})`; batch `k` consists of the
snapshots `ω k 0, …, ω k (N−1)`. -/
noncomputable def batchMean {K N : ℕ} (E : Primitive n ι) (O : Op n)
    (ω : Fin K → Fin N → ι × Bits n) (k : Fin K) : ℝ :=
  (1 / (N : ℝ)) * ∑ j, snapEstimate E O (ω k j)

/-- (S12): the median of means `ô(N, K) = median{ô^{(1)}, …, ô^{(K)}}`. -/
noncomputable def momEstimate {K N : ℕ} (E : Primitive n ι) (O : Op n)
    (ω : Fin K → Fin N → ι × Bits n) : ℝ :=
  median (fun k => batchMean E O ω k)

/-- The probability of an event `A` under `NK` independent snapshots of `ρ`: the sum over all
outcome arrays `ω` in `A` of `∏_{k,j} Pr[ω k j]`. -/
noncomputable def sampleProb {K N : ℕ} (E : Primitive n ι) (ρ : Op n)
    (A : (Fin K → Fin N → ι × Bits n) → Prop) : ℝ :=
  ∑ ω, if A ω then ∏ k, ∏ j, snapProb E ρ (ω k j) else 0

end ClassicalShadow.Linear


