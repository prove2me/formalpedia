-- Prove2me | Definitions.Def_MemoSDPI_Main_Memorization
-- name    : MemoSDPI_Main_Memorization
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T21:41:34.684484+00:00
-- url     : https://prove2.me/theorems/3604cadb-b117-47f5-9420-7c8d2776639d
-- title:
--   Average-case problems, their joint laws, and excess memorization mem_n(A, D), mem_n(A, P)
-- statement:
--   An **average-case problem** $P = (P_\theta)_{\theta \sim \Psi}$ consists of a family of data distributions $P_\theta$ on a space $X$ and a prior $\Psi$ on the parameter space $\Theta$: first $\theta \sim \Psi$, then a sample $S = (X_1, \dots, X_n)$ of $n$ records drawn independently from $P_\theta$. An algorithm $A$ outputs $U = A(S)$ using randomness (a seed) independent of $(\theta, S)$, so $\theta \to S \to U$ is a Markov chain.
--
--   For a data distribution $D$ on $X$, the **excess memorization** of $A$ on $n$ samples is
--   $$
--   \mathrm{mem}_n(A, D) \;:=\; I(A(S); S), \qquad S \sim D^n,
--   $$
--   and the excess memorization of $A$ on the average-case problem $P$ is the average
--   $$
--   \mathrm{mem}_n(A, P) \;:=\; \mathbb E_{\theta \sim \Psi}\big[\mathrm{mem}_n(A, P_\theta)\big].
--   $$
--   The module also names the joint law of $(\theta, S)$, the joint law of $(\theta, S, \omega)$ with an independent seed $\omega$, and the two informations $I(A(S);\theta)$ and $I(A(S); S)$ computed under the latter.
--
--   **Formalization Note** The algorithm is the published `DPVerify.RandAlg`: a seed $\omega$ drawn from a probability space $(\Omega, P)$ and a jointly measurable output map $(S, \omega) \mapsto A(S;\omega)$. Mutual information is the published `ThompsonTutorial.InfoRatio.mutualInfo` (nats, $[0,\infty]$). The family $\theta \mapsto P_\theta$ is a function into probability measures and the joint law of $(\theta,S)$ is `Ψ.bind`; for a measurable family (a Markov kernel) this is the law described in the paper, and theorems about a general family assume measurability. The expectation over $\Psi$ is a lower Lebesgue integral in $[0,\infty]$. The further equalities of eq. (2.1) are a theorem of this mission, not part of the definition.
-- source:
--   Feldman, Lyu, Talwar, Lower Bounds for Memorization, Privacy and Replicability from Not-So-Strong Data Processing Inequalities, STOC 2027 submission (manuscript sha256 dbb300da…), p. 9, §2 and eq. (2.1) (first expression)

import Mathlib
import Definitions.Def_DPVerify_RandAlg
import Definitions.Def_ThompsonTutorial_InfoRatio_mutualInfo

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace MemoSDPI.Main

/-- **Excess memorization on one data distribution** (Feldman, Lyu, Talwar, *Lower Bounds for
Memorization, Privacy and Replicability from Not-So-Strong Data Processing Inequalities*, STOC
2027 submission (manuscript sha256 dbb300da…), p. 9, §2): `mem_n(A, D) := I(A(S); S)` with
`S ∼ D^n` and the randomness of `A` independent of `S`.

**Formalization Note.** The algorithm is the published `DPVerify.RandAlg` (seed `ω ∼ A.P`, output
`A.run S ω`). The underlying probability space is `D^n ⊗ A.P`; mutual information is the published
`ThompsonTutorial.InfoRatio.mutualInfo` (nats, `ℝ≥0∞`). -/
noncomputable def memD {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y] {n : ℕ}
    (A : DPVerify.RandAlg X Y n) (D : Measure X) [IsProbabilityMeasure D] : ℝ≥0∞ :=
  ThompsonTutorial.InfoRatio.mutualInfo ((Measure.pi fun _ : Fin n => D).prod A.P)
    (fun q => A.run q.1 q.2) (fun q => q.1)

/-- **Joint law of parameter and sample of an average-case problem** `P = (P_θ)_{θ∼Ψ}`
(p. 9, §2): draw `θ ∼ Ψ`, then a sample `S = (X_1, …, X_n)` of `n` records independently from
`P_θ`. This is the law of `(θ, S)`.

**Formalization Note.** The family `θ ↦ P_θ` is a function into probability measures and the law
is `Ψ.bind (θ ↦ law of (θ, S) given θ)`. For a measurable family (a Markov kernel) this is the
law the paper describes; the theorems about a general family assume `Measurable P`. -/
noncomputable def paramSampleLaw {Θ X : Type} [MeasurableSpace Θ] [MeasurableSpace X]
    (Ψ : Measure Θ) (P : Θ → Measure X) [∀ θ, IsProbabilityMeasure (P θ)] (n : ℕ) :
    Measure (Θ × (Fin n → X)) :=
  Ψ.bind fun θ => (Measure.pi fun _ : Fin n => P θ).map (fun s => (θ, s))

/-- **Joint law of parameter, sample and seed** for an algorithm run on an average-case problem
(p. 9, §2): `θ ∼ Ψ`, `S ∼ P_θ^n` given `θ`, and the seed `ω ∼ A.P` independent of `(θ, S)`; the
output is `U = A.run S ω`, so that `θ → S → U` is a Markov chain. -/
noncomputable def algJointLaw {Θ X Y : Type} [MeasurableSpace Θ] [MeasurableSpace X]
    [MeasurableSpace Y] {n : ℕ} (A : DPVerify.RandAlg X Y n) (Ψ : Measure Θ)
    (P : Θ → Measure X) [∀ θ, IsProbabilityMeasure (P θ)] :
    Measure ((Θ × (Fin n → X)) × A.Ω) :=
  (paramSampleLaw Ψ P n).prod A.P

/-- **Excess memorization on an average-case problem** (p. 9, eq. (2.1), first expression):
`mem_n(A, P) := E_{θ∼Ψ}[mem_n(A, P_θ)]`.

**Formalization Note.** The expectation is a lower Lebesgue integral in `ℝ≥0∞`. The further
equalities of eq. (2.1) are a theorem of this mission, not part of the definition. -/
noncomputable def memAvg {Θ X Y : Type} [MeasurableSpace Θ] [MeasurableSpace X]
    [MeasurableSpace Y] {n : ℕ} (A : DPVerify.RandAlg X Y n) (Ψ : Measure Θ)
    (P : Θ → Measure X) [∀ θ, IsProbabilityMeasure (P θ)] : ℝ≥0∞ :=
  ∫⁻ θ, memD A (P θ) ∂Ψ

/-- **Information about the parameter** `I(A(S); θ)` (p. 9): the mutual information between the
output `U = A(S)` and the parameter `θ` under `algJointLaw A Ψ P`. -/
noncomputable def infoParam {Θ X Y : Type} [MeasurableSpace Θ] [MeasurableSpace X]
    [MeasurableSpace Y] {n : ℕ} (A : DPVerify.RandAlg X Y n) (Ψ : Measure Θ)
    (P : Θ → Measure X) [∀ θ, IsProbabilityMeasure (P θ)] : ℝ≥0∞ :=
  ThompsonTutorial.InfoRatio.mutualInfo (algJointLaw A Ψ P)
    (fun q => A.run q.1.2 q.2) (fun q => q.1.1)

/-- **Information about the sample** `I(A(S); S)` (p. 9): the mutual information between the
output `U = A(S)` and the sample `S` under `algJointLaw A Ψ P` (θ drawn from the prior). -/
noncomputable def infoSample {Θ X Y : Type} [MeasurableSpace Θ] [MeasurableSpace X]
    [MeasurableSpace Y] {n : ℕ} (A : DPVerify.RandAlg X Y n) (Ψ : Measure Θ)
    (P : Θ → Measure X) [∀ θ, IsProbabilityMeasure (P θ)] : ℝ≥0∞ :=
  ThompsonTutorial.InfoRatio.mutualInfo (algJointLaw A Ψ P)
    (fun q => A.run q.1.2 q.2) (fun q => q.1.2)

end MemoSDPI.Main


