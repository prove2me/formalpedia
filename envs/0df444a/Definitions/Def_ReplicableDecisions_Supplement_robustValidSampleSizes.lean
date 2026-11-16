-- Prove2me | Definitions.Def_ReplicableDecisions_Supplement_robustValidSampleSizes
-- name    : ReplicableDecisions_Supplement_robustValidSampleSizes
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:03:53.919366+00:00
-- url     : https://prove2.me/theorems/d7dfd3af-f950-4e17-81cd-f2116910b0ad
-- title:
--   Robust neighborhood $\mathcal T_\tau$, acceptable sets $\Gamma_\tau$ and $n^\star_{\mathcal T_\tau}$
-- statement:
--   For $\tau\ge0$ let
--   $$\mathcal T_\tau=\{Q\text{ on }\mathcal Z:\min_{P\in\mathcal P}h(Q,P)\le\tau\},\qquad \Gamma_\tau(Q)=\bigcap_{P\in\mathcal P:\,h(Q,P)\le\tau}\Gamma(P).$$
--   An $n$-sample algorithm is **robustly $(\beta,\rho)$-valid on $\mathcal T_\tau$** if, at every $Q\in\mathcal T_\tau$, $\Pr_{S\sim Q^n}[A(S;R)\notin\Gamma_\tau(Q)]\le\beta$ and $\mathrm{rep}_Q(A)\le\rho$. The least such $n$ is $n^\star_{\mathcal T_\tau}(\beta,\rho)$.
--
--   This is the misspecification contract of Theorem 6.11: the neighborhood may contain infinitely many laws, while the algorithm uses only the supplied finite family.
--
--   **Formalization Note** $Q$ ranges over all probability vectors on $\mathcal Z$; seed law and measurability as in the published `IsValid`; the least element is read through `IsLeast`.
-- source:
--   Chen, Replicable Decisions in Finite Experiments: A Chain Converse and Its Limits, STOC 2027 submission (sha256 52d181db50a1641806d046c9e7d92377e64271681f0fc36c7e6be16d6dabb868), §6.3, p.34 (PDF p.36)

import Mathlib
import Definitions.Def_ReplicableDecisions_hellinger
import Definitions.Def_ReplicableDecisions_Supplement_strongValidSampleSizes

open MeasureTheory

namespace ReplicableDecisions.Supplement

/-- **The robust neighborhood** `T_τ = {Q on Z : min_{P∈P} h(Q, P) ≤ τ}`. Chen, *Replicable
Decisions in Finite Experiments*, STOC 2027 submission (sha256 52d181db…), §6.3, p.34 (PDF p.36).

**Formalization Note.** `Q` ranges over all probability vectors on `Z`; the minimum over the finite
family is `≤ τ` iff some model is within `τ`. -/
def robustNbhd {ι : Type*} {Z : Type} [Fintype Z] (E : Experiment ι Z) (τ : ℝ) : Set (Z → ℝ) :=
  {q | q ∈ stdSimplex ℝ Z ∧ ∃ i, hellinger q (E.P i) ≤ τ}

/-- **The robust acceptable sets** `Γ_τ(Q) = ⋂_{P∈P: h(Q,P)≤τ} Γ(P)`. Chen, STOC 2027 submission
(sha256 52d181db…), §6.3, p.34 (PDF p.36). -/
def robustΓ {ι : Type*} {Z : Type} [Fintype Z] {Y : Type*} (E : Experiment ι Z)
    (Γ : ι → Set Y) (τ : ℝ) (q : Z → ℝ) : Set Y :=
  ⋂ i ∈ {i | hellinger q (E.P i) ≤ τ}, Γ i

/-- **Accuracy error under an arbitrary law** `q` with respect to an acceptable set `C`:
`Pr[A(S; R) ∉ C]` with `S ∼ qⁿ` and the independent seed `R ∼ μ`. Chen, STOC 2027 submission
(sha256 52d181db…), §6.3, p.34 (PDF p.36). -/
noncomputable def errDist {Z : Type} [Fintype Z] {Y : Type*} {n : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] (q : Z → ℝ) (C : Set Y) (μ : Measure Ω) (A : (Fin n → Z) → Ω → Y) : ℝ :=
  ∑ x : Fin n → Z, productLaw q x * μ.real {ω | A x ω ∉ C}

/-- **Robust (β, ρ)-validity on `T_τ`:** "accuracy with respect to Γ_τ and agreement at every
Q ∈ T_τ". Chen, STOC 2027 submission (sha256 52d181db…), §6.3, p.34 (PDF p.36).

**Formalization Note.** As the published `IsValid`, with a probability seed law and measurability in
the seed, and both requirements imposed at every `Q ∈ T_τ`. -/
def IsRobustValid {ι : Type*} {Z : Type} [Fintype Z] {Y : Type*} {n : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] (E : Experiment ι Z) (Γ : ι → Set Y) (τ β ρ : ℝ) (μ : Measure Ω)
    (A : (Fin n → Z) → Ω → Y) : Prop :=
  IsProbabilityMeasure μ ∧ IsSeedMeasurable A ∧
    ∀ q ∈ robustNbhd E τ, errDist q (robustΓ E Γ τ q) μ A ≤ β ∧ repDist q μ A ≤ ρ

/-- **The sample sizes admitting a robustly valid algorithm;** `n⋆_{T_τ}` is the least element.
Chen, STOC 2027 submission (sha256 52d181db…), §6.3, p.34 (PDF p.36): "Let n⋆_{T_τ} be the least
fixed sample size guaranteeing accuracy with respect to Γ_τ and agreement at every Q ∈ T_τ." -/
def robustValidSampleSizes {ι : Type*} {Z : Type} [Fintype Z] {Y : Type*} (E : Experiment ι Z)
    (Γ : ι → Set Y) (τ β ρ : ℝ) : Set ℕ :=
  {n | ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (A : (Fin n → Z) → Ω → Y),
    IsRobustValid E Γ τ β ρ μ A}

end ReplicableDecisions.Supplement


