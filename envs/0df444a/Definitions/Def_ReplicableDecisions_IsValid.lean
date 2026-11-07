-- Prove2me | Definitions.Def_ReplicableDecisions_IsValid
-- name    : ReplicableDecisions_IsValid
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:03:11.49183+00:00
-- url     : https://prove2.me/theorems/2b7b4f00-e1b5-4163-8359-0a8098fa4554
-- title:
--   Accuracy error, replication failure, $(\beta,\rho)$-validity and $n^\star$
-- statement:
--   Let $\Gamma(P)\subseteq\mathcal Y$ be the acceptable outputs at $P$. An $n$-sample algorithm is a map $A:\mathcal Z^n\times\mathcal R\to\mathcal Y$, measurable in its seed, whose seed law is independent of the model and of the data. With $S,S'\sim P^n$ independent and the same independent seed $R$,
--
--   $$
--   \mathrm{err}_P(A)=\Pr[A(S;R)\notin\Gamma(P)],\qquad \mathrm{rep}_P(A)=\Pr[A(S;R)\ne A(S';R)].
--   $$
--
--   The algorithm is **$(\beta,\rho)$-valid** if $\mathrm{err}_P(A)\le\beta$ and $\mathrm{rep}_P(A)\le\rho$ at every $P\in\mathcal P$, and
--
--   $$
--   n^\star(\beta,\rho)=\min\{n\in\mathbb Z_{\ge0}:\text{a }(\beta,\rho)\text{-valid }n\text{-sample algorithm exists}\},
--   $$
--
--   with $\min\emptyset=+\infty$.
--
--   Replication is required at every model of the family, including those with several acceptable outputs, and not outside the family. This is the contract the mission's goal characterizes.
--
--   **Formalization Note** `validSampleSizes` is the set in the minimum, with $n=0$ a candidate, and statements read $n^\star$ through `IsLeast`. Seed spaces range over `Type`. The seed law is one measure, chosen before the quantifier over models. The two runs share one point $\omega$ of the seed space.
-- source:
--   Chen, Replicable Decisions in Finite Experiments, STOC 2027 submission (sha256 52d181db…), §2 "Experiments and validity", p.8 (PDF p.10)

import Mathlib
import Definitions.Def_ReplicableDecisions_Experiment

open MeasureTheory

namespace ReplicableDecisions

/-- **Measurable in its seed.** Chen, *Replicable Decisions in Finite Experiments*, STOC 2027
submission (sha256 52d181db…), §2, p.8 (PDF p.10): "An n-sample algorithm is a map
A : Z^n × R → Y, measurable in its seed".

**Formalization Note.** Stated on the finite output set as: each `{ω | A x ω = y}` is measurable.
Every event of `err` and `rep` is then a finite union of such sets when `Y` is finite. -/
def IsSeedMeasurable {Z : Type} {Y : Type*} {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (A : (Fin n → Z) → Ω → Y) : Prop :=
  ∀ x y, MeasurableSet {ω | A x ω = y}

/-- **Accuracy error** `err_P(A) = Pr[A(S; R) ∉ Γ(P)]` at the model of index `i`, with `S ∼ Pⁿ` and
the independent seed `R ∼ μ`. Chen, STOC 2027 submission (sha256 52d181db…), §2, p.8 (PDF p.10).

**Formalization Note.** The data side is a finite sum over samples; the seed side is the seed
measure. -/
noncomputable def err {ι : Type*} {Z : Type} [Fintype Z] {Y : Type*} {n : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] (E : Experiment ι Z) (Γ : ι → Set Y) (μ : Measure Ω)
    (A : (Fin n → Z) → Ω → Y) (i : ι) : ℝ :=
  ∑ x : Fin n → Z, productLaw (E.P i) x * μ.real {ω | A x ω ∉ Γ i}

/-- **Replication failure probability** `rep_P(A) = Pr[A(S; R) ≠ A(S′; R)]`, with `S, S′ ∼ Pⁿ`
independent and the same independent seed `R`. Chen, STOC 2027 submission (sha256 52d181db…), §2,
p.8 (PDF p.10).

**Formalization Note.** One `ω` enters both runs: the two samples are summed independently, and the
event compares `A x ω` with `A x′ ω`. -/
noncomputable def rep {ι : Type*} {Z : Type} [Fintype Z] {Y : Type*} {n : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] (E : Experiment ι Z) (μ : Measure Ω)
    (A : (Fin n → Z) → Ω → Y) (i : ι) : ℝ :=
  ∑ x : Fin n → Z, ∑ x' : Fin n → Z,
    productLaw (E.P i) x * productLaw (E.P i) x' * μ.real {ω | A x ω ≠ A x' ω}

/-- **(β, ρ)-validity.** Chen, STOC 2027 submission (sha256 52d181db…), §2, p.8 (PDF p.10): "The
algorithm is (β, ρ)-valid if these two quantities are at most β and ρ, respectively, at every
P ∈ P."

**Formalization Note.** The clauses that the seed law is a probability measure and that `A` is
measurable in its seed are part of the page's definition of an algorithm, so they are bundled here.
The seed law `μ` does not depend on the model: `∀ i` comes after `μ` and `A`. -/
def IsValid {ι : Type*} {Z : Type} [Fintype Z] {Y : Type*} {n : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] (E : Experiment ι Z) (Γ : ι → Set Y) (β ρ : ℝ) (μ : Measure Ω)
    (A : (Fin n → Z) → Ω → Y) : Prop :=
  IsProbabilityMeasure μ ∧ IsSeedMeasurable A ∧ ∀ i, err E Γ μ A i ≤ β ∧ rep E μ A i ≤ ρ

/-- **The sample sizes admitting a (β, ρ)-valid algorithm.** Chen, STOC 2027 submission
(sha256 52d181db…), §2, p.8 (PDF p.10): `n⋆(β, ρ) = min{n ∈ Z≥0 : a (β, ρ)-valid n-sample algorithm
exists}`, with `min ∅ = +∞`.

**Formalization Note.** `n⋆` is read through `IsLeast (validSampleSizes E Γ β ρ) N`, not through
`sInf`, so an empty set gives no junk value; `n = 0` is a candidate. Seed spaces range over `Type`;
the page notes that arbitrary seed spaces offer no additional power, since a seed induces a
distribution on the finitely many deterministic maps. -/
def validSampleSizes {ι : Type*} {Z : Type} [Fintype Z] {Y : Type*} (E : Experiment ι Z)
    (Γ : ι → Set Y) (β ρ : ℝ) : Set ℕ :=
  {n | ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (A : (Fin n → Z) → Ω → Y),
    IsValid E Γ β ρ μ A}

end ReplicableDecisions


