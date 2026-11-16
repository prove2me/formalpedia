-- Prove2me | Definitions.Def_ReplicableDecisions_Supplement_strongValidSampleSizes
-- name    : ReplicableDecisions_Supplement_strongValidSampleSizes
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:00:10.106212+00:00
-- url     : https://prove2.me/theorems/37c6357a-4d15-47e2-a38f-18eea3c5c6c4
-- title:
--   Strong replication: $\mathrm{rep}_Q$ at every law $Q$, strong $(\beta,\rho)$-validity and $n^\star_{\mathrm{str}}$
-- statement:
--   Let $\mathcal P=\{P_i\}$ be a known finite experiment on a finite observation space $\mathcal Z$ with acceptable sets $\Gamma(P_i)$, and let $A:\mathcal Z^n\times\mathcal R\to\mathcal Y$ be an $n$-sample algorithm whose seed $R\sim\mu$ is independent of the data. For any probability vector $q$ on $\mathcal Z$ put
--   $$\mathrm{rep}_q(A)=\Pr\big[A(S;R)\neq A(S';R)\big],\qquad S,S'\sim q^{n}\ \text{independent},$$
--   with one shared seed $R$ in both runs.
--
--   The algorithm is **strongly $(\beta,\rho)$-valid** if its seed law is a probability measure, it is measurable in its seed, its accuracy error is at most $\beta$ at every model of the experiment, and $\mathrm{rep}_q(A)\le\rho$ for **every** probability vector $q$ on $\mathcal Z$. The set of sample sizes $n$ admitting such an algorithm has least element $n^\star_{\mathrm{str}}(\beta,\rho)$, when it is nonempty.
--
--   This is the paper's comparison contract: accuracy only at the specified models, replication under every distribution on the observation space, including laws outside the family.
--
--   **Formalization Note** $n^\star_{\mathrm{str}}$ is read through `IsLeast` of `strongValidSampleSizes`, never through `sInf`; seed spaces range over `Type`, as in the published `validSampleSizes`.
-- source:
--   Chen, Replicable Decisions in Finite Experiments: A Chain Converse and Its Limits, STOC 2027 submission (sha256 52d181db50a1641806d046c9e7d92377e64271681f0fc36c7e6be16d6dabb868), §1, p.4 (PDF p.6); §4.1, p.20 (PDF p.22); Appendix B.1, p.41 (PDF p.43)

import Mathlib
import Definitions.Def_ReplicableDecisions_IsValid

open MeasureTheory

namespace ReplicableDecisions.Supplement

/-- **Replication failure under an arbitrary law** `q` on `Z`: `Pr[A(S; R) ≠ A(S′; R)]` with
`S, S′ ∼ qⁿ` independent and one shared independent seed `R ∼ μ`. Chen, *Replicable Decisions in
Finite Experiments*, STOC 2027 submission (sha256 52d181db…), §1, p.4 (PDF p.6) and Appendix B.1,
p.41 (PDF p.43): "replication is required under every distribution on its observation space".

**Formalization Note.** Same form as the published `rep`, with the model `E.P i` replaced by any
function `q : Z → ℝ`; it is used only for `q ∈ stdSimplex ℝ Z`. -/
noncomputable def repDist {Z : Type} [Fintype Z] {Y : Type*} {n : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] (q : Z → ℝ) (μ : Measure Ω) (A : (Fin n → Z) → Ω → Y) : ℝ :=
  ∑ x : Fin n → Z, ∑ x' : Fin n → Z,
    productLaw q x * productLaw q x' * μ.real {ω | A x ω ≠ A x' ω}

/-- **Strong (β, ρ)-validity.** Chen, STOC 2027 submission (sha256 52d181db…), Appendix B.1, p.41
(PDF p.43): "accuracy is required at the specified finite experiment, but replication is required
under every distribution on its observation space. This convention imposes no accuracy requirement
outside the experiment."

**Formalization Note.** As the published `IsValid`: a probability seed law, measurability in the
seed, accuracy `err ≤ β` at every model; replication `repDist q ≤ ρ` at every probability vector
`q` on `Z` (not only at the models). -/
def IsStronglyValid {ι : Type*} {Z : Type} [Fintype Z] {Y : Type*} {n : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] (E : Experiment ι Z) (Γ : ι → Set Y) (β ρ : ℝ) (μ : Measure Ω)
    (A : (Fin n → Z) → Ω → Y) : Prop :=
  IsProbabilityMeasure μ ∧ IsSeedMeasurable A ∧ (∀ i, err E Γ μ A i ≤ β) ∧
    ∀ q ∈ stdSimplex ℝ Z, repDist q μ A ≤ ρ

/-- **The sample sizes admitting a strongly (β, ρ)-valid algorithm.** `n⋆_str(β, ρ)` is the least
element. Chen, STOC 2027 submission (sha256 52d181db…), Appendix B.1, p.41 (PDF p.43): "Write
n⋆_str(β, ρ) for the optimal fixed sample size …".

**Formalization Note.** `n⋆_str` is read through `IsLeast`, never `sInf`; seed spaces range over
`Type`, as in the published `validSampleSizes`. -/
def strongValidSampleSizes {ι : Type*} {Z : Type} [Fintype Z] {Y : Type*} (E : Experiment ι Z)
    (Γ : ι → Set Y) (β ρ : ℝ) : Set ℕ :=
  {n | ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω) (A : (Fin n → Z) → Ω → Y),
    IsStronglyValid E Γ β ρ μ A}

end ReplicableDecisions.Supplement


