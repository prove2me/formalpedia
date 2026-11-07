-- Prove2me | Definitions.Def_ReplicableDecisions_thresholdRule
-- name    : ReplicableDecisions_thresholdRule
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:02:32.524893+00:00
-- url     : https://prove2.me/theorems/2304930f-6c43-4a10-a706-c05e53a7214e
-- title:
--   The rule of Theorem 3.1: shared random breadth-first threshold after maximum likelihood
-- statement:
--   Let $G$ be a graph on the models, $D=\mathrm{dist}_G(A_0,A_1)$ and $d(P)=\mathrm{dist}_G(A_0,P)$. If $D<\infty$, the shared seed $t$ is uniform on the odd integers in $[1,D-2]$, and the selector is $f_t(P)=\mathbf 1\{d(P)>t\}$. If $D=\infty$, the seed is trivial and the selector is $\mathbf 1\{d(P)=\infty\}$. On a sample $S$ the rule outputs $f_t(\widehat P(S))$.
--
--   This rule reads only the probability tables and the acceptable sets; in Theorem 3.1 it runs on $G=G_{<s_\rho}$.
--
--   **Formalization Note** The seed space is $\mathbb N$ with its discrete $\sigma$-algebra, and in the trivial case the seed is a point mass at $0$. For $D=\infty$, the paper's proof uses a neighborhood-correct component labeling, with label $0$ on components meeting neither class; the selector $\mathbf 1\{d(P)=\infty\}$ differs from it only on those components, where the label is an arbitrary choice.
-- source:
--   Chen, Replicable Decisions in Finite Experiments, STOC 2027 submission (sha256 52d181db…), proof of Theorem 3.1, p.11 (PDF p.13); proof of Theorem 3.2, pp.11–12 (PDF pp.13–14)

import Mathlib
import Definitions.Def_ReplicableDecisions_forcedDist

open MeasureTheory

namespace ReplicableDecisions

/-- **The odd thresholds** `t ∈ [1, D − 2]`. Chen, *Replicable Decisions in Finite Experiments*, STOC
2027 submission (sha256 52d181db…), proof of Theorem 3.2, p.12 (PDF p.14).

**Formalization Note.** Natural subtraction: `D − 2 = 0` for `D ≤ 2`, and the set is then empty, as
the page's range is. -/
def oddThresholds (D : ℕ) : Finset ℕ :=
  (Finset.Icc 1 (D - 2)).filter Odd

open Classical in
/-- **The shared seed law.** Chen, STOC 2027 submission (sha256 52d181db…), proof of Theorem 3.1, p.11
(PDF p.13), "that theorem's uniform odd threshold": uniform on the odd `t ∈ [1, D − 2]` when
`D = dist_G(A₀, A₁) < ∞`, and trivial when `D = ∞`.

**Formalization Note.** The seed space is `ℕ` with its discrete σ-algebra. In the trivial case the seed
is the point mass at `0`. -/
noncomputable def thresholdSeedLaw {ι : Type*} (G : SimpleGraph ι) (Γ : ι → Set Bool) : Measure ℕ :=
  if forcedDist G Γ false true = ⊤ then Measure.dirac 0
  else ProbabilityTheory.uniformOn (↑(oddThresholds (forcedDist G Γ false true).toNat) : Set ℕ)

open Classical in
/-- **The breadth-first threshold selector.** Chen, STOC 2027 submission (sha256 52d181db…), proof of
Theorem 3.2, p.11 (PDF p.13): `f_t(P) = 1{d(P) > t}` when `D < ∞`.

**Formalization Note.** When `D = ∞` the selector is `1{d(P) = ∞}`, independent of `t`. It is a
breadth-first threshold, as Theorem 3.1 says. It differs from the "neighborhood-correct component
labeling" of the proof (p.12) only on components meeting neither class, where the proof's label is
an arbitrary choice. -/
noncomputable def ruleSelector {ι : Type*} (G : SimpleGraph ι) (Γ : ι → Set Bool) (t : ℕ) (i : ι) :
    Bool :=
  if forcedDist G Γ false true = ⊤ then decide (layerDist G Γ i = ⊤)
  else decide ((t : ℕ∞) < layerDist G Γ i)

/-- **The rule of Theorem 3.1.** Chen, STOC 2027 submission (sha256 52d181db…), Theorem 3.1, p.10
(PDF p.12): "maximum likelihood followed by a shared random breadth-first threshold". The output is
`f_t(P̂(x))` on the sample `x` and the seed `t`. -/
noncomputable def thresholdRule {ι : Type*} {Z : Type} {n : ℕ} (G : SimpleGraph ι)
    (Γ : ι → Set Bool) (mle : (Fin n → Z) → ι) : (Fin n → Z) → ℕ → Bool :=
  fun x t => ruleSelector G Γ t (mle x)

end ReplicableDecisions


