-- Prove2me | Definitions.Def_InfoGen_HighProb_Setting
-- name    : InfoGen_HighProb_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T01:27:23.696233+00:00
-- url     : https://prove2.me/theorems/61ee93a3-21aa-4a52-b28f-ea3a33769690
-- title:
--   §1, p. 2, (11), p. 4, App. A–B, pp. 11–12 — mutual information, the empirical-risk vector Λ_W(S), I(Λ_W(S);W), and m parallel copies of P_{W|S}
-- statement:
--   These are the objects of Xu and Raginsky's high-probability generalization bound. The setting is that of §1 (p. 2): "there is an instance space $\mathsf Z$, a hypothesis space $\mathsf W$, and a nonnegative loss function $\ell : \mathsf W \times \mathsf Z \to \mathbb R_+$. A learning algorithm characterized by a Markov kernel $P_{W|S}$ takes as input a dataset of size $n$, i.e., an $n$-tuple $S = (Z_1, \dots, Z_n)$ of i.i.d. random elements of $\mathsf Z$ with some unknown distribution $\mu$, and picks a random element $W$ of $\mathsf W$ as the output hypothesis according to $P_{W|S}$." The population risk is $L_\mu(w) = \int_{\mathsf Z} \ell(w,z)\,\mu(dz)$ and the empirical risk is $L_S(w) = \frac1n\sum_{i=1}^n \ell(w, Z_i)$; these, together with the sample law $\mu^{\otimes n}$, are taken from the published definition `LearnStability.Characterization.Setting`. The joint law of the dataset and the output is $P_{S,W} = \mu^{\otimes n} \otimes P_{W|S}$.
--
--   This file introduces:
--
--   1. **Mutual information of a joint law.** For a probability measure $P_{X,Y}$ on a product space with marginals $P_X$ and $P_Y$,
--   $$I(X;Y) = D(P_{X,Y} \,\|\, P_X \otimes P_Y) \in [0, \infty],$$
--   the Kullback–Leibler divergence from the joint law to the product of its marginals (App. A, p. 11).
--   2. **The empirical-risk vector** (eq. (11), p. 4): $\Lambda_{\mathsf W}(s) = (L_s(w))_{w\in\mathsf W}$, an element of $\mathbb R^{\mathsf W}$, the collection of empirical risks of all hypotheses on the dataset $s$.
--   3. **The quantity $I(\Lambda_{\mathsf W}(S); W)$**, the mutual information between the empirical-risk vector and the output, computed from the image of $P_{S,W}$ under $(s,w) \mapsto (\Lambda_{\mathsf W}(s), w)$.
--   4. **The parallel execution** of Lemma B.1 (p. 11): the law of $m$ independent copies $(S_1,W_1),\dots,(S_m,W_m)$ of $(S,W)$, each with law $P_{S,W}$, i.e. the product measure $P_{S,W}^{\otimes m}$.
--   5. **The sign map** $r \mapsto \pm 1$, encoding the sign $r \in \{\pm1\}$ used in Lemma B.2 and in the monitor of the proof of Theorem 3.
--
--   These objects state Theorem 3 (the sample complexity of high-probability generalization under an input-output mutual-information budget), Theorem 4, and the lemmas of Appendix B.
--
--   **Formalization Note.** Mutual information takes values in $[0,\infty]$ (`ℝ≥0∞`). $\mathbb R^{\mathsf W}$ carries the product σ-algebra. The theorems using these objects assume that $\mathsf W$ is countable with measurable singletons; under the product σ-algebra the paper's claim that the results hold "even when $\mathsf W$ is uncountably infinite" (p. 4) fails (see the theorems' notes). The sign $r \in \{\pm1\}$ is encoded by a Boolean, `true` $\mapsto 1$ and `false` $\mapsto -1$, so that $\mathsf W \times [m] \times \{\pm1\}$ is countable; $[m]$ is `Fin m` (indices $0,\dots,m-1$).
-- source:
--   Xu & Raginsky, arXiv:1705.07809v2, §1 eqs. (1)–(3), p. 2; eq. (11), p. 4; App. A, p. 11 (I(X;Y) = D(P_{X,Y}‖P_X ⊗ P_Y)); Lemmas B.1–B.2, p. 11

import Mathlib
import Definitions.Def_LearnStability_Characterization_Setting
import Definitions.Def_InfoGen_Expected_Setting

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal

namespace InfoGen.HighProb

open LearnStability.Characterization

/-- The collection of empirical risks `Λ_W(s) = (L_s(w))_{w ∈ W}` of eq. (11), p. 4. -/
noncomputable def empRiskVec {Z W : Type*} (ℓ : W → Z → ℝ) {n : ℕ} (s : Fin n → Z) : W → ℝ :=
  fun w => empRisk ℓ s w

/-- `I(Λ_W(S); W)`, the mutual information between the vector of empirical risks and the output of the
algorithm `P_{W|S} = κ`, under the joint law `P_{S,W} = μ^{⊗n} ⊗ κ` (eq. (11) and Theorem 3, p. 4). -/
noncomputable def lambdaInfo {Z W : Type*} [MeasurableSpace Z] [MeasurableSpace W]
    (ℓ : W → Z → ℝ) (μ : Measure Z) {n : ℕ} (κ : Kernel (Fin n → Z) W) : ℝ≥0∞ :=
  InfoGen.Expected.mutualInfo ((sampleLaw μ n ⊗ₘ κ).map (fun p => (empRiskVec ℓ p.1, p.2)))

/-- The parallel execution of `m` independent copies of `P_{W|S} = κ` on independent datasets
`S_1, …, S_m ∼ μ^{⊗n}` (Lemma B.1, p. 11): the law of `((S_1, W_1), …, (S_m, W_m))`. -/
noncomputable def parallelLaw {Z W : Type*} [MeasurableSpace Z] [MeasurableSpace W]
    (μ : Measure Z) {n : ℕ} (κ : Kernel (Fin n → Z) W) (m : ℕ) :
    Measure (Fin m → (Fin n → Z) × W) :=
  Measure.pi (fun _ : Fin m => sampleLaw μ n ⊗ₘ κ)

/-- The sign `r ∈ {±1}` encoded by a Boolean: `true ↦ 1`, `false ↦ -1` (Lemma B.2, p. 11). -/
def sgn (r : Bool) : ℝ := if r then 1 else -1

end InfoGen.HighProb


