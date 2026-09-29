-- Prove2me | Definitions.Def_SoarModel
-- name    : SoarModel
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-22T18:55:50.442717+00:00
-- url     : https://prove2.me/theorems/1a2fa7f8-276e-488e-9ee4-6e2bbe4a502a
-- title:
--   Dynamic two-sided matching: the hindsight benchmark and regret
-- statement:
--   This module fixes the model of Chen, Kanoria, Kumar and Zhang: a centralized platform holds $n$ supply units and must irrevocably assign one to each of $n$ sequentially arriving demand units, and its performance is measured against the value of the best assignment made with full hindsight.
--
--   **Primitives.** The demand weight space $\mathcal X$ and the supply feature space $\mathcal Y$ are measurable spaces. Supply units $Y_1, \dots, Y_n$ are drawn i.i.d. from a supply distribution $Q$ on $\mathcal Y$ and demand units $X_1, \dots, X_n$ i.i.d. from a demand distribution $P$ on $\mathcal X$; the joint law of an $n$-tuple of each is the product measure $P^{\otimes n} \otimes Q^{\otimes n}$ on $\mathcal X^n \times \mathcal Y^n$. Matching demand $x$ to supply $y$ generates the match value $\varphi(x, y)$ for a quality function $\varphi : \mathcal X \times \mathcal Y \to \mathbb R$. The quality function is **bounded by $C$** when $|\varphi(x,y)| \le C$ for all $x, y$; the paper imposes boundedness so that the benchmark below is well defined.
--
--   **Hindsight relaxation.** For realized tuples $x \in \mathcal X^n$ and $y \in \mathcal Y^n$ the hindsight-optimal cumulative match value is the best perfect assignment,
--   $$\sup_{\sigma \in S_n} \sum_{t=1}^{n} \varphi\bigl(x_t, y_{\sigma(t)}\bigr),$$
--   where $S_n$ is the symmetric group on $\{1, \dots, n\}$ (the permutations of the finite index set, which carry the discrete $\sigma$-algebra in which every subset is measurable). The **hindsight optimum value** is its expectation per match,
--   $$U^H_n = \frac{1}{n}\,\mathbb E_{X \sim P^{\otimes n},\, Y \sim Q^{\otimes n}}\Bigl[\sup_{\sigma \in S_n} \sum_{t=1}^{n} \varphi\bigl(X_t, Y_{\sigma(t)}\bigr)\Bigr]$$
--   (equation (2)). The **limiting hindsight optimum** is the thick-market limit $U_\infty = \lim_{n \to \infty} U^H_n$, which the paper shows exists because $U^H_n$ is monotone and bounded; it is recorded here as the supremum $U_\infty = \sup_{n \ge 1} U^H_n$ of the sequence, which coincides with the limit once monotonicity is established. The **regret of the hindsight-optimal algorithm** on horizon $n$ (Remark 4) is
--   $$\mathrm{Reg}_n(\mathrm{H\text{-}OPT}) = U_\infty - U^H_n .$$
--
--   **Role.** Every performance statement of the paper is phrased against $U_\infty$: the regret of a policy is $U_\infty$ minus its average expected match value (equation (3)), and the meta-theorem expresses the value of the SOAR policy as an average of the $U^H_k$. The definitions here are shared by every theorem of the mission.
--
--   **Formalization Note** The supremum over $S_n$ is a maximum over a finite nonempty set, so it is attained. The expectation is a Bochner integral against $P^{\otimes n} \otimes Q^{\otimes n}$; the theorems of the mission carry the hypotheses (measurability and boundedness of $\varphi$) under which the integrand is integrable, so no junk value of a non-integrable integral is ever used. Dividing by $n$ is real division, so $U^H_0 = 0$ is a junk value; $U_\infty$ is defined as the supremum over $n \ge 1$ only, and statements about the sequence $U^H_n$ are made for $n \ge 1$. The $\sigma$-algebras on $\mathcal X$ and $\mathcal Y$ are arbitrary; $P$ and $Q$ are required to be probability measures in every theorem, and the definitions only need them $\sigma$-finite.
-- source:
--   Y. Chen, Y. Kanoria, A. Kumar, W. Zhang, Feature-Based Dynamic Matching, SSRN working paper 4451799 (version of 27 May 2025; extended abstract in Proc. 24th ACM Conference on Economics and Computation, EC'23), https://ssrn.com/abstract=4451799, Section 2 (equations (1), (2), (3)), Remark 4, and Appendix A

import Mathlib

/-!
# Feature-based dynamic matching: the hindsight benchmark

Chen, Kanoria, Kumar, Zhang, *Feature-Based Dynamic Matching*, Section 2 and Appendix A.

A demand distribution `P` on the demand-weight space `X`, a supply distribution `Q` on the
supply-feature space `Y`, and a match quality function `φ : X → Y → ℝ`.  With `n` demand units
`x : Fin n → X` and `n` supply units `y : Fin n → Y`, the hindsight relaxation matches them by the
best perfect assignment.  Expectations over i.i.d. draws are integrals against the product
measures `P^n ⊗ Q^n`.
-/

open MeasureTheory
open scoped BigOperators

/-- The hindsight-optimal cumulative match value of the demand units `x` against the supply units
`y`: the largest total quality `∑ₜ φ(xₜ, y_{σ(t)})` over all perfect assignments `σ` (eq. (2),
before taking expectations). -/
noncomputable def SoarHindsightSum {X Y : Type*} (φ : X → Y → ℝ) {n : ℕ}
    (x : Fin n → X) (y : Fin n → Y) : ℝ :=
  ⨆ σ : Equiv.Perm (Fin n), ∑ t : Fin n, φ (x t) (y (σ t))

/-- Permutations of a finite set carry the discrete σ-algebra, so that assignment rules valued
in permutations are measurable exactly when their fibres are. -/
instance soarPermMeasurableSpace (m : ℕ) : MeasurableSpace (Equiv.Perm (Fin m)) := ⊤

instance soarPermDiscrete (m : ℕ) : DiscreteMeasurableSpace (Equiv.Perm (Fin m)) :=
  ⟨fun _ => trivial⟩

/-- The joint law `P^n ⊗ Q^n` of `n` i.i.d. demand units and `n` independent i.i.d. supply
units. -/
noncomputable def SoarPairMeasure {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (P : Measure X) (Q : Measure Y) [SigmaFinite P] [SigmaFinite Q] (n : ℕ) :
    Measure ((Fin n → X) × (Fin n → Y)) :=
  (Measure.pi fun _ : Fin n => P).prod (Measure.pi fun _ : Fin n => Q)

/-- The hindsight optimum value `U^H_n(P, Q, φ)` (eq. (2)): the expected hindsight-optimal
cumulative match value of `n` i.i.d. demand and supply units, per match. -/
noncomputable def SoarHindsight {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (P : Measure X) (Q : Measure Y) [SigmaFinite P] [SigmaFinite Q] (φ : X → Y → ℝ) (n : ℕ) :
    ℝ :=
  (∫ p, SoarHindsightSum φ p.1 p.2 ∂SoarPairMeasure P Q n) / n

/-- The limiting hindsight optimum `U_∞(P, Q, φ) = lim_{n → ∞} U^H_n`, taken as the supremum of
the sequence `U^H_1, U^H_2, …` (the sequence is monotone and bounded when `φ` is bounded). -/
noncomputable def SoarLimit {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (P : Measure X) (Q : Measure Y) [SigmaFinite P] [SigmaFinite Q] (φ : X → Y → ℝ) : ℝ :=
  ⨆ n : ℕ, SoarHindsight P Q φ (n + 1)

/-- The regret of the hindsight-optimal algorithm, `Reg_n(H-OPT) = U_∞ - U^H_n` (Remark 4). -/
noncomputable def SoarRegretH {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (P : Measure X) (Q : Measure Y) [SigmaFinite P] [SigmaFinite Q] (φ : X → Y → ℝ) (n : ℕ) :
    ℝ :=
  SoarLimit P Q φ - SoarHindsight P Q φ n

/-- The quality function is bounded by `C` in absolute value. -/
def SoarBounded {X Y : Type*} (φ : X → Y → ℝ) (C : ℝ) : Prop :=
  ∀ x y, |φ x y| ≤ C


