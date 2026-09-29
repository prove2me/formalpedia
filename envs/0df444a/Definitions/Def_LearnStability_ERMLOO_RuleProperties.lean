-- Prove2me | Definitions.Def_LearnStability_ERMLOO_RuleProperties
-- name    : LearnStability_ERMLOO_RuleProperties
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T18:20:11.412862+00:00
-- url     : https://prove2.me/theorems/17bedc0c-19b8-41ca-87b7-6cd332c92f56
-- title:
--   Consistency, AERM, generalization, on-average generalization and LOO stability (Definition 29)
-- statement:
--   Let $A$ be a learning rule for a learning problem $(\mathcal H,\mathcal Z,f)$, let $\mathcal D$ be a probability measure on $\mathcal Z$, and let $\varepsilon:\mathbb N\to\mathbb R$. For every sample size $m\ge1$, with $S\sim\mathcal D^m$:
--
--   1. $A$ is **consistent** with rate $\varepsilon$ under $\mathcal D$ if $\mathbb E_S[F(A(S))-F^*]\le\varepsilon(m)$ (Eq. (2));
--   2. $A$ is an **AERM** with rate $\varepsilon$ under $\mathcal D$ if $\mathbb E_S[F_S(A(S))-F_S(\hat h_S)]\le\varepsilon(m)$;
--   3. $A$ **generalizes** with rate $\varepsilon$ under $\mathcal D$ if $\mathbb E_S[|F(A(S))-F_S(A(S))|]\le\varepsilon(m)$;
--   4. $A$ **on-average generalizes** with rate $\varepsilon$ under $\mathcal D$ if $|\mathbb E_S[F(A(S))-F_S(A(S))]|\le\varepsilon(m)$ (Eq. (11));
--   5. (Definition 29) $A$ is **LOO stable** with rate $\varepsilon$ under $\mathcal D$ if for every $m\ge2$
--   $$\frac1m\sum_{i=1}^m\mathbb E_{S\sim\mathcal D^m}\Big[\big|f(A(S^{\setminus i});z_i)-f(A(S);z_i)\big|\Big]\le\varepsilon(m),$$
--   where $S^{\setminus i}$ is the sample $S$ with the instance $z_i$ removed, a sample of size $m-1$.
--
--   A rule is **universally** consistent, generalizing or LOO stable with rate $\varepsilon$ if the corresponding property holds with the same $\varepsilon$ under every probability measure $\mathcal D$ on $\mathcal Z$.
--
--   These are the three properties that Theorem 31 shows to be equivalent for an ERM, and the two auxiliary notions (AERM, on-average generalization) through which the equivalence passes. The absolute value in LOO stability is inside the expectation; the weaker notion with the absolute value outside (on-average-LOO stability, Definition 30) is not equivalent to it.
--
--   **Formalization Note.** Samples are tuples $S:\mathrm{Fin}\,m\to\mathcal Z$ and $S^{\setminus i}$ is `Fin.removeNth i S`. LOO stability is stated for $m=n+1$ with $n\ge1$, because a rule acts on samples of size at least $1$. The universal notions quantify over probability measures with a fixed $\varepsilon$; whether $\varepsilon$ is a rate is asserted separately where needed.
-- source:
--   Shalev-Shwartz, Shamir, Srebro and Sridharan, Learnability, Stability and Uniform Convergence, JMLR 11 (2010), p. 2638 Eq. (2) and Definition 1; p. 2639 (AERM, generalization); p. 2650 Eq. (11); p. 2665 Definition 29

import Mathlib
import Definitions.Def_LearnStability_ERMLOO_Setting

open MeasureTheory

namespace LearnStability.ERMLOO

variable {H Z : Type*} [MeasurableSpace Z]

/-- `A` is consistent with rate `ε` under `D`, Eq. (2), p. 2638:
`E_{S∼D^m}[F(A(S)) − F*] ≤ ε(m)` for all `m ≥ 1`. -/
def Consistent (f : H → Z → ℝ) (A : Rule H Z) (D : Measure Z) (ε : ℕ → ℝ) : Prop :=
  ∀ m : ℕ, 1 ≤ m →
    ∫ S, (risk f D (A m S) - optRisk f D) ∂(sampleLaw D m) ≤ ε m

/-- `A` is universally consistent with rate `ε`: consistent with the same rate `ε` under every
probability distribution `D` on `Z` (Definition 1, p. 2638). -/
def UniversallyConsistent (f : H → Z → ℝ) (A : Rule H Z) (ε : ℕ → ℝ) : Prop :=
  ∀ D : Measure Z, IsProbabilityMeasure D → Consistent f A D ε

/-- `A` is an AERM with rate `ε` under `D` (p. 2639):
`E_{S∼D^m}[F_S(A(S)) − F_S(ĥ_S)] ≤ ε(m)` for all `m ≥ 1`. -/
def IsAERM (f : H → Z → ℝ) (A : Rule H Z) (D : Measure Z) (ε : ℕ → ℝ) : Prop :=
  ∀ m : ℕ, 1 ≤ m →
    ∫ S, (empRisk f S (A m S) - ermValue f S) ∂(sampleLaw D m) ≤ ε m

/-- `A` generalizes with rate `ε` under `D` (p. 2639):
`E_{S∼D^m}[|F(A(S)) − F_S(A(S))|] ≤ ε(m)` for all `m ≥ 1`. -/
def Generalizes (f : H → Z → ℝ) (A : Rule H Z) (D : Measure Z) (ε : ℕ → ℝ) : Prop :=
  ∀ m : ℕ, 1 ≤ m →
    ∫ S, |risk f D (A m S) - empRisk f S (A m S)| ∂(sampleLaw D m) ≤ ε m

/-- `A` universally generalizes with rate `ε`: it generalizes with the same rate `ε` under
every probability distribution `D` on `Z` (p. 2639). -/
def UniversallyGeneralizes (f : H → Z → ℝ) (A : Rule H Z) (ε : ℕ → ℝ) : Prop :=
  ∀ D : Measure Z, IsProbabilityMeasure D → Generalizes f A D ε

/-- `A` on-average generalizes with rate `ε` under `D`, Eq. (11), p. 2650:
`|E_{S∼D^m}[F(A(S)) − F_S(A(S))]| ≤ ε(m)` for all `m ≥ 1`. -/
def OnAverageGeneralizes (f : H → Z → ℝ) (A : Rule H Z) (D : Measure Z) (ε : ℕ → ℝ) : Prop :=
  ∀ m : ℕ, 1 ≤ m →
    |∫ S, (risk f D (A m S) - empRisk f S (A m S)) ∂(sampleLaw D m)| ≤ ε m

/-- Definition 29 (p. 2665): `A` is LOO stable with rate `ε` under `D` if, for every sample
size `m = n + 1 ≥ 2`,
`(1/m) ∑_{i=1}^m E_{S∼D^m}[|f(A(S^{\i}); z_i) − f(A(S); z_i)|] ≤ ε(m)`,
where `S^{\i} = Fin.removeNth i S` is the sample `S` with the instance `z_i` removed (a
sample of size `n`, to which the rule is applied at size `n`). The absolute value is inside
the expectation. Sizes `m ≤ 1` are not constrained, since a rule acts on samples of size
at least `1` (p. 2637). -/
def LOOStable (f : H → Z → ℝ) (A : Rule H Z) (D : Measure Z) (ε : ℕ → ℝ) : Prop :=
  ∀ n : ℕ, 1 ≤ n →
    (∑ i : Fin (n + 1),
        ∫ S, |f (A n (Fin.removeNth i S)) (S i) - f (A (n + 1) S) (S i)|
          ∂(sampleLaw D (n + 1))) / (n + 1) ≤ ε (n + 1)

/-- `A` is universally LOO stable with rate `ε`: LOO stable with the same rate `ε` under every
probability distribution `D` on `Z` (Definition 29 and p. 2667). -/
def UniversallyLOOStable (f : H → Z → ℝ) (A : Rule H Z) (ε : ℕ → ℝ) : Prop :=
  ∀ D : Measure Z, IsProbabilityMeasure D → LOOStable f A D ε

end LearnStability.ERMLOO


