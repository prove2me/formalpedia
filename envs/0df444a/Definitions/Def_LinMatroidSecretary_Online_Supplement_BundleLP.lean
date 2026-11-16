-- Prove2me | Definitions.Def_LinMatroidSecretary_Online_Supplement_BundleLP
-- name    : LinMatroidSecretary_Online_Supplement_BundleLP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T20:03:11.505235+00:00
-- url     : https://prove2.me/theorems/ad380312-d699-4d91-85b5-44a1105b5e88
-- title:
--   Randomized bundle selection and the allocation LP (19), (22a)–(22e)
-- statement:
--   Work in $V=F^d$ with a labelled vector family $v:E\to V$. The span $\langle B\rangle$ is the span of the vectors indexed by a finite bundle $B$; different labels remain different items. Reuse the published finitely supported subspace distributions $\nu$, their expectations, and the dimension invariant. The real-parameter condition (19) is
--   $$\mathbb E_{W\sim\nu}\dim(W\cap L)\le(1-\alpha)\dim L\quad(L\le V).$$
--   A selection rule $\rho(W,T)$ describes, after observing $W$, the conditional probability of choosing $T\subseteq B$. Validity requires nonnegative entries summing to one on $B$'s powerset for each $W$ in the support of $\nu$, and zero probability unless $\dim(W+\langle T\rangle)=\dim W+|T|$. Its marginal for $e$ and its expectation of a function $g$ are
--   $$\Pr[e\in T]=\sum_W\nu(W)\sum_{T\subseteq B:e\in T}\rho(W,T),\qquad \mathbb E[g(W,T)]=\sum_W\nu(W)\sum_{T\subseteq B}\rho(W,T)g(W,T).$$
--   For agents $N=\{0,\ldots,n-1\}$, let $X\subseteq N$, $i=|X|$, eligibility sets $E_a$, bundles $B_a$, sample size $k$, and predecessor laws $\mu_a$. Set $V_X=\langle\bigcup_{a\in X}E_a\rangle$. The LP uses one rule $p(a,W,T)$ per $a\in X$, with variables only for $W\in\operatorname{supp}\mu_a$ and $T\subseteq B_a$. It imposes all five families:
--   1. Nonnegativity of every variable.
--   2. $\sum_{T\subseteq B_a}p(a,W,T)=1$.
--   3. $p(a,W,T)=0$ unless $\dim(W+\langle T\rangle)=\dim W+|T|$.
--   4. Each $e\in B_a$ has marginal $k/(i-1)$.
--   5. For every $L\le V_X$, $g_p(L)\le0$, where
--   $$g_p(L)=-(i-k)\dim L+\sum_{a\in X}\sum_W\mu_a(W)\sum_{T\subseteq B_a}p(a,W,T)\dim((W+\langle T\rangle)\cap L).$$
--
--   Unused coordinates outside these variable ranges are unconstrained and never enter the formulas. Uses of $k/(i-1)$ in Lemma 7 assume $1\le k<i$, so the denominator is positive. These definitions supply the shared interfaces for Lemmas 6, 9 and 7 without assuming their conclusions.
-- source:
--   Kristóf Bérczi, Shaddin Dughmi, Vasilis Livanos, Jose Soto, Victor Verdugo, The Strong Secretary Conjecture is True for Linear Matroids, STOC 2027 submission #608 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/608.pdf, §§5.1–5.3, (19), (22a)–(22e), PDF pp. 22–27 (printed pp. 20–25)

import Mathlib
import Definitions.Def_LinMatroidSecretary_Online_DimensionLP

/-!
§5.1–§5.3 (PDF pp. 22–27): randomized subset rules and LP_XOS, (19), (22a)–(22e).
Subsets are sets of labels: equal vectors do not identify distinct elements.
-/
namespace LinMatroidSecretary.Online.Supplement

open Finset
noncomputable section

variable {F : Type} [Field F] {d : ℕ}
variable {E : Type} [DecidableEq E]

/-- Span of a finite set of labelled vectors, with no order on the labels. -/
def bundleSpan (v : E → Fin d → F) (B : Finset E) : Submodule F (Fin d → F) :=
  Submodule.span F (v '' (B : Set E))

/-- The real-parameter dimension inequality (19), for every ambient subspace. -/
def DimIneqAlpha (ν : Dist F d) (α : ℝ) : Prop :=
  ∀ L : Submodule F (Fin d → F),
    expect ν (fun W => dimInter W L) ≤ (1 - α) * (Module.finrank F L : ℝ)

/-- Conditional probabilities after observing `W`; only subsets of the fixed bundle are used. -/
abbrev SelectionRule (F : Type) [Field F] (d : ℕ) (E : Type) :=
  Submodule F (Fin d → F) → Finset E → ℝ

/-- For every positive-mass subspace, a distribution on subsets independent modulo `W`.
Values off `B.powerset` or off `ν.support` do not participate in the experiment. -/
def SelectionValid (v : E → Fin d → F) (ν : Dist F d) (B : Finset E)
    (ρ : SelectionRule F d E) : Prop :=
  ∀ W ∈ ν.support,
    (∀ T ∈ B.powerset, 0 ≤ ρ W T) ∧
    (∑ T ∈ B.powerset, ρ W T) = 1 ∧
    (∀ T ∈ B.powerset,
      Module.finrank F ↥(W ⊔ bundleSpan v T) ≠ Module.finrank F ↥W + T.card → ρ W T = 0)

/-- Marginal inclusion probability, averaged over `W` and the conditional subset rule. -/
def selectionMarginal (ν : Dist F d) (B : Finset E) (ρ : SelectionRule F d E) (e : E) : ℝ := by
  classical
  exact expect ν fun W => ∑ T ∈ B.powerset, if e ∈ T then ρ W T else 0

/-- Expectation of a function of the observed subspace and selected bundle. -/
def selectionExpect (ν : Dist F d) (B : Finset E) (ρ : SelectionRule F d E)
    (g : Submodule F (Fin d → F) → Finset E → ℝ) : ℝ :=
  expect ν fun W => ∑ T ∈ B.powerset, ρ W T * g W T

variable {n : ℕ}

/-- `V_X`, the span of the eligibility sets of `X`, not merely its allocated bundles. -/
def eligibilitySpan (v : E → Fin d → F) (elig : Fin n → Finset E)
    (X : Finset (Fin n)) : Submodule F (Fin d → F) :=
  bundleSpan v (X.biUnion elig)

/-- Expanded `g_p` preceding (22), with no extra factor `1/i` in the sum over agents. -/
def bundleGp (v : E → Fin d → F) (X : Finset (Fin n)) (k : ℕ)
    (B : Fin n → Finset E) (μ : Fin n → Dist F d)
    (p : Fin n → SelectionRule F d E) (L : Submodule F (Fin d → F)) : ℝ :=
  -((X.card : ℝ) - (k : ℝ)) * (Module.finrank F L : ℝ) +
    ∑ a ∈ X, selectionExpect (μ a) (B a) (p a)
      (fun W T => dimInter (W ⊔ bundleSpan v T) L)

/-- All five constraint families of LP_XOS(X). The variables outside `a ∈ X`,
`W ∈ supp μ_a`, `T ⊆ B_a` are irrelevant unconstrained coordinates. -/
def BundleLPFeasible (v : E → Fin d → F) (elig : Fin n → Finset E)
    (X : Finset (Fin n)) (k : ℕ) (B : Fin n → Finset E)
    (μ : Fin n → Dist F d) (p : Fin n → SelectionRule F d E) : Prop :=
  (∀ a ∈ X, SelectionValid v (μ a) (B a) (p a)) ∧
  (∀ a ∈ X, ∀ e ∈ B a,
    selectionMarginal (μ a) (B a) (p a) e = (k : ℝ) / ((X.card : ℝ) - 1)) ∧
  (∀ L : Submodule F (Fin d → F), L ≤ eligibilitySpan v elig X →
    bundleGp v X k B μ p L ≤ 0)

end
end LinMatroidSecretary.Online.Supplement


