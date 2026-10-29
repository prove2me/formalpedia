-- Prove2me | Definitions.Def_ZhangTangLabelCut_LP2_Configurations
-- name    : ZhangTangLabelCut_LP2_Configurations
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T05:13:41.099999+00:00
-- url     : https://prove2.me/theorems/36c66a47-e3a9-4b95-b6ae-a38d71a01376
-- title:
--   Light elements, configuration events and the analytic union-bound expression
-- statement:
--   Fix a candidate label set $S$ before drawing permutations, write $c=|S|$, $a=c/k$, and let $J_\mu=\{j:(\mu,j)\in S\}$. Its light ground set is $\Phi'(S)=\{\mu:|J_\mu|\le4a\}$, including zero-count elements. Its configuration is $F(S)=\{(\mu,j)\in S:\mu\in\Phi'(S)\}$. The family of configurations is the image of all size-$c$ candidates under $F$, counting distinct sets only.
--
--   A chain-separation event means every simple terminal path confined to that chain is hit by $S$. A good-configuration event means every simple terminal path confined to shutters with both ground elements in $\Phi'(S)$ is hit by $F(S)$. The event retains its originating candidate $S$: equality of two displayed sets $F$ is not assumed to identify their light ground sets.
--
--   Define
--   $$B(a,d)=1-(1-8a/d)^{4a},\quad Q(k,h,a,d)=B(a,d)^{(h/2)(3k/4)(3k/4-1)},$$
--   $$T(k,a,d)=(4a+1)^k d^{(4a+1)k},\qquad z(k,d,h,a)=T(k,a,d)Q(k,h,a,d).$$
--   Every exponent here is real. The analytic specialization substitutes $d=32k^{2\delta}$, $h=k^\beta$, $a=k^\delta$. The real vertex-count expression is
--   $$n(k,\beta,\delta)=2+(96k^{2\delta}-1)k^\beta k(k-1)/2.$$
--   It agrees with the construction's vertex count when the powers give integral graph parameters; it does not construct a graph for arbitrary real powers.
-- source:
--   Zhang and Tang, Minimum Label s-t Cut has Large Integrality Gaps, arXiv:1908.11491v1 (2019), pp. 14–22, Definition 6.1 and equations (6)–(21), (25)

import Definitions.Def_ZhangTangLabelCut_LP2_Shutter

namespace ZhangTangLabelCut.LP2

noncomputable def counts {k d : ℕ} (S : Finset (Fin k × Fin d)) (μ : Fin k) : ℕ := by
  classical
  exact (S.filter (fun l => l.1 = μ)).card

noncomputable def average (k c : ℕ) : ℝ := (c : ℝ) / k

/-- Includes elements with zero labels. The original candidate is retained. -/
noncomputable def light {k d : ℕ} (S : Finset (Fin k × Fin d)) : Finset (Fin k) := by
  classical
  exact Finset.univ.filter (fun μ => (counts S μ : ℝ) ≤ 4 * average k S.card)

noncomputable def configuration {k d : ℕ} (S : Finset (Fin k × Fin d)) : Finset (Fin k × Fin d) := by
  classical
  exact S.filter (fun l => l.1 ∈ light S)

/-- Distinct sets F, rather than their possibly many candidate preimages. -/
noncomputable def configurations (k d c : ℕ) : Finset (Finset (Fin k × Fin d)) := by
  classical
  exact (Finset.univ.filter (fun S : Finset (Fin k × Fin d) => S.card = c)).image configuration

/-- Cut restricted to paths all of whose edges are in a specified subgraph. -/
def CutsOn (I : LabelCut) (allowed : I.graph.E → Prop) (S : Finset I.L) : Prop :=
  ∀ p : Path I.graph I.s I.t, (∀ j, allowed (p.edge j)) →
    ∃ j, I.label (p.edge j) ∈ S

def chainSeparated {k d h : ℕ} (directed : Bool) (S : Finset (Fin k × Fin d))
    (c : Chain k h) (σ : Sample k d h) : Prop :=
  CutsOn (shutterInstance k d h directed σ) (fun e => e.1 = c) S

/-- Goodness refers to F together with the light ground set of its original candidate S. -/
noncomputable def good {k d h : ℕ} (directed : Bool) (S : Finset (Fin k × Fin d))
    (σ : Sample k d h) : Prop :=
  CutsOn (shutterInstance k d h directed σ)
    (fun e => e.1.1.val.1 ∈ light S ∧ e.1.1.val.2 ∈ light S) (configuration S)

noncomputable def chainBound (a d : ℝ) : ℝ := 1 - (1 - 8 * a / d) ^ (4 * a)

noncomputable def configurationBound (k h a d : ℝ) : ℝ :=
  chainBound a d ^ ((h / 2) * (3 * k / 4) * (3 * k / 4 - 1))

noncomputable def countBound (k a d : ℝ) : ℝ := (4 * a + 1) ^ k * d ^ ((4 * a + 1) * k)

/-- Equation (16), with its literal constants and real exponents. -/
noncomputable def z (k d h a : ℝ) : ℝ := countBound k a d * configurationBound k h a d

/-- Equations (17)--(19) and (21), used analytically without pretending real powers are cardinals. -/
noncomputable def analyticZ (k β δ : ℝ) : ℝ := z k (32 * k ^ (2 * δ)) (k ^ β) (k ^ δ)

/-- The real extension of the exact construction size, equal to the vertex count when integral. -/
noncomputable def analyticVertices (k β δ : ℝ) : ℝ :=
  2 + (3 * (32 * k ^ (2 * δ)) - 1) * k ^ β * (k * (k - 1) / 2)

end ZhangTangLabelCut.LP2


