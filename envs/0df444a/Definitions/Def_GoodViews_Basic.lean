-- Prove2me | Definitions.Def_GoodViews_Basic
-- name    : GoodViews_Basic
-- status  : Definition
-- author  : @Xeroth
-- created : 2026-11-24T05:38:14.635707+00:00
-- url     : https://prove2.me/theorems/e6b70681-1992-4bad-be4b-4efa53f36308
-- title:
--   Mutual information, minimal sufficient encoders and InfoMin optimal views
-- statement:
--   Objects of Section 3 and Appendix A of Tian, Sun, Poole, Krishnan, Schmid and Isola (2020), for finitely-valued random variables.
--
--   1. **Probability space.** All random variables are functions on one finite sample space $\Omega$ carrying a probability mass function $P$ ($P(\omega)\ge0$, $\sum_\omega P(\omega)=1$). The law of $A:\Omega\to\alpha$ is $P(A=a)=\sum_{\omega:A(\omega)=a}P(\omega)$.
--   2. **Entropy and mutual information.** $H(A)=-\sum_a P(A=a)\log P(A=a)$ with $0\log0=0$; $I(A;B)=H(A)+H(B)-H(A,B)$; $I(A;B\mid C)=H(A,C)+H(B,C)-H(A,B,C)-H(C)$.
--   3. **Data, label, views, representations.** The data is $x:\Omega\to X$ and the task label is $y:\Omega\to Y$. Views are created from the data, $v_1=g_1(x)$ and $v_2=g_2(x)$ with $g_i:X\to V_i$. Representations are $z_1=f_1(v_1)$ and $z_2=f_2(v_2)$ for encoders $f_i:V_i\to Z_i$.
--   4. **Definition 1 (sufficient encoder).** $f_1$ is sufficient if $I(v_1;v_2)=I(f_1(v_1);v_2)$. Symmetrically, $f_2$ is sufficient if $I(v_2;v_1)=I(f_2(v_2);v_1)$.
--   5. **Definition 2 (minimal sufficient encoder).** A sufficient $f_1$ is minimal if $I(f_1(v_1);v_1)\le I(f(v_1);v_1)$ for every sufficient encoder $f$ of $v_1$ into any finite set.
--   6. **Sufficient and minimal sufficient statistics.** $f(v)$ is a sufficient statistic of $v$ for $y$ if $I(f(v);y)=I(v;y)$. It is minimal if moreover $I(f(v);v)\le I(t(v);v)$ for every sufficient statistic $t(v)$ of $v$ for $y$, with $t$ into any finite set.
--   7. **Definition 3 (optimal representation of a task).** $e(x)$ is optimal for predicting $y$ from $x$ if it is a minimal sufficient statistic of $x$ for $y$.
--   8. **InfoMin views (Proposition 3.1).** $(g_1,g_2)$ is feasible if $I(g_1(x);y)=I(g_2(x);y)=I(x;y)$. It is optimal if it is feasible and minimises $I(g_1(x);g_2(x))$ over all feasible pairs $g_1':X\to V_1$, $g_2':X\to V_2$.
--
--   **Formalization Note** The paper does not fix the class of random variables. Here every variable takes finitely many values, views are deterministic functions of $x$ into given finite view spaces $V_1,V_2$ (the proof of Proposition A.1 uses that $v_1,v_2$ are functions of $x$), and representations are deterministic functions of the views. Logarithms are natural; the base does not affect any statement.
-- source:
--   Tian, Sun, Poole, Krishnan, Schmid and Isola, What Makes for Good Views for Contrastive Learning?, arXiv:2005.10243v3 (2020), Section 3.1 (Definitions 1-3, p. 3), Section 3.2 (Proposition 3.1, p. 4), Appendix A.1-A.2 (pp. 15-16)

import Mathlib

/-!
Tian, Sun, Poole, Krishnan, Schmid and Isola, *What Makes for Good Views for Contrastive
Learning?*, arXiv:2005.10243v3 (2020): Shannon (conditional) mutual information of finitely-valued
random variables, sufficient and minimal sufficient encoders (Section 3.1, Definitions 1-3), and
the InfoMin optimal views of Proposition 3.1 (Section 3.2) with the notions used in its proof
(Appendix A).

All random variables live on one finite probability space `S` with probability weights `P`.
-/

noncomputable section

namespace GoodViews

/-- The standing probabilistic setting: `P` is a probability mass function on the finite sample
space `S` (`P ω ≥ 0`, `∑ ω, P ω = 1`). -/
def IsPMF {S : Type} [Fintype S] (P : S → ℝ) : Prop :=
  (∀ ω, 0 ≤ P ω) ∧ ∑ ω, P ω = 1

open Classical in
/-- The law of the random variable `A`: `P(A = a)`. -/
def law {S α : Type} [Fintype S] (P : S → ℝ) (A : S → α) (a : α) : ℝ :=
  ∑ ω ∈ Finset.univ.filter (fun ω => A ω = a), P ω

/-- Shannon entropy (natural logarithm) `H(A) = -∑_a P(A = a) log P(A = a)`, with
`0 log 0 = 0`, as in Cover and Thomas, cited in Appendix A.1. -/
def entropy {S α : Type} [Fintype S] [Fintype α] (P : S → ℝ) (A : S → α) : ℝ :=
  ∑ a, Real.negMulLog (law P A a)

/-- Mutual information `I(A; B) = H(A) + H(B) - H(A, B)` (Section 3.1; Appendix A.1). -/
def mutualInfo {S α β : Type} [Fintype S] [Fintype α] [Fintype β] (P : S → ℝ) (A : S → α)
    (B : S → β) : ℝ :=
  entropy P A + entropy P B - entropy P (fun ω => (A ω, B ω))

/-- Conditional mutual information
`I(A; B | C) = H(A, C) + H(B, C) - H(A, B, C) - H(C)` (Appendix A.1). -/
def condMutualInfo {S α β γ : Type} [Fintype S] [Fintype α] [Fintype β] [Fintype γ]
    (P : S → ℝ) (A : S → α) (B : S → β) (C : S → γ) : ℝ :=
  entropy P (fun ω => (A ω, C ω)) + entropy P (fun ω => (B ω, C ω)) -
    entropy P (fun ω => (A ω, B ω, C ω)) - entropy P C

/-- Definition 1 (Sufficient Encoder), Section 3.1: the encoder `f` of the view `v₁` is
sufficient for the contrastive task between `v₁` and `v₂` iff `I(v₁; v₂) = I(f(v₁); v₂)`.
(The encoder of the second view is sufficient iff it is sufficient with the roles of the views
exchanged.) -/
def IsSufficientEncoder {S V₁ V₂ Z : Type} [Fintype S] [Fintype V₁] [Fintype V₂] [Fintype Z]
    (P : S → ℝ) (v₁ : S → V₁) (v₂ : S → V₂) (f : V₁ → Z) : Prop :=
  mutualInfo P v₁ v₂ = mutualInfo P (f ∘ v₁) v₂

/-- Definition 2 (Minimal Sufficient Encoder), Section 3.1: a sufficient encoder `f` of `v₁` is
minimal iff `I(f(v₁); v₁) ≤ I(f'(v₁); v₁)` for every sufficient encoder `f'` of `v₁` (with any
finite codomain). -/
def IsMinimalSufficientEncoder {S V₁ V₂ Z : Type} [Fintype S] [Fintype V₁] [Fintype V₂]
    [Fintype Z] (P : S → ℝ) (v₁ : S → V₁) (v₂ : S → V₂) (f : V₁ → Z) : Prop :=
  IsSufficientEncoder P v₁ v₂ f ∧
    ∀ (W : Type) [Fintype W] (f' : V₁ → W), IsSufficientEncoder P v₁ v₂ f' →
      mutualInfo P (f ∘ v₁) v₁ ≤ mutualInfo P (f' ∘ v₁) v₁

/-- Appendix A, Proposition A.2: the representation `f(v)` is a sufficient statistic of `v` for
the label `y`, i.e. `I(f(v); y) = I(v; y)`. -/
def IsSufficientStat {S V Y Z : Type} [Fintype S] [Fintype V] [Fintype Y] [Fintype Z]
    (P : S → ℝ) (v : S → V) (y : S → Y) (f : V → Z) : Prop :=
  mutualInfo P (f ∘ v) y = mutualInfo P v y

/-- Definition 3 and Appendix A, Proposition A.3: `f(v)` is a minimal sufficient statistic of `v`
for `y`: it is sufficient, and `I(f(v); v) ≤ I(t(v); v)` for every sufficient statistic `t(v)` of
`v` for `y` (with any finite codomain), the information form of minimality used in the proof of
Proposition A.3. -/
def IsMinimalSufficientStat {S V Y Z : Type} [Fintype S] [Fintype V] [Fintype Y] [Fintype Z]
    (P : S → ℝ) (v : S → V) (y : S → Y) (f : V → Z) : Prop :=
  IsSufficientStat P v y f ∧
    ∀ (W : Type) [Fintype W] (t : V → W), IsSufficientStat P v y t →
      mutualInfo P (f ∘ v) v ≤ mutualInfo P (t ∘ v) v

/-- Definition 3 (Optimal Representation of a Task), Section 3.1: for the task of predicting the
label `y` from the data `x`, the representation `e(x)` is optimal iff it is a minimal sufficient
statistic of `x` for `y`. -/
def IsOptimalRep {S X Y Z : Type} [Fintype S] [Fintype X] [Fintype Y] [Fintype Z]
    (P : S → ℝ) (x : S → X) (y : S → Y) (e : X → Z) : Prop :=
  IsMinimalSufficientStat P x y e

/-- The constraint of Proposition 3.1 (Section 3.2): the views `v₁ = g₁(x)`, `v₂ = g₂(x)`
created from the data `x` keep all task information, `I(v₁; y) = I(v₂; y) = I(x; y)`. -/
def IsFeasibleViews {S X Y V₁ V₂ : Type} [Fintype S] [Fintype X] [Fintype Y] [Fintype V₁]
    [Fintype V₂] (P : S → ℝ) (x : S → X) (y : S → Y) (g₁ : X → V₁) (g₂ : X → V₂) : Prop :=
  mutualInfo P (g₁ ∘ x) y = mutualInfo P x y ∧ mutualInfo P (g₂ ∘ x) y = mutualInfo P x y

/-- Proposition 3.1 (Section 3.2), the InfoMin optimal views: `(v₁*, v₂*) = (g₁(x), g₂(x))`
minimises `I(v₁; v₂)` over all views `g₁' : X → V₁`, `g₂' : X → V₂` of the data subject to
`I(v₁; y) = I(v₂; y) = I(x; y)`. -/
def IsOptimalViews {S X Y V₁ V₂ : Type} [Fintype S] [Fintype X] [Fintype Y] [Fintype V₁]
    [Fintype V₂] (P : S → ℝ) (x : S → X) (y : S → Y) (g₁ : X → V₁) (g₂ : X → V₂) : Prop :=
  IsFeasibleViews P x y g₁ g₂ ∧
    ∀ (g₁' : X → V₁) (g₂' : X → V₂), IsFeasibleViews P x y g₁' g₂' →
      mutualInfo P (g₁ ∘ x) (g₂ ∘ x) ≤ mutualInfo P (g₁' ∘ x) (g₂' ∘ x)

end GoodViews


