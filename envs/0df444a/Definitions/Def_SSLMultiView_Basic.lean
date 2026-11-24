-- Prove2me | Definitions.Def_SSLMultiView_Basic
-- name    : SSLMultiView_Basic
-- status  : Definition
-- author  : @Xeroth
-- created : 2026-11-24T17:53:42.936376+00:00
-- url     : https://prove2.me/theorems/a9eea650-02da-4625-a28d-50a8c430a311
-- title:
--   Finite-alphabet information quantities, multi-view assumption and self-supervised representations
-- statement:
--   Objects of Section 2 of Tsai, Wu, Salakhutdinov and Morency (ICLR 2021), in the setting of finite alphabets.
--
--   1. **Probability space.** The input $X$, the self-supervised signal $S$ and the task-relevant variable $T$ take values in finite sets $\mathcal X,\mathcal S,\mathcal T$ and have a joint probability mass function $P$ on $\mathcal X\times\mathcal S\times\mathcal T$ ($P\ge0$, $\sum P=1$). The law of a random variable $f$ is $P(f=a)$.
--   2. **Information quantities (nats).** $H(f)=-\sum_a P(f=a)\log P(f=a)$, $H(f\mid g)=H(f,g)-H(g)$, $I(f;g)=H(f)+H(g)-H(f,g)$ and $I(f;g\mid h)=H(f,h)+H(g,h)-H(f,g,h)-H(h)$. Conditional independence $f\perp g\mid h$ means $P(h=c)P(f=a,g=b,h=c)=P(f=a,h=c)P(g=b,h=c)$ for all $a,b,c$.
--   3. **Representations.** A representation is $Z_X=F_X(X)$ for a deterministic map $F_X:\mathcal X\to\mathcal Z$ into a finite representation space $\mathcal Z$.
--   4. **Assumption 1 (multi-view).** $\epsilon_{\rm info}>0$ and $I(X;T\mid S)\le\epsilon_{\rm info}$.
--   5. **Definition 1.** $Z_X^{\rm sup}$ maximizes $I(Z_X;T)$ over all maps $F_X:\mathcal X\to\mathcal Z$. $Z_X^{\rm sup_{min}}$ minimizes $H(Z_X\mid T)$ among the maximizers of $I(Z_X;T)$.
--   6. **Definition 2.** $Z_X^{\rm ssl}$ maximizes $I(Z_X;S)$ over all maps $F_X:\mathcal X\to\mathcal Z$. $Z_X^{\rm ssl_{min}}$ minimizes $H(Z_X\mid S)$ among the maximizers of $I(Z_X;S)$.
--   7. **Bayes error rate (Section 2.4).** $P_e=\mathbb E_{z\sim P_{Z_X}}\big[1-\max_{t}P(T=t\mid Z_X=z)\big]=1-\sum_z\max_t P(Z_X=z,T=t)$. The thresholding function is ${\rm Th}(x)=\min\{\max\{x,0\},1-1/|\mathcal T|\}$.
--
--   **Formalization Note** The paper does not fix the alphabets. Finite alphabets are used because the proofs rely on facts that hold for Shannon entropy of discrete variables, such as $H(Z_X\mid X)=0$ for a deterministic $Z_X$. The paper writes the Bayes error with $P(\hat T=t\mid z_x)$. It is formalized with $P(T=t\mid z_x)$, the Bayes (maximum a posteriori) error to which the Feder–Merhav and Fano inequalities in the proofs apply. The optimization in Definitions 1 and 2 ranges over all deterministic maps into the fixed space $\mathcal Z$.
-- source:
--   Tsai, Wu, Salakhutdinov and Morency, Self-supervised Learning from a Multi-view Perspective, ICLR 2021, arXiv:2006.05576v4, Section 2 (Notations), Section 2.1 (Assumption 1), Section 2.2 (Definitions 1 and 2), Section 2.4 (Bayes error rate, Th), Appendix B (Lemma 1), pp. 2-6, 12

import Mathlib

/-!
Tsai, Wu, Salakhutdinov and Morency, *Self-supervised Learning from a Multi-view Perspective*,
ICLR 2021, arXiv:2006.05576v4: the information quantities, the multi-view assumption, the
supervised and self-supervised representations and the Bayes error rate of Section 2
(Notations, Assumption 1, Definitions 1 and 2, Section 2.4).

The input `X`, the self-supervised signal `S` and the task variable `T` take values in finite
sets, with joint probability mass function `P` on `X × S × T`; entropies are Shannon entropies
in nats. A representation is `Z_X = F_X(X)` for a deterministic map `F_X : X → Zs` into a
finite representation space `Zs`.
-/

noncomputable section

namespace SSLMultiView

section General

variable {Ω : Type*} [Fintype Ω]

/-- Section 2, Notations: `P` is a probability mass function on the finite sample space `Ω`. -/
def IsPMF (P : Ω → ℝ) : Prop :=
  (∀ ω, 0 ≤ P ω) ∧ ∑ ω, P ω = 1

/-- Section 2, Notations: the law `P(f = a)` of a random variable `f` on `Ω`. -/
def law {α : Type*} [DecidableEq α] (P : Ω → ℝ) (f : Ω → α) (a : α) : ℝ :=
  ∑ ω ∈ Finset.univ.filter (fun ω => f ω = a), P ω

/-- Section 2, Notations: the Shannon entropy `H(f) = -∑_a P(f = a) log P(f = a)` (nats). -/
def entropy {α : Type*} [Fintype α] [DecidableEq α] (P : Ω → ℝ) (f : Ω → α) : ℝ :=
  ∑ a, Real.negMulLog (law P f a)

/-- Section 2, Notations: the conditional entropy `H(f | g) = H(f, g) - H(g)`. -/
def condEntropy {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (P : Ω → ℝ) (f : Ω → α) (g : Ω → β) : ℝ :=
  entropy P (fun ω => (f ω, g ω)) - entropy P g

/-- Section 2, Notations: the mutual information `I(f; g) = H(f) + H(g) - H(f, g)`. -/
def mutualInfo {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (P : Ω → ℝ) (f : Ω → α) (g : Ω → β) : ℝ :=
  entropy P f + entropy P g - entropy P (fun ω => (f ω, g ω))

/-- Section 2, Notations: the conditional mutual information
`I(f; g | h) = H(f, h) + H(g, h) - H(f, g, h) - H(h)`. -/
def condMutualInfo {α β γ : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    [Fintype γ] [DecidableEq γ] (P : Ω → ℝ) (f : Ω → α) (g : Ω → β) (h : Ω → γ) : ℝ :=
  entropy P (fun ω => (f ω, h ω)) + entropy P (fun ω => (g ω, h ω)) -
    entropy P (fun ω => (f ω, g ω, h ω)) - entropy P h

/-- Appendix B, Lemma 1: conditional independence `f ⊥ g | h`, in the form
`P(h = c) P(f = a, g = b, h = c) = P(f = a, h = c) P(g = b, h = c)`. -/
def CondIndep {α β γ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (P : Ω → ℝ) (f : Ω → α) (g : Ω → β) (h : Ω → γ) : Prop :=
  ∀ a b c, law P h c * law P (fun ω => (f ω, g ω, h ω)) (a, b, c) =
    law P (fun ω => (f ω, h ω)) (a, c) * law P (fun ω => (g ω, h ω)) (b, c)

/-- Section 2.4: the Bayes error rate of predicting `g` from `f`,
`P_e = E_{z ∼ P_f}[1 - max_t P(g = t | f = z)] = 1 - ∑_z max_t P(f = z, g = t)`. -/
def bayesError {α β : Type*} [Fintype α] [DecidableEq α] [DecidableEq β]
    (P : Ω → ℝ) (f : Ω → α) (g : Ω → β) : ℝ :=
  1 - ∑ a, ⨆ b, law P (fun ω => (f ω, g ω)) (a, b)

end General

/-- Section 2.4: the thresholding function `Th(x) = min {max {x, 0}, 1 - 1/|T|}`, with `m = |T|`. -/
def thresh (m : ℕ) (x : ℝ) : ℝ :=
  min (max x 0) (1 - 1 / (m : ℝ))

section Views

variable {X S T : Type*}

/-- Section 2, Notations: the input `X` as a random variable on `X × S × T`. -/
def inputX : X × S × T → X := fun ω => ω.1

/-- Section 2, Notations: the self-supervised signal `S` as a random variable on `X × S × T`. -/
def signalS : X × S × T → S := fun ω => ω.2.1

/-- Section 2, Notations: the task-relevant variable `T` as a random variable on `X × S × T`. -/
def taskT : X × S × T → T := fun ω => ω.2.2

/-- Section 2.2, Theorem 2: the pair `(S, T)` as a random variable on `X × S × T`. -/
def signalTask : X × S × T → S × T := fun ω => ω.2

/-- Section 2, Notations: the representation `Z_X = F_X(X)` of a deterministic map `F_X`. -/
def rep {Zs : Type*} (F : X → Zs) : X × S × T → Zs := fun ω => F ω.1

variable [Fintype X] [DecidableEq X] [Fintype S] [DecidableEq S] [Fintype T] [DecidableEq T]

/-- Section 2.1, Assumption 1 (multi-view): `ε_info > 0` and `I(X; T | S) ≤ ε_info`. -/
def MultiViewAssumption (P : X × S × T → ℝ) (ε : ℝ) : Prop :=
  0 < ε ∧ condMutualInfo P inputX taskT signalS ≤ ε

variable {Zs : Type*} [Fintype Zs] [DecidableEq Zs]

/-- Section 2.2, Definition 1: `Z_X^sup = F(X)` maximizes `I(Z_X; T)` over all deterministic
maps `X → Zs`. -/
def IsSupRep (P : X × S × T → ℝ) (F : X → Zs) : Prop :=
  ∀ F' : X → Zs, mutualInfo P (rep F') taskT ≤ mutualInfo P (rep F) taskT

/-- Section 2.2, Definition 1: `Z_X^supmin = F(X)` minimizes `H(Z_X | T)` subject to
`I(Z_X; T)` being maximized. -/
def IsSupMinRep (P : X × S × T → ℝ) (F : X → Zs) : Prop :=
  IsSupRep P F ∧
    ∀ F' : X → Zs, IsSupRep P F' → condEntropy P (rep F) taskT ≤ condEntropy P (rep F') taskT

/-- Section 2.2, Definition 2: `Z_X^ssl = F(X)` maximizes `I(Z_X; S)` over all deterministic
maps `X → Zs`. -/
def IsSslRep (P : X × S × T → ℝ) (F : X → Zs) : Prop :=
  ∀ F' : X → Zs, mutualInfo P (rep F') signalS ≤ mutualInfo P (rep F) signalS

/-- Section 2.2, Definition 2: `Z_X^sslmin = F(X)` minimizes `H(Z_X | S)` subject to
`I(Z_X; S)` being maximized. -/
def IsSslMinRep (P : X × S × T → ℝ) (F : X → Zs) : Prop :=
  IsSslRep P F ∧
    ∀ F' : X → Zs, IsSslRep P F' → condEntropy P (rep F) signalS ≤ condEntropy P (rep F') signalS

end Views

end SSLMultiView


