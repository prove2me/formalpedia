-- Prove2me | Definitions.Def_MultiphaseDisj_FiniteInfo
-- name    : MultiphaseDisj_FiniteInfo
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:27:44.027306+00:00
-- url     : https://prove2.me/theorems/aade5b89-fbfb-4829-9b5e-666679f76ea4
-- title:
--   Finite probability spaces: entropy, conditional mutual information and min-entropy in bits
-- statement:
--   All random variables of the mission live on a finite sample space $\Omega$ with point masses $P(\omega)$. For an event $E$, $\Pr[E]=\sum_{\omega\in E}P(\omega)$, and the space **conditioned on** $E$ has masses $P(\omega)/\Pr[E]$ on $E$ and $0$ elsewhere. The law of a random variable $X$ is $a\mapsto\Pr[X=a]$. Logarithms are base $2$.
--
--   1. **Entropy** $H(X)=\sum_x\Pr[X=x]\log\frac1{\Pr[X=x]}$, summed over the values of $X$.
--   2. **Conditional entropy** $H(X\mid Y)=\mathbb E_{y\sim Y}\big[H(X\mid Y=y)\big]$.
--   3. **Conditional mutual information** $I(X;Y\mid Z)=H(X\mid Z)-H(X\mid Y,Z)$, and $I(X;Y)$ is the unconditional version.
--   4. **Min-entropy** of a distribution $\nu$ on a finite set, $H_\infty(\nu)=-\log\max_a\nu(a)$; for a random variable, $H_\infty(A)$ is the min-entropy of its law.
--
--   The module also defines the product $\nu_1\otimes\nu_2$ of two distributions, the two marginals of a distribution on a product, the uniform distribution $U_A$ on a finite set $A$, the predicate "$\mu$ is a distribution (on $F$)", and the number of values a random variable takes on the support of $P$: a message of length $\lambda$ bits takes at most $2^\lambda$ values.
--
--   **Formalization Note** Masses are real numbers. Conditioning on an event of probability $0$ gives the all-zero masses; every statement of the mission conditions only on events of positive probability. Values of probability $0$ contribute $0$ to every entropy.
-- source:
--   Ko, Unconditional Boolean Dynamic Lower Bounds from Disjointness, arXiv:2610.10904 (held version, sha256 ba26649b…), Definition 2.1, pp.11–12; §2.3 Min-entropy, p.13; §3.2, p.17 (message lengths)

import Mathlib

set_option autoImplicit false

noncomputable section

open Classical

namespace MultiphaseDisj

/-- A probability distribution on a finite type, given by its point masses (Ko,
*Unconditional Boolean Dynamic Lower Bounds from Disjointness*, arXiv:2610.10904, held version
sha256 ba26649b…, §2.2, pp.11–12). -/
def IsDist {β : Type*} [Fintype β] (μ : β → ℝ) : Prop :=
  (∀ b, 0 ≤ μ b) ∧ ∑ b, μ b = 1

/-- A probability distribution on a finite type supported on the finite set `F`
("a distribution on `F`"). -/
def IsDistOn {β : Type*} [Fintype β] (F : Finset β) (μ : β → ℝ) : Prop :=
  IsDist μ ∧ ∀ b, b ∉ F → μ b = 0

section RV

variable {Ω : Type*} [Fintype Ω]

/-- The probability of an event `E` under the point masses `P` of a finite sample space. -/
def pr (P : Ω → ℝ) (E : Ω → Prop) : ℝ :=
  ∑ ω, if E ω then P ω else 0

/-- The sample space conditioned on the event `E` (§2.2, p.12, "X|E"): masses
`P ω / Pr[E]` on `E` and `0` off `E`.

**Formalization Note** Every statement of the mission conditions only on events of positive
probability; on an event of probability `0` the masses are all `0`. -/
def cond (P : Ω → ℝ) (E : Ω → Prop) : Ω → ℝ :=
  fun ω => if E ω then P ω / pr P E else 0

/-- The expectation `E[f] = Σ_ω P(ω) f(ω)`. -/
def expect (P : Ω → ℝ) (f : Ω → ℝ) : ℝ :=
  ∑ ω, P ω * f ω

/-- The law (distribution) of the random variable `X`: `a ↦ Pr[X = a]`. -/
def law {α : Type*} (P : Ω → ℝ) (X : Ω → α) : α → ℝ :=
  fun a => pr P (fun ω => X ω = a)

/-- **Entropy** in bits (Definition 2.1, p.11): `H(X) = Σ_x Pr[X = x] log₂ (1 / Pr[X = x])`, the
sum over the values of `X`; values of probability `0` contribute `0`. -/
def entropy {α : Type*} (P : Ω → ℝ) (X : Ω → α) : ℝ :=
  ∑ a ∈ Finset.univ.image X, Real.negMulLog (law P X a) / Real.log 2

/-- **Conditional entropy** (Definition 2.1, p.11): `H(X|Y) = E_{y∼Y}[H(X | Y = y)]`. -/
def condEntropy {α γ : Type*} (P : Ω → ℝ) (X : Ω → α) (Y : Ω → γ) : ℝ :=
  ∑ y ∈ Finset.univ.image Y, law P Y y * entropy (cond P (fun ω => Y ω = y)) X

/-- **Conditional mutual information** (Definition 2.1, p.11):
`I(X; Y | Z) = H(X | Z) − H(X | Y, Z)`, in bits. -/
def condMI {α β γ : Type*} (P : Ω → ℝ) (X : Ω → α) (Y : Ω → β) (Z : Ω → γ) : ℝ :=
  condEntropy P X Z - condEntropy P X (fun ω => (Y ω, Z ω))

/-- **Mutual information** `I(X; Y) = I(X; Y | const)`, in bits (Definition 2.1, p.11). -/
def mutualInfo {α β : Type*} (P : Ω → ℝ) (X : Ω → α) (Y : Ω → β) : ℝ :=
  condMI P X Y (fun _ => ())

end RV

/-- **Min-entropy** of a distribution `ν` on a finite type, in bits (§2.3, p.13):
`H∞(ν) = −log₂ max_a ν(a)`. The min-entropy `H∞(A)` of a random variable `A` is that of its law,
`minEntropy (law P A)`. -/
def minEntropy {β : Type*} [Fintype β] (ν : β → ℝ) : ℝ :=
  -Real.logb 2 (⨆ b, ν b)

/-- The product `ν₁ ⊗ ν₂` of two distributions. -/
def prodDist {α β : Type*} (ν₁ : α → ℝ) (ν₂ : β → ℝ) : α × β → ℝ :=
  fun p => ν₁ p.1 * ν₂ p.2

/-- The first marginal `μ_A` of a distribution `μ` on a product. -/
def marg1 {α β : Type*} [Fintype β] (μ : α × β → ℝ) : α → ℝ :=
  fun a => ∑ b, μ (a, b)

/-- The second marginal `μ_B` of a distribution `μ` on a product. -/
def marg2 {α β : Type*} [Fintype α] (μ : α × β → ℝ) : β → ℝ :=
  fun b => ∑ a, μ (a, b)

/-- The uniform distribution `U_A` on a finite set `A` (§2.3, p.13). -/
def unif {β : Type*} (A : Finset β) : β → ℝ :=
  fun b => if b ∈ A then 1 / (A.card : ℝ) else 0

/-- The number of values that `f` takes on the support of `P`. A message of length `λ` bits
takes at most `2 ^ λ` values (§3.2, p.17), so "`|f| ≤ λ`" is encoded as
`(supportRangeCard P f : ℝ) ≤ 2 ^ λ`. -/
def supportRangeCard {Ω α : Type*} [Fintype Ω] (P : Ω → ℝ) (f : Ω → α) : ℕ :=
  ((Finset.univ.filter (fun ω => P ω ≠ 0)).image f).card

end MultiphaseDisj


