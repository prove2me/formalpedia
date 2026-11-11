-- Prove2me | Definitions.Def_SpanForestStream_Unrestricted_Info
-- name    : SpanForestStream_Unrestricted_Info
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T02:30:54.584362+00:00
-- url     : https://prove2.me/theorems/65cc04c2-2cbd-40af-a57e-d78b5903a6ed
-- title:
--   Discrete entropy, KL divergence and (conditional) mutual information in bits, on countable carriers
-- statement:
--   A **joint law** is a probability mass function $\pi$ on an arbitrary set $\Omega$ (so it has countable support), and a random variable is a function out of $\Omega$; carriers need not be finite, so a message may be a binary string of unbounded length. All quantities are measured in **bits** (binary logarithms) and take values in $[0,\infty]$.
--
--   - $D_{\mathrm{KL}}(p\,\|\,q)=\sum_a p(a)\log_2\frac{p(a)}{q(a)}$, equal to $\infty$ unless $p\ll q$ with a summable log-likelihood ratio (Mathlib's `klDiv` divided by $\ln 2$).
--   - $\pi(\cdot\mid W)$ is $\pi$ conditioned on an event $W$; on an event of probability zero, where conditioning is undefined, the definition returns $\pi$ (every use assumes $\pi(W)>0$ or weights by $\pi(W)=0$).
--   - $I_\pi(A;B)=D_{\mathrm{KL}}\big(\pi[A,B]\,\|\,\pi[A]\otimes\pi[B]\big)$ and $I_\pi(A;B\mid C)=\sum_c \pi(C=c)\, I_{\pi(\cdot\mid C=c)}(A;B)$.
--   - $H(p)=\sum_a -p(a)\log_2 p(a)$.
--   - $\pi[Y\mid X=x]$ is the conditional law, and $\mathbb E_{x\sim\nu[X]} D_{\mathrm{KL}}(\nu[Y\mid x]\,\|\,\mu[Y\mid x])$ is averaged under the first law's marginal.
--   - $A$ and $B$ are conditionally independent given $C$ when $\pi(a,b,c)\,\pi(c)=\pi(a,c)\,\pi(b,c)$ for all values.
--
--   **Formalization Note** These are the paper's information quantities (App. A: all logarithms binary; §4.4 for success-conditioned information). A published finite-carrier version cannot hold Lemma 3.4's unrestricted-length message, and the published `ShuffleDecoys_Hierarchy_Info` measures in nats and has no entropy or conditional information.
-- source:
--   Chao, Cen, Ma, Wang, Space-Optimal Algorithms for Spanning Forests in Dynamic Streams at Every Confidence Level, arXiv:2611.04365 (PDF sha256 00f5bb17…69c92), p. 45 (PDF 48), Appendix A; p. 29 (PDF 32), §4.4

import Mathlib

open scoped ENNReal

namespace SpanForestStream.Unrestricted

noncomputable section

/-!
# Discrete information quantities in bits

Chao, Cen, Ma, Wang, *Space-Optimal Algorithms for Spanning Forests in Dynamic Streams at Every
Confidence Level*, arXiv:2611.04365: App. A, p. 45 ("All logarithms are binary unless written
ln"); §4.4, p. 29 (success-conditioned information).

A joint law is a probability mass function `π : PMF Ω` on an arbitrary type `Ω` (so it is
discrete, with countable support), and a random variable is a function out of `Ω`. Carriers need
not be finite: a message may be an unbounded bit string. All quantities take values in `[0, ∞]`.
-/

/-- Kullback–Leibler divergence `D_KL(p ‖ q)` **in bits**: Mathlib's `InformationTheory.klDiv`
(natural logarithm, value `∞` unless `p ≪ q` with integrable log-likelihood ratio) divided by
`ln 2`, with every subset measurable. -/
def klBits {α : Type} (p q : PMF α) : ℝ≥0∞ :=
  letI : MeasurableSpace α := ⊤
  InformationTheory.klDiv p.toMeasure q.toMeasure / ENNReal.ofReal (Real.log 2)

/-- Probability `π(E)` of an event. -/
def probOf {Ω : Type} (π : PMF Ω) (E : Set Ω) : ℝ≥0∞ :=
  π.toOuterMeasure E

open Classical in
/-- The law `π(· | W)` conditioned on an event `W`. On an event of probability zero, where
conditioning is undefined, it returns `π`; every use either assumes `π(W) > 0` or weights the
result by `π(W) = 0`. -/
def condOn {Ω : Type} (π : PMF Ω) (W : Set Ω) : PMF Ω :=
  if h : ∃ a ∈ W, a ∈ π.support then π.filter W h else π

/-- The product law `p ⊗ q`. -/
def prodLaw {α β : Type} (p : PMF α) (q : PMF β) : PMF (α × β) :=
  p.bind fun a => q.map fun b => (a, b)

/-- Mutual information `I_π(A; B)` in bits: the divergence of the joint law of `(A, B)` from the
product of its marginals. -/
def mutualInfo {Ω α β : Type} (π : PMF Ω) (A : Ω → α) (B : Ω → β) : ℝ≥0∞ :=
  klBits (π.map fun ω => (A ω, B ω)) (prodLaw (π.map A) (π.map B))

/-- Conditional mutual information `I_π(A; B | C) = Σ_c π(C = c) · I_{π(· | C = c)}(A; B)`. -/
def condMutualInfo {Ω α β γ : Type} (π : PMF Ω) (A : Ω → α) (B : Ω → β) (C : Ω → γ) :
    ℝ≥0∞ :=
  ∑' c, (π.map C) c * mutualInfo (condOn π {ω | C ω = c}) A B

/-- Shannon entropy in bits `H(p) = Σ_a −p(a) log₂ p(a)` of a discrete law (possibly `∞`). -/
def entropyBits {α : Type} (p : PMF α) : ℝ≥0∞ :=
  ∑' a, ENNReal.ofReal (-((p a).toReal * Real.logb 2 (p a).toReal))

/-- The conditional law `π[Y | X = x]` of `Y` given `X = x`. -/
def condLaw {Ω α β : Type} (π : PMF Ω) (X : Ω → α) (Y : Ω → β) (x : α) : PMF β :=
  (condOn π {ω | X ω = x}).map Y

/-- The averaged conditional divergence `E_{x ∼ ν[X]} D_KL(ν[Y | x] ‖ μ[Y | x])`, the average
taken under the first law's marginal. -/
def avgCondKL {Ω α β : Type} (ν μ : PMF Ω) (X : Ω → α) (Y : Ω → β) : ℝ≥0∞ :=
  ∑' x, (ν.map X) x * klBits (condLaw ν X Y x) (condLaw μ X Y x)

/-- `A` and `B` are conditionally independent given `C` under `π`:
`π(A = a, B = b, C = c) π(C = c) = π(A = a, C = c) π(B = b, C = c)` for all values. -/
def CondIndep {Ω α β γ : Type} (π : PMF Ω) (A : Ω → α) (B : Ω → β) (C : Ω → γ) : Prop :=
  ∀ a b c, (π.map fun ω => (A ω, B ω, C ω)) (a, b, c) * (π.map C) c =
    (π.map fun ω => (A ω, C ω)) (a, c) * (π.map fun ω => (B ω, C ω)) (b, c)

end

end SpanForestStream.Unrestricted


