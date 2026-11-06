-- Prove2me | Definitions.Def_BorelRobustMDP_AmbiguityFamily
-- name    : BorelRobustMDP_AmbiguityFamily
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:11:51.792447+00:00
-- url     : https://prove2.me/theorems/5360f3e4-6c46-4380-ac1e-d07d4b13dc26
-- title:
--   Reference laws $\mathbb P_n$ and ambiguity sets $\mathcal Q_n$
-- statement:
--   Exponents $q\in(1,\infty]$ and $p$ with $\frac1p+\frac1q=1$, and for $n=1,\dots,N$ a separable probability measure $P_n$ on the disturbance space, the law of $Z_n$, and a non-empty **ambiguity set** $\mathcal Q_n\subseteq\mathcal M^q(P_n)$.
--
--   The type $\mathcal Q_n$ carries the trace of the weak* topology and the Borel σ-algebra of that topology. The set $\mathcal Q_n$ is **norm bounded** by $K$ if $\|dQ/dP_n\|_{L^q(P_n)}\le K$ for every $Q\in\mathcal Q_n$.
--
--   **Formalization Note.** Separability is `MeasureTheory.IsSeparable`. The norm bound reads Assumption 3.1 (iii) as a bound on the norm, since the printed $\mathbb E|dQ/dP_n|^q\le K$ has no meaning at $q=\infty$ and the proof of Lemma 2.3 uses the norm.
-- source:
--   Bäuerle & Glauner, arXiv:2007.13103v1, §2, p.4, and Assumption 3.1 (iii), p.6

import Mathlib
import Definitions.Def_BorelRobustMDP_Mq
import Definitions.Def_BorelRobustMDP_weakStarTopology

open MeasureTheory
open scoped ENNReal

namespace BorelRobustMDP

universe v

/-- The reference laws and ambiguity sets of Bäuerle & Glauner, arXiv:2007.13103v1, p.4: exponents
`q ∈ (1, ∞]` and `p` with `1/p + 1/q = 1`; for `n = 1, …, N` a separable probability measure
`P_n` on the disturbance space (the law of `Z_n`) and a non-empty set `𝒬_n ⊆ 𝓜^q(P_n)`.

**Formalization Note.** Indices `n` outside `1, …, N` are unused. The product space
`(Ω, 𝒜, ℙ) = ⊗ (Ω_n, 𝒜_n, ℙ_n)` of the paper enters only through these marginals. Separability
of `P_n` ("we will require ℙ_n to be separable", p.4) is `MeasureTheory.IsSeparable`. -/
structure AmbiguityFamily (Z : Type v) [MeasurableSpace Z] (N : ℕ) where
  /-- The exponent `q ∈ (1, ∞]`. -/
  q : ℝ≥0∞
  /-- The conjugate exponent `p`. -/
  p : ℝ≥0∞
  one_lt_q : 1 < q
  holderConjugate : ENNReal.HolderConjugate p q
  /-- The reference law `P_n` of the disturbance `Z_n`. -/
  P : ℕ → Measure Z
  isProbabilityMeasure_P : ∀ n, 1 ≤ n → n ≤ N → IsProbabilityMeasure (P n)
  isSeparable_P : ∀ n, 1 ≤ n → n ≤ N → IsSeparable (P n)
  /-- The ambiguity set `𝒬_n`. -/
  𝒬 : ℕ → Set (Measure Z)
  nonempty_𝒬 : ∀ n, 1 ≤ n → n ≤ N → (𝒬 n).Nonempty
  subset_Mq : ∀ n, 1 ≤ n → n ≤ N → 𝒬 n ⊆ Mq (P n) q

namespace AmbiguityFamily

variable {Z : Type v} [MeasurableSpace Z] {N : ℕ}

/-- The ambiguity set `𝒬_n` as a type, carrying the trace of the weak* topology and its Borel
σ-algebra (Bäuerle & Glauner, arXiv:2007.13103v1, p.4).

**Formalization Note.** A separate type, so that these structures are not confused with the
σ-algebra Mathlib puts on `Measure Z`. -/
def Amb (𝔸 : AmbiguityFamily Z N) (n : ℕ) : Type v := ↥(𝔸.𝒬 n)

/-- The probability measure underlying a point of `𝒬_n`. -/
def Amb.measure {𝔸 : AmbiguityFamily Z N} {n : ℕ} (Q : 𝔸.Amb n) : Measure Z := Q.1

noncomputable instance (𝔸 : AmbiguityFamily Z N) (n : ℕ) : TopologicalSpace (𝔸.Amb n) :=
  weakStarTopology (𝔸.P n) 𝔸.p (𝔸.𝒬 n)

noncomputable instance (𝔸 : AmbiguityFamily Z N) (n : ℕ) : MeasurableSpace (𝔸.Amb n) := borel _

instance (𝔸 : AmbiguityFamily Z N) (n : ℕ) : BorelSpace (𝔸.Amb n) := ⟨rfl⟩

/-- `𝒬_n` is weak* closed. -/
def WeakStarClosed (𝔸 : AmbiguityFamily Z N) (n : ℕ) : Prop :=
  IsWeakStarClosed (𝔸.P n) 𝔸.p 𝔸.q (𝔸.𝒬 n)

/-- `𝒬_n` is norm bounded by `K` in `L^q(P_n)` (Bäuerle & Glauner, arXiv:2007.13103v1, Assumption
3.1 (iii), p.6).

**Formalization Note.** The bound is on the norm `‖dQ/dP_n‖_{L^q} ≤ K`: the printed
`E|dQ/dP_n|^q ≤ K` has no meaning at `q = ∞`, and the proof of Lemma 2.3 (p.23) uses the norm. For
`q < ∞` the two give the same "there exists `K`". -/
def NormBounded (𝔸 : AmbiguityFamily Z N) (n : ℕ) (K : ℝ) : Prop :=
  ∀ Q ∈ 𝔸.𝒬 n, eLpNorm (fun z => (Q.rnDeriv (𝔸.P n) z).toReal) 𝔸.q (𝔸.P n) ≤ ENNReal.ofReal K

end AmbiguityFamily

end BorelRobustMDP


