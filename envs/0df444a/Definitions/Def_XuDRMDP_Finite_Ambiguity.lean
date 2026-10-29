-- Prove2me | Definitions.Def_XuDRMDP_Finite_Ambiguity
-- name    : XuDRMDP_Finite_Ambiguity
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T05:27:51.715979+00:00
-- url     : https://prove2.me/theorems/2c0aee29-6e77-476d-913b-f43f148973bf
-- title:
--   Nested confidence sets, product laws, means and reduction sets
-- statement:
--   Fix staged data. There are $n\ge1$ layers, represented by `layers + 1`, and confidence levels $0\le\lambda_1\le\cdots\le\lambda_n=1$. At each state, the local sets $P_s^1\subseteq\cdots\subseteq P_s^n$ are nonempty, compact and convex sets of valid local parameter vectors. They may couple different actions and rewards with transitions. No strict inclusions or strict confidence increments are required.
--
--   The local ambiguity class consists of all Borel probability measures $\mu_s$ satisfying $\mu_s(P_s^n)=1$ and $\mu_s(P_s^i)\ge\lambda_i$. Including the last inequality is redundant because its two sides are one. Admissible global laws are exactly the finite products of admissible marginals. Arbitrary nonatomic measures are included. Local means and global coordinate means are Bochner integrals of the identity and coordinate projections respectively.
--
--   With $\lambda_0=0$, define $\widehat P_s=\{\sum_i(\lambda_i-\lambda_{i-1})y_i:y_i\in P_s^i\}$. This follows Definition 3.2 in consistent $(p,r)$ order, reading its reversed displayed pair as the typography error confirmed by Lemma 3.3. The construction does not assume that the reduction set is the attainable-mean set. Compact support makes means integrable in all admissible instances; the raw integral functions are also defined on inadmissible laws, where Lean's total integral convention applies.
-- source:
--   Xu and Mannor (2012), Distributionally Robust Markov Decision Processes, Mathematics of Operations Research 37(2), 288–300, DOI:10.1287/moor.1120.0540. Published basis; printed page = PDF page + 287. Sections 2–3, printed pp. 289–293 (PDF pp. 2–6).

import Definitions.Def_XuDRMDP_Finite_Setup
open MeasureTheory
open scoped BigOperators

namespace XuDRMDP.Finite

/-- Assumption 2.1 and the confidence levels. There are layers+1 layers, indexed from zero. -/
structure Uncertainty {n : ℕ} [NeZero n] {a : Fin n → ℕ} [∀ s, NeZero (a s)]
    (G : Setup n a) where
  layers : ℕ
  confidence : Fin (layers + 1) → ℝ
  confidence_nonneg : ∀ i, 0 ≤ confidence i
  confidence_mono : Monotone confidence
  confidence_last : confidence (Fin.last layers) = 1
  sets : (s : Fin n) → Fin (layers + 1) → Set (Local n a s)
  nonempty : ∀ s i, (sets s i).Nonempty
  convex : ∀ s i, Convex ℝ (sets s i)
  compact : ∀ s i, IsCompact (sets s i)
  nested : ∀ s, Monotone (sets s)
  valid : ∀ s i x, x ∈ sets s i → ValidLocal G s x

/-- Equation (1): all Borel probability measures with the specified lower confidence bounds. -/
def localClass {n : ℕ} [NeZero n] {a : Fin n → ℕ} [∀ s, NeZero (a s)]
    {G : Setup n a} (U : Uncertainty G) (s : Fin n) : Set (Measure (Local n a s)) :=
  {μ | IsProbabilityMeasure μ ∧ μ (U.sets s (Fin.last U.layers)) = 1 ∧
    ∀ i, ENNReal.ofReal (U.confidence i) ≤ μ (U.sets s i)}

abbrev Marginals (n : ℕ) (a : Fin n → ℕ) := (s : Fin n) → Measure (Local n a s)

def admissibleMarginals {n : ℕ} [NeZero n] {a : Fin n → ℕ} [∀ s, NeZero (a s)]
    {G : Setup n a} (U : Uncertainty G) (μ : Marginals n a) : Prop :=
  ∀ s, μ s ∈ localClass U s

noncomputable def productLaw {n : ℕ} {a : Fin n → ℕ} (μ : Marginals n a) :
    Measure (Parameters n a) := Measure.pi μ

/-- The global ambiguity class is exactly the image of admissible marginal families. -/
def globalClass {n : ℕ} [NeZero n] {a : Fin n → ℕ} [∀ s, NeZero (a s)]
    {G : Setup n a} (U : Uncertainty G) : Set (Measure (Parameters n a)) :=
  {ν | ∃ μ, admissibleMarginals U μ ∧ productLaw μ = ν}

noncomputable def confidenceIncrement {n : ℕ} [NeZero n] {a : Fin n → ℕ}
    [∀ s, NeZero (a s)] {G : Setup n a} (U : Uncertainty G)
    (i : Fin (U.layers + 1)) : ℝ :=
  U.confidence i - if h : i.val = 0 then 0
    else U.confidence ⟨i.val - 1, by omega⟩

/-- Definition 3.2's weighted Minkowski set, in consistent (p,r) coordinates. -/
noncomputable def reducedSet {n : ℕ} [NeZero n] {a : Fin n → ℕ}
    [∀ s, NeZero (a s)] {G : Setup n a} (U : Uncertainty G) (s : Fin n) :
    Set (Local n a s) :=
  {x | ∃ y : Fin (U.layers + 1) → Local n a s,
    (∀ i, y i ∈ U.sets s i) ∧ x = ∑ i, confidenceIncrement U i • y i}

noncomputable def localMean {n : ℕ} {a : Fin n → ℕ} {s : Fin n}
    (μ : Measure (Local n a s)) : Local n a s := ∫ x, x ∂μ

noncomputable def globalMean {n : ℕ} {a : Fin n → ℕ}
    (ν : Measure (Parameters n a)) : Parameters n a := fun s => ∫ x, x s ∂ν

end XuDRMDP.Finite


