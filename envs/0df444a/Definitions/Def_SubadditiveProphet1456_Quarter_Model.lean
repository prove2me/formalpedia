-- Prove2me | Definitions.Def_SubadditiveProphet1456_Quarter_Model
-- name    : SubadditiveProphet1456_Quarter_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T07:03:31.786644+00:00
-- url     : https://prove2.me/theorems/3b89f000-5cb7-4776-848c-c5dc618fc690
-- title:
--   Independent finite-support allocation model, configuration LP, causal policies and score thresholds
-- statement:
--   Let $n$ buyers arrive in the fixed order $0,\ldots,n-1$ and let $m$ items be labeled $0,\ldots,m-1$. Buyer $i$ has a nonempty finite type support $\Gamma_i$, a strictly positive probability $q_{i,\tau}$ for each type, and a normalized, monotone, subadditive real valuation $v_{i,\tau}$. The instance contains no uniform bound or rationality restriction on valuations. Normalization and monotonicity imply nonnegativity. The valuation and disjoint-allocation predicates are the published complement-free auction primitives.
--
--   The generic finite LP data are separated into objective, constraint matrix and right-hand side. The allocation LP uses joint masses $x_{i,\tau,A}$ for nonempty bundles, with
--   $$
--   x\ge0,\qquad \sum_{A\ne\varnothing}x_{i,\tau,A}\le q_{i,\tau},\qquad
--   \sum_{i,\tau,A\ni j}x_{i,\tau,A}\le\theta.
--   $$
--   Its objective is $\sum x_{i,\tau,A}v_{i,\tau}(A)$, and $\mathrm{LP}(\theta)^*$ is its supremum over this concrete feasible set. For $0\le\theta\le1$ the zero solution is feasible and the objective is bounded, so this is the usual attained finite LP value. The conditional tentative law puts mass $x_{i,\tau,A}/q_{i,\tau}$ on each nonempty $A$ and the residual mass on the empty bundle. Independent buyer types use the product of their probabilities. The offline benchmark maximizes welfare over all disjoint allocations for each type profile.
--
--   A policy is a joint allocation law for each realized type profile. Its online condition requires feasible support and equality of all prefix allocation marginals whenever the observable type prefixes agree. This describes causal randomized allocation with immediate commitments and allows correlations through internal memory. Welfare averages this same law over the independent type profiles.
--
--   Scores are nonnegative real vectors. The full and prefix maxima include zero, eligibility uses weak inequalities, and actual winning uses a strict inequality. The effective threshold is the minimum of the eligible full maxima, with the larger candidate always eligible. General score laws are Borel probability measures; capped score laws are PMFs with support explicitly constrained to integer coordinates $0,\ldots,N$. Their fixed-point identity uses independent tentative bundles and two fresh independent full reference profiles.
--
--   The tail notation $q,Q,\pi,\alpha,\beta,\rho,s,f$ follows Appendix A, with buyer $i$ included in the suffix product. Finally,
--   $$
--   J_s(t)=e^{-s^2t-(s/2)(1-e^{-2t})},\quad F(s)=1-(1+s^2)\int_0^1J_s(t)\,dt,
--   $$
--   and the universal constant and retention cap are the explicit integral and logarithmic expressions from printed pp.14,34. The normalization fallback for invalid mass arrays is outside the feasible-instance domain and adds no assumption on an LP solution.
--
--   **Formalization Note** Finite indices start at zero; every nonempty finite support is represented as $\mathrm{Fin}(k+1)$. This includes zero buyers and zero items. Real suprema are used only on nonempty bounded feasible objectives in the theorem domains. These definitions supply reusable finite LP and causal-policy interfaces as well as the paper's exact allocation model.
-- source:
--   Twan Kroll, Calum MacRury, Rebecca Reiffenhäuser, Siddharth M. Sundaram, STOC 2027 submission #1456 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1456.pdf, §2 (printed pp.7–9, PDF pp.8–10), §3 (printed pp.9–10, PDF pp.10–11), §4.3 Algorithm 1 (printed pp.15–17, PDF pp.16–18), Appendix A (printed pp.31–34, PDF pp.32–35).

import Mathlib
import Definitions.Def_ComplementFreeCA_CFRounding_Auction

open scoped BigOperators NNReal ENNReal
open MeasureTheory

namespace SubadditiveProphet1456.Quarter

abbrev Bundle (m : ℕ) := Finset (Fin m)
abbrev Allocation (n m : ℕ) := Fin n → Bundle m
abbrev Score (m : ℕ) := Fin m → ℝ≥0
abbrev ScoreProfile (n m : ℕ) := Fin n → Score m

/-- Generic finite-dimensional inequality LP, separated from the allocation model. -/
structure FiniteLP (V C : Type) where
  objective : V → ℝ
  matrix : C → V → ℝ
  rhs : C → ℝ

def FiniteLP.Feasible {V C : Type} [Fintype V] (L : FiniteLP V C) (x : V → ℝ) : Prop :=
  (∀ v, 0 ≤ x v) ∧ ∀ c, ∑ v, L.matrix c v * x v ≤ L.rhs c

noncomputable def FiniteLP.value {V C : Type} [Fintype V] (L : FiniteLP V C) : ℝ :=
  sSup {z | ∃ x, L.Feasible x ∧ z = ∑ v, L.objective v * x v}

/-- Every buyer has a nonempty finite type support; zero-probability labels are removed. -/
structure Instance (n m : ℕ) where
  types : Fin n → ℕ
  probability : (i : Fin n) → Fin (types i + 1) → ℝ
  positive : ∀ i t, 0 < probability i t
  total : ∀ i, ∑ t, probability i t = 1
  valuation : (i : Fin n) → Fin (types i + 1) → Bundle m → ℝ
  normalized : ∀ i t, ComplementFreeCA.CFRounding.IsNormalized (valuation i t)
  monotone : ∀ i t, ComplementFreeCA.CFRounding.IsMonotone (valuation i t)
  subadditive : ∀ i t, ComplementFreeCA.CFRounding.IsSubadditive (valuation i t)

abbrev Profile {n m : ℕ} (I : Instance n m) := (i : Fin n) → Fin (I.types i + 1)
abbrev Variable {n m : ℕ} (I : Instance n m) :=
  (i : Fin n) × Fin (I.types i + 1) × {A : Bundle m // A ≠ ∅}
abbrev Constraint {n m : ℕ} (I : Instance n m) :=
  ((i : Fin n) × Fin (I.types i + 1)) ⊕ Fin m

noncomputable def configurationLP {n m : ℕ} (I : Instance n m) (θ : ℝ) :
    FiniteLP (Variable I) (Constraint I) := by
  classical
  exact {
    objective := fun v => I.valuation v.1 v.2.1 v.2.2.val
    matrix := fun c v => match c with
      | .inl it => if v.1 = it.1 ∧ HEq v.2.1 it.2 then 1 else 0
      | .inr j => if j ∈ v.2.2.val then 1 else 0
    rhs := fun c => match c with
      | .inl it => I.probability it.1 it.2
      | .inr _ => θ }

abbrev Fractional {n m : ℕ} (I : Instance n m) := Variable I → ℝ

noncomputable def Feasible {n m : ℕ} (I : Instance n m) (θ : ℝ) (x : Fractional I) : Prop :=
  (configurationLP I θ).Feasible x

noncomputable def objective {n m : ℕ} (I : Instance n m) (x : Fractional I) : ℝ :=
  ∑ v, x v * I.valuation v.1 v.2.1 v.2.2.val

noncomputable def lpValue {n m : ℕ} (I : Instance n m) (θ : ℝ) : ℝ :=
  (configurationLP I θ).value

noncomputable def Optimal {n m : ℕ} (I : Instance n m) (θ : ℝ) (x : Fractional I) : Prop :=
  Feasible I θ x ∧ objective I x = lpValue I θ

/-- Normalize nonnegative weights; the fallback is only used on invalid weights. -/
noncomputable def weightedLaw {α : Type} [Inhabited α] (w : α → ℝ≥0∞) : PMF α := by
  classical
  exact if h : (∑' a, w a) ≠ 0 ∧ (∑' a, w a) ≠ ⊤ then
    PMF.normalize w h.1 h.2 else PMF.pure default

/-- Independent draws, one per buyer. The fold visits each index once. -/
noncomputable def independent {α : Type} [Inhabited α] {n : ℕ}
    (p : Fin n → PMF α) : PMF (Fin n → α) := by
  classical
  exact (List.finRange n).foldl (fun law i =>
    law.bind fun a => (p i).map fun z => Function.update a i z) (PMF.pure fun _ => default)

noncomputable def profileMass {n m : ℕ} (I : Instance n m) (t : Profile I) : ℝ :=
  ∏ i, I.probability i (t i)

noncomputable def tentativeMass {n m : ℕ} (I : Instance n m) (x : Fractional I)
    (i : Fin n) (t : Fin (I.types i + 1)) (A : Bundle m) : ℝ := by
  classical
  exact if h : A = ∅ then
    1 - (∑ B : {B : Bundle m // B ≠ ∅}, x ⟨i, t, B⟩) / I.probability i t
  else x ⟨i, t, ⟨A, h⟩⟩ / I.probability i t

noncomputable def tentative {n m : ℕ} (I : Instance n m) (x : Fractional I)
    (i : Fin n) (t : Fin (I.types i + 1)) : PMF (Bundle m) :=
  weightedLaw fun A => ENNReal.ofReal (tentativeMass I x i t A)

noncomputable def unconditionalBundle {n m : ℕ} (I : Instance n m) (x : Fractional I)
    (i : Fin n) : PMF (Bundle m) :=
  (weightedLaw fun t : Fin (I.types i + 1) => ENNReal.ofReal (I.probability i t)).bind
    (tentative I x i)

noncomputable def offlineValue {n m : ℕ} (I : Instance n m) (t : Profile I) : ℝ :=
  sSup {z | ∃ A : Allocation n m, ComplementFreeCA.CFRounding.IsAllocation A ∧
    z = ComplementFreeCA.CFRounding.welfare (fun i => I.valuation i (t i)) A}

noncomputable def expectedOffline {n m : ℕ} (I : Instance n m) : ℝ :=
  ∑ t : Profile I, profileMass I t * offlineValue I t

/-- Joint allocation law, with causality checked through all prefix marginals below. -/
abbrev Policy {n m : ℕ} (I : Instance n m) := Profile I → PMF (Allocation n m)

noncomputable def IsOnline {n m : ℕ} (I : Instance n m) (P : Policy I) : Prop :=
  (∀ t A, P t A ≠ 0 → ComplementFreeCA.CFRounding.IsAllocation A) ∧
  ∀ (k : ℕ) (t u : Profile I), (∀ i, i.val < k → t i = u i) →
    (P t).map (fun A => fun i : {i : Fin n // i.val < k} => A i.val) =
    (P u).map (fun A => fun i : {i : Fin n // i.val < k} => A i.val)

noncomputable def policyWelfare {n m : ℕ} (I : Instance n m) (P : Policy I) : ℝ :=
  ∑ t : Profile I, profileMass I t *
    ∑ A : Allocation n m, (P t A).toReal *
      ComplementFreeCA.CFRounding.welfare (fun i => I.valuation i (t i)) A

noncomputable def fullMaximum {n m : ℕ} (Y : ScoreProfile n m) (j : Fin m) : ℝ≥0 :=
  Finset.univ.sup fun k => Y k j

noncomputable def prefixMaximum {n m : ℕ} (i : Fin n) (Y : ScoreProfile n m)
    (j : Fin m) : ℝ≥0 :=
  (Finset.univ.filter fun k : Fin n => k < i).sup fun k => Y k j

/-- The larger full maximum is always eligible, so the last branch is unreachable. -/
noncomputable def threshold {n m : ℕ} (i : Fin n) (Y Z : ScoreProfile n m) : Score m :=
  fun j => if fullMaximum Y j ≥ prefixMaximum i Z j then
    if fullMaximum Z j ≥ prefixMaximum i Y j then min (fullMaximum Y j) (fullMaximum Z j)
    else fullMaximum Y j
  else fullMaximum Z j

noncomputable def allocated {n m : ℕ} (i : Fin n) (b : Score m)
    (Y Z : ScoreProfile n m) : Bundle m :=
  Finset.univ.filter fun j => b j > fullMaximum Y j ∧ fullMaximum Y j ≥ prefixMaximum i Z j

noncomputable def mirrorSet {n m : ℕ} (i : Fin n) (b : Score m)
    (Y Z : ScoreProfile n m) : Bundle m :=
  Finset.univ.filter fun j => b j > threshold i Y Z j

noncomputable def restrictScore {m : ℕ} (A : Bundle m) (b : Score m) : Score m :=
  fun j => if j ∈ A then b j else 0

noncomputable def capScore {m : ℕ} (N : ℕ) (b : Score m) : Score m :=
  fun j => min (N : ℝ≥0) (b j)

noncomputable def cappedSuccessor {n m : ℕ} (N : ℕ) (i : Fin n)
    (Y Z : ScoreProfile n m) (A : Bundle m) : Score m :=
  restrictScore A fun j => min (N : ℝ≥0) (1 + threshold i Y Z j)

/-- Arbitrary Borel score laws: no boundedness or discrete support restriction. -/
noncomputable def referenceMeasure {n m : ℕ} (I : Instance n m)
    (φ : (i : Fin n) → Fin (I.types i + 1) → Measure (Score m)) : Measure (ScoreProfile n m) :=
  Measure.pi fun i => ∑ t, (ENNReal.ofReal (I.probability i t)) • φ i t

/-- Discrete score laws used by the capped construction. -/
abbrev RSG {n m : ℕ} (I : Instance n m) :=
  (i : Fin n) → Fin (I.types i + 1) → PMF (Score m)

noncomputable def scoreLaw {n m : ℕ} (I : Instance n m) (φ : RSG I) (i : Fin n) : PMF (Score m) :=
  (weightedLaw fun t : Fin (I.types i + 1) => ENNReal.ofReal (I.probability i t)).bind (φ i)

noncomputable def referenceLaw {n m : ℕ} (I : Instance n m) (φ : RSG I) : PMF (ScoreProfile n m) :=
  independent (scoreLaw I φ)

noncomputable def fixedPointLaw {n m : ℕ} (I : Instance n m) (x : Fractional I)
    (N : ℕ) (φ : RSG I) (i : Fin n) (t : Fin (I.types i + 1)) : PMF (Score m) :=
  (tentative I x i t).bind fun A => (referenceLaw I φ).bind fun Y =>
    (referenceLaw I φ).map fun Z => cappedSuccessor N i Y Z A

noncomputable def DistributionalEquation {n m : ℕ} (I : Instance n m) (x : Fractional I)
    (N : ℕ) (φ : RSG I) : Prop :=
  (∀ i t b, φ i t b ≠ 0 → ∀ j, ∃ h : ℕ, h ≤ N ∧ b j = (h : ℝ≥0)) ∧
  ∀ i t, φ i t = fixedPointLaw I x N φ i t

noncomputable def q {n m : ℕ} (I : Instance n m) (φ : RSG I)
    (i : Fin n) (j : Fin m) (h : ℕ) : ℝ :=
  ((scoreLaw I φ i).toMeasure {b | (h : ℝ≥0) ≤ b j}).toReal

noncomputable def Q {n m : ℕ} (I : Instance n m) (φ : RSG I) (j : Fin m) (h : ℕ) : ℝ :=
  ∑ i, q I φ i j h

noncomputable def π {n m : ℕ} (I : Instance n m) (x : Fractional I) (i : Fin n) (j : Fin m) : ℝ :=
  ((unconditionalBundle I x i).toMeasure {A | j ∈ A}).toReal

noncomputable def α {n m : ℕ} (I : Instance n m) (φ : RSG I) (i : Fin n) (j : Fin m) (h : ℕ) : ℝ :=
  ∏ k ∈ Finset.univ.filter (fun k : Fin n => k < i), (1 - q I φ k j h)

noncomputable def β {n m : ℕ} (I : Instance n m) (φ : RSG I) (i : Fin n) (j : Fin m) (h : ℕ) : ℝ :=
  ∏ k ∈ Finset.univ.filter (fun k : Fin n => i ≤ k), (1 - q I φ k j h)

noncomputable def ρ {n m : ℕ} (I : Instance n m) (x : Fractional I) (i : Fin n) (j : Fin m) : ℝ :=
  ∏ k ∈ Finset.univ.filter (fun k : Fin n => k < i), (1 - π I x k j)

noncomputable def s {n m : ℕ} (I : Instance n m) (φ : RSG I) (j : Fin m) (h : ℕ) : ℝ :=
  ∏ k, (1 - q I φ k j h)

noncomputable def f {n m : ℕ} (I : Instance n m) (φ : RSG I) (i : Fin n) (j : Fin m) (h : ℕ) : ℝ :=
  α I φ i j h - s I φ j h

noncomputable def J (s t : ℝ) : ℝ := Real.exp (-s^2*t - (s/2)*(1-Real.exp (-2*t)))
noncomputable def F (s : ℝ) : ℝ := 1 - (1+s^2) * ∫ t in (0:ℝ)..1, J s t
noncomputable def tailConstant : ℝ :=
  (Real.exp (-(3:ℝ)/2)/2) * ∫ t in (0:ℝ)..1,
    (1-t)^2 * ((1+t)*Real.exp (-2*t) - (1-t))
noncomputable def retentionCap (c δ θ : ℝ) (m : ℕ) : ℕ :=
  1 + ⌈Real.log (max 1 ((m:ℝ)*θ^2/(δ*(1-θ)^2))) / (2*Real.log (1+c))⌉₊

end SubadditiveProphet1456.Quarter


