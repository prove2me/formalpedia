-- Prove2me | Definitions.Def_MetricTesting_Characterization_sampling
-- name    : MetricTesting_Characterization_sampling
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:36:58.685415+00:00
-- url     : https://prove2.me/theorems/a16ad55a-6759-473b-8dea-ae78a96db4f6
-- title:
--   Uniform permutation experiments, lazy exposure and canonical inspection
-- statement:
--   For a fixed input array $D$ and decision tree, the permutation experiment samples a uniform permutation of the $n$ labels and answers queries on the permuted input. The lazy experiment first samples a uniform $r$-set, orders it uniformly, and assigns its next unused element whenever a new label is queried. Endpoints of a query are exposed in increasing order. A uniform injection from $r$ labels into $n$ labels encodes exactly this set-and-order experiment. The oracle reads only edges between assigned images. The fallback value outside the touched-label cap is irrelevant under that cap.
--
--   For an experiment $X$ with a finite sample space $S$, its pushforward law is
--   $$\mathcal L(X)=\frac1{|S|}\sum_{s\in S}\delta_{X(s)}.$$
--   The definition records the full infinite sequence of finite transcript prefixes, including stopping decisions, and the sequence of newly assigned images. A coupling is a nonnegative table on the two finite sample spaces with uniform marginals, supported on equal image sequences and transcripts. Randomized-tester rejection probabilities average over label sampling independently of the original seed.
--
--   The simulated tester reads the whole sampled submatrix, then uses these cached values to run the original adaptive rule lazily. It rejects according to that simulation. The separate canonical inspection rule queries every edge of a uniform induced $r$-submatrix and rejects exactly when the restriction is invalid; when $n<r$ it inspects the entire array. The canonical-tester predicate specifies both this literal rule and the uniform sampler law, as well as one-sided tester performance. These definitions do not assume the canonicalization theorem.
-- source:
--   Zihan Tan, Theo Teske, STOC 2027 submission #385 (October 2026), pp. 9–10, Lemmas 3.1–3.2 and Theorem 3.4 (PDF pp. 10–11)

import Mathlib
import Definitions.Def_MetricTesting_Characterization_decision_tree

set_option autoImplicit false

noncomputable section

namespace MetricTesting.Characterization

open MeasureTheory
open scoped BigOperators

attribute [local instance] Classical.propDecidable Classical.decEq

/-- Only finite label samplers are discrete; real oracle answers retain
inherited Borel sigma algebras. -/
instance embeddingSpace (r n : ℕ) : MeasurableSpace (Fin r ↪ Fin n) := ⊤
instance permutationSpace (n : ℕ) : MeasurableSpace (Equiv.Perm (Fin n)) := ⊤

/-- Uniform pushforward, written directly as a finite mixture of point masses.
When the source type is empty this is the zero measure; uses below ensure r ≤ n. -/
def uniformImage {α β : Type} [Fintype α] [MeasurableSpace β]
    (f : α → β) : Measure β :=
  ∑ a : α, (Fintype.card α : ENNReal)⁻¹ • Measure.dirac (f a)

def uniformAverage {α : Type} [Fintype α] (f : α → ENNReal) : ENNReal :=
  (∑ a : α, f a) / (Fintype.card α : ENNReal)

def defaultValue (Λ : Set NNReal) (hΛ : Λ.Nonempty) : Λ :=
  ⟨hΛ.choose, hΛ.choose_spec⟩

/-- Deterministic increasing endpoint order handles two new endpoints in one query. -/
def touched {Λ : Set NNReal} {n : ℕ} (h : History Λ n) : List (Fin n) :=
  (h.flatMap fun p => p.1.1.sort (· ≤ ·)).eraseDups

def exposure {Λ : Set NNReal} {n : ℕ} (h : History Λ n) (e : Edge n) : List (Fin n) :=
  (touched h ++ e.1.sort (· ≤ ·)).eraseDups

/-- An ordered uniform r-sample is exactly a uniform r-set followed by a
uniform ordering of that set. The next unused position supplies each new image.
The fallback is used only outside the touched-label cap. -/
def lazyOracle {Λ : Set NNReal} (hΛ : Λ.Nonempty) {r n : ℕ}
    (D : Array Λ n) (f : Fin r ↪ Fin n) (h : History Λ n) (e : Edge n) : Λ :=
  let images := (e.1.sort (· ≤ ·)).filterMap fun v =>
    (List.ofFn f)[(exposure h e).idxOf v]?
  if hc : images.toFinset.card = 2 then D ⟨images.toFinset, hc⟩
  else defaultValue Λ hΛ

def TouchesAtMost {Λ : Set NNReal} {n : ℕ} (T : DecisionTree Λ n) (r : ℕ) : Prop :=
  ∀ D : Array Λ n, ∀ t : ℕ, (touched (run T (fun _ => D) t).history).length ≤ r

def permutationTrace {Λ : Set NNReal} {n : ℕ} (D : Array Λ n)
    (T : DecisionTree Λ n) (σ : Equiv.Perm (Fin n)) :=
  trace T (fun _ => restrictArray D σ.toEmbedding)

def lazyTrace {Λ : Set NNReal} (hΛ : Λ.Nonempty) {r n : ℕ}
    (D : Array Λ n) (T : DecisionTree Λ n) (f : Fin r ↪ Fin n) :=
  trace T (lazyOracle hΛ D f)

def permutationImages {Λ : Set NNReal} {n : ℕ} (D : Array Λ n)
    (T : DecisionTree Λ n) (σ : Equiv.Perm (Fin n)) : ℕ → List (Fin n) :=
  fun t => (touched (run T (fun _ => restrictArray D σ.toEmbedding) t).history).map σ

def lazyImages {Λ : Set NNReal} (hΛ : Λ.Nonempty) {r n : ℕ}
    (D : Array Λ n) (T : DecisionTree Λ n) (f : Fin r ↪ Fin n) : ℕ → List (Fin n) :=
  fun t => (List.ofFn f).take (touched (run T (lazyOracle hΛ D f) t).history).length

/-- A coupling of the finite random label samplers, with uniform marginals.
The common image sequence is asserted at every time, including nontermination. -/
def ImageCoupling {Λ : Set NNReal} (hΛ : Λ.Nonempty) {r n : ℕ}
    (D : Array Λ n) (T : DecisionTree Λ n) : Prop :=
  ∃ w : Equiv.Perm (Fin n) → (Fin r ↪ Fin n) → ENNReal,
    (∀ σ, ∑ f, w σ f = (Fintype.card (Equiv.Perm (Fin n)) : ENNReal)⁻¹) ∧
    (∀ f, ∑ σ, w σ f = (Fintype.card (Fin r ↪ Fin n) : ENNReal)⁻¹) ∧
    ∀ σ f, w σ f ≠ 0 →
      permutationImages D T σ = lazyImages hΛ D T f ∧
      permutationTrace D T σ = lazyTrace hΛ D T f

/-- The symmetrizing sampler is independent of the tester seed. -/
def symmetrizedRejection (F : LocalData) {n : ℕ}
    (A : RandomTree F.values n) (q : ℕ) (D : Array F.values n) : ENNReal :=
  uniformAverage fun σ : Equiv.Perm (Fin n) =>
    A.law (rejectEvent A q (restrictArray D σ.toEmbedding))

/-- C first reads every entry on the sampled r-set; the subsequent lazy
simulation uses these cached values and makes no further oracle calls. -/
def simulatedRejection (F : LocalData) {n : ℕ}
    (A : RandomTree F.values n) (q r : ℕ) (D : Array F.values n) : ENNReal :=
  uniformAverage fun f : Fin r ↪ Fin n =>
    A.law {ω | (run (A.rule ω) (lazyOracle F.values_nonempty D f) (q+1)).decision = some false}

def submatrixRejection (F : LocalData) {n : ℕ} (s : ℕ)
    (D : Array F.values n) : ENNReal :=
  uniformAverage fun f : Fin s ↪ Fin n =>
    if Valid F (restrictArray D f) then 0 else 1

/-- Cache lookup after all sampled entries have been queried. -/
def cachedArray (F : LocalData) {s n : ℕ} (f : Fin s ↪ Fin n)
    (h : History F.values n) : Array F.values s :=
  fun e => match h.find? (fun p => p.1 = edgeMap f e) with
    | some p => p.2
    | none => defaultValue F.values F.values_nonempty

/-- The literal full-inspection decision tree, rejecting exactly when the
sampled induced array fails the local property. -/
def inspectionRule (F : LocalData) {s n : ℕ} (f : Fin s ↪ Fin n) :
    DecisionTree F.values n := fun h =>
  let edges := (Finset.univ : Finset (Edge s)).toList
  match edges[h.length]? with
  | some e => .inr (edgeMap f e)
  | none => .inl (if Valid F (cachedArray F f h) then true else false)

/-- Uniform induced r-submatrix inspection, with full inspection when n < r.
The random law and the operational rule are both specified, rather than only
postulating that a tester with the right success probability exists. -/
def CanonicalTesters (F : LocalData) (ε : ℝ) (r : ℕ) : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∃ A : RandomTree F.values n,
    ∃ sample : A.Seed → (Fin (min r n) ↪ Fin n),
      Measurable sample ∧
      Measure.map sample A.law = uniformImage (fun f : Fin (min r n) ↪ Fin n => f) ∧
      (∀ ω, A.rule ω = inspectionRule F (sample ω)) ∧
      IsTester F ε (Nat.choose r 2) A

end MetricTesting.Characterization


