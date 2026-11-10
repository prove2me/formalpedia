-- Prove2me | Definitions.Def_FengLiYangMatching_General_Local
-- name    : FengLiYangMatching_General_Local
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T11:47:16.403311+00:00
-- url     : https://prove2.me/theorems/7358d797-318d-45f4-94bf-d72b35405b3d
-- title:
--   Coupled finite Greedy experiments and conditioning on a recovery background
-- statement:
--   A reduced local configuration consists of a finite loopless base graph B, two distinct added endpoints x₁,x₂ outside B, a set Y of base vertices, potential added edges from {x₁,x₂} to Y, and at most two distinct marked reference vertices in Y. Validity asserts only these structural facts. It does not assume any desired inequality or force a deleted reference edge to exist. The base graph may be arbitrary; the configurations obtained from the source recovery graph are included.
--
--   Choose one uniform order σ of all base and potential edges, independently retaining each potential edge with probability q∈[5/8,1]. The run on B skips all potential edges; the augmented run skips only unretained edges. The run C additionally skips edges incident to x₂. Thus all runs have the same order on common edges. Let N count matched added endpoints and R count matched marked vertices in the augmented run, K count matched marked vertices in B, and N₁,R₁ be the corresponding counts in C. For a marked vertex y, μ(y) is the probability that Greedy on B matches y, computed by averaging the base run over the common uniform order.
--
--   $$\mathbb E_q[f]=\frac1{|\mathcal O|}\sum_{\sigma\in\mathcal O}\sum_{S\subseteq P}q^{|S|}(1-q)^{|P\setminus S|}f(\sigma,S).$$
--
--   Here P is the finite potential-edge set and 𝒪 contains every permutation of B∪P exactly once. The implementation uses a product of Bernoulli factors, including q=1, rather than dividing by a zero retention probability. There is one permutation even when the edge set is empty. The marked-edge average fixes arbitrary retention outcomes of all edges to unmarked vertices, while independently retaining marked-reference edges with probability q, exactly as in §4.3. Single-edge averaging leaves only the distinguished reference edge random, so Lemma 4.3 also covers fixed outcomes of the other retention coins. Vertex deletion removes incident edges but retains marked labels.
--
--   The continuous conditional experiment is also defined concretely: for an early shadow edge e, B contains all recovery YY edges and recovery edges from other reserved vertices to Y, with both endpoints of e removed. Its construction never reads e's reservation coin. The augmented graph restores precisely the post-b edges from those endpoints to Y. Both Greedy runs use the original common arrival times. Conditioning on the finite-valued B uses normalized restriction only for positive-probability backgrounds; the exact-time H_b conditioning uses the candidate residual law whose correctness is Lemma 4.1. No finite-permutation replacement is made in the goal. These experiments supply the counts in the local comparisons and the genuine conditional expectation in Lemma 2.2.
-- source:
--   Yilong Feng, Haolong Li, Zonghan Yang, STOC 2027 submission #1018 (October 2026), §§2.1, 4.1–4.3 and Appendix A, pp. 7, 13–16, 24–26; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1018.pdf

import Definitions.Def_FengLiYangMatching_General_Process

open MeasureTheory Finset
open scoped BigOperators

namespace FengLiYangMatching.General
noncomputable section

/-- Reduced experiments keep marked vertices even after a reference edge is deleted. -/
structure Local (n : ℕ) where
  base : EdgeSet n
  potential : EdgeSet n
  x1 : Fin n
  x2 : Fin n
  Y : Finset (Fin n)
  marked : Finset (Fin n)

def Local.Valid {n : ℕ} (d : Local n) : Prop :=
  d.x1 ≠ d.x2 ∧
  (∀ e ∈ d.base, ¬ e.IsDiag ∧ d.x1 ∉ e ∧ d.x2 ∉ e) ∧
  d.x1 ∉ d.Y ∧ d.x2 ∉ d.Y ∧ d.marked ⊆ d.Y ∧ d.marked.card ≤ 2 ∧
  (∀ e ∈ d.potential, ∃ x ∈ ({d.x1,d.x2} : Finset (Fin n)),
    ∃ y ∈ d.Y, e = s(x,y))

def Local.Partners {n : ℕ} (d : Local n) : Prop :=
  ∃ f : d.marked → Fin n, Function.Injective f ∧
    ∀ y, f y ∈ ({d.x1,d.x2} : Finset (Fin n)) ∧ s(f y, y.val) ∈ d.potential

def localRun {n : ℕ} (d : Local n) (σ : List (Edge n)) (retained : EdgeSet n) : EdgeSet n := by
  classical
  exact greedy (σ.filter fun e => e ∈ d.base ∨ e ∈ retained)

def baseRun {n : ℕ} (d : Local n) (σ : List (Edge n)) : EdgeSet n := by
  classical
  exact greedy (σ.filter fun e => e ∈ d.base)

def oneRun {n : ℕ} (d : Local n) (σ : List (Edge n)) (retained : EdgeSet n) : EdgeSet n := by
  classical
  exact greedy (σ.filter fun e => (e ∈ d.base ∨ e ∈ retained) ∧ d.x2 ∉ e)

def count {n : ℕ} (A : Finset (Fin n)) (M : EdgeSet n) : ℝ := by
  classical
  exact Nat.cast (A ∩ covered M).card

def N {n : ℕ} (d : Local n) (σ : List (Edge n)) (r : EdgeSet n) : ℝ :=
  count {d.x1,d.x2} (localRun d σ r)
def R {n : ℕ} (d : Local n) (σ : List (Edge n)) (r : EdgeSet n) : ℝ :=
  count d.marked (localRun d σ r)
def K {n : ℕ} (d : Local n) (σ : List (Edge n)) : ℝ :=
  count d.marked (baseRun d σ)
def N1 {n : ℕ} (d : Local n) (σ : List (Edge n)) (r : EdgeSet n) : ℝ :=
  count {d.x1} (oneRun d σ r)
def R1 {n : ℕ} (d : Local n) (σ : List (Edge n)) (r : EdgeSet n) : ℝ :=
  count d.marked (oneRun d σ r)

def orders {n : ℕ} (d : Local n) : Finset (List (Edge n)) := by
  classical
  exact (d.base ∪ d.potential).toList.permutations.toFinset

def retentionWeight {n : ℕ} (d : Local n) (q : ℝ) (r : EdgeSet n) : ℝ := by
  classical
  exact ∏ e ∈ d.potential, if e ∈ r then q else 1-q

/-- One common uniform order, independent Bernoulli retention on potential edges. -/
def localMean {n : ℕ} (d : Local n) (q : ℝ)
    (f : List (Edge n) → EdgeSet n → ℝ) : ℝ := by
  classical
  exact (∑ σ ∈ orders d, ∑ r ∈ d.potential.powerset, retentionWeight d q r * f σ r) /
    (orders d).card

/-- Potential edges to marked vertices: these coins remain random in Section 4.3. -/
def markedPotential {n : ℕ} (d : Local n) : EdgeSet n := by
  classical
  exact d.potential.filter fun e => ∃ y ∈ d.marked, y ∈ e

/-- Condition on every nonreference retention outcome, as in the first-edge induction.
Only potential edges to marked vertices are independently retained with probability q. -/
def markedMean {n : ℕ} (d : Local n) (q : ℝ) (fixed : EdgeSet n)
    (f : List (Edge n) → EdgeSet n → ℝ) : ℝ := by
  classical
  exact (∑ σ ∈ orders d, ∑ r ∈ (markedPotential d).powerset,
    (∏ e ∈ markedPotential d, if e ∈ r then q else 1-q) * f σ (fixed ∪ r)) /
      (orders d).card

def mu {n : ℕ} (d : Local n) (y : Fin n) : ℝ :=
  (∑ σ ∈ orders d, count {y} (baseRun d σ)) / (orders d).card

/-- Delete z, retain only edges of the chosen endpoint, and use the common order. -/
def deletedRun {n : ℕ} (d : Local n) (x z : Fin n) (σ : List (Edge n))
    (r : EdgeSet n) : EdgeSet n := by
  classical
  exact greedy (σ.filter fun e => z ∉ e ∧ (e ∈ d.base ∨ (e ∈ r ∧ x ∈ e)))

/-- The distinguished edge alone is random; other retention outcomes can be fixed. -/
def singleMean {n : ℕ} (d : Local n) (q : ℝ) (ref : Edge n) (fixed : EdgeSet n)
    (f : List (Edge n) → EdgeSet n → ℝ) : ℝ :=
  (∑ σ ∈ orders d, (q * f σ (insert ref fixed) + (1-q) * f σ fixed)) / (orders d).card

/-- All other reservations, never the distinguished shadow edge's coin. -/
def otherX {n : ℕ} (G : SimpleGraph (Fin n)) (a : ℝ) (h : History n)
    (e : Edge n) (w : Sample G) : Finset (Fin n) := by
  classical
  exact covered ((early a h).filter fun f => f ≠ e ∧ ∃ hf : f ∈ G.edgeSet, w.2 ⟨f,hf⟩ = true)

def background {n : ℕ} (G : SimpleGraph (Fin n)) (a b : ℝ) (h : History n)
    (e : Edge n) (w : Sample G) : EdgeSet n := by
  classical
  exact (graphEdges G).filter fun f =>
    (∀ v, v ∈ e → v ∉ f) ∧ (∃ hf : f ∈ G.edgeSet, b ≤ w.1 ⟨f,hf⟩) ∧
    ((∀ v, v ∈ f → v ∈ Yset h) ∨
      ∃ x y, f = s(x,y) ∧ x ∈ otherX G a h e w ∧ y ∈ Yset h)

def augmented {n : ℕ} (G : SimpleGraph (Fin n)) (a b : ℝ) (h : History n)
    (e : Edge n) (w : Sample G) : EdgeSet n := by
  classical
  exact background G a b h e w ∪ ((graphEdges G).filter fun f =>
    (∃ hf : f ∈ G.edgeSet, b ≤ w.1 ⟨f,hf⟩) ∧
    ∃ x y, f = s(x,y) ∧ x ∈ e ∧ y ∈ Yset h)

def coupledRun {n : ℕ} (G : SimpleGraph (Fin n)) (F : EdgeSet n) (w : Sample G) : EdgeSet n := by
  classical
  exact greedy (((orderedEdges G w.1).map Subtype.val).filter fun f => f ∈ F)

/-- Conditioning on a finite-valued background uses positive-mass event restriction.
Exact shadow histories use residualLaw, not division by a zero-probability history event. -/
def backgroundLaw {n : ℕ} (G : SimpleGraph (Fin n)) (a b p : ℝ) (h : History n)
    (e : Edge n) (B : EdgeSet n) : Measure (Sample G) :=
  let ν := conditionalLaw G b p h
  (ν {w | background G a b h e w = B})⁻¹ • ν.restrict {w | background G a b h e w = B}

def coupledScore {n : ℕ} (G : SimpleGraph (Fin n)) (M : EdgeSet n) (a b : ℝ)
    (h : History n) (e : Edge n) (w : Sample G) : ℝ :=
  let MB := coupledRun G (background G a b h e w) w
  let ME := coupledRun G (augmented G a b h e w) w
  3 * count (covered {e}) ME + 2 * count (references M h e) ME + count (references M h e) MB

end
end FengLiYangMatching.General


