-- Prove2me | Definitions.Def_FlowOptimalSeparators_MinorFree_AlgorithmOutputs
-- name    : FlowOptimalSeparators_MinorFree_AlgorithmOutputs
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T00:07:52.625338+00:00
-- url     : https://prove2.me/theorems/ede8a728-63c8-435f-9537-b78631959ef4
-- title:
--   Section 6 algorithm inputs and all output alternatives
-- statement:
--   Section 6.1 uses symmetric edge lengths in $(0,1]$ and $b=n/(8h^2)$. The ball-or-pair output is either a centre $x$ satisfying $|B(x,11)|>b$ or disjoint sets $A,B$ satisfying
--   $$|A|,|B|\ge b,\qquad d(A,B)>1.$$
--   A prefix output is either such a centre or an index $1\le t\le |Y|$ with $b<|B(Y_t,4)|\le3b$.
--
--   For positive integer vertex weights, distances use edge length $(w(u)+w(v))/2$. GROW is given these distances in its input, with explicit flags for infinity, and returns $X\subseteq R\subseteq B(X,2\delta)$ with
--   $$|\partial R|\le\delta^{-1}\ln\frac{w(V)}{w(X)}\,w(R).$$
--   CUTORCLUSTER returns a tagged cluster or separator; both vertex masks are decoded from actual output memory. The cluster uses full vertex-path sums, while the separator size is bounded by $C W\ln(hW/n)/D$. No valid outcome or candidate solution is supplied as input.
-- source:
--   Hung Le, Jack Spalding-Jamieson, STOC 2027 submission #1211 (October 2026), p. 14, 22–25, Theorem 7; Lemmas 7–9

import Mathlib
import Definitions.Def_FlowOptimalSeparators_MinorFree_SeparatorOutput
import Definitions.Def_FlowOptimalSeparators_MinorFree_ShortestPaths

open scoped ENNReal
set_option autoImplicit false

namespace FlowOptimalSeparators.MinorFree

/-- Data for Section 6.1. Positivity, symmetry and the upper bound are genuine metric conditions. -/
def ValidLengths {n : ℕ} (G : Graph n) (ℓ : Fin n → Fin n → ℝ) : Prop :=
  ∀ u v, G.Adj u v → 0 < ℓ u v ∧ ℓ u v ≤ 1 ∧ ℓ u v = ℓ v u

noncomputable def edgeMetric {n : ℕ} (ℓ : Fin n → Fin n → ℝ) :
    Fin n → Fin n → ℝ≥0∞ := fun u v => ENNReal.ofReal (ℓ u v)

noncomputable def edgeInput {n : ℕ} {G : Graph n} (A : AdjacencyInput G)
    (ℓ : Fin n → Fin n → ℝ) : List ℝ :=
  (List.finRange n).flatMap fun u => (A.rows u).map (ℓ u)

noncomputable def maskAt (n off : ℕ) (s : VehicleRoutingSurvey.Routing.ArithmeticState) :
    Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun v => s.nm (off + v.val) = 1)

def IsMaskAt (n off : ℕ) (s : VehicleRoutingSurvey.Routing.ArithmeticState) : Prop :=
  ∀ v : Fin n, s.nm (off + v.val) ≤ 1

noncomputable def threshold (n h : ℕ) : ℝ := (n : ℝ) / (8 * (h : ℝ) ^ 2)

/-- Output tag 0: a centre. Tag 1: two explicit bit masks. -/
noncomputable def BallOrPairOutput {n : ℕ} (G : Graph n)
    (ℓ : Fin n → Fin n → ℝ) (h : ℕ)
    (s : VehicleRoutingSurvey.Routing.ArithmeticState) : Prop :=
  (s.nr 0 = 0 ∧ ∃ x : Fin n, s.nr 1 = x.val ∧
    threshold n h < ((ball G (edgeMetric ℓ) {x} 11).card : ℝ)) ∨
  (s.nr 0 = 1 ∧ IsMaskAt n 1 s ∧ IsMaskAt n (n + 1) s ∧
    Disjoint (maskAt n 1 s) (maskAt n (n + 1) s) ∧
    threshold n h ≤ ((maskAt n 1 s).card : ℝ) ∧
    threshold n h ≤ ((maskAt n (n + 1) s).card : ℝ) ∧
    (1 : ℝ≥0∞) < setDistance G (edgeMetric ℓ) (maskAt n 1 s) (maskAt n (n + 1) s))

noncomputable def PrefixOutput {n : ℕ} (G : Graph n)
    (ℓ : Fin n → Fin n → ℝ) (h : ℕ) (Y : List (Fin n))
    (s : VehicleRoutingSurvey.Routing.ArithmeticState) : Prop :=
  (s.nr 0 = 0 ∧ ∃ x : Fin n, s.nr 1 = x.val ∧
    threshold n h < ((ball G (edgeMetric ℓ) {x} 11).card : ℝ)) ∨
  (s.nr 0 = 1 ∧ 1 ≤ s.nr 1 ∧ s.nr 1 ≤ Y.length ∧
    threshold n h < ((ball G (edgeMetric ℓ) (Y.take (s.nr 1)).toFinset 4).card : ℝ) ∧
    ((ball G (edgeMetric ℓ) (Y.take (s.nr 1)).toFinset 4).card : ℝ) ≤ 3 * threshold n h)

noncomputable def growInputN {n : ℕ} {G : Graph n} (A : AdjacencyInput G)
    (X : Finset (Fin n)) (w : Fin n → ℕ) : List ℕ :=
  A.encode 0 ++ (List.finRange n).map (fun v => if v ∈ X then 1 else 0) ++
    (List.finRange n).map (fun v =>
      if (⨅ x ∈ X, distance G (vertexMetric (fun u => (w u : ℝ))) x v) = ⊤ then 0 else 1)

/-- Distances supplied as input; flags in growInputN distinguish infinity from finite zero. -/
noncomputable def growInputR {n : ℕ} (G : Graph n) (X : Finset (Fin n))
    (w : Fin n → ℕ) (δ : ℝ) : List ℝ :=
  [δ] ++ (List.finRange n).map (fun v => (w v : ℝ)) ++
    (List.finRange n).map (fun v =>
      (⨅ x ∈ X, distance G (vertexMetric (fun u => (w u : ℝ))) x v).toReal)

noncomputable def GrowOutput {n : ℕ} (G : Graph n) (X : Finset (Fin n))
    (w : Fin n → ℕ) (δ : ℝ) (s : VehicleRoutingSurvey.Routing.ArithmeticState) : Prop :=
  IsVertexMask n s ∧ X ⊆ outputSet n s ∧
    outputSet n s ⊆ ball G (vertexMetric (fun u => (w u : ℝ))) X (2 * δ) ∧
    ((boundary G (outputSet n s)).card : ℝ) ≤
      δ⁻¹ * Real.log ((∑ v, (w v : ℝ)) / ∑ v ∈ X, (w v : ℝ)) *
        ∑ v ∈ outputSet n s, (w v : ℝ)

/-- Separate output tag distinguishes a cluster from a balanced separator. -/
noncomputable def CutOrClusterOutput {n : ℕ} (G : Graph n) (w : Fin n → ℕ)
    (h : ℕ) (D C : ℝ) (s : VehicleRoutingSurvey.Routing.ArithmeticState) : Prop :=
  IsVertexMask n s ∧
    ((s.nr 0 = 0 ∧ Cluster G (fun v => (w v : ℝ)) D (outputSet n s)) ∨
     (s.nr 0 = 1 ∧ Balanced G (outputSet n s) ∧
      ((outputSet n s).card : ℝ) ≤
        C * (∑ v, (w v : ℝ)) * Real.log ((h : ℝ) * (∑ v, (w v : ℝ)) / n) / D))

end FlowOptimalSeparators.MinorFree


