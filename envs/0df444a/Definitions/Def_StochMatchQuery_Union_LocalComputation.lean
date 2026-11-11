-- Prove2me | Definitions.Def_StochMatchQuery_Union_LocalComputation
-- name    : StochMatchQuery_Union_LocalComputation
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T20:07:44.483219+00:00
-- url     : https://prove2.me/theorems/031af31c-7984-4842-a1a1-d27925cced9b
-- title:
--   Adaptive local computations and the radii (3.2), (5.4)–(5.6)
-- statement:
--   A local computation is a terminating adaptive decision tree. Its nodes read a named edge indicator from an endpoint or read a vertex seed; subsequent branches depend on the answer. Only present edges already read may join the root to a newly reached vertex. An edge read is legal only from a reached endpoint, and a seed read only at a reached vertex, within the prescribed radius. Seeds have arbitrary measurable probability laws and their joint law is the independent product. One global matching supplies all vertex answers.
--   $$L=\lceil4/h\rceil,\ \ell=2L+1,\ d=4(\ell+1)^4(D+1)^{\ell+2},\ t=\frac1{4(d+1)},\ k=\lceil t^{-1}\log(2/h)\rceil,\ R=k(4\ell+4).$$
--   The bundle additionally defines trimming and the exact degree, radius, and covariance constants of §5. It assumes no marginal, locality, or covariance theorem.
-- source:
--   Mahsa Derakhshan, Andisheh Ghasemi, Tao Yu, STOC 2027 submission #394 (October 2026), Lemma 3.1, pp.11–12; Lemma 4.1, p.21; Lemma 5.1, pp.23–24. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/394.pdf

import Definitions.Def_StochMatchQuery_Union_Algorithm1

open MeasureTheory ProbabilityTheory ProphetMatchingEFGT

namespace StochMatchQuery.Union
noncomputable section
open Classical
variable {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- A walk in S, with a length bound. Zero steps reach precisely the start. -/
def Reached (S : Realization G) (root v : V) (R : ℕ) : Prop :=
  ∃ n ≤ R, ∃ path : Fin (n+1) → V, path 0 = root ∧ path (Fin.last n) = v ∧
    ∀ i : Fin n, ∃ e ∈ S, path i.castSucc ∈ (e : Sym2 V) ∧
      path i.succ ∈ (e : Sym2 V) ∧ path i.castSucc ≠ path i.succ

/-- A well-founded adaptive decision tree. Branching on vertex randomness may be continuous.
Every execution is finite, with no uniform bound on the number of inspections required. -/
inductive DecisionTree (α : V → Type) (B : Type) where
  | leaf : B → DecisionTree α B
  | edge : V → Edge G → (Bool → DecisionTree α B) → DecisionTree α B
  | vertex : (v : V) → (α v → DecisionTree α B) → DecisionTree α B

variable {G}

def DecisionTree.run {α : V → Type} {B : Type} (F : Realization G) (ξ : (v : V) → α v) :
    DecisionTree G α B → B
  | .leaf b => b
  | .edge _ e next => (next (decide (e ∈ F))).run F ξ
  | .vertex v next => (next (ξ v)).run F ξ

/-- Legality along the actual execution, with the present edges inspected so far.
Absent edges never enter the reached graph. The edge's inspection endpoint is explicit. -/
def DecisionTree.legal {α : V → Type} {B : Type} (root : V) (R : ℕ)
    (F : Realization G) (ξ : (v : V) → α v) (seen : Realization G) : DecisionTree G α B → Prop
  | .leaf _ => True
  | .edge v e next => v ∈ (e : Sym2 V) ∧ Reached G seen root v R ∧
      (next (decide (e ∈ F))).legal root R F ξ (if e ∈ F then insert e seen else seen)
  | .vertex v next => Reached G seen root v R ∧ (next (ξ v)).legal root R F ξ seen

/-- The sequential list of inspected coordinate names, including repeated reads. -/
def DecisionTree.inspections {α : V → Type} {B : Type}
    (F : Realization G) (ξ : (v : V) → α v) : DecisionTree G α B → List (Edge G ⊕ V)
  | .leaf _ => []
  | .edge _ e next => Sum.inl e :: (next (decide (e ∈ F))).inspections F ξ
  | .vertex v next => Sum.inr v :: (next (ξ v)).inspections F ξ

variable (G)

/-- Actual computation semantics, not a certificate or an assumed covariance bound. -/
def ComputesLocally {α : V → Type} [(v : V) → MeasurableSpace (α v)]
    {B : Type} [MeasurableSpace B] (R : ℕ)
    (out : Realization G → ((v : V) → α v) → V → B) : Prop :=
  ∃ trees : V → DecisionTree G α B,
    (∀ v (l : List (Edge G ⊕ V)), MeasurableSet {z : Realization G × ((v : V) → α v) |
      (trees v).inspections z.1 z.2 = l}) ∧
    (∀ v, Measurable (fun z : Realization G × ((v : V) → α v) =>
      (trees v).run z.1 z.2)) ∧
    ∀ F ξ v, (trees v).legal v R F ξ ∅ ∧ (trees v).run F ξ = out F ξ v

/-- Vertex seeds are arbitrary measurable probability spaces. This includes finite vectors
of real uniforms; no finite-alphabet restriction is imposed. -/
structure VertexLaw (V : Type) where
  carrier : V → Type
  measurable : (v : V) → MeasurableSpace (carrier v)
  law : (v : V) → @Measure (carrier v) (measurable v)
  probability : ∀ v, @IsProbabilityMeasure (carrier v) (measurable v) (law v)

attribute [instance] VertexLaw.measurable VertexLaw.probability

def VertexLaw.joint (ν : VertexLaw V) : Measure ((v : V) → ν.carrier v) := Measure.pi ν.law

/-- One global matching, whose answer at v is the set of its edges incident at v. -/
def LocalMatching (R : ℕ) (ν : VertexLaw V)
    (alg : Realization G → ((v : V) → ν.carrier v) → Realization G) : Prop :=
  Measurable (Function.uncurry alg) ∧
  (∀ F ξ, alg F ξ ⊆ F ∧ IsMatching G (alg F ξ)) ∧
  ComputesLocally G R (fun F ξ v => incident G (alg F ξ) v)

/-- Exact constants (3.2), with natural logarithm and real divisions. -/
def cutPeriod (h : ℝ) : ℕ := ⌈4/h⌉₊
def pieceLength (h : ℝ) : ℕ := 2 * cutPeriod h + 1
def conflictBound (D : ℕ) (h : ℝ) : ℕ :=
  4 * (pieceLength h + 1)^4 * (D+1)^(pieceLength h + 2)
def roundRate (D : ℕ) (h : ℝ) : ℝ := 1 / (4 * ((conflictBound D h : ℝ) + 1))
def roundCount (D : ℕ) (h : ℝ) : ℕ := ⌈(roundRate D h)⁻¹ * Real.log (2/h)⌉₊
def localRadius (D : ℕ) (h : ℝ) : ℕ := roundCount D h * (4 * pieceLength h + 4)
def trimDegree (s h : ℝ) : ℕ := ⌈2 / (h*s^2)⌉₊ + 2
def rawRadius (s h : ℝ) : ℕ := localRadius (trimDegree s h) h + 2
def covarianceBound (s h : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (2 * rawRadius s h + 2), (2/s)^j

def trim (D : ℕ) (F : Realization G) : Realization G :=
  F.filter (fun e => ∀ v, v ∈ (e : Sym2 V) → degree G F v ≤ D)
end
end StochMatchQuery.Union


