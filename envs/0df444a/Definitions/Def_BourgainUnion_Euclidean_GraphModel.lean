-- Prove2me | Definitions.Def_BourgainUnion_Euclidean_GraphModel
-- name    : BourgainUnion_Euclidean_GraphModel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:25:44.606837+00:00
-- url     : https://prove2.me/theorems/eabbde67-4554-4cb4-b513-cb7faa5d0534
-- title:
--   Finite graph energies, computed elimination and the heat matrix
-- statement:
--   The imported general weighted graph has real nonnegative symmetric weights $g_{xy}$. The paper-specific condition is $g_{xx}=0$; isolated vertices and disconnected graphs are allowed. For a finite set $S$, the quadratic energy and crossing energy are
--   $$E_G(d^2;S)=\tfrac12\sum_{x,y\in S}g_{xy}d(x,y)^2,\qquad J=\sum_{a\in A,b\in B}g_{ab}d(a,b)^2.$$
--   Map energy substitutes $\|F(x)-F(y)\|$ for $d(x,y)$.
--
--   Removing a nonisolated vertex $v$ adds $g_{xv}g_{yv}/\delta_v$ to each distinct surviving pair, where $\delta_v=\sum_zg_{vz}>0$. An isolated vertex is deleted without division. Iteration along a fixed enumeration of the complement computes $G^A$. The predicate describing its Dirichlet property includes nonnegative symmetric weights supported on $A$, and an attained minimum of extension energies for every prescribed map; Lemma 4.4 proves that predicate and order independence.
--
--   A fixed partition defines $\mathcal D$, the class of pseudometrics that are Euclidean on each part. The cost $\operatorname{min-ext}_{\mathcal D}(\rho,G)$ is the extended nonnegative infimum over members of this class agreeing with $\rho$ on the terminals, so an empty admissible class costs infinity. The nonnormalized Laplacian $L$, positive diagonal matrix $C=\operatorname{diag}(s)$ and heat matrix are computed as
--   $$P(t)=\exp(-tC^{-1}L).$$
--   These definitions specify the actual graphs, admissible metrics and semigroups needed by the energy lemmas, without imposing their conclusions as axioms.
-- source:
--   Dimitar Chakarov, Sepideh Mahabadi, Yury Makarychev, Ali Vakilian, Bourgain's Theorem for a Union of Euclidean Metric Spaces, STOC 2027 submission #699 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/699.pdf, PDF = printed p. 12–16, §§4.1–4.3, equations (3), (6)–(8)

import Mathlib
import Definitions.Def_BourgainUnion_Euclidean_EmbeddingModel
import Definitions.Def_ClusterDecomp_WGraph
import Definitions.Def_GeometryOfGraphs_FlowCut_Pseudometric

set_option autoImplicit false
open scoped BigOperators ENNReal
noncomputable section

namespace BourgainUnion.Euclidean

/-- The published general graph object is refined by the source's zero diagonal. -/
def Loopless {X : Type*} (G : ClusterDecomp.WGraph X) : Prop := ∀ x, G.w x x = 0

/-- Half the ordered sum counts each unordered pair once; the diagonal is zero. -/
def energy {X : Type*} [Fintype X] (w d : X → X → ℝ) (S : Finset X) : ℝ :=
  (1/2) * ∑ x ∈ S, ∑ y ∈ S, w x y * (d x y)^2

def mapEnergy {X : Type*} [Fintype X] (w : X → X → ℝ) (f : X → H2)
    (S : Finset X) : ℝ := energy w (fun x y => dist (f x) (f y)) S

def crossing {X : Type*} [Fintype X] (w d : X → X → ℝ) (A B : Finset X) : ℝ :=
  ∑ a ∈ A, ∑ b ∈ B, w a b * (d a b)^2

/-- Section 4.2's computed single-vertex update, with isolated vertices deleted. -/
def eliminate {X : Type*} [Fintype X] [DecidableEq X]
    (w : X → X → ℝ) (S : Finset X) (v : X) : X → X → ℝ :=
  fun x y => if x ∈ S.erase v ∧ y ∈ S.erase v ∧ x ≠ y then
    w x y + (if 0 < ∑ z ∈ S, w v z then w x v * w y v / (∑ z ∈ S, w v z) else 0)
  else 0

def eliminateList {X : Type*} [Fintype X] [DecidableEq X]
    (w : X → X → ℝ) (S : Finset X) : List X → X → X → ℝ
  | [] => fun x y => if x ∈ S ∧ y ∈ S then w x y else 0
  | v :: vs => eliminateList (eliminate w S v) (S.erase v) vs

def canonical {X : Type*} [Fintype X] [DecidableEq X]
    (w : X → X → ℝ) (A : Finset X) : X → X → ℝ :=
  eliminateList w Finset.univ (Finset.univ \ A).toList

/-- Existence and attainment belong to Lemma 4.4, not to the computed graph definition. -/
def DirichletGraph {X : Type*} [Fintype X] (w h : X → X → ℝ) (A : Finset X) : Prop :=
  (∀ x y, 0 ≤ h x y) ∧ (∀ x y, h x y = h y x) ∧ (∀ x, h x x = 0) ∧
  (∀ x y, x ∉ A ∨ y ∉ A → h x y = 0) ∧
  ∀ f : X → H2, ∃ F : X → H2, Set.EqOn F f (A : Set X) ∧
    mapEnergy w F Finset.univ = mapEnergy h f A ∧
    ∀ F' : X → H2, Set.EqOn F' f (A : Set X) →
      mapEnergy h f A ≤ mapEnergy w F' Finset.univ

def RawEuclidean {X : Type*} (d : X → X → ℝ) (A : Set X) : Prop :=
  ∃ f : X → H2, ∀ x ∈ A, ∀ y ∈ A, dist (f x) (f y) = d x y

/-- Fixed nonempty disjoint partition, as in Section 4.1. -/
def Partition {X : Type*} {k : ℕ} (U : Fin k → Set X) : Prop :=
  Covers U ∧ (∀ i, (U i).Nonempty) ∧
    ∀ i j, i ≠ j → Disjoint (U i) (U j)

def MetricClass {X : Type*} {k : ℕ} (U : Fin k → Set X) (d : X → X → ℝ) : Prop :=
  GeometryOfGraphs.FlowCut.IsPseudometric d ∧ ∀ i, RawEuclidean d (U i)

/-- Equation (3), in extended nonnegative reals (empty admissible set gives infinity). -/
def minExt {X : Type*} [Fintype X] {k : ℕ} (U : Fin k → Set X)
    (A : Finset X) (ρ w : X → X → ℝ) : ℝ≥0∞ :=
  sInf {q | ∃ d : X → X → ℝ, MetricClass U d ∧
    (∀ x ∈ A, ∀ y ∈ A, d x y = ρ x y) ∧
    q = ENNReal.ofReal (energy w d Finset.univ)}

/-- Actual nonnormalized Laplacian, positive diagonal C, and exp(-t C^-1 L). -/
def laplacian {B : Type*} [Fintype B] [DecidableEq B]
    (w : B → B → ℝ) : Matrix B B ℝ :=
  fun b c => if b = c then ∑ j, w b j else -w b c

def heatMatrix {B : Type*} [Fintype B] [DecidableEq B]
    (w : B → B → ℝ) (s : B → ℝ) (t : ℝ) : Matrix B B ℝ :=
  NormedSpace.exp ((-t) • ((Matrix.diagonal (fun b => (s b)⁻¹)) * laplacian w))

end BourgainUnion.Euclidean


