-- Prove2me | Definitions.Def_BourgainUnion_Euclidean_VoronoiModel
-- name    : BourgainUnion_Euclidean_VoronoiModel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:25:46.622177+00:00
-- url     : https://prove2.me/theorems/96f8a9fe-d5f1-4a48-9de1-c6d0a65e741c
-- title:
--   Two-sided collapse constants and the constructed Voronoi map
-- statement:
--   The predicate $\mathrm{CollapseConstants}(a,b)$ records the same positive constants for every nonempty subset $S$ of every separable real Hilbert space $H$. It asks for a map $\psi:H\to H_2$, vanishing on $S$, whose distances lie between $a$ and $b$ times
--   $$\min\{\|x-y\|,\operatorname{dist}(x,S)+\operatorname{dist}(y,S)\}.$$
--   The hyperplane version uses $\min\{\|u-v\|+|h-j|,h+j\}$ at nonnegative heights.
--
--   For nonempty subsets $V_i\subseteq X$ and maps $\phi_i:X\to H_2$, define $R_i(x)=\operatorname{dist}(x,V_i)$, $\widehat R_i(x)=\min_{j\ne i}R_j(x)$, the strict nearest-set cell $N_i=\{x:R_i(x)<R_j(x)\text{ for all }j\ne i\}$, and $\Delta_i(x)=\max\{(\widehat R_i(x)-R_i(x))/2,0\}$. For $r>1$ the actual map is
--   $$f(x)=\bigoplus_{2,i}\psi(\phi_i(x),\Delta_i(x)).$$
--   For $r=1$ it is the single terminal map, with no evaluation of an infinite height or empty real infimum. The separate gap expression then uses $d(x,y)/(2D)-R_1(x)$. Ties belong to no strict cell and all corresponding components vanish. The direct-sum target is a finite Hilbert sum of copies of $H_2$, isometric to $H_2$ when $r\ge1$. This construction, rather than an arbitrary map satisfying desired estimates, is used in Theorem 2.6.
-- source:
--   Dimitar Chakarov, Sepideh Mahabadi, Yury Makarychev, Ali Vakilian, Bourgain's Theorem for a Union of Euclidean Metric Spaces, STOC 2027 submission #699 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/699.pdf, PDF = printed p. 5, 7–9, Lemma 2.1, Corollary 2.2 and §2.3

import Mathlib
import Definitions.Def_BourgainUnion_Euclidean_EmbeddingModel

set_option autoImplicit false
open scoped BigOperators ENNReal
noncomputable section

namespace BourgainUnion.Euclidean

/-- The uniform two-sided Kirszbraun constants, including finite and infinite dimensions. -/
def CollapseConstants (a b : ℝ) : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
    (S : Set H), S.Nonempty → ∃ ψ : H → H2,
      (∀ x ∈ S, ψ x = 0) ∧ ∀ x y,
        a * min (dist x y) (Metric.infDist x S + Metric.infDist y S) ≤ dist (ψ x) (ψ y) ∧
        dist (ψ x) (ψ y) ≤ b * min (dist x y) (Metric.infDist x S + Metric.infDist y S)

/-- The corollary's l1 expression on nonnegative heights. -/
def HyperplaneCollapse {H : Type*} [NormedAddCommGroup H]
    (a b : ℝ) (ψ : H → ℝ → H2) : Prop :=
  (∀ u, ψ u 0 = 0) ∧ ∀ u v h j, 0 ≤ h → 0 ≤ j →
    a * min (dist u v + |h-j|) (h+j) ≤ dist (ψ u h) (ψ v j) ∧
    dist (ψ u h) (ψ v j) ≤ b * min (dist u v + |h-j|) (h+j)

def radius {X : Type*} [PseudoMetricSpace X] {r : ℕ}
    (V : Fin r → Set X) (i : Fin r) (x : X) : ℝ := Metric.infDist x (V i)

/-- Used only when r>1; the index set is then finite and nonempty. -/
def otherRadius {X : Type*} [PseudoMetricSpace X] {r : ℕ}
    (V : Fin r → Set X) (i : Fin r) (x : X) : ℝ :=
  sInf {q | ∃ j : Fin r, j ≠ i ∧ q = radius V j x}

def cell {X : Type*} [PseudoMetricSpace X] {r : ℕ}
    (V : Fin r → Set X) (i : Fin r) : Set X :=
  {x | ∀ j, j ≠ i → radius V i x < radius V j x}

def height {X : Type*} [PseudoMetricSpace X] {r : ℕ}
    (V : Fin r → Set X) (i : Fin r) (x : X) : ℝ :=
  max ((otherRadius V i x - radius V i x) / 2) 0

/-- Section 2.3's actual direct sum, with the r=1 convention handled before heights. -/
def voronoiMap {X : Type*} [PseudoMetricSpace X] {r : ℕ}
    (V : Fin r → Set X) (φ : Fin r → X → H2) (ψ : H2 → ℝ → H2)
    (x : X) : PiLp 2 (fun _ : Fin r => H2) :=
  WithLp.toLp 2 (fun i => if r = 1 then φ i x else ψ (φ i x) (height V i x))

/-- The r=1 expression is the finite value min(q,infinity)-R=q-R. -/
def gap {X : Type*} [PseudoMetricSpace X] {r : ℕ}
    (V : Fin r → Set X) (D : ℝ) (i : Fin r) (x y : X) : ℝ :=
  (if r = 1 then dist x y / (2*D)
   else min (dist x y / (2*D)) (otherRadius V i x)) - radius V i x

end BourgainUnion.Euclidean


