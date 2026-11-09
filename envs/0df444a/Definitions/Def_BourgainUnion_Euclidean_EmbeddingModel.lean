-- Prove2me | Definitions.Def_BourgainUnion_Euclidean_EmbeddingModel
-- name    : BourgainUnion_Euclidean_EmbeddingModel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:25:07.454205+00:00
-- url     : https://prove2.me/theorems/4559f1c7-7cf5-4a54-9344-9031b6c80c45
-- title:
--   Euclidean subsets, normalized ℓ₂ distortion, covers and terminal maps
-- statement:
--   Let $(X,d)$ be a metric or pseudometric space. The target $H_2$ is the real Hilbert space of square-summable sequences. A subset $A\subseteq X$ is Euclidean when its induced distances admit an isometric realization in $H_2$; no closure, boundedness, convexity or dimension restriction is imposed. It is one-point strongly Euclidean when $A$ is Euclidean and $A\cup\{x\}$ is Euclidean for every $x\in X$. A family $U_1,\ldots,U_k$ covers $X$ when every point belongs to some member; members may overlap.
--
--   A normalized embedding $f:X\to H_2$ of factor $D$ satisfies
--   $$D\ge1,\qquad d(x,y)\le\|f(x)-f(y)\|\le Dd(x,y)\quad(x,y\in X).$$
--   Its admissible factors define $c_2(X)$ by an extended nonnegative infimum, equal to infinity when there is no finite-distortion embedding. Empty and singleton spaces have factor one. A $D$-terminal embedding for a nonempty set $A$ is globally $1$-Lipschitz and satisfies
--   $$\|f(u)-f(x)\|\ge d(u,x)/D\qquad(u\in A,\ x\in X).$$
--   The shared predicate $\mathrm{CombinationConstant}(C)$ says that every finite nonempty terminal cover with factor $D$ admits a normalized embedding of factor at most $CD\log(k+1)$. This predicate states a bound to be established by Theorem 2.7; no such bound is built into the space or cover. These definitions provide the common interface for the goal and extension comparisons.
-- source:
--   Dimitar Chakarov, Sepideh Mahabadi, Yury Makarychev, Ali Vakilian, Bourgain's Theorem for a Union of Euclidean Metric Spaces, STOC 2027 submission #699 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/699.pdf, PDF = printed p. 2, 5–6, §1.1, equation (1), Definition 2.3

import Mathlib

set_option autoImplicit false
open scoped BigOperators ENNReal
noncomputable section

namespace BourgainUnion.Euclidean

/-- Real square-summable sequences; infinite-dimensional separable Hilbert target (§1.1). -/
abbrev H2 := lp (fun _ : ℕ => ℝ) 2

/-- Equation (1), with the conventional factor at least one even on a singleton. -/
def Normalized {X : Type*} [PseudoMetricSpace X] (D : ℝ) (f : X → H2) : Prop :=
  1 ≤ D ∧ ∀ x y, dist x y ≤ dist (f x) (f y) ∧ dist (f x) (f y) ≤ D * dist x y

def Embeds {X : Type*} [PseudoMetricSpace X] (D : ℝ) : Prop :=
  ∃ f : X → H2, Normalized D f

/-- A subset with its induced metric; no linearity, boundedness or closure condition. -/
def IsEuclidean {X : Type*} [PseudoMetricSpace X] (A : Set X) : Prop :=
  ∃ f : A → H2, Isometry f

def OneStrong {X : Type*} [PseudoMetricSpace X] (A : Set X) : Prop :=
  IsEuclidean A ∧ ∀ x : X, IsEuclidean (A ∪ {x})

def Covers {X : Type*} {k : ℕ} (U : Fin k → Set X) : Prop :=
  ∀ x, ∃ i, x ∈ U i

/-- Infinite distortion is represented by top, never the real infimum's default zero. -/
def c2 (X : Type*) [PseudoMetricSpace X] : ℝ≥0∞ :=
  sInf {q | ∃ D : ℝ, Embeds (X := X) D ∧ q = ENNReal.ofReal D}

/-- Lipschitz control restricted to a subset; values elsewhere are irrelevant. -/
def LipOn {X : Type*} [PseudoMetricSpace X] {H : Type*} [PseudoMetricSpace H]
    (L : ℝ) (f : X → H) (A : Set X) : Prop :=
  ∀ x ∈ A, ∀ y ∈ A, dist (f x) (f y) ≤ L * dist x y

def Terminal {X : Type*} [PseudoMetricSpace X] (A : Set X) (D : ℝ) (f : X → H2) : Prop :=
  A.Nonempty ∧ 1 ≤ D ∧ LipOn 1 f Set.univ ∧
    ∀ u ∈ A, ∀ x, dist u x / D ≤ dist (f u) (f x)

/-- The terminal combination constant is shared by subsequent comparison statements. -/
def CombinationConstant (C : ℝ) : Prop :=
  ∀ (X : Type) [MetricSpace X] (k : ℕ), 1 ≤ k →
    ∀ (U : Fin k → Set X) (D : ℝ), Covers U → 1 ≤ D →
      (∀ i, ∃ f : X → H2, Terminal (U i) D f) →
      ∃ d : ℝ, d ≤ C * D * Real.log (k + 1) ∧ Embeds (X := X) d

end BourgainUnion.Euclidean


