-- Prove2me | Definitions.Def_PolynomialSampling137_OneThird_Supplement_FlatSources
-- name    : PolynomialSampling137_OneThird_Supplement_FlatSources
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T07:44:53.930618+00:00
-- url     : https://prove2.me/theorems/14a2cf6b-c0ba-4bd9-925c-00290fdb0e3c
-- title:
--   Flat laws, actual polynomial sources and affine support geometry
-- statement:
--   A probability mass function on a finite carrier is nonnegative and sums to one; a subprobability has total mass at most one. A law is flat of entropy $k$ bits if it is uniform on a set of $2^k$ distinct words. Supported measures vanish outside the specified set. Polynomial sources are exactly the fiber-counting laws of coordinatewise degree-at-most-$d$ maps from a uniform finite binary seed, with no bound on seed length.
--
--   $$\mathcal O_d(\pi)=\sup_{s,Q:\deg Q_i\le d}\sum_y\min\{P_Q(y),\pi(y)\},\quad L(a,d)=\sum_{j=0}^{\min(a,d)}\binom aj,\quad\beta(a,d)=2^{-a}L(a,d).$$
--
--   Minimum degree $e$ means exact membership at degree $e$ and nonmembership at every smaller degree. The no-short-even-relation predicate forbids nonempty even-cardinality subsets with zero binary sum, up to the stated size. Affine independence is linear independence of the augmented vectors $(1,y)$. These definitions describe source and support objects independently of any estimate. The real supremum is used only for probability targets, for which its defining set is nonempty and bounded in $[0,1]$.
-- source:
--   Yan Zhong, Exponential Sampling Lower Bounds for Polynomial Sources, STOC 2027 submission #137 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/137.pdf, §§2.1, 4.1, 4.5, printed pp. 7–8, 14–15, 19–20; PDF pp. 9–10, 16–17, 21–22

import Definitions.Def_PolynomialSampling137_OneThird_FiniteProbability
import Definitions.Def_PolynomialSampling137_OneThird_BooleanSources

noncomputable section

namespace PolynomialSampling137.OneThird.Supplement

/-- Genuine finite probability masses, allowing zeros. -/
def IsLaw {α : Type*} [Fintype α] (P : α → ℝ) : Prop :=
  (∀ y, 0 ≤ P y) ∧ ∑ y, P y = 1

def IsSubprobability {α : Type*} [Fintype α] (ν : α → ℝ) : Prop :=
  (∀ y, 0 ≤ ν y) ∧ ∑ y, ν y ≤ 1

def SupportedOn {α : Type*} (P : α → ℝ) (T : Set α) : Prop :=
  ∀ y, y ∉ T → P y = 0

def UniformOn {α : Type*} [DecidableEq α] (T : Finset α) (y : α) : ℝ :=
  if y ∈ T then (T.card : ℝ)⁻¹ else 0

def Flat {n : ℕ} (k : ℕ) (P : Word n → ℝ) : Prop :=
  ∃ T : Finset (Word n), T.card = 2 ^ k ∧ P = UniformOn T

def MapDegreeLE {s n : ℕ} (d : ℕ) (Q : Word s → Word n) : Prop :=
  ∀ i, DegreeLE d (fun x => Q x i)

/-- Actual sampler laws; the seed dimension is existential and unrestricted. -/
def PolySources (d n : ℕ) : Set (Word n → ℝ) :=
  {P | ∃ (s : ℕ) (Q : Word s → Word n), MapDegreeLE d Q ∧ P = samplerMass Q}

/-- For a probability target this set is nonempty and contained in [0,1]. -/
def BestOverlap {n : ℕ} (d : ℕ) (P : Word n → ℝ) : ℝ :=
  sSup {w | ∃ μ ∈ PolySources d n, w = overlap μ P}

/-- Exact minimum, stated without a default-valued natural infimum. -/
def MinimumDegree {n : ℕ} (e : ℕ) (P : Word n → ℝ) : Prop :=
  P ∈ PolySources e n ∧ ∀ d < e, P ∉ PolySources d n

def NoShortEvenRelation {n : ℕ} (T : Set (Word n)) (b : ℕ) : Prop :=
  ∀ A : Finset (Word n), (↑A : Set (Word n)) ⊆ T →
    A.Nonempty → Even A.card → A.card ≤ b → ∑ y ∈ A, y ≠ 0

/-- Augmentation uses an extra coordinate, before all of the old coordinates. -/
def Augment {n : ℕ} (y : Word n) : Option (Fin n) → ZMod 2 :=
  fun i => match i with | none => 1 | some j => y j

def AffinelyIndependent {n : ℕ} (T : Set (Word n)) : Prop :=
  LinearIndependent (ZMod 2) (fun y : T => Augment y.val)

def MonomialCount (a d : ℕ) : ℕ :=
  ∑ j ∈ Finset.range (min a d + 1), a.choose j

def BinomialTail (a d : ℕ) : ℝ := (2 : ℝ) ^ (-(a : ℤ)) * MonomialCount a d

def CollisionExponent (d : ℕ) : ℕ := 2 ^ (d + 1) - d - 1

/-- Push-forward of the uniform law, on arbitrary finite nonempty seed carriers. -/
def UniformImage {α β : Type*} [Fintype α] [DecidableEq β]
    (f : α → β) (y : β) : ℝ :=
  uniformAverage (fun x => if f x = y then 1 else 0)

end PolynomialSampling137.OneThird.Supplement


