-- Prove2me | Definitions.Def_MemOracleLB_Optimization_Partitions
-- name    : MemOracleLB_Optimization_Partitions
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:34:48.277519+00:00
-- url     : https://prove2.me/theorems/a22207a2-b9b7-4ae6-bf11-5d2fbbae6965
-- title:
--   Countable convex product partitions and deterministic decision trees
-- statement:
--   A countable convex product partition of $(\mathbb R^n)^m$ has factors $F_i(p)$, indexed by parts $p$, such that each factor is convex, the product parts are pairwise disjoint, and their union is the whole row space. Factors may be empty and need not be Borel. Part mass and family mass are computed under the original product of $N(0,I_n/n)$ row laws, with countable sums valued in $[0,\infty]$.
--
--   For a positive-measure part, localization around its unit vector $u(p)$ at radius $r$ means
--
--   $$\Pr(d_{\mathbb P}(v(A),u(p))\le r\mid A\in p)\ge1-\frac1{1024}.$$
--
--   The predicate for Lemma 1.5 includes every part of its conclusion: a retained subfamily of mass at least $\eta/2$ and the exponential upper bound on every retained part. It binds the localization constant used in Corollary 1.6.
--
--   A deterministic decision tree chooses a query from the response history, or stops. Its response map has a finite alphabet of size $b$. Reached leaf sets and their depths are computed from the actual queries and responses, and a leaf-partition predicate identifies those sets with the convex product parts. No upper bound on the number of shallow leaves is included as an assumption.
--
--   This interface permits countably many leaves and unrestricted query objects; the corollary uses $b=2n+1$.
-- source:
--   Santosh Vempala, STOC 2027 submission #365 (October 2026), §§1.3,3.1,3.3, PDF pp.4–6,12–13,19 (printed pp.3–5,11–12,18), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/365.pdf

import Mathlib
import Definitions.Def_MemOracleLB_Optimization_Probability

open MeasureTheory ProbabilityTheory
open scoped ENNReal RealInnerProductSpace
noncomputable section

namespace MemOracleLB.Optimization

/-- Countable convex product partition; empty factors and non-Borel convex factors are allowed. -/
structure ConvexProductPartition (ι : Type*) (m n : ℕ) where
  factor : ι → Fin m → Set (E n)
  convex_factor : ∀ p i, Convex ℝ (factor p i)
  disjoint_parts : Pairwise (fun p q => Disjoint (Set.pi Set.univ (factor p)) (Set.pi Set.univ (factor q)))
  covers : ∀ x : Fin m → E n, ∃ p, x ∈ Set.pi Set.univ (factor p)

def ConvexProductPartition.part {ι : Type*} {m n : ℕ}
    (P : ConvexProductPartition ι m n) (p : ι) : Set (Fin m → E n) :=
  Set.pi Set.univ (P.factor p)

def rowLaw (m n : ℕ) : Measure (Fin m → E n) := Measure.pi (fun _ => scaledGaussian n)

def ConvexProductPartition.mass {ι : Type*} {m n : ℕ}
    (P : ConvexProductPartition ι m n) (S : Set ι) : ℝ≥0∞ :=
  ∑' p : S, rowLaw m n (P.part p)

def ConvexProductPartition.partLaws {ι : Type*} {m n : ℕ}
    (P : ConvexProductPartition ι m n) (p : ι) : Fin m → Measure (E n) :=
  fun i => cond (scaledGaussian n) (P.factor p i)

/-- PDF pp.5,12: the localization hypothesis is imposed only on positive-measure parts. -/
def Localizes {ι : Type*} {m : ℕ} (P : ConvexProductPartition ι m (m + 1))
    (S : Set ι) (u : ι → E (m + 1)) (r : ℝ) : Prop :=
  ∀ p ∈ S, 0 < rowLaw m (m + 1) (P.part p) →
    ‖u p‖ = 1 ∧ 1 - 1 / 1024 ≤
      (cond (rowLaw m (m + 1)) (P.part p)).real
        {A | projectiveDistance (normal A) (u p) ≤ r}

/-- Full per-dimension conclusion of Lemma 1.5, so its constants can be bound in Corollary 1.6. -/
def LocalizingPartitionProperty (m : ℕ) (a c : ℝ) : Prop :=
  ∀ {ι : Type} [Countable ι] (P : ConvexProductPartition ι m (m + 1))
    (S : Set ι) (u : ι → E (m + 1)) (η : ℝ),
    0 < η → η < 1 → ENNReal.ofReal η ≤ P.mass S → Localizes P S u (c * η) →
    ∃ S' : Set ι, S' ⊆ S ∧ ENNReal.ofReal (η / 2) ≤ P.mass S' ∧
      ∀ p ∈ S', rowLaw m (m + 1) (P.part p) ≤
        ENNReal.ofReal (Real.exp (-a * (m + 1 : ℝ) ^ 2 / Real.log (m + 1)))

/-- General deterministic tree. Each node specifies a query or a terminal leaf;
only the b possible responses determine the next node. No leaf-count bound is assumed. -/
structure DecisionTree (α Q : Type*) (b : ℕ) where
  query : List (Fin b) → Option Q
  response : Q → α → Fin b

def DecisionTree.Reaches {α Q : Type*} {b : ℕ} (D : DecisionTree α Q b)
    (x : α) (h : List (Fin b)) : Prop :=
  ∀ k : Fin h.length, ∃ q, D.query (h.take k.val) = some q ∧ D.response q x = h[k]

def DecisionTree.leaf {α Q : Type*} {b : ℕ} (D : DecisionTree α Q b)
    (h : List (Fin b)) : Set α := {x | D.query h = none ∧ D.Reaches x h}

def DecisionTree.depth {α Q : Type*} {b : ℕ} (D : DecisionTree α Q b) (x : α) : ℕ∞ :=
  sInf {t | ∃ h, t = (h.length : ℕ∞) ∧ x ∈ D.leaf h}

/-- The leaf sets really are the partition parts, including their reached histories. -/
def IsLeafPartition {m : ℕ} {Q : Type*}
    (D : DecisionTree (Fin m → E (m + 1)) Q (2 * (m + 1) + 1))
    (P : ConvexProductPartition (List (Fin (2 * (m + 1) + 1))) m (m + 1)) : Prop :=
  ∀ h, P.part h = D.leaf h

end MemOracleLB.Optimization


