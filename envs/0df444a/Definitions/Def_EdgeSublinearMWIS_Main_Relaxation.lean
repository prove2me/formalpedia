-- Prove2me | Definitions.Def_EdgeSublinearMWIS_Main_Relaxation
-- name    : EdgeSublinearMWIS_Main_Relaxation
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T13:41:00.714822+00:00
-- url     : https://prove2.me/theorems/b3407062-aaf6-4382-aa50-01c2e7ce612a
-- title:
--   The relaxation and the indicator convex hull
-- statement:
--   Coordinates are the subsets $A\subseteq W$ with $|A|\le r+2$. The relaxation includes all five rows of (13): normalization, bounds, monotonicity, vanishing on nonindependent sets, and the equations $\sum_{v\in W}y_{A\cup\{v\}}=ky_A$. Conditioning uses a positive denominator $y_A$.
--
--   The distinct indicator hull is
--   $$P_r(G[W],k)=\operatorname{conv}\{(1[A\subseteq I])_A:I\subseteq W,\ I\text{ independent},\ |I|=k\}.$$
--   The hull is taken in the actual finite coordinate space and an empty generator set has empty hull. Integer targets include all integers for the validity lemma; the relaxation is used at positive integer targets. Total-array adapters ignore values outside the coordinate set. Query serialization uses a deterministic enumeration of all coordinate subsets. No relaxation point is identified with a probability measure on independent sets.
-- source:
--   Édouard Bonnet, Yeonsu Chang, STOC 2027 submission #1044 (October 2026), §4, Eqs. (13)–(14); §5.1, Eq. (19), p.12 (PDF p.12), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1044.pdf

import Definitions.Def_EdgeSublinearMWIS_Main_Graphs
import Definitions.Def_EdgeSublinearMWIS_Main_Encoding

open scoped BigOperators

namespace EdgeSublinearMWIS.Main

/-- A coordinate exists precisely for |A| ≤ r+2. Functions on all subsets below use
only these coordinates; values at other subsets are immaterial and never encoded. -/
def Coordinates {n : ℕ} (W : Finset (Fin n)) (r : ℕ) : Finset (Finset (Fin n)) :=
  W.powerset.filter (fun A => A.card ≤ r + 2)

/-- Equation (13), on the active vertex set W; no independent-set law is assumed. -/
def Relaxation {n : ℕ} (G : SimpleGraph (Fin n)) (W : Finset (Fin n)) (r k : ℕ)
    (y : Finset (Fin n) → ℝ) : Prop :=
  y ∅ = 1 ∧
  (∀ A ∈ Coordinates W r, 0 ≤ y A ∧ y A ≤ 1) ∧
  (∀ A ⊆ W, A.card ≤ r + 1 → ∀ v ∈ W, y (insert v A) ≤ y A) ∧
  (∀ A ∈ Coordinates W r, ¬ G.IsIndepSet (A : Set (Fin n)) → y A = 0) ∧
  ∀ A ⊆ W, A.card ≤ r + 1 → ∑ v ∈ W, y (insert v A) = (k : ℝ) * y A

noncomputable def conditional {n : ℕ} (y : Finset (Fin n) → ℝ)
    (A : Finset (Fin n)) (_positive : 0 < y A) : Fin n → ℝ :=
  fun v => y (insert v A) / y A

noncomputable def indicatorPoint {n : ℕ} (W I : Finset (Fin n)) (r : ℕ) :
    ({A // A ∈ Coordinates W r} → ℝ) :=
  fun A => if A.val ⊆ I then 1 else 0

/-- Equation (19), as an actual convex hull in the finite coordinate space. -/
noncomputable def IndependentHull {n : ℕ} (G : SimpleGraph (Fin n))
    (W : Finset (Fin n)) (r : ℕ) (k : ℤ) : Set ({A // A ∈ Coordinates W r} → ℝ) :=
  convexHull ℝ {z | ∃ I ⊆ W, G.IsIndepSet (I : Set (Fin n)) ∧ (I.card : ℤ) = k ∧
    z = indicatorPoint W I r}

/-- Total-array adapter; membership only inspects the true coordinates. -/
def InHull {n : ℕ} (G : SimpleGraph (Fin n)) (W : Finset (Fin n)) (r : ℕ) (k : ℤ)
    (z : Finset (Fin n) → ℝ) : Prop :=
  (fun A => z A.val) ∈ IndependentHull G W r k

noncomputable def encodePoint {n : ℕ} (W : Finset (Fin n)) (r : ℕ)
    (y : Finset (Fin n) → ℚ) : List Bool :=
  ((((W.sort (· ≤ ·)).sublists).map List.toFinset).filter (fun A => A.card ≤ r + 2)).flatMap
    (fun A => encodeRat (y A))

end EdgeSublinearMWIS.Main


