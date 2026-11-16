-- Prove2me | Definitions.Def_ThinningSprinkling306_ToughCycles_Supplement_Layers
-- name    : ThinningSprinkling306_ToughCycles_Supplement_Layers
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T17:42:48.383495+00:00
-- url     : https://prove2.me/theorems/c9a06f82-deda-4c71-a99e-3cde15492b26
-- title:
--   Ordered partitions and consecutive-pair degrees
-- statement:
--   An ordered partition $W_1,\ldots,W_m$ is a disjoint cover of the vertex set by nonempty sets. The first-largest condition is $|W_i|\le|W_1|$ for every $i$. Given vertex weights $w_v$ and an error $\alpha$, consecutive-pair degrees mean that for every $1\le i<m$,
--   $$
--   (1-\alpha)w_v\le d_G(v,W_{i+1})\le(1+\alpha)w_v\quad(v\in W_i),
--   $$
--   and the same two inequalities with $i$ and $i+1$ reversed for vertices of $W_{i+1}$. The boundary set is $W_1\cup W_m$.
--
--   These predicates supply the data for Lemma 10.2 and impose no path-existence condition. Lean uses indices $0,\ldots,m-1$; boundary indices are tested by $i=0$ or $i+1=m$, avoiding truncated subtraction.
-- source:
--   Micha Christoph, Zach Hunter, Benny Sudakov, STOC 2027 submission #306 (October 2026), p. 25, Lemma 10.2 (PDF p. 27); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/306.pdf

import Definitions.Def_ThinningSprinkling306_ToughCycles_Supplement_GraphParameters
import Definitions.Def_ThinningSprinkling306_ToughCycles_Paths

namespace ThinningSprinkling306.ToughCycles.Supplement

/-- An ordered partition; indices 0,...,m-1 represent printed W₁,...,Wₘ. -/
noncomputable def LayerPartition {n m : ℕ} (W : Fin m → Finset (Fin n)) : Prop :=
  (∀ i, (W i).Nonempty) ∧
  (∀ i j, i ≠ j → Disjoint (W i) (W j)) ∧
  Finset.univ.biUnion W = Finset.univ

/-- First part largest; no maximum is taken over an empty index set. -/
noncomputable def FirstLargest {n m : ℕ} (W : Fin m → Finset (Fin n)) : Prop :=
  ∀ i j : Fin m, i.val = 0 → (W j).card ≤ (W i).card

/-- Both sides of each consecutive pair use the weight of the vertex being tested. -/
noncomputable def ConsecutiveDegrees {n m : ℕ} (G : SimpleGraph (Fin n))
    (W : Fin m → Finset (Fin n)) (α : ℝ) (w : Fin n → ℝ) : Prop :=
  ∀ i j : Fin m, j.val = i.val + 1 →
    (∀ v ∈ W i,
      (1 - α) * w v ≤ ((CharonChurn.Main.nbrsIn G (W j) v).card : ℝ) ∧
      ((CharonChurn.Main.nbrsIn G (W j) v).card : ℝ) ≤ (1 + α) * w v) ∧
    (∀ v ∈ W j,
      (1 - α) * w v ≤ ((CharonChurn.Main.nbrsIn G (W i) v).card : ℝ) ∧
      ((CharonChurn.Main.nbrsIn G (W i) v).card : ℝ) ≤ (1 + α) * w v)

/-- Union of the first and last parts, without truncated subtraction or partial indices. -/
noncomputable def outerLayers {n m : ℕ} (W : Fin m → Finset (Fin n)) : Finset (Fin n) := by
  classical
  exact Finset.univ.biUnion fun i => if i.val = 0 ∨ i.val + 1 = m then W i else ∅

end ThinningSprinkling306.ToughCycles.Supplement


