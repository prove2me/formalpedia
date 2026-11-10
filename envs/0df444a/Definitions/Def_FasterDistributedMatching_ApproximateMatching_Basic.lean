-- Prove2me | Definitions.Def_FasterDistributedMatching_ApproximateMatching_Basic
-- name    : FasterDistributedMatching_ApproximateMatching_Basic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T12:08:50.155203+00:00
-- url     : https://prove2.me/theorems/0cc0c091-3be6-4a52-a59e-7cf05c6a8298
-- title:
--   Finite matching quantities and rounding potential
-- statement:
--   Let $G$ be a finite simple undirected graph and let $x_e$ be real edge values, extended by zero to nonedges. The load at $v$, total weight, quadratic penalty and potential are
--
--   $$c_v=\sum_{e\ni v}x_e,\qquad W=\sum_e x_e,\qquad Q=2\sum_v c_v^2,\qquad \Phi=W-Q.$$
--
--   Raw nonnegative assignments impose no upper load bound. Fractional feasibility uses the published ordinary degree constraints. Integral matchings and their maximum cardinality use the published finite matching interface. A $1/d$-fractional assignment has values that are nonnegative integer multiples of $1/d$, with $d\ge1$. Cleanup deletes exactly edges incident to a vertex of load strictly greater than $1/2$. Base-two logarithms are padded to at least one; the finite iterated logarithm stops at one. Budgets are natural ceilings.
--
--   These quantities are shared by the matching goal and all rounding statements. Neither an optimum nor a potential guarantee is supplied as an input.
-- source:
--   Mohsen Ghaffari, Christoph Grunau, STOC 2027 submission #1024 (October 2026), §2, printed pp.6–7, PDF pp.8–9; §3.1, printed p.8, PDF p.10; §3.3, printed p.13, PDF p.15; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1024.pdf

import Mathlib
import Definitions.Def_RandomOrderCRS_FractionalMatching
import Definitions.Def_SemiStreamMWM_Graph

namespace FasterDistributedMatching.ApproximateMatching

/-! Source: Ghaffari--Grunau, STOC 2027 submission #1024, §§2, 3.1, 3.3.
Finite simple graphs; zero extension off edges. No feasibility is bundled into raw weights. -/
open Classical in
noncomputable def totalWeight {N : ℕ} (G : SimpleGraph (Fin N)) (x : Sym2 (Fin N) → ℝ) : ℝ :=
  ∑ e ∈ G.edgeFinset, x e

noncomputable def load {N : ℕ} (G : SimpleGraph (Fin N)) (x : Sym2 (Fin N) → ℝ)
    (v : Fin N) : ℝ := @RandomOrderCRS.fracDegree _ _ _ G (Classical.decRel _) x v

noncomputable def fractional {N : ℕ} (G : SimpleGraph (Fin N)) (x : Sym2 (Fin N) → ℝ) : Prop :=
  @RandomOrderCRS.IsFractionalMatching _ _ _ G (Classical.decRel _) x

def NonnegativeAssignment {N : ℕ} (G : SimpleGraph (Fin N)) (x : Sym2 (Fin N) → ℝ) : Prop :=
  (∀ e, 0 ≤ x e) ∧ (∀ e, e ∉ G.edgeSet → x e = 0)

noncomputable def penalty {N : ℕ} (G : SimpleGraph (Fin N)) (x : Sym2 (Fin N) → ℝ) : ℝ :=
  2 * ∑ v, (load G x v) ^ 2

noncomputable def potential {N : ℕ} (G : SimpleGraph (Fin N)) (x : Sym2 (Fin N) → ℝ) : ℝ :=
  totalWeight G x - penalty G x

/- Ordinary matchings from the published graph interface, with an ambient containment condition. -/
open Classical in
noncomputable def Matching {N : ℕ} (G : SimpleGraph (Fin N)) (M : SimpleGraph (Fin N)) : Prop :=
  M ≤ G ∧ SemiStreamMWM.IsMatching M Finset.univ

open Classical in
noncomputable def matchingSize {N : ℕ} (M : SimpleGraph (Fin N)) : ℕ := M.edgeFinset.card

/- A finite maximum over the actual feasible matchings, including the empty graph. -/
open Classical in
noncomputable def optimum {N : ℕ} (G : SimpleGraph (Fin N)) : ℕ :=
  SemiStreamMWM.mcm G

def Bipartition {N : ℕ} (G : SimpleGraph (Fin N)) (side : Fin N → Bool) : Prop :=
  ∀ u v, G.Adj u v → side u ≠ side v

def FractionalGrid {N : ℕ} (x : Sym2 (Fin N) → ℝ) (d : ℕ) : Prop :=
  1 ≤ d ∧ ∀ e, ∃ k : ℕ, x e = (k : ℝ) / d

open Classical in
noncomputable def cleanup {N : ℕ} (G : SimpleGraph (Fin N))
    (x : Sym2 (Fin N) → ℝ) (e : Sym2 (Fin N)) : ℝ :=
  if ∃ v ∈ e, 1 / 2 < load G x v then 0 else x e

noncomputable def logTwo (x : ℝ) : ℝ := Real.logb 2 x
noncomputable def degreeLog (D : ℕ) : ℝ := max 1 (logTwo (max 2 (D : ℝ)))
noncomputable def doubleLog (D : ℕ) : ℝ := max 1 (logTwo (degreeLog D))
noncomputable def iterLog : ℕ → ℝ → ℕ
  | 0, _ => 0
  | k + 1, x => if x ≤ 1 then 0 else 1 + iterLog k (logTwo x)
noncomputable def logStar (n : ℕ) : ℕ := max 1 (iterLog n n)
noncomputable def matchingTime (n D : ℕ) : ℝ :=
  (degreeLog D) ^ (3 / 2 : ℝ) * (doubleLog D) ^ 2 +
    Real.sqrt (degreeLog D) * (logStar n : ℝ)
noncomputable def budget (C f : ℝ) : ℕ := ⌈C * f⌉₊

end FasterDistributedMatching.ApproximateMatching


