-- Prove2me | Definitions.Def_EdgeSublinearMWIS_Main_WeightedReduction
-- name    : EdgeSublinearMWIS_Main_WeightedReduction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T13:41:09.79803+00:00
-- url     : https://prove2.me/theorems/32ea4307-fc1a-47f0-9007-906db472f2cf
-- title:
--   Explicit scaling and independent blow-up for rational weights
-- statement:
--   For a nonnegative weight vector on at least two vertices with positive maximum and rational accuracy $0<\varepsilon<1$, the guarded rounding routine sets
--   $$\tau=\varepsilon w_{\max}/(2n),\qquad t_v=\lfloor w_v/\tau\rfloor.$$
--   Other inputs take the direct-case branch before a scale is formed. The rounded graph has $\sum_vt_v$ labels in lexicographic original-vertex/copy order. Prefix counts compute each label's original owner, so zero-sized fibers are omitted explicitly. Distinct copies are adjacent exactly when their owners were adjacent. A selected set maps back to precisely those original vertices owning a selected copy. These definitions contain no independence, approximation or runtime guarantee; the numerical comparisons and copy bound are separate theorem targets.
-- source:
--   Édouard Bonnet, Yeonsu Chang, STOC 2027 submission #1044 (October 2026), §6, Theorem 2 proof, scale and copy construction, p.20 (PDF p.20), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1044.pdf

import Definitions.Def_EdgeSublinearMWIS_Main_Graphs
import Definitions.Def_EdgeSublinearMWIS_Main_Encoding

open scoped BigOperators

namespace EdgeSublinearMWIS.Main

def maximumWeight {n : ℕ} (w : Fin n → ℚ) : ℚ := (List.ofFn w).foldl max 0

/-- Direct cases are handled before the positive scale is formed. -/
def weightRounding {n : ℕ} (w : Fin n → ℚ) (ε : ℚ) : Option (ℚ × (Fin n → ℕ)) :=
  if n ≤ 1 ∨ maximumWeight w ≤ 0 ∨ ε ≤ 0 ∨ 1 ≤ ε ∨ ¬ (∀ v, 0 ≤ w v) then none else
  let τ := ε * maximumWeight w / (2 * (n : ℚ))
  some (τ, fun v => ⌊w v / τ⌋₊)

def totalCopies {n : ℕ} (t : Fin n → ℕ) : ℕ := ∑ v, t v

/-- Lexicographic (original vertex,copy index) labels, implemented by prefix counts.
A zero-sized fiber has no labels. No choice of an arbitrary relabeling is used. -/
def copyOwner {n : ℕ} (t : Fin n → ℕ) (j : Fin (totalCopies t)) : Option (Fin n) :=
  (List.finRange n).find? (fun v =>
    j.val < ∑ u ∈ (Finset.univ.filter (fun u => u ≤ v)), t u)

def roundedGraph {n : ℕ} (G : SimpleGraph (Fin n)) (t : Fin n → ℕ) :
    SimpleGraph (Fin (totalCopies t)) where
  Adj i j := ∃ u v, copyOwner t i = some u ∧ copyOwner t j = some v ∧ G.Adj u v
  symm := by
    constructor
    rintro i j ⟨u, v, hi, hj, h⟩
    exact ⟨v, u, hj, hi, G.adj_symm h⟩
  loopless := by
    constructor
    rintro i ⟨u, v, hu, hv, h⟩
    have huv : u = v := Option.some.inj (hu.symm.trans hv)
    subst v
    exact G.irrefl h

noncomputable def originalVertices {n : ℕ} (t : Fin n → ℕ)
    (I : Finset (Fin (totalCopies t))) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun v => ∃ i ∈ I, copyOwner t i = some v)

end EdgeSublinearMWIS.Main


