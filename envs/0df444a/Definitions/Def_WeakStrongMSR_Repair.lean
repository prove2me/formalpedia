-- Prove2me | Definitions.Def_WeakStrongMSR_Repair
-- name    : WeakStrongMSR_Repair
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T08:29:03.574014+00:00
-- url     : https://prove2.me/theorems/196e63ec-1493-4062-a3f1-17b3c33e07d2
-- title:
--   The repair step (§3.3.2, Algorithm 3, threshold (21))
-- statement:
--   Repair takes the rounding output and $\gamma=\tfrac12-\delta$.
--
--   1. $D$ collects the unqueried points $x$ assigned through $i$ with $\mathrm{md}(x,s_i)>5R_i$, and those with $\mathrm{md}(x,s_j)\le 7R_j$ for some $j$ in another component. Abort if $|D|>2ckh$; otherwise query $D$ and let $S_D$ be the strong set.
--   2. Remove $S_D$ from every list. A component is **small** if $|X_J|<\frac{2c}{\gamma}\big(|S_D\cap B'_J|+|J|h\big)$ (Eq. (21)). Query and empty the small lists.
--   3. Every large component draws $h$ distinct points $W_J$ uniformly from its list and queries them. Its list is then recomputed as $\{x\notin S:\mathrm{md}(x,J)\le 3R_J\}$.
--   4. Let $U$ be the unqueried points on no list. Abort if $|U|>2ckh$; otherwise query $U$.
--
--   **Formalization Note** The large components draw independently. The outcome records whether repair aborted, the strong set, the repaired lists and the strong queries repair made.
-- source:
--   Friggstad–Jamshidian–Vakilian, Minimum Sum-of-Radii Clustering with Strong and Weak Oracles (manuscript, STOC 2027 submission, sha256 5f8fbaf3…67e8f92a0), §3.3.2, p.21 (PDF 22), Algorithm 3, p.22 (PDF 23); Eq. (14), p.21; Eq. (21), p.34 (PDF 35)

import Mathlib
import Definitions.Def_WeakStrongMSR_Model
import Definitions.Def_WeakStrongMSR_Estimates
import Definitions.Def_WeakStrongMSR_Rounding

open scoped Classical

set_option autoImplicit false

namespace WeakStrongMSR

/-!
# The repair step (§3.3.2, Algorithm 3, threshold (21))

Friggstad–Jamshidian–Vakilian, *Minimum Sum-of-Radii Clustering with Strong and Weak Oracles*
(manuscript, sha256 5f8fbaf3…67e8f92a0), §3.3.2, p.21 and Algorithm 3, p.22: `D` collects the
unqueried points `x` assigned through `i` with `md(x, s_i) > 5R_i`, or assigned to `J` with
`md(x, s_j) ≤ 7R_j` for some `j ∉ J`; "if |D| > 2ckh then abort"; query `D`, `S_D := S`; each
component list loses `S_D` and is small iff `|X_J| < 2c(|S_D ∩ B′_J| + |J|h)` — in the general-δ
algorithm of App. A, Eq. (21), p.34, `|X_J| < (2c/γ)(|S_D ∩ B′_J| + |J|h)` with `γ = 1/2 − δ`;
small lists are queried and emptied; each large component draws `h` distinct points `W_J` uniformly
from its list and queries them; large lists are recomputed as `{x ∈ X ∖ S : md(x, J) ≤ 3R_J}`
(Eq. (14)); `U` = unqueried points on no list; "if |U| > 2ckh then abort"; query `U`.

This module bundles the outcome type and the law of the repair step.

**Formalization Note.**
* The estimate `md(x, s_i)` uses the witness set `W_{s_i}` that `s_i` received in sampling; for an
  unqueried point it is `max {0, median} + r_{s_i}` (Eq. (3)).
* "Draw h distinct points uniformly from X_J" is the uniform law on the `h`-subsets of the list; the
  large components draw independently. (A large list has at least `h` points when `c ≥ 1`; if not,
  the whole list is taken.)
* Lists are indexed by component roots; non-root indices carry the empty list.
* The repair outcome records whether it aborted, the final strong set, the final lists and the
  number of strong queries repair made (up to the abort, on an aborted run). -/

/-- The outcome of repair. -/
structure RepairOut (n m : ℕ) where
  /-- Whether repair aborted. -/
  aborted : Bool
  /-- The strong set at the end of repair. -/
  S : Finset (Fin n)
  /-- The repaired list of each component (by root). -/
  lists : Fin m → Finset (Fin n)
  /-- The strong queries made by repair. -/
  queries : ℕ

/-- Independent uniform `h`-subsets of the given sets, one for each listed index. -/
noncomputable def drawWitnesses {n m : ℕ} (h : ℕ) (X : Fin m → Finset (Fin n)) :
    List (Fin m) → PMF (Fin m → Finset (Fin n))
  | [] => PMF.pure (fun _ => ∅)
  | j :: rest =>
      (if hne : ((X j).powersetCard h).Nonempty then PMF.uniformOfFinset _ hne
        else PMF.pure (X j)).bind
        (fun WJ => (drawWitnesses h X rest).map (fun f => Function.update f j WJ))

/-- The repair step (Algorithm 3 with the threshold (21)) on the rounding output `r`, with
parameters `c, k, h`, margin `γ = 1/2 − δ`, metric `d` (read on strongly queried points only) and
weak table `w`. -/
noncomputable def repairLaw {n : ℕ} (c k h : ℕ) (γ : ℝ) (d w : Fin n → Fin n → ℝ)
    (r : RoundOut n) : PMF (RepairOut n r.m) :=
  let md : Fin r.m → Fin n → ℝ := fun i => mdEst d w r.S (r.ctr i) (r.W i)
  let D := Finset.univ.filter (fun x => x ∉ r.S ∧ ∃ i, r.rep x = some i ∧
    (5 * r.R i < md i x ∨ ∃ j, r.root j ≠ r.root i ∧ md j x ≤ 7 * r.R j))
  if 2 * c * k * h < D.card then PMF.pure ⟨true, r.S, fun _ => ∅, 0⟩ else
    let SD := r.S ∪ D
    let old : Fin r.m → Finset (Fin n) := fun j => if r.root j = j then r.list j \ SD else ∅
    let small : Fin r.m → Prop := fun j =>
      ((old j).card : ℝ) < (2 * c / γ) * ((SD ∩ r.inflated d j).card + (r.comp j).card * h)
    let smallRoots := r.roots.filter small
    let largeRoots := r.roots.filter (fun j => ¬ small j)
    let S1 := SD ∪ smallRoots.biUnion old
    (drawWitnesses h old (largeRoots.sort (· ≤ ·))).map (fun WJ =>
      let S2 := S1 ∪ largeRoots.biUnion WJ
      let newList : Fin r.m → Finset (Fin n) := fun j =>
        if j ∈ largeRoots then
          Finset.univ.filter (fun x => x ∉ S2 ∧ mdComp d w (r.ctr j) (WJ j) x ≤ 3 * r.radiusJ j)
        else ∅
      let U := Finset.univ.filter (fun x => x ∉ S2 ∧ ∀ j, x ∉ newList j)
      if 2 * c * k * h < U.card then ⟨true, S2, newList, (S2 \ r.S).card⟩
      else ⟨false, S2 ∪ U, newList, ((S2 ∪ U) \ r.S).card⟩)

end WeakStrongMSR


