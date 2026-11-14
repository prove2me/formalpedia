-- Prove2me | Definitions.Def_NarrowDNF_AdaptiveShift
-- name    : NarrowDNF_AdaptiveShift
-- status  : Definition
-- author  : @chenghua.liu
-- created : 2026-11-13T07:59:16.332945+00:00
-- url     : https://prove2.me/theorems/5f394fd6-e567-433a-9c0a-be91edce7531
-- title:
--   Forcing activation tests while retaining original adaptive labels
-- statement:
--   Let $x\in\{0,1\}^I$ and let $D\subseteq I$ be finite. The forced input $x^{D\leftarrow1}$ replaces every coordinate in $D$ by one and leaves the remaining coordinates unchanged. For a local activation family $J$, define the forced family by
--   $$J^D_S(x)=J_S(x^{D\leftarrow1}).$$
--   The bundled locality proof ensures that this is again a local activation family. Forcing changes the test used to determine which sets activate. The adaptive atom of the resulting family still stores the labels of the original input $x$ on its active union; it does not replace those stored labels by the forced labels.
--
--   A finite ordered shift sequence is encoded by a list of pairs $(i,b)$, where $b=\mathrm{true}$ selects a lower shift. The function $\operatorname{lowerCoordinates}$ returns the finite set of coordinates for which at least one lower shift occurs. Repetitions are removed in this set, while the separate shift list retains its order and all repeated operations. These definitions provide the forcing interface for adaptive measurability under successive shifts.
-- source:
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/AdaptiveShift.lean#L89-L98
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/AdaptiveShift.lean#L18-L19
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/AdaptiveShift.lean#L162-L167

import Mathlib.Data.Bool.Basic
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Real.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_NarrowDNF_Adaptive

namespace NarrowDNF
end NarrowDNF

namespace NarrowDNF.Activation
end NarrowDNF.Activation


/-!
# Adaptive atoms under shifts

The precise content of Lemma 3.2 of the 2026-11-06 STOC revision, including its
atom-recovery proof (formerly in Appendix B of arXiv:2609.00240v1).
All activations carry the locality field from `Activation`; no decoder or atom
recovery oracle is assumed. The unbranched formulas for shifts are equivalent
to the paper's two-slice formulas by Boolean idempotence.
-/

namespace NarrowDNF

variable {ι : Type*} [DecidableEq ι]

def forceInput (D : Finset ι) (x : Cube ι) : Cube ι :=
  fun i => if i ∈ D then true else x i







namespace Activation







/-- Forcing changes the activation test, but never the labels stored by its
adaptive atom. -/
def force (J : Activation ι) (D : Finset ι) : Activation ι where
  fires S x := J.fires S (forceInput D x)
  locality S x y hxy := J.locality S (forceInput D x) (forceInput D y) (by
    intro i hi
    simp only [forceInput]
    split
    · rfl
    · exact hxy i hi)

















/-- Coordinates on which at least one lower shift occurs. Repeated coordinates
are intentionally allowed, and the chosen processing order is retained in the
separate list passed to `applyShifts`. -/
def lowerCoordinates : List (ι × Bool) → Finset ι
  | [] => ∅
  | (i, b) :: rest => if b then insert i (lowerCoordinates rest) else lowerCoordinates rest



end Activation
end NarrowDNF


