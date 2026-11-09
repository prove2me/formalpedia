-- Prove2me | Definitions.Def_WatsonPseudodeterminism_MASeparation_Balance
-- name    : WatsonPseudodeterminism_MASeparation_Balance
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T08:27:22.83132+00:00
-- url     : https://prove2.me/theorems/f145110e-e38a-4249-bafe-6b38a208a524
-- title:
--   Gadget slices and two-sided rectangle balance
-- statement:
--   For a rectangle $R\subseteq S^m$ and $z\in\{0,1\}^m$, define its output slice by
--
--   $$R_z=\{(x,y)\in R:g^m(x,y)=z\}.$$
--
--   The full rectangle $S^m$ has both sides equal to all $m$-tuples of $h$-bit blocks. A rectangle is balanced when, for every $z$,
--
--   $$\frac{|R|}{1.01\,2^m}\le |R_z|\le1.01\frac{|R|}{2^m}.$$
--
--   Cardinalities are cast to real numbers before division. The denominator is always positive, even for $m=0$, and both inequalities are retained. The empty rectangle is balanced because its cardinalities and all slice cardinalities are zero. This is the paper's multiplicative balance condition, rather than a one-sided density estimate.
-- source:
--   Thomas Watson, STOC 2027 submission #13 (October 2026), §2.2, p. 7 (R_z and balanced); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/13.pdf

import Definitions.Def_WatsonPseudodeterminism_MASeparation_Gadget
import Definitions.Def_WatsonPseudodeterminism_MASeparation_Rectangles

namespace WatsonPseudodeterminism.MASeparation

abbrev GadgetRectangle (h m : ℕ) := Rectangle (BlockInput h m) (BlockInput h m)

/-- §2.2, p. 7: S^m as the full rectangle. -/
noncomputable def fullRectangle (h m : ℕ) : GadgetRectangle h m :=
  (Finset.univ, Finset.univ)

/-- R_z is the subset on which g^m equals z. -/
noncomputable def slice {h m : ℕ} (R : GadgetRectangle h m) (z : Fin m → Bool) :
    Finset (BlockInput h m × BlockInput h m) := by
  classical
  exact (rectPoints R).filter (fun xy => gadgetPower xy.1 xy.2 = z)

/-- Within a multiplicative factor 1.01, in both directions. -/
def WithinFactor (count mean : ℝ) : Prop :=
  mean / (1.01 : ℝ) ≤ count ∧ count ≤ (1.01 : ℝ) * mean

/-- §2.2, p. 7: all 2^m output slices have approximately equal cardinality. -/
def Balanced {h m : ℕ} (R : GadgetRectangle h m) : Prop :=
  ∀ z, WithinFactor ((slice R z).card : ℝ) ((rectPoints R).card / (2 : ℝ) ^ m)

end WatsonPseudodeterminism.MASeparation


