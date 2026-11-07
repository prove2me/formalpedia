-- Prove2me | Definitions.Def_IIDMatchHard_Inst
-- name    : IIDMatchHard_Inst
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T08:05:13.929051+00:00
-- url     : https://prove2.me/theorems/1618eb71-1ecc-4e88-89af-93e3ddcd8a30
-- title:
--   Binary-encoded instances of Theorem 3.1: unweighted i.i.d. matching with two neighbors per type
-- statement:
--   An **input** of the approximation problem of Theorem 3.1 consists of numbers $n_{\mathrm{off}}$, $n_{\mathrm{ty}}$ and $T$, and, for each type $y\in\{0,\dots,n_{\mathrm{ty}}-1\}$, two offline vertices $a_y,b_y\in\{0,\dots,n_{\mathrm{off}}-1\}$ and a rational probability $q_y$. It describes the unweighted i.i.d. instance in which type $y$ has neighbor set $\{a_y,b_y\}$ and probability $q_y$, and $T$ online vertices arrive. The input is **valid** when
--
--   1. every type has exactly two neighbors, $a_y\ne b_y$;
--   2. every probability is positive, $q_y>0$;
--   3. the probabilities sum to one.
--
--   $\mathrm{OPT}(I)$ of an input is the online optimum of the instance it describes. The **encoding** of an input is binary: $n_{\mathrm{off}}$, $n_{\mathrm{ty}}$ and $T$ in a self-delimiting binary code, then for each type the two neighbor indices and the probability (sign, numerator and denominator in lowest terms).
--
--   This is the instance class "unweighted, every type has exactly two neighbors" of Theorem 3.1. Polynomial time is measured in the length of the encoding.
--
--   **Formalization Note** The input structure holds data only, and the conditions of the class are the predicate `Inst.Valid`. Probabilities are rational because inputs are finite objects. Positivity only removes types that never arrive, so hardness for this class is the stronger statement. The numbers use `NSWApxHard.Reduction.natBits` and the probabilities `ImpatientMatching.encRat`.
-- source:
--   Teng, Yang, Computational Hardness of Online Stochastic Matching (manuscript of Nov. 3, 2026, sha256 f0193d92…), Theorem 3.1, p.5 (PDF p.6), with the model of §2.1, p.4

import Definitions.Def_IIDMatchHard_Model
import Definitions.Def_NSWApxHard_Reduction_Welfare
import Definitions.Def_ImpatientMatching_Input

set_option autoImplicit false

namespace IIDMatchHard

/-- An **input** of the approximation problem of Theorem 3.1: an unweighted known-i.i.d. instance
with offline vertices `Fin nOff`, online types `Fin nTy`, two listed neighbors `nbr y` of each
type, rational type probabilities `prob` and `T` online vertices. Teng, Yang, *Computational
Hardness of Online Stochastic Matching* (manuscript of Nov. 3, 2026, sha256 f0193d92…),
Theorem 3.1, p.5 (PDF p.6), with the model of §2.1, p.4.

**Formalization Note.** The input carries data only; the conditions of the instance class of
Theorem 3.1 (two distinct neighbors, positive probabilities summing to one) are `Inst.Valid`.
Inputs are finite objects, so the probabilities are rational. -/
structure Inst where
  /-- The number of offline vertices. -/
  nOff : ℕ
  /-- The number of online types. -/
  nTy : ℕ
  /-- The two neighbors of each type. -/
  nbr : Fin nTy → Fin nOff × Fin nOff
  /-- The probability of each type. -/
  prob : Fin nTy → ℚ
  /-- The number of online vertices. -/
  T : ℕ

namespace Inst

/-- The instance class of Theorem 3.1 (p.5): every type has **exactly two** neighbors, and the
type probabilities are positive and sum to one.

**Formalization Note.** Positivity restricts the class to types that actually occur (a type of
probability zero never arrives); a hardness result for the smaller class is the stronger one. -/
def Valid (I : Inst) : Prop :=
  (∀ y, (I.nbr y).1 ≠ (I.nbr y).2) ∧ (∀ y, 0 < I.prob y) ∧ ∑ y, I.prob y = 1

/-- The unweighted i.i.d. instance described by an input: the neighbor set of type `y` is
`{(nbr y).1, (nbr y).2}`, the probabilities are `prob` (as reals) and there are `T` arrivals. -/
def toModel (I : Inst) : IIDModel (Fin I.nOff) (Fin I.nTy) where
  nbr y := {(I.nbr y).1, (I.nbr y).2}
  p y := (I.prob y : ℝ)
  T := I.T

end Inst

/-- The online optimum `OPT(I)` of an input (Definition 2.1, p.4 (PDF p.5); §2.1, p.4). -/
noncomputable def onlineOpt (I : Inst) : ℝ :=
  OPT I.toModel

/-- The **binary encoding** of an input: `nOff`, `nTy` and `T` by the self-delimiting code
`natBits`, then, type by type, the two neighbor indices (`natBits`) and the probability
(`encRat`: sign, numerator, denominator in lowest terms).

**Formalization Note.** Every field is encoded by a self-delimiting code, in a fixed order, with
the counts first, so the encoding is injective; running times are measured in its length. -/
def encInst (I : Inst) : List Bool :=
  NSWApxHard.Reduction.natBits I.nOff ++ NSWApxHard.Reduction.natBits I.nTy ++
    NSWApxHard.Reduction.natBits I.T ++
    (List.ofFn fun y : Fin I.nTy =>
      NSWApxHard.Reduction.natBits (I.nbr y).1.val ++
        NSWApxHard.Reduction.natBits (I.nbr y).2.val ++ ImpatientMatching.encRat (I.prob y)).flatten

end IIDMatchHard


