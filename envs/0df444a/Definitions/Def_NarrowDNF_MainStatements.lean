-- Prove2me | Definitions.Def_NarrowDNF_MainStatements
-- name    : NarrowDNF_MainStatements
-- status  : Definition
-- author  : @chenghua.liu
-- created : 2026-11-13T08:00:41.734242+00:00
-- url     : https://prove2.me/theorems/47bc98f9-9d64-412e-ba38-43c0a1cca81b
-- title:
--   The narrow-DNF and quantitative adaptive-approximation propositions
-- statement:
--   A finite family of coordinate sets evaluates to true exactly when some member has all its coordinates equal to one. This includes the false empty disjunction and the true empty conjunction.
--
--   The narrow-DNF proposition quantifies one constant $C>0$ before all $n\ge1$, $K>0$, $0<p\le1/2$, $0<\varepsilon<1$, and increasing Boolean functions $f$ with $I_p(f)\le K$. Its conclusion is a finite positive-term family whose every term has size at most $\exp(C(K+1)^2/\varepsilon^2)$ and whose evaluation disagrees with $f$ with probability at most $\varepsilon$. The width condition is termwise and places no bound on the number of terms.
--
--   The quantitative adaptive-input proposition applies in every natural dimension, for $0<p\le1/2$, any Boolean $f$, and $0<a\le1$. Put $C_f=\lceil I_p(f)\rceil$, $d=\lceil1000C_f/a\rceil$, and $L=\exp(10^{10}C_f^2/a^2)$. It asks for increasing local activations $J$ and a Boolean $J$-measurable readout $h$ with error at most $a$, arity at most $d$, and multiplicity-counted load at most $L$. It does not require $h$ to be increasing. These are explicit propositions; their proofs are supplied by separate declarations.
-- source:
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/MainStatements.lean#L29-L40
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/MainStatements.lean#L14-L17
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/MainStatements.lean#L19-L27

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Real.Basic
import Mathlib.Logic.Equiv.Prod
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_NarrowDNF_ActivationLoad
import Definitions.Def_NarrowDNF_Adaptive
import Definitions.Def_NarrowDNF_Certificates
import Definitions.Def_NarrowDNF_Influence
import Definitions.Def_NarrowDNF_ProductMeasure

namespace NarrowDNF
end NarrowDNF


/-! Exact formal target propositions for the 2026-11-06 STOC headline results.
The bundled manuscript is identified in `paper/manifest.json`. These definitions
are not axioms. Their unconditional proofs are provided in `Paper.lean`. -/
noncomputable section
namespace NarrowDNF
attribute [local instance] Classical.propDecidable

/-- Boolean evaluation of any finite positive DNF, with the conventional empty
conjunction and empty disjunction already supplied by `DNFHolds`. -/
def evalDNF {ι : Type*} (terms : Finset (Finset ι)) (x : Cube ι) : Bool :=
  decide (DNFHolds terms x)

/-- Exact target for Theorem 1.2. The absolute constant is quantified before
all dimensions, influence bounds, biases, errors and functions. -/
def NarrowDNFApproximation : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ), 1 ≤ n → ∀ K p ε : ℝ,
    0 < K → 0 < p → p ≤ 1/2 → 0 < ε → ε < 1 →
    ∀ f : Cube (Fin n) → Bool, Monotone f → Influence.totalInfluence p f ≤ K →
    ∃ terms : Finset (Finset (Fin n)),
      (∀ T ∈ terms, (T.card : ℝ) ≤ Real.exp (C * (K+1)^2 / ε^2)) ∧
      ProductMeasure.error p f (evalDNF terms) ≤ ε

/-- Exact simultaneous approximation, increasing-locality, arity and
multiplicity-load target for Lemma 2.1. This is not a hypothesis silently
imported into the final theorem. -/
def HatamiArityLoad : Prop :=
  ∀ (n : ℕ) (p : ℝ), 0 < p → p ≤ 1/2 → ∀ (f : Cube (Fin n) → Bool) (a : ℝ),
    0 < a → a ≤ 1 →
    let C : ℕ := Nat.ceil (Influence.totalInfluence p f)
    let d : ℕ := Nat.ceil (1000 * (C : ℝ) / a)
    let L : ℝ := Real.exp (10000000000 * (C : ℝ)^2 / a^2)
    ∃ (J : Activation (Fin n)) (h : Cube (Fin n) → Bool),
      J.Increasing ∧ ProductMeasure.error p f h ≤ a ∧ J.Measurable h ∧
      J.ArityLE d ∧ J.load p ≤ L



end NarrowDNF


