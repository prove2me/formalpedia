-- Prove2me | Definitions.Def_NarrowDNF_ActivationLoad
-- name    : NarrowDNF_ActivationLoad
-- status  : Definition
-- author  : @chenghua.liu
-- created : 2026-11-13T07:59:25.680978+00:00
-- url     : https://prove2.me/theorems/b8d77a83-34a3-4a4d-a92a-cf9492703300
-- title:
--   Multiplicity-counted load and arity of a local activation family
-- statement:
--   Let $I$ be a finite coordinate set, $J$ a local activation family on $\{0,1\}^I$, and $\mu_p$ the Bernoulli product law. For each $S\subseteq I$, the event $J_S(x)$ is the activation test indexed by $S$. The load is
--   $$\Lambda_p(J)=\sum_{S\subseteq I}|S|\,\mu_p\{x:J_S(x)\}.$$
--   It counts activated coordinate sets with multiplicity: a coordinate lying in several firing sets contributes once for each such set. It is therefore distinct from the expected cardinality of the union of activated coordinates.
--
--   For a natural number $d$, the predicate $\operatorname{ArityLE}(J,d)$ says that no activation indexed by a set of cardinality greater than $d$ ever fires: $|S|>d$ implies $\neg J_S(x)$ for every input $x$. These two quantities express the separate load and local-set-size controls used in Hatami's construction and in the monotonicization argument. No approximation or load bound is assumed by either definition.
-- source:
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/ActivationLoad.lean#L11-L12
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/ActivationLoad.lean#L14-L15

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
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
import Definitions.Def_NarrowDNF_Adaptive
import Definitions.Def_NarrowDNF_ProductMeasure

namespace NarrowDNF
end NarrowDNF

namespace NarrowDNF.Activation
end NarrowDNF.Activation


namespace NarrowDNF
namespace Activation
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def load (J : Activation ι) (p : ℝ) : ℝ := by
  classical exact ∑ S : Finset ι, (S.card : ℝ) * ProductMeasure.probability p (J.fires S)

def ArityLE (J : Activation ι) (d : ℕ) : Prop :=
  ∀ S, d < S.card → ∀ x, ¬ J.fires S x







end Activation
end NarrowDNF


