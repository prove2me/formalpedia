-- Prove2me | Definitions.Def_NarrowDNF_HatamiResidual
-- name    : NarrowDNF_HatamiResidual
-- status  : Definition
-- author  : @chenghua.liu
-- created : 2026-11-13T08:00:44.398382+00:00
-- url     : https://prove2.me/theorems/15510ee9-fca1-453c-a2b1-d36f65ddef05
-- title:
--   Restricted adaptive partitions and conditional Fourier approximants
-- statement:
--   Let $J$ be a local activation family on $\{0,1\}^{\iota}$. For $S\subseteq\iota$, define its restriction by
--   $$(J|_S)_T(x)\iff T\subseteq S\ \text{and}\ J_T(x).$$
--   An adaptive atom records both the active union and the actual input labels on that union. The operator $\mathbb E_p[F\mid J]$ is the finite weighted conditional expectation on this actual partition. For the $p$-biased Fourier component $F_S$ of a real-valued $f$, set
--   $$\widetilde F_S=\mathbb E_p[F_S\mid J|_S].$$
--   Thus each component is conditioned on its own restricted activation family.
--
--   For a retained family $A$, the bundle defines both $\sum_{S\in A}F_S$ and $\sum_{S\in A}\widetilde F_S$. It also defines the simpler revealed-component competitor $\mathbf1_{\{J_S(x)\}}F_S(x)$ and the literal coordinate restriction $x\mapsto x_T$. These constructions are the concrete functions compared in the diagonal and cross-term residual analysis. No residual bound or projection optimality conclusion is assumed by introducing them.
-- source:
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/HatamiResidual.lean#L534-L535
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/HatamiResidual.lean#L76-L78
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/HatamiResidual.lean#L80-L83
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/HatamiResidual.lean#L85-L87
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/HatamiResidual.lean#L89-L92
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/HatamiResidual.lean#L26-L29
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/HatamiResidual.lean#L177-L180

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Real.Basic
import Mathlib.Logic.Equiv.Prod
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_NarrowDNF_Adaptive
import Definitions.Def_NarrowDNF_ConditionalExpectation
import Definitions.Def_NarrowDNF_Fourier
import Definitions.Def_NarrowDNF_ProductMeasure

namespace NarrowDNF.HatamiResidual
end NarrowDNF.HatamiResidual

namespace NarrowDNF.ProductMeasure
end NarrowDNF.ProductMeasure


/-!
# Hatami's actual restricted-activation conditional components

This file formalizes the Step III/IV construction using actual adaptive atom
labels. `approxComponent` is conditional expectation onto the family retaining
only activations whose index is contained in the component's support. Generic
projection and diagonal estimates are proved here. Construction-specific
cross-term bounds are stated only when proved; no analytic estimate is an axiom.
-/

noncomputable section
open scoped BigOperators

namespace NarrowDNF.HatamiResidual

open ProductMeasure
attribute [local instance] Classical.propDecidable

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Hatami's family `J_S`: retain exactly the original activations indexed inside `S`. -/
def restrict (J : Activation ι) (S : Finset ι) : Activation ι where
  fires T x := T ⊆ S ∧ J.fires T x
  locality T x y hxy := and_congr_right fun _ => J.locality T x y hxy











/-- Real-valued conditional expectation on the actual full adaptive partition. -/
def adaptiveConditional (p : ℝ) (J : Activation ι) (F : Cube ι → ℝ) : Cube ι → ℝ :=
  ConditionalExpectation.conditional (ConditionalExpectation.adaptiveCode J) (weight p) F

/-- Hatami's `F̃_S = E[F_S | F_(J_S)]`, with actual labels and the exact restricted family. -/
def approxComponent (p : ℝ) (J : Activation ι) (f : Cube ι → ℝ)
    (S : Finset ι) : Cube ι → ℝ :=
  adaptiveConditional p (restrict J S) (Fourier.component p f S)

/-- The retained Fourier polynomial. -/
def truncated (p : ℝ) (f : Cube ι → ℝ) (retained : Finset (Finset ι)) (x : Cube ι) : ℝ :=
  ∑ S ∈ retained, Fourier.component p f S x

/-- The measurable competitor used in Hatami's Step III. -/
def approxTruncated (p : ℝ) (J : Activation ι) (f : Cube ι → ℝ)
    (retained : Finset (Finset ι)) (x : Cube ι) : ℝ :=
  ∑ S ∈ retained, approxComponent p J f S x









section Generic
variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]





end Generic



/-- The competitor that keeps the component only when its complete support is revealed. -/
def revealedComponent (p : ℝ) (J : Activation ι) (f : Cube ι → ℝ)
    (S : Finset ι) (x : Cube ι) : ℝ :=
  if J.fires S x then Fourier.component p f S x else 0














section GenericBound
variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]



end GenericBound





















section GenericMeanBound
variable {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]







end GenericMeanBound



/-- Fixed-coordinate restriction of a cube point. -/
def restriction (T : Finset ι) (x : Cube ι) : T → Bool := fun i => x i







end NarrowDNF.HatamiResidual


