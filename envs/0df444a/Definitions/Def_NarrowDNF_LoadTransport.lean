-- Prove2me | Definitions.Def_NarrowDNF_LoadTransport
-- name    : NarrowDNF_LoadTransport
-- status  : Definition
-- author  : @chenghua.liu
-- created : 2026-11-13T07:59:48.31767+00:00
-- url     : https://prove2.me/theorems/92a9ab01-dc4d-4089-a36b-6f3d0b7a8e5f
-- title:
--   Forcing-coordinate sets and extension of local Boolean inputs
-- statement:
--   For a Boolean assignment $d\in\{0,1\}^{\iota}$ on a finite coordinate set, define the forcing set
--   $$D(d)=\{i\in\iota:d_i=1\}.$$
--   It translates a cube-valued random choice into the set of coordinates forced to one when evaluating a local activation family. If $d$ is sampled from the Bernoulli product law, membership of distinct coordinates in $D(d)$ is represented by the corresponding independent bits.
--
--   For a finite set $S\subseteq\iota$ and a local assignment $z:S\to\{0,1\}$, define its full-cube extension by
--   $$\operatorname{extend}_S(z)_i=\begin{cases}z_i&i\in S,\\0&i\notin S.\end{cases}$$
--   This makes a local activation evaluable using the global-input encoding. The activation's locality condition ensures that the choice of labels outside $S$ carries no additional information. These two objects support the later point-mass and load-transport estimates under forcing, including the effective bias $2p-p^2$; those estimates are separate theorem nodes.
-- source:
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/LoadTransport.lean#L69-L70
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/LoadTransport.lean#L82-L85

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
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
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_NarrowDNF_Adaptive

namespace NarrowDNF
end NarrowDNF

namespace NarrowDNF.Activation
end NarrowDNF.Activation

namespace NarrowDNF.ProductMeasure
end NarrowDNF.ProductMeasure


/-!
# Load transport under random forcing

Point-mass and expectation bounds at effective bias `2*p-p^2`. Bounds are stated
without division by point masses, so they hold also for degenerate biases.
-/

noncomputable section
open scoped BigOperators

namespace NarrowDNF.ProductMeasure

variable {ι : Type*} [Fintype ι] [DecidableEq ι]











end NarrowDNF.ProductMeasure

namespace NarrowDNF

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def forcingCoordinates (d : Cube ι) : Finset ι :=
  Finset.univ.filter fun i => d i = true



namespace Activation

open ProductMeasure
attribute [local instance] Classical.propDecidable

/-- Extend a local input by zero; locality makes this particular extension
irrelevant to the activation's value. -/
def extendLocal (S : Finset ι) (z : S → Bool) : Cube ι :=
  fun i => if hi : i ∈ S then z ⟨i, hi⟩ else false

















end Activation
end NarrowDNF


