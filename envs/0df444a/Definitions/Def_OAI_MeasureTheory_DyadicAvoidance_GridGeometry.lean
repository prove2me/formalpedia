-- Prove2me | Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_GridGeometry
-- name    : OAI_MeasureTheory_DyadicAvoidance_GridGeometry
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-16T03:41:10.54003+00:00
-- url     : https://prove2.me/theorems/4d0f21f6-7bac-49f3-9210-bf4cfadfe2e0
-- title:
--   Periodic grid keys $\lfloor q\{x\}\rfloor$ and dyadic grid keys of mesh $2^{-(b+2)}$
-- statement:
--   For $x\in\mathbb{R}$ write $\{x\}=x-\lfloor x\rfloor\in[0,1)$ for its fractional part.
--
--   1. **Periodic grid key.** For $q,x\in\mathbb{R}$,
--   $$K_q(x)=\big\lfloor q\{x\}\big\rfloor\in\mathbb{Z}.$$
--   For $q>0$ this is the integer $k$ with $k/q\le\{x\}<(k+1)/q$, i.e. the label of the half-open cell of the grid $q^{-1}\mathbb{Z}$ that contains $\{x\}$; for a positive integer $q$ the label lies in $\{0,1,\dots,q-1\}$. The key depends only on $x$ modulo $1$.
--   2. **Dyadic grid key.** For $b\in\mathbb{N}$,
--   $$J_b(x)=K_{2^{b+2}}(x)=\big\lfloor 2^{b+2}\{x\}\big\rfloor,$$
--   the cell label at mesh $2^{-(b+2)}$ used for a dyadic window whose last index is $b$.
--
--   The file also records the periodicity $J_b(x+1)=J_b(x)$ for all $b\in\mathbb{N}$ and $x\in\mathbb{R}$.
--
--   In the construction of a compact set avoiding the affine copies $\{x+s\,2^{-n}:n\ge1\}$, $s\neq0$, of the dyadic sequence, membership of a point $y$ in a random $1$-periodic set is decided by Boolean tables read at the keys $J_b(y)$. Because the cells are closed on the left and open on the right, for a positive integer $q$ the key $K_q$ is unchanged under a forward displacement $y\mapsto y+u$ with $u>0$ as long as no grid point $k/q$, $k\in\mathbb{Z}$, lies in $(y,y+u]$; this is the mechanism behind the stability of routing decisions under small dyadic translations.
--
--   **Formalization Note** `periodicGridKey q x` is `⌊q * Int.fract x⌋`, integer-valued and defined for an arbitrary real `q`; `dyadicGridKey b x` is `periodicGridKey (2 ^ (b + 2)) x`; the periodicity is the simp lemma `dyadicGridKey_add_one`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/DyadicAvoidance/GridGeometry.lean

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/DyadicAvoidance/GridGeometry.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the DyadicAvoidance mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_DyadicAvoidance
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_PeriodicBasic
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_GridSeparation
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_FiniteTableModel
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_OrderedRouting
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_RoutingPath
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_CenterRouteExposure
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_ExceptionalCenters
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_CenterFailureBound
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_FirstDefault
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_ConcreteLabelMeasures
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_CenterFirstDefault
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_RandomSetDensity
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_RoutedSetDensity
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_RoutedExposure
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_FirstDefaultSelection
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_FiniteLocalPredicate
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_WindowData
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_WindowTableModel
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_StableRoutingBridge
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_WindowExceptionalTransfer
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_TrialAddresses
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_WindowTrialAddresses
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_ConcreteWindowAtom
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_PeriodicEnvelope
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_GlobalFromPeriodic

namespace OAI

noncomputable section
namespace Problem310

/-- The integer label of the half-open periodic grid cell containing a point. -/
def periodicGridKey (q x : ℝ) : ℤ := ⌊q * Int.fract x⌋

/-- Periodic cells used for a dyadic window with last index `b`. -/
def dyadicGridKey (b : ℕ) (x : ℝ) : ℤ := periodicGridKey ((2 : ℝ) ^ (b + 2)) x

@[simp] theorem dyadicGridKey_add_one (b : ℕ) (x : ℝ) :
    dyadicGridKey b (x + 1) = dyadicGridKey b x := by
  simp [dyadicGridKey, periodicGridKey, Int.fract_add_one]

end Problem310

end

end OAI


