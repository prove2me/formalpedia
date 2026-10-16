-- Prove2me | Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_TrialAddresses
-- name    : OAI_MeasureTheory_DyadicAvoidance_TrialAddresses
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-16T03:28:20.535322+00:00
-- url     : https://prove2.me/theorems/0c55d38b-3e87-49c2-9b45-96600e45cf91
-- title:
--   Named grid addresses for families of dyadic tables and uniform blocks of window trials
-- statement:
--   This file fixes the coordinate system for a finite family of Boolean tables that are read at dyadic grid cells. For $y\in\mathbb{R}$ write $\{y\}=y-\lfloor y\rfloor\in[0,1)$ for its fractional part, and for $b\in\mathbb{N}$ let
--   $$J_b(y)=\big\lfloor 2^{b+2}\{y\}\big\rfloor\in\{0,1,\dots,2^{b+2}-1\}$$
--   be the periodic dyadic key of $y$ at resolution $b$, i.e. the index $k$ of the half-open cell $[k\,2^{-(b+2)},(k+1)\,2^{-(b+2)})$ that contains $\{y\}$. Let $E$ be a set of table names and $b:E\to\mathbb{N}$ an assignment of a resolution to each table.
--
--   1. **Grid addresses.** The address set of the family is the disjoint union
--   $$\mathcal{A}_b=\bigsqcup_{e\in E}\{0,1,\dots,2^{b(e)+2}-1\}=\{(e,k): e\in E,\ 0\le k<2^{b(e)+2}\}.$$
--   Table $e$ has one entry for each key at its own resolution. Because the table name is part of the address, entries of different tables are different coordinates even when their numerical keys coincide.
--   2. **Center addresses.** For $x\in\mathbb{R}$ and $e\in E$, the center address of $x$ in table $e$ is $(e,J_{b(e)}(x))\in\mathcal{A}_b$.
--   3. **Trial addresses.** Let $I$ be a set of trials, $\theta:I\to E$ an assignment of a table to each trial, $n:I\to\mathbb{N}$ an assignment of a dyadic index to each trial, and $x,t\in\mathbb{R}$. Trial $i\in I$ reads the address
--   $$\tau_{x,t}(i)=\Big(\theta(i),\ J_{b(\theta(i))}\big(x+t\,2^{-n(i)}\big)\Big)\in\mathcal{A}_b,$$
--   the entry of table $\theta(i)$ whose cell contains the displaced point $x+t\,2^{-n(i)}$.
--   4. **Uniform window trials.** For $M,r\in\mathbb{N}$ the window-trial set is $\{0,\dots,M-1\}\times\{0,\dots,r-1\}$, a block of $r$ trials for each of $M$ children; it has exactly $Mr$ elements. Given start indices $a:\{0,\dots,M-1\}\to\mathbb{N}$, the trial $(i,k)$ uses the dyadic index $a(i)+k$, so the block of child $i$ runs through the consecutive indices $a(i),a(i)+1,\dots,a(i)+r-1$.
--
--   These objects are the bookkeeping for an independence argument in the construction of a compact set of large measure that contains no affine copy $\{x+s\,2^{-n}:n\ge1\}$, $s\neq0$, of the dyadic sequence. There, tables of independent random bits indexed by $\mathcal{A}_b$ form a finite product probability space in which different addresses are different coordinates. Showing that a family of trials reads pairwise distinct addresses, i.e. that the trial map $\tau_{x,t}$ is injective, is therefore what makes the bits read by these trials independent, and the cardinality $Mr$ becomes the exponent of the resulting miss probability.
--
--   **Formalization Note** `GridAddress b` is the sigma type `Σ e : E, Fin (2 ^ (b e + 2))`, and the key $J_b$ is `GridSeparation.dyadicKey b`, valued in `Fin (2 ^ (b + 2))`. Items 2 to 4 are `centerAddress`, `trialAddress b edge n x t` (with $\theta$ = `edge`), `WindowTrial M r = Fin M × Fin r` together with `windowTrialIndex`, and the cardinality lemma `card_windowTrial`. Lean writes $2^{-n}$ as $(2^{-1})^n$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/DyadicAvoidance/TrialAddresses.lean

-- Generated from openai/math@1581d4c lean/OAI/MeasureTheory/DyadicAvoidance/TrialAddresses.lean by skeleton subtraction
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

namespace OAI

universe u_E u_I u_C u_L

noncomputable section

namespace Problem310.TrialAddresses

open GridSeparation

/-- Coordinates of a finite family of dyadic tables. Different table names
are different coordinates even when their numeric cell keys coincide. -/
abbrev GridAddress {E : Type u_E} (b : E → ℕ) := Σ e : E, Fin (2 ^ (b e + 2))

def centerAddress {E : Type u_E} (b : E → ℕ) (x : ℝ) (e : E) : GridAddress b :=
  ⟨e, dyadicKey (b e) x⟩

def trialAddress {I : Type u_I} {E : Type u_E} (b : E → ℕ) (edge : I → E)
    (n : I → ℕ) (x t : ℝ) (i : I) : GridAddress b :=
  ⟨edge i, dyadicKey (b (edge i)) (x + t * (2 : ℝ)⁻¹ ^ n i)⟩

/-- A uniform block of `r` indices for each of `M` nondefault children.
This finite trial type has exactly the exponent used in the miss formula. -/
abbrev WindowTrial (M r : ℕ) := Fin M × Fin r

def windowTrialIndex {M r : ℕ} (a : Fin M → ℕ) (i : WindowTrial M r) : ℕ :=
  a i.1 + i.2.val

@[simp] theorem card_windowTrial (M r : ℕ) :
    Fintype.card (WindowTrial M r) = M * r := by simp [WindowTrial]

end Problem310.TrialAddresses

end

end OAI


