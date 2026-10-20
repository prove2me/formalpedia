-- Prove2me | Definitions.Def_OAI_Combinatorics_ExpectationThreshold_SelectorCountingEncoding
-- name    : OAI_Combinatorics_ExpectationThreshold_SelectorCountingEncoding
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T12:35:39.892237+00:00
-- url     : https://prove2.me/theorems/627dfa3f-330a-47b8-a327-ad0c165c80f3
-- title:
--   Encoding a coloring by its moved rows
-- statement:
--   Fix $s\in\mathbb{N}$. Colors are $0,1,\dots,s$ and a coloring is a map $a:X\to\{0,\dots,s\}$. For $i<s$ the prefix of a coloring $z$ is $P_i(z)=\{x:z(x)\le i\}$, and $d_i=2^{-(i+1)}$. A mass family assigns to every member $H\in\mathcal{F}$ a probability vector $\mu_H$ on $X$ supported in $H$. For colorings $a,z$ and $i<s$, the moved row $i$ is $\{x:z(x)=i<a(x)\}$.
--
--   1. **Row record.** A pair consisting of a subset $U$ and a labelling $U\to\{0,\dots,s\}$. The record of row $i$ is the moved row together with the original colors $a|_{\text{row}}$.
--   2. **Lookup.** Reading a point $x$ of a record gives its label if $x\in U$, and nothing otherwise:
--   $$
--   \mathrm{lookup}(U,\ell)(x)=\begin{cases}\ell(x),&x\in U,\\\text{none},&x\notin U.\end{cases}
--   $$
--
--   For an earlier coloring $z$, the moved rows and their original labels determine $a$. Outside the rows, $a$ agrees with $z$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/ExpectationThreshold/SelectorCountingEncoding.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/ExpectationThreshold/SelectorCountingEncoding.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the TalagrandExpectationThreshold mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Find
import Mathlib.Data.Real.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Order.Compact
import Definitions.Def_TalagrandExpectationThreshold
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_Model
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_Basic
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_RoundingMasses
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_ProbabilityFinite
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_ProbabilityProduct
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_RoundingExpectation
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_ProbabilityColors
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_ScaleBounds
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_SelectorTruncationDefinitions
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_SelectorDefinitions
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_SelectorFeasibility

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-!
# Reconstruction from the actual changed rows

For an earlier coloring, every point outside the changed rows retains its final
color. Inside a changed row its original color is recorded. Thus the changed
subsets and their original labels determine the entire original coloring.
-/

noncomputable section

namespace TalagrandThreshold.Selector

variable {α : Type*} [Fintype α] [DecidableEq α] {s : ℕ}

/-- The unrestricted row record consists of its actual support and its labels. -/
abbrev RawRowEncoding (α : Type*) (s : ℕ) :=
  Σ U : Finset α, (↥U → Color s)

def rawRowEncoding (a z : Coloring α s) (i : Fin s) : RawRowEncoding α s :=
  ⟨movedRow a z i, fun x => a x.1⟩

/-- Reading one point avoids any dependence on the chosen subtype proof. -/
def rawRowLookup (E : RawRowEncoding α s) (x : α) : Option (Color s) :=
  if hx : x ∈ E.1 then some (E.2 ⟨x, hx⟩) else none

end TalagrandThreshold.Selector

end

end OAI


