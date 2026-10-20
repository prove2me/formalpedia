-- Prove2me | Definitions.Def_OAI_Combinatorics_DiscreteConvexity_CoveringBasic
-- name    : OAI_Combinatorics_DiscreteConvexity_CoveringBasic
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T15:33:56.618137+00:00
-- url     : https://prove2.me/theorems/6d4e0c56-019a-411f-ab6e-26c648aa3035
-- title:
--   Edge tuples, sampling indices, weighted degrees and regular edges
-- statement:
--   Let $V$ be a set and $H$ a finite family of subsets of $V$ (edges).
--
--   1. **Edge tuples.** An injective ordered $t$-tuple of edges of $H$, with union $\bigcup_ie_i$ and set of ordered pairs $\{(e_i,e_j)\}$, diagonal pairs included.
--   2. **Sampling.** Sampling indices are the ordered pairs of edges; a sample is a set of such pairs.
--   3. **Weighted degree.** For $\rho\in\mathbb{R}$, $r\in\mathbb{N}$ and $I\subseteq V$,
--   $$
--   d_\rho(I)=\#\{e\in H:I\subseteq e\}\cdot\rho^{\,r-|I|}.
--   $$
--   4. **Regular edges.** Given a family $\mathcal{C}_0$, the edges containing no member of $\mathcal{C}_0$. With $V$ finite, the initial family consists of the sets $I$ with $|I|\le r$ and $d_\rho(I)>T$, and the regular edges are those avoiding all initial sets.
--   5. **Dense family.** The sets containing at least $m$ distinct edges of $H$.
--
--   These are the objects of the elementary covering lemma. Dense sets are covered either by a high-degree initial set, by a sampled pair union, or by a residual tuple union.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/DiscreteConvexity/CoveringBasic.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/DiscreteConvexity/CoveringBasic.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the TalagrandDiscreteConvexity mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Monoid.Unbundled.Pow
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Definitions.Def_TalagrandDiscreteConvexity
import Definitions.Def_OAI_Combinatorics_DiscreteConvexity_Model
import Definitions.Def_OAI_Combinatorics_DiscreteConvexity_Basic
import Definitions.Def_OAI_Combinatorics_DiscreteConvexity_DyadicBins
import Definitions.Def_OAI_Combinatorics_DiscreteConvexity_FiniteFibers
import Definitions.Def_OAI_Combinatorics_DiscreteConvexity_Bins

namespace OAI

/-!
# Finite objects in the elementary covering argument

Sampling is indexed by ordered pairs of edges, including diagonal pairs.
Different pairs remain different indices even if their unions coincide.
Residual generators are indexed by injective ordered tuples.
-/

namespace TalagrandDiscreteConvexity.Covering

variable {V : Type*} [DecidableEq V]

/-- An ordered tuple of distinct members of a finite edge family. -/
def EdgeTuple (H : Family V) (t : ℕ) :=
  {f : Fin t → ↥H // Function.Injective f}

noncomputable instance edgeTupleFintype (H : Family V) (t : ℕ) :
    Fintype (EdgeTuple H t) := by
  classical
  exact Subtype.fintype _

/-- All independent ordered-pair sampling indices. -/
abbrev PairIndex (H : Family V) := ↥H × ↥H

/-- A sampling outcome specifies precisely the pairs selected. -/
abbrev Sample (H : Family V) := Finset (PairIndex H)

def tupleUnion {H : Family V} {t : ℕ} (f : EdgeTuple H t) : Finset V :=
  Finset.univ.biUnion (fun i => (f.val i).val)

noncomputable def tuplePairs {H : Family V} {t : ℕ}
    (f : EdgeTuple H t) : Finset (PairIndex H) := by
  classical
  exact Finset.univ.image (fun ij : Fin t × Fin t => (f.val ij.1, f.val ij.2))

@[simp] theorem mem_tupleUnion {H : Family V} {t : ℕ}
    {f : EdgeTuple H t} {v : V} :
    v ∈ tupleUnion f ↔ ∃ i, v ∈ (f.val i).val := by
  simp [tupleUnion]

@[simp] theorem mem_tuplePairs {H : Family V} {t : ℕ}
    {f : EdgeTuple H t} {p : PairIndex H} :
    p ∈ tuplePairs f ↔ ∃ i j, (f.val i, f.val j) = p := by
  classical
  simp [tuplePairs, Prod.exists]

/-- The weighted number of edges containing a prescribed vertex set. -/
noncomputable def weightedDegree (H : Family V) (rho : ℝ) (r : ℕ)
    (I : Finset V) : ℝ := by
  classical
  exact ((H.filter (fun e => I ⊆ e)).card : ℝ) * rho ^ (r - I.card)

/-- Edges avoiding all prescribed initial generators. -/
noncomputable def regularFamily (H C0 : Family V) : Family V := by
  classical
  exact H.filter (fun e => ∀ I ∈ C0, ¬ I ⊆ e)

@[simp] theorem mem_regularFamily {H C0 : Family V} {e : Finset V} :
    e ∈ regularFamily H C0 ↔ e ∈ H ∧ ∀ I ∈ C0, ¬ I ⊆ e := by
  classical
  simp [regularFamily]

section FiniteGround

variable [Fintype V]

/-- The high weighted-degree sets used as the initial generators. -/
noncomputable def initialFamily (H : Family V) (rho : ℝ) (r : ℕ)
    (T : ℝ) : Family V := by
  classical
  exact Finset.univ.filter (fun I => I.card ≤ r ∧ T < weightedDegree H rho r I)

/-- The regular edges for the actual high-degree initial family. -/
noncomputable def regularEdges (H : Family V) (rho : ℝ) (r : ℕ)
    (T : ℝ) : Family V := regularFamily H (initialFamily H rho r T)

/-- Sets containing at least `m` distinct edges of the original family. -/
noncomputable def denseFamily (H : Family V) (m : ℕ) : Family V := by
  classical
  exact Finset.univ.filter (fun S => m ≤ (H.filter (fun e => e ⊆ S)).card)

@[simp] theorem mem_initialFamily {H : Family V} {rho T : ℝ}
    {r : ℕ} {I : Finset V} :
    I ∈ initialFamily H rho r T ↔ I.card ≤ r ∧ T < weightedDegree H rho r I := by
  classical
  simp [initialFamily]

@[simp] theorem mem_regularEdges {H : Family V} {rho T : ℝ}
    {r : ℕ} {e : Finset V} :
    e ∈ regularEdges H rho r T ↔
      e ∈ H ∧ ∀ I ∈ initialFamily H rho r T, ¬ I ⊆ e := by
  exact mem_regularFamily

@[simp] theorem mem_denseFamily {H : Family V} {m : ℕ} {S : Finset V} :
    S ∈ denseFamily H m ↔ m ≤ (H.filter (fun e => e ⊆ S)).card := by
  classical
  simp [denseFamily]

end FiniteGround

end TalagrandDiscreteConvexity.Covering

end OAI


