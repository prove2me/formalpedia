-- Prove2me | Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteCoordinates
-- name    : OAI_Combinatorics_BinaryEdit_FiniteCoordinates
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T15:17:34.580121+00:00
-- url     : https://prove2.me/theorems/73b2467d-dd89-4e2f-bd96-802f901b32b2
-- title:
--   Cyclic leaf coordinates of the state group
-- statement:
--   These notions belong to a formal proof that edit distance on binary words is far from $\ell_1$: for some $c>0$ and all large $d$ there are sets of equal-length binary words of length at most $d$ whose least $\ell_1$ distortion under edit distance is at least $\exp\bigl(c\sqrt{\log d\,\log\log d}\bigr)$. Words over a large alphabet are built recursively along a finite tree, with states in a product of cyclic groups. A Fourier argument shows that every $1$-Lipschitz map into $\ell_1$ moves a fixed translation little on average, while longest-common-subsequence estimates keep that translation far in edit distance. A random binary block code transfers the bound to binary words. The finite tree has branching $m$ and depth $k$; nodes are lists $p$ of child labels, and a leaf is a path of length $k$. A row word at a node of height $h+1$ concatenates, for $a=0,\dots,T-1$, the $m$ child words with state shifted by $a\,u(p)$. Let the state group be $\prod_a\mathbb Z/Q(a)$, with $Q(a)=2\prod_qp(q,a_q)$.
--
--   1. **Leaf coordinate.** For a leaf $a$, the homomorphism
--   $$
--   \iota_a:\mathbb Z/Q(a)\to\prod_b\mathbb Z/Q(b),\qquad\iota_a(z)_b=\begin{cases}z,&b=a,\\0,&b\ne a.\end{cases}
--   $$
--   Its generator $\iota_a(1)$ is the leaf vector $w_k(a)$. The obstruction averages over these coordinate cyclic subgroups.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/BinaryEdit/FiniteCoordinates.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/BinaryEdit/FiniteCoordinates.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the BinaryEditLower mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_BinaryEditLower
import Definitions.Def_OAI_Combinatorics_TreeEdit_Model__BinaryEditLower
import Definitions.Def_OAI_Combinatorics_BinaryEdit_Model
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteTreeWords
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteTreeGeometry
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteVectors
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteVectorRestrictions
import Definitions.Def_OAI_Combinatorics_BinaryEdit_WordFinite
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteTreeInstantiation
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteTreeTags
import Definitions.Def_OAI_Combinatorics_BinaryEdit_TaggedGaps
import Definitions.Def_OAI_Combinatorics_BinaryEdit_TaggedNonsplit
import Definitions.Def_OAI_Combinatorics_TreeEdit_EditMetric__BinaryEditLower
import Definitions.Def_OAI_Combinatorics_TreeEdit_Alignments__BinaryEditLower
import Definitions.Def_OAI_Combinatorics_BinaryEdit_LCS
import Definitions.Def_OAI_Combinatorics_BinaryEdit_TaggedExtraction
import Definitions.Def_OAI_Combinatorics_BinaryEdit_BlockExtraction
import Definitions.Def_OAI_Combinatorics_BinaryEdit_TaggedRowLCS
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteSeparation
import Definitions.Def_OAI_Combinatorics_BinaryEdit_Branching
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteActivityBridge
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteFourier
import Definitions.Def_OAI_Combinatorics_BinaryEdit_ScalarCutsBool

namespace OAI

/-!
# Cyclic leaf coordinates

The obstruction averages over the coordinate cyclic groups of the concrete
finite parameter space. Coordinate homomorphisms have exact generators
and a natural-multiple representation.
-/

noncomputable section

namespace TreeEdit.BinaryLower.FiniteVectors

variable {m k : ℕ}

/-- Insertion into one factor of the manuscript's product of cyclic groups. -/
def leafCoordinate (p : Fin k → Fin m → ℕ) (a : Leaf m k) :
    ZMod (leafPeriod p a) →+ State p where
  toFun := Pi.single (M := fun b : Leaf m k => ZMod (leafPeriod p b)) a
  map_zero' := Pi.single_zero (M := fun b : Leaf m k => ZMod (leafPeriod p b)) a
  map_add' := Pi.single_add (f := fun b : Leaf m k => ZMod (leafPeriod p b)) a

@[simp] theorem leafCoordinate_apply_self (p : Fin k → Fin m → ℕ)
    (a : Leaf m k) (z : ZMod (leafPeriod p a)) :
    leafCoordinate p a z a = z :=
  Pi.single_eq_same (M := fun b : Leaf m k => ZMod (leafPeriod p b)) a z

@[simp] theorem leafCoordinate_apply_ne (p : Fin k → Fin m → ℕ)
    (a b : Leaf m k) (h : b ≠ a) (z : ZMod (leafPeriod p a)) :
    leafCoordinate p a z b = 0 :=
  Pi.single_eq_of_ne (M := fun b : Leaf m k => ZMod (leafPeriod p b)) h z

/-- The coordinate generator is exactly the already constructed leaf vector. -/
@[simp] theorem leafCoordinate_one (p : Fin k → Fin m → ℕ) (a : Leaf m k) :
    leafCoordinate p a 1 = w p k a := by
  funext b
  rw [w_leaf]
  by_cases hab : b = a
  · subst b
    simp
  · simp [hab]

end TreeEdit.BinaryLower.FiniteVectors

end

end OAI


