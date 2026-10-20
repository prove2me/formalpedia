-- Prove2me | Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteWordDetection
-- name    : OAI_Combinatorics_BinaryEdit_FiniteWordDetection
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T15:18:52.423047+00:00
-- url     : https://prove2.me/theorems/bde2c322-8e1d-4231-9108-2135f6cd5ceb
-- title:
--   Leaf coordinates in the word-state presentation
-- statement:
--   These notions belong to a formal proof that edit distance on binary words is far from $\ell_1$: for some $c>0$ and all large $d$ there are sets of equal-length binary words of length at most $d$ whose least $\ell_1$ distortion under edit distance is at least $\exp\bigl(c\sqrt{\log d\,\log\log d}\bigr)$. Words over a large alphabet are built recursively along a finite tree, with states in a product of cyclic groups. A Fourier argument shows that every $1$-Lipschitz map into $\ell_1$ moves a fixed translation little on average, while longest-common-subsequence estimates keep that translation far in edit distance. A random binary block code transfers the bound to binary words. The finite tree has branching $m$ and depth $k$; nodes are lists $p$ of child labels, and a leaf is a path of length $k$. A row word at a node of height $h+1$ concatenates, for $a=0,\dots,T-1$, the $m$ child words with state shifted by $a\,u(p)$.
--
--   1. **Additive relabeling.** The pullback of states from function-indexed leaves to list-indexed leaves, as a group homomorphism.
--   2. **Word leaf coordinate.** For a leaf $f$, the cyclic coordinate $\mathbb Z/Q(f)\to$ (word state group) obtained by composing the leaf coordinate with this relabeling. Its generator is the word vector at the leaf,
--   $$
--   \iota_f(1)=w(f),
--   $$
--   so the spectral detection argument applies to the actual recursive words.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/BinaryEdit/FiniteWordDetection.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/BinaryEdit/FiniteWordDetection.lean by skeleton subtraction
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
import Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteCoordinates

namespace OAI

/-!
# Sparse detection for the concrete recursive word model

The list-prefix vectors used by `finiteWord` satisfy the same exact recursion
and period bounds as the function-prefix vectors. This closes the algebraic
inputs of the finite spectral detector in the actual word-state presentation.
-/

noncomputable section

open scoped BigOperators
open Classical

namespace TreeEdit.BinaryLower.FiniteTree

variable {m k : ℕ}

/-- Relabeling the product factors is additive, not merely a map of sets. -/
def pullStateHom (Q : (Fin k → Fin m) → ℕ) :
    (∀ l, ZMod (Q l)) →+ State (fun l => Q (leafEquiv m k l)) where
  toFun := pullState Q
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The actual word-state cyclic coordinate, indexed by the same function
leaves as the spectral tree's finite leaf set. -/
def wordLeafCoordinate (primes : Fin k → Fin m → ℕ) (f : Fin k → Fin m) :
    ZMod (FiniteVectors.leafPeriod primes f) →+ State (wordPeriods primes) :=
  (pullStateHom (FiniteVectors.leafPeriod primes)).comp
    (FiniteVectors.leafCoordinate primes f)

@[simp] theorem extendPrefix_ofFn (i₀ : Fin m) (f : Fin k → Fin m) :
    extendPrefix i₀ (List.ofFn f) = f := by
  funext q
  simp [extendPrefix, q.isLt]

/-- This is precisely the generator identity of the spectral tree theorem. -/
@[simp] theorem wordLeafCoordinate_one (primes : Fin k → Fin m → ℕ)
    (i₀ : Fin m) (f : Fin k → Fin m) :
    wordLeafCoordinate primes f 1 = wordW primes i₀ (List.ofFn f) := by
  change pullState (FiniteVectors.leafPeriod primes)
    (FiniteVectors.leafCoordinate primes f 1) = _
  rw [FiniteVectors.leafCoordinate_one]
  simp only [wordW, List.length_ofFn, extendPrefix_ofFn]

end TreeEdit.BinaryLower.FiniteTree

end

end OAI


