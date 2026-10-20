-- Prove2me | Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteSeparation
-- name    : OAI_Combinatorics_BinaryEdit_FiniteSeparation
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T15:07:15.148845+00:00
-- url     : https://prove2.me/theorems/837abc7a-a535-46fb-854f-b8ba131a995b
-- title:
--   Block arrays and separated children in the finite tree
-- statement:
--   These notions belong to a formal proof that edit distance on binary words is far from $\ell_1$: for some $c>0$ and all large $d$ there are sets of equal-length binary words of length at most $d$ whose least $\ell_1$ distortion under edit distance is at least $\exp\bigl(c\sqrt{\log d\,\log\log d}\bigr)$. Words over a large alphabet are built recursively along a finite tree, with states in a product of cyclic groups. A Fourier argument shows that every $1$-Lipschitz map into $\ell_1$ moves a fixed translation little on average, while longest-common-subsequence estimates keep that translation far in edit distance. A random binary block code transfers the bound to binary words. The finite tree has branching $m$ and depth $k$; nodes are lists $p$ of child labels, and a leaf is a path of length $k$. A row word at a node of height $h+1$ concatenates, for $a=0,\dots,T-1$, the $m$ child words with state shifted by $a\,u(p)$.
--
--   1. **Finite blocks.** At a node $p$ with state $x$, the $T\times m$ array of child words
--   $$
--   X_{a,i}=\omega_h\bigl(p\,i,\ x+a\,u(p)\bigr),
--   $$
--   whose concatenation is the node word.
--   2. **Row shift.** For rows $a,b$ and $t\in\mathbb Z$, the coefficient $(b-a)+t\,\prod_ip(|p|,i)$ comparing two rows.
--   3. **Separated children.** The children $i$ whose prescribed period $\pi(p\,i)$ does not divide this coefficient; their rows are genuinely shifted relative to each other.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/BinaryEdit/FiniteSeparation.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/BinaryEdit/FiniteSeparation.lean by skeleton subtraction
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

namespace OAI

/-!
# Geometric separation for the concrete finite tree

The prime construction supplies the half-child condition in the
geometric induction.
-/

noncomputable section
namespace TreeEdit.BinaryLower.FiniteTree

open scoped BigOperators

/-- Literal row/block array of a concrete node word. -/
def finiteBlocks {m k : ℕ} (primes : Fin k → Fin m → ℕ) (i₀ : Fin m)
    (T h : ℕ) (p : List (Fin m)) (x : State (wordPeriods primes)) :
    Fin T → Fin m → Word (Symbol (wordPeriods primes)) ((m * T) ^ h) :=
  fun a i => ⟨finiteWord primes i₀ T h (p ++ [i]) (x + a.val • wordU primes i₀ p),
    finiteWord_length primes i₀ T h _ _⟩

/-- The relative coefficient comparing two rows in a child. -/
def finiteRowShift {m k T : ℕ} (primes : Fin k → Fin m → ℕ)
    (p : List (Fin m)) (hp : p.length < k) (a b : Fin T) (t : ℤ) : ℤ :=
  (b.val : ℤ) - (a.val : ℤ) + t *
    (FiniteVectors.levelProduct primes ⟨p.length, hp⟩ : ℤ)

/-- Children whose prescribed period does not divide the relative coefficient. -/
def separatedChildren {m k T : ℕ} (primes : Fin k → Fin m → ℕ)
    (i₀ : Fin m) (p : List (Fin m)) (hp : p.length < k) (a b : Fin T) (t : ℤ) :
    Finset (Fin m) :=
  Finset.univ.filter fun i => ¬ (wordPeriod primes i₀ (p ++ [i]) : ℤ) ∣
    finiteRowShift primes p hp a b t

end TreeEdit.BinaryLower.FiniteTree

end

end OAI


