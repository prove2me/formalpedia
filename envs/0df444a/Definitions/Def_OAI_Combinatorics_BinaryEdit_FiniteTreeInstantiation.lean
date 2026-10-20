-- Prove2me | Definitions.Def_OAI_Combinatorics_BinaryEdit_FiniteTreeInstantiation
-- name    : OAI_Combinatorics_BinaryEdit_FiniteTreeInstantiation
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T14:42:51.52466+00:00
-- url     : https://prove2.me/theorems/78e7d942-baf5-49b8-8d59-14f3a78c7f7c
-- title:
--   The concrete finite-tree words
-- statement:
--   These notions belong to a formal proof that edit distance on binary words is far from $\ell_1$: for some $c>0$ and all large $d$ there are sets of equal-length binary words of length at most $d$ whose least $\ell_1$ distortion under edit distance is at least $\exp\bigl(c\sqrt{\log d\,\log\log d}\bigr)$. Words over a large alphabet are built recursively along a finite tree, with states in a product of cyclic groups. A Fourier argument shows that every $1$-Lipschitz map into $\ell_1$ moves a fixed translation little on average, while longest-common-subsequence estimates keep that translation far in edit distance. A random binary block code transfers the bound to binary words. The finite tree has branching $m$ and depth $k$; nodes are lists $p$ of child labels, and a leaf is a path of length $k$. A row word at a node of height $h+1$ concatenates, for $a=0,\dots,T-1$, the $m$ child words with state shifted by $a\,u(p)$. Fix integers $p(q,i)$ and a default child $i_0$.
--
--   1. **Prefix extension.** A node $p$ of depth at most $k$ is extended to a full leaf by filling the remaining levels with $i_0$.
--   2. **Word vectors and periods.** The leaf periods $Q(l)$, and at each node $p$ the vectors $u(p)=u_{|p|}(\cdot)$ and $w(p)=w_{|p|}(\cdot)$ of the extended leaf, with prefix period $\pi(p)$. Then $\pi(\varnothing)=2$, and at a leaf $w(l)_l=1$.
--   3. **Tree word and root word.** $\omega_h(p,x)$, the recursive node word with the tagged leaf decoder and the shifts $u(p)$; and the root word
--   $$
--   G(x)=\omega_k(\varnothing,x),\qquad|G(x)|=(mT)^k .
--   $$
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/BinaryEdit/FiniteTreeInstantiation.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/BinaryEdit/FiniteTreeInstantiation.lean by skeleton subtraction
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

namespace OAI

/-! Instantiate the recursive word evaluator with the explicit finite state
group and subtree vectors. -/

noncomputable section

namespace TreeEdit.BinaryLower.FiniteTree

/-- Total extension of a node prefix to a full leaf path. Its unused tail is
irrelevant to every vector at the depth of that prefix. -/
def extendPrefix {m k : ℕ} (i₀ : Fin m) (p : List (Fin m)) : Fin k → Fin m :=
  fun q => p.getD q.val i₀

theorem agrees_extendPrefix_iff {m k : ℕ} (i₀ : Fin m) (p : List (Fin m))
    (hp : p.length ≤ k) (l : Fin k → Fin m) :
    FiniteVectors.Agrees p.length (extendPrefix i₀ p) l ↔ p <+: List.ofFn l := by
  constructor
  · intro ha
    apply List.prefix_iff_getElem.mpr
    refine ⟨by simpa using hp, ?_⟩
    intro j hj
    have h := ha ⟨j, lt_of_lt_of_le hj hp⟩ hj
    change l ⟨j, _⟩ = p.getD j i₀ at h
    rw [List.getD_eq_getElem p i₀ hj] at h
    simpa using h.symm
  · intro ha q hq
    have h := ha.getElem hq
    change l q = p.getD q.val i₀
    rw [List.getD_eq_getElem p i₀ hq]
    simpa using h.symm

theorem extendPrefix_leaf {m k : ℕ} (i₀ : Fin m) (p : List (Fin m))
    (hp : p.length = k) : extendPrefix i₀ p = leafEquiv m k ⟨p, hp⟩ := by
  funext q
  change p.getD q.val i₀ = p.get (q.cast hp.symm)
  exact List.getD_eq_get p i₀ (q.cast hp.symm)

/-- The actual leaf periods, in the list-path presentation used by the words. -/
def wordPeriods {m k : ℕ} (primes : Fin k → Fin m → ℕ) : Leaf m k → ℕ :=
  fun l => FiniteVectors.leafPeriod primes (leafEquiv m k l)

/-- Actual cheap subgroup vector at a list prefix. -/
def wordU {m k : ℕ} (primes : Fin k → Fin m → ℕ) (i₀ : Fin m)
    (p : List (Fin m)) : State (wordPeriods primes) :=
  pullState (FiniteVectors.leafPeriod primes)
    (FiniteVectors.u primes p.length (extendPrefix i₀ p))

/-- Actual distinguished subgroup vector at a list prefix. -/
def wordW {m k : ℕ} (primes : Fin k → Fin m → ℕ) (i₀ : Fin m)
    (p : List (Fin m)) : State (wordPeriods primes) :=
  pullState (FiniteVectors.leafPeriod primes)
    (FiniteVectors.w primes p.length (extendPrefix i₀ p))

/-- Prescribed period at a list prefix. -/
def wordPeriod {m k : ℕ} (primes : Fin k → Fin m → ℕ) (i₀ : Fin m)
    (p : List (Fin m)) : ℕ :=
  FiniteVectors.prefixPeriod primes p.length (extendPrefix i₀ p)

/-- The concrete tree word at an arbitrary node. -/
def finiteWord {m k : ℕ} (primes : Fin k → Fin m → ℕ) (i₀ : Fin m)
    (T h : ℕ) (p : List (Fin m)) (x : State (wordPeriods primes)) :
    List (Symbol (wordPeriods primes)) :=
  nodeWord T (leafDecoder (wordPeriods primes) ⟨List.replicate k i₀, by simp⟩)
    (wordU primes i₀) h p x

@[simp] theorem finiteWord_length {m k : ℕ} (primes : Fin k → Fin m → ℕ)
    (i₀ : Fin m) (T h : ℕ) (p : List (Fin m)) (x : State (wordPeriods primes)) :
    (finiteWord primes i₀ T h p x).length = (m * T) ^ h := by
  simp [finiteWord]

@[simp] theorem ofFn_leafEquiv {m k : ℕ} (l : Leaf m k) :
    List.ofFn (leafEquiv m k l) = l.val := by
  rcases l with ⟨l, hl⟩
  subst k
  change List.ofFn l.get = l
  exact List.ofFn_get l

@[simp] theorem wordW_leaf_self {m k : ℕ} (primes : Fin k → Fin m → ℕ)
    (i₀ : Fin m) (p : List (Fin m)) (hp : p.length = k) :
    wordW primes i₀ p ⟨p, hp⟩ = 1 := by
  change FiniteVectors.w primes p.length (extendPrefix i₀ p)
    (leafEquiv m k ⟨p, hp⟩) = 1
  rw [hp, extendPrefix_leaf i₀ p hp]
  simp [FiniteVectors.w_leaf]

@[simp] theorem wordPeriod_leaf {m k : ℕ} (primes : Fin k → Fin m → ℕ)
    (i₀ : Fin m) (p : List (Fin m)) (hp : p.length = k) :
    wordPeriod primes i₀ p = wordPeriods primes ⟨p, hp⟩ := by
  simp [wordPeriod, wordPeriods, hp, extendPrefix_leaf i₀ p hp,
    FiniteVectors.prefixPeriod, FiniteVectors.leafPeriod]

@[simp] theorem wordPeriod_root {m k : ℕ} (primes : Fin k → Fin m → ℕ) (i₀ : Fin m) :
    wordPeriod primes i₀ [] = 2 := by simp [wordPeriod]

@[simp] theorem wordU_off_subtree {m k : ℕ} (primes : Fin k → Fin m → ℕ)
    (i₀ : Fin m) (p : List (Fin m)) (hp : p.length ≤ k)
    (l : Leaf m k) (hl : ¬ p <+: l.val) : wordU primes i₀ p l = 0 := by
  have ha : ¬ FiniteVectors.Agrees p.length (extendPrefix i₀ p) (leafEquiv m k l) := by
    rw [agrees_extendPrefix_iff i₀ p hp, ofFn_leafEquiv]
    exact hl
  exact FiniteVectors.u_off_subtree primes p.length (extendPrefix i₀ p) (leafEquiv m k l) ha

@[simp] theorem wordW_off_subtree {m k : ℕ} (primes : Fin k → Fin m → ℕ)
    (i₀ : Fin m) (p : List (Fin m)) (hp : p.length ≤ k)
    (l : Leaf m k) (hl : ¬ p <+: l.val) : wordW primes i₀ p l = 0 := by
  have ha : ¬ FiniteVectors.Agrees p.length (extendPrefix i₀ p) (leafEquiv m k l) := by
    rw [agrees_extendPrefix_iff i₀ p hp, ofFn_leafEquiv]
    exact hl
  exact FiniteVectors.w_off_subtree primes p.length (extendPrefix i₀ p) (leafEquiv m k l) ha

/-- Root words, retaining their exact common length in the type. -/
def rootWord {m k : ℕ} (primes : Fin k → Fin m → ℕ) (i₀ : Fin m) (T : ℕ)
    (x : State (wordPeriods primes)) : Word (Symbol (wordPeriods primes)) ((m * T) ^ k) :=
  ⟨finiteWord primes i₀ T k [] x, finiteWord_length primes i₀ T k [] x⟩

end TreeEdit.BinaryLower.FiniteTree

end

end OAI


