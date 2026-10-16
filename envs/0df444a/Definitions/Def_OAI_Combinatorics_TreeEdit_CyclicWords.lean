-- Prove2me | Definitions.Def_OAI_Combinatorics_TreeEdit_CyclicWords
-- name    : OAI_Combinatorics_TreeEdit_CyclicWords
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-16T01:17:46.725987+00:00
-- url     : https://prove2.me/theorems/84ab0c34-0336-4525-854f-ed538718f2d9
-- title:
--   Fixed-length words as functions and row-by-row interleaving of child words
-- statement:
--   This file provides a functional interface to fixed-length words and the interleaving operation that builds a node's word from its children's words in a tree construction. Here $\mathrm{Word}(\beta,n)$ denotes the words of length exactly $n$ over an alphabet $\beta$, positions are numbered from $0$, and $[n]=\{0,\dots,n-1\}$.
--
--   1. **Reading and building words.** For $x\in\mathrm{Word}(\beta,n)$ and $i\in[n]$, $x[i]$ is the symbol of $x$ at position $i$. A function $u:[n]\to\beta$ defines the word $u(0)u(1)\cdots u(n-1)$, whose symbol at position $i$ is $u(i)$.
--
--   2. **Letterwise map.** For $f:\beta\to\gamma$, the word $f(x)\in\mathrm{Word}(\gamma,n)$ applies $f$ to every symbol, so $f(x)[i]=f(x[i])$.
--
--   3. **Cyclic interleaving.** Let $\beta_0,\dots,\beta_{m-1}$ be alphabets, and for every row $a\in[T]$ and child $i\in[m]$ let $X_{a,i}\in\mathrm{Word}(\beta_i,B)$. Tag each symbol $b$ of $X_{a,i}$ by its child index, $b\mapsto(i,b)$, and write $\overline{X}_{a,i}$ for the tagged word. The interleaved word is the concatenation of $T$ rows, each row being the concatenation of the $m$ tagged child words in order:
--
--      $$\operatorname{cyc}(X)=\bigl(\overline{X}_{0,0}\cdots\overline{X}_{0,m-1}\bigr)\bigl(\overline{X}_{1,0}\cdots\overline{X}_{1,m-1}\bigr)\cdots\bigl(\overline{X}_{T-1,0}\cdots\overline{X}_{T-1,m-1}\bigr),$$
--
--      a word of length $TmB$ over the disjoint union of the alphabets $\beta_i$. Explicitly, position $r=a\,mB+iB+p$ with $a\in[T]$, $i\in[m]$, $p\in[B]$ carries the symbol $\bigl(i,\,X_{a,i}[p]\bigr)$.
--
--   In tree constructions for edit-distance lower bounds, each internal node writes $T$ rows, and the $a$-th row lists the words of its $m$ children computed with row-dependent parameters. Tagging by the child index makes the child alphabets disjoint, so a common subsequence of two interleaved words can only match symbols coming from the same child; this is what allows deficits to be accumulated over children and rows.
--
--   **Formalization Note** The Lean names are `Words.get`, `Words.ofFn`, `Words.map` and `Words.cycles`, with the simp lemmas `at_ofFn`, `at_map` and `at_cycles` giving the symbol at each position. The tagged alphabet is the dependent sum `Sigma β`, and a position of `Fin (T * (m * B))` is decomposed with `Fin.divNat` and `Fin.modNat`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/TreeEdit/CyclicWords.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/TreeEdit/CyclicWords.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the TreeEdit mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_TreeEdit
import Definitions.Def_OAI_Combinatorics_TreeEdit_Model
import Definitions.Def_OAI_Combinatorics_TreeEdit_FiniteProbability
import Definitions.Def_OAI_Combinatorics_TreeEdit_EditMetric
import Definitions.Def_OAI_Combinatorics_TreeEdit_Alignments
import Definitions.Def_OAI_Combinatorics_TreeEdit_SegmentComparison

namespace OAI

namespace TreeEdit

universe u

attribute [local instance] Classical.propDecidable

namespace Words

variable {β : Type*} {n : ℕ}

def get (x : Word β n) (i : Fin n) : β := x.val.get (Fin.cast x.property.symm i)

def ofFn (x : Fin n → β) : Word β n := ⟨List.ofFn x, List.length_ofFn⟩

@[simp] lemma at_ofFn (x : Fin n → β) (i : Fin n) : get (ofFn x) i = x i := by
  simp [get, ofFn, List.get_eq_getElem, Fin.cast]

def map {γ : Type*} (f : β → γ) (x : Word β n) : Word γ n :=
  ⟨x.val.map f, by simp [x.property]⟩

@[simp] lemma at_map {γ : Type*} (f : β → γ) (x : Word β n) (i : Fin n) :
    get (map f x) i = f (get x i) := by simp [get, map, List.get_eq_getElem, Fin.cast]

def cycles {m T B : ℕ} {β : Fin m → Type*}
    (blocks : Fin T → ∀ i, Word (β i) B) : Word (Sigma β) (T * (m * B)) :=
  ofFn fun r => ⟨r.modNat.divNat, get (blocks r.divNat r.modNat.divNat) r.modNat.modNat⟩

@[simp] lemma at_cycles {m T B : ℕ} {β : Fin m → Type*}
    (blocks : Fin T → ∀ i, Word (β i) B) (r : Fin (T * (m * B))) :
    get (cycles blocks) r =
      ⟨r.modNat.divNat, get (blocks r.divNat r.modNat.divNat) r.modNat.modNat⟩ := by
  simp [cycles]

end Words

end TreeEdit

end OAI


