-- Prove2me | Definitions.Def_OAI_Combinatorics_FiniteCircle_ExcludedSeparation
-- name    : OAI_Combinatorics_FiniteCircle_ExcludedSeparation
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T12:43:43.181379+00:00
-- url     : https://prove2.me/theorems/f0191129-8f57-45b2-a62a-e8fe0f43b190
-- title:
--   Excluded-index phase homomorphisms, excluded costs, and rows and lengths of excluded words
-- statement:
--   Fix $m,M,R\in\mathbb{N}$ and a table $p(l,k)$ of natural numbers (level $l$, index $k<m$), and put $P_l=\prod_{k<m}p(l,k)$. When $p(l,k)\mid M$, write $\iota_{l,k}:\mathbb{Z}/p(l,k)\to\mathbb{Z}/M$, $a\mapsto(M/p(l,k))\,a$, for the subcircle homomorphism, and let $\operatorname{cc}(x)=|\tilde x|/M$ be the circle cost of $x\in\mathbb{Z}/M$ ($\tilde x$ the representative of least absolute value). An excluded state of level $0$ is a residue $v\in\mathbb{Z}/M$, and one of level $l+1$ is an $m$-tuple $(v_0,\dots,v_{m-1})$ of states of level $l$; adding $\theta\in\mathbb{Z}/M$ to a state adds it to all residues it contains. The excluded word $X_0(v)$ is the word of length $M$ over $\{0,\dots,M-1\}\times\{0,1\}$ whose $b$-th letter is $(b,\beta_v(b))$, where $\beta_v(b)=1$ exactly when the least nonnegative residue of $b-v$ is smaller than $\lfloor M/2\rfloor$, and
--
--   $$
--   X_{l+1}(v)=\prod_{s=0}^{RP_{l+1}-1}\ \prod_{i=0}^{m-1} i\otimes X_l\bigl(v_i+\tau_{l+1}(s,i)\bigr),\qquad \tau_l(s,i)=\sum_{j<m,\ j\ne i}\frac{M}{p(l,j)}\bigl(s\bmod p(l,j)\bigr),
--   $$
--
--   where the products are concatenations and $i\otimes u$ labels every letter of $u$ with $i$. The shift of block $i$ thus omits ("excludes") the $i$-th residue.
--
--   The module defines the following objects.
--
--   1. **Excluded phase homomorphism.** If $p(l,k)\mid M$ for all $k<m$, then $\sigma^{\mathrm{ex}}_l:\prod_{k<m}\mathbb{Z}/p(l,k)\to(\mathbb{Z}/M)^m$ is the group homomorphism
--   $$
--   \sigma^{\mathrm{ex}}_l(z)_i=\sum_{j<m,\ j\ne i}\iota_{l,j}(z_j);
--   $$
--   for $z_j=s\bmod p(l,j)$ it reproduces the shift $\tau_l(s,i)$.
--   2. **Excluded cost.** Assume $p(l,k)\mid M$ and $p(l,k)>0$ for all levels $l$ and all $k<m$. Then $e_0=\operatorname{cc}$ and
--   $$
--   e_{l+1}(x)=\min_{z\in\prod_{k<m}\mathbb{Z}/p(l+1,k)}\ \frac{1}{m}\sum_{i<m}e_l\bigl(x+\sigma^{\mathrm{ex}}_{l+1}(z)_i\bigr).
--   $$
--   Each $e_l$ is a phase cost on $\mathbb{Z}/M$ (nonnegative, zero at $0$, even and subadditive).
--   3. **Excluded tags.** At every level the list of tags is $(0,1,\dots,m-1)$, of length $m$.
--   4. **Excluded lengths.** $E_0=M$ and $E_{l+1}=R\,P_{l+1}\,m\,E_l$; every excluded word of level $l$ has length exactly $E_l$, and adding $0$ to a state does not change it.
--   5. **Excluded rows.** For a state $v$ of level $l+1$ and $s\in\mathbb{N}$, $\operatorname{row}_s(v)=\prod_{i<m} i\otimes X_l\bigl(v_i+\tau_{l+1}(s,i)\bigr)$, a word of length $m\,E_l$; the module proves the unfolding identity expressing $X_{l+1}(v)$ as the concatenation of the rows $s=0,\dots,RP_{l+1}-1$.
--
--   The excluded words form the second family of binary lower-bound witnesses, encoded with anchor-local codes instead of offset-local ones. As for the mask construction, the excluded cost of level $l$ is the quantity that bounds from below the deficit between an excluded word and its copy with all phases rotated by a common $\theta$, and the row decomposition and common length $E_l$ are what the separation argument works with.
--
--   **Formalization Note** The alphabets, states and words are `ExcludedAlphabet`, `ExcludedState`, `excludedWord`, `shiftExcludedState` and `excludedTranslation` from the base file. The new definitions are `excludedPhaseHom` (an additive monoid homomorphism on `MaskResidues m p l`), `excludedCost` (recursion through `PhaseCost.step`, taking divisibility and positivity hypotheses for all levels), `excludedTags m l` (which ignores $l$), `excludedLength` and `excludedRow`; in `excludedLength`, `excludedRow` and the related lemmas the parameter $m$ is named `h`. `excludedWord_succ`, `length_excludedWord`, `length_excludedRow`, `length_excludedTags` and `shiftExcludedState_zero` are the accompanying lemmas.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/FiniteCircle/ExcludedSeparation.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/FiniteCircle/ExcludedSeparation.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the FiniteCircle mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_FiniteCircle
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Model
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Edit
import Definitions.Def_OAI_Combinatorics_FiniteCircle_Matching
import Definitions.Def_OAI_Combinatorics_FiniteCircle_TaggedRows
import Definitions.Def_OAI_Combinatorics_FiniteCircle_PhaseCost
import Definitions.Def_OAI_Combinatorics_FiniteCircle_CircleWords
import Definitions.Def_OAI_Combinatorics_FiniteCircle_MaskSeparation

namespace OAI

namespace FiniteCircle

open scoped BigOperators List

noncomputable def excludedPhaseHom (m : ℕ) (p : ℕ → ℕ → ℕ) (M l : ℕ)
    (hd : ∀ k : Fin m, p l k ∣ M) : MaskResidues m p l →+ (Fin m → ZMod M) where
  toFun z i := ∑ j ∈ Finset.univ.erase i, subcircle (hd j) (z j)
  map_zero' := by ext i; simp
  map_add' z w := by ext i; simp [Finset.sum_add_distrib]

noncomputable def excludedCost (m : ℕ) (p : ℕ → ℕ → ℕ) (M : ℕ)
    (hd : ∀ l (k : Fin m), p l k ∣ M) (hn : ∀ l (k : Fin m), 0 < p l k) :
    ℕ → PhaseCost (ZMod M)
  | 0 => circlePhaseCost M
  | l+1 => by
    let : ∀ k : Fin m, NeZero (p (l+1) k) := fun k => ⟨(hn _ k).ne'⟩
    exact (excludedCost m p M hd hn l).step (excludedPhaseHom m p M (l+1) (hd _))

 def excludedTags (m _l : ℕ) : List (Fin m) := List.ofFn id

@[simp] theorem length_excludedTags (m l : ℕ) : (excludedTags m l).length = m := by
  simp [excludedTags]

 theorem excludedWord_succ (m : ℕ) (p : ℕ → ℕ → ℕ) (R M l : ℕ)
    (v : ExcludedState m M (l+1)) :
    excludedWord m p R M (l+1) v = (List.range (R*period m p (l+1))).flatMap (fun a =>
      taggedRow (excludedTags m (l+1)) (fun j => excludedWord m p R M l
        (shiftExcludedState m M l (v j) (excludedTranslation m p M (l+1) a j)))) := by
  have he := excludedWord.eq_2 m p R M l v
  dsimp only [ExcludedAlphabet, ExcludedState] at he
  refine he.trans ?_
  unfold taggedRow excludedTags
  simp only [List.flatMap_def, List.map_ofFn, Function.comp_id]
noncomputable def excludedLength (h : ℕ) (p : ℕ → ℕ → ℕ) (R M : ℕ) : ℕ → ℕ
  | 0 => M
  | l+1 => (R*period h p (l+1))*((excludedTags h (l+1)).length*excludedLength h p R M l)

@[simp] theorem length_excludedWord (h : ℕ) (p : ℕ → ℕ → ℕ) (R M l : ℕ)
    (v : ExcludedState h M l) : (excludedWord h p R M l v).length = excludedLength h p R M l := by
  induction l with
  | zero =>
    have he := excludedWord.eq_1 h p R M v
    dsimp only [ExcludedAlphabet, ExcludedState] at he
    exact (congrArg List.length he).trans (List.length_ofFn)
  | succ l ih =>
    rw [excludedWord_succ]
    change ((List.range (R*period h p (l+1))).flatMap (fun a =>
      taggedRow (excludedTags h (l+1)) (fun j => excludedWord h p R M l
        (shiftExcludedState h M l (v j) (excludedTranslation h p M (l+1) a j))))).length = _
    rw [length_flatMap_uniform _ _ ((excludedTags h (l+1)).length*excludedLength h p R M l)]
    · simp [excludedLength]
    · intro a _
      apply length_flatMap_uniform
      intro j _
      simp [ih]

@[simp] theorem shiftExcludedState_zero (h : ℕ) (M l : ℕ)
    (v : ExcludedState h M l) : shiftExcludedState h M l v 0 = v := by
  induction l with
  | zero => change ZMod M at v; exact add_zero v
  | succ l ih => funext j; exact ih (v j)

def excludedRow (h : ℕ) (p : ℕ → ℕ → ℕ) (R M l : ℕ)
    (v : ExcludedState h M (l+1)) (a : ℕ) : List (ExcludedAlphabet h M (l+1)) :=
  taggedRow (excludedTags h (l+1)) (fun j => excludedWord h p R M l
    (shiftExcludedState h M l (v j) (excludedTranslation h p M (l+1) a j)))

@[simp] theorem length_excludedRow (h : ℕ) (p : ℕ → ℕ → ℕ) (R M l : ℕ)
    (v : ExcludedState h M (l+1)) (a : ℕ) :
    (excludedRow h p R M l v a).length = (excludedTags h (l+1)).length*excludedLength h p R M l := by
  change (Fin h → ExcludedState h M l) at v
  change (taggedRow (excludedTags h (l+1)) (fun j => excludedWord h p R M l
    (shiftExcludedState h M l (v j) (excludedTranslation h p M (l+1) a j)))).length = _
  unfold taggedRow
  apply length_flatMap_uniform
  intro j _
  rw [List.length_map, length_excludedWord]

end FiniteCircle

end OAI


