-- Prove2me | Definitions.Def_OAI_RepresentationTheory_Saxl_PositionSplit
-- name    : OAI_RepresentationTheory_Saxl_PositionSplit
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T22:54:06.007279+00:00
-- url     : https://prove2.me/theorems/e604518e-0d11-456b-8fa1-b213cc92ced1
-- title:
--   Splitting positions into two blocks: block permutations, restricted words and fiber groups
-- statement:
--   For $n\in\mathbb{N}$ write $[n]=\{0,1,\dots,n-1\}$ and let $S_n$ be the symmetric group on $[n]$. A *word* of length $n$ over the alphabet $[d]$ is a map $a:[n]\to[d]$, and $W_{n,d}=\mathbb{C}^{[d]^n}$ is the space of complex functions on words, with standard basis vectors $e_a$ (the indicator function of the word $a$), so that $W_{n,d}\cong(\mathbb{C}^d)^{\otimes n}$. The group $S_n$ acts on $W_{n,d}$ by permuting positions, $(\rho_{n,d}(g)x)(a)=x(a\circ g)$; equivalently $\rho_{n,d}(g)e_a=e_{a\circ g^{-1}}$. For a subgroup $G\le S_n$ and a word $a$, write $\operatorname{alt}_G(a)=\sum_{g\in G}\operatorname{sgn}(g)\rho_{n,d}(g)e_a$, and for a set of positions $D$ let $\operatorname{Stab}(D)=\{g\in S_n:\ g(i)\in D\iff i\in D\ \text{for all } i\}$.
--
--   Fix a bijection $\varepsilon:[n]\to[a]\sqcup[b]$ splitting the positions into a left block $\varepsilon^{-1}([a])$ and a right block $\varepsilon^{-1}([b])$. The file introduces:
--
--   1. **Block permutations.** For $g\in S_a$ and $h\in S_b$, the permutation $g\boxplus_\varepsilon h=\varepsilon^{-1}\circ(g\sqcup h)\circ\varepsilon\in S_n$, acting as $g$ on the left block and as $h$ on the right block. The map $(g,h)\mapsto g\boxplus_\varepsilon h$ is injective.
--   2. **Restricted words.** For $w\in[d]^n$, the words $w^{(1)}\in[d]^a$ and $w^{(2)}\in[d]^b$ with $w^{(1)}(i)=w(\varepsilon^{-1}(i))$ for $i$ in the first summand and $w^{(2)}(j)=w(\varepsilon^{-1}(j))$ for $j$ in the second.
--   3. **Position product.** For $x\in W_{a,d}$ and $y\in W_{b,d}$, the vector $x\boxtimes_\varepsilon y\in W_{n,d}$,
--   $$
--   (x\boxtimes_\varepsilon y)(w)=x\big(w^{(1)}\big)\,y\big(w^{(2)}\big).
--   $$
--   4. **Fiber groups.** For any map $f$ from $[n]$ to a set $X$, the subgroup $\operatorname{Fib}(f)=\{g\in S_n:\ f\circ g=f\}$ of label-preserving permutations (with row or column labels of a tableau these are its row and column groups).
--   5. **Restrictions.** Every $g\in\operatorname{Stab}(\varepsilon^{-1}([a]))$ restricts to permutations $g_1\in S_a$ and $g_2\in S_b$ of the two blocks (transported along $\varepsilon$), and $g_1\boxplus_\varepsilon g_2=g$.
--   6. **Fiber splitting.** For $f:[n]\to X$ put $f_1=f\circ\varepsilon^{-1}$ on $[a]$ and $f_2=f\circ\varepsilon^{-1}$ on $[b]$. Then $(g_1,g_2)\mapsto g_1\boxplus_\varepsilon g_2$ is a bijection
--   $$
--   \operatorname{Fib}(f_1)\times\operatorname{Fib}(f_2)\ \longrightarrow\ \operatorname{Fib}(f)\cap\operatorname{Stab}\big(\varepsilon^{-1}([a])\big).
--   $$
--   7. **Column lengths of the staircase.** For the staircase diagram $\delta_m=\{(i,j)\in\mathbb{N}^2:i+j<m\}$, column $j$ has $\max(m-j,0)$ cells; in particular $\delta_m$ has $m$ rows.
--
--   These objects support the block factorization of alternating sums used in the surrounding development: $\operatorname{alt}_{\operatorname{Fib}(f)\cap\operatorname{Stab}(\varepsilon^{-1}([a]))}(w)=\operatorname{alt}_{\operatorname{Fib}(f_1)}(w^{(1)})\boxtimes_\varepsilon\operatorname{alt}_{\operatorname{Fib}(f_2)}(w^{(2)})$, since the sign of $g_1\boxplus_\varepsilon g_2$ is the product of the signs. Applied to the cut of the staircase $\delta_{h+s}$ into the sub-staircase $\delta_h$ and an outer band, it separates the two pieces.
--
--   **Formalization Note** The objects are `sumPerm` (via `Equiv.permCongr` and `Equiv.sumCongr`), `leftWord`, `rightWord`, `positionProduct`, `fiberGroup`, `leftPositions`, `rightPositions`, `leftRestriction`, `rightRestriction` and `fiberSplit`; the left block is expressed by the predicate that `(e i).isLeft = true`. The lemmas `sumPerm_left`, `sumPerm_right`, `leftRestriction_apply`, `rightRestriction_apply`, `sumPerm_restrictions` and `sumPerm_injective` are the facts in items 1 and 5, and item 7 is `staircase_colLen`, stated with truncated subtraction as `(staircase m).colLen j = m - j`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/Saxl/PositionSplit.lean

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/Saxl/PositionSplit.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the Saxl mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_Saxl
import Definitions.Def_OAI_RepresentationTheory_Saxl_Basic
import Definitions.Def_OAI_RepresentationTheory_Saxl_Polytabloid
import Definitions.Def_OAI_RepresentationTheory_Saxl_SpechtSubmodule
import Definitions.Def_OAI_RepresentationTheory_Saxl_SpechtDuality
import Definitions.Def_OAI_RepresentationTheory_Saxl_TableauTransport
import Definitions.Def_OAI_RepresentationTheory_Saxl_StaircaseTensor
import Definitions.Def_OAI_RepresentationTheory_Saxl_HighProjection
import Definitions.Def_OAI_RepresentationTheory_Saxl_CoordinateSector

namespace OAI

noncomputable section

open scoped TensorProduct

universe uAlpha

namespace Saxl
/- The genuine product position permutation under a disjoint-set enumeration. -/
def sumPerm {n a b : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b)
    (g : Equiv.Perm (Fin a)) (h : Equiv.Perm (Fin b)) : Equiv.Perm (Fin n) :=
  e.symm.permCongr (Equiv.sumCongr g h)

@[simp] lemma sumPerm_left {n a b : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b)
    (g : Equiv.Perm (Fin a)) (h : Equiv.Perm (Fin b)) (i : Fin a) :
    sumPerm e g h (e.symm (Sum.inl i)) = e.symm (Sum.inl (g i)) := by
  simp [sumPerm, Equiv.permCongr_apply]

@[simp] lemma sumPerm_right {n a b : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b)
    (g : Equiv.Perm (Fin a)) (h : Equiv.Perm (Fin b)) (i : Fin b) :
    sumPerm e g h (e.symm (Sum.inr i)) = e.symm (Sum.inr (h i)) := by
  simp [sumPerm, Equiv.permCongr_apply]

def leftWord {n a b d : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b) (w : Fin n → Fin d) : Fin a → Fin d :=
  fun i => w (e.symm (Sum.inl i))

def rightWord {n a b d : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b) (w : Fin n → Fin d) : Fin b → Fin d :=
  fun i => w (e.symm (Sum.inr i))

def positionProduct {n a b d : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b)
    (x : WordSpace a d) (y : WordSpace b d) : WordSpace n d :=
  fun w => x (leftWord e w) * y (rightWord e w)

/- Independent block permutations factor with exactly the product sign. -/
def fiberGroup {n : ℕ} {α : Type uAlpha} (f : Fin n → α) : Subgroup (Equiv.Perm (Fin n)) where
  carrier := {g | ∀ i, f (g i) = f i}
  one_mem' _ := rfl
  mul_mem' hg hh i := (hg _).trans (hh i)
  inv_mem' := by
    intro g hg i
    simpa using (hg (g⁻¹ i)).symm

def leftPositions {n a b : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b) :
    Fin a ≃ {i : Fin n // (e i).isLeft = true} where
  toFun i := ⟨e.symm (Sum.inl i), by simp⟩
  invFun i := (e i.val).getLeft i.property
  left_inv i := by simp
  right_inv i := by
    apply Subtype.ext
    apply e.injective
    simp only [Equiv.apply_symm_apply]
    exact Sum.inl_getLeft _ _

def rightPositions {n a b : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b) :
    Fin b ≃ {i : Fin n // ¬(e i).isLeft = true} where
  toFun i := ⟨e.symm (Sum.inr i), by simp⟩
  invFun i := (e i.val).getRight (by
    have hi := i.property
    cases h : e i.val <;> simp_all)
  left_inv i := by simp
  right_inv i := by
    apply Subtype.ext
    apply e.injective
    simp only [Equiv.apply_symm_apply]
    exact Sum.inr_getRight _ _

def leftRestriction {n a b : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b)
    (g : sectorGroup (fun i => (e i).isLeft = true)) : Equiv.Perm (Fin a) :=
  (leftPositions e).symm.permCongr ((g : Equiv.Perm (Fin n)).subtypePerm g.property)

def rightRestriction {n a b : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b)
    (g : sectorGroup (fun i => (e i).isLeft = true)) : Equiv.Perm (Fin b) :=
  (rightPositions e).symm.permCongr ((g : Equiv.Perm (Fin n)).subtypePerm (fun i => not_congr (g.property i)))

lemma leftRestriction_apply {n a b : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b)
    (g : sectorGroup (fun i => (e i).isLeft = true)) (i : Fin a) :
    e.symm (Sum.inl (leftRestriction e g i)) = g.val (e.symm (Sum.inl i)) := by
  apply e.injective
  simp only [Equiv.apply_symm_apply]
  exact Sum.inl_getLeft _ _

lemma rightRestriction_apply {n a b : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b)
    (g : sectorGroup (fun i => (e i).isLeft = true)) (i : Fin b) :
    e.symm (Sum.inr (rightRestriction e g i)) = g.val (e.symm (Sum.inr i)) := by
  apply e.injective
  simp only [Equiv.apply_symm_apply]
  exact Sum.inr_getRight _ _

lemma sumPerm_restrictions {n a b : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b)
    (g : sectorGroup (fun i => (e i).isLeft = true)) :
    sumPerm e (leftRestriction e g) (rightRestriction e g) = g.val := by
  apply Equiv.ext
  intro i
  obtain ⟨j,rfl⟩ := e.symm.surjective i
  cases j with
  | inl j => simpa using leftRestriction_apply e g j
  | inr j => simpa using rightRestriction_apply e g j

lemma sumPerm_injective {n a b : ℕ} (e : Fin n ≃ Fin a ⊕ Fin b) :
    Function.Injective (fun p : Equiv.Perm (Fin a) × Equiv.Perm (Fin b) => sumPerm e p.1 p.2) := by
  intro p q hpq
  apply Prod.ext
  · apply Equiv.ext
    intro i
    have h := congrArg (fun g : Equiv.Perm (Fin n) => e (g (e.symm (Sum.inl i)))) hpq
    simpa using h
  · apply Equiv.ext
    intro i
    have h := congrArg (fun g : Equiv.Perm (Fin n) => e (g (e.symm (Sum.inr i)))) hpq
    simpa using h

def fiberSplit {n a b : ℕ} {α : Type uAlpha} (e : Fin n ≃ Fin a ⊕ Fin b) (f : Fin n → α) :
    (fiberGroup (fun i => f (e.symm (Sum.inl i)))) × (fiberGroup (fun i => f (e.symm (Sum.inr i)))) ≃
      ↥(fiberGroup f ⊓ sectorGroup (fun i => (e i).isLeft = true)) := by
  let F : (fiberGroup (fun i => f (e.symm (Sum.inl i)))) ×
      (fiberGroup (fun i => f (e.symm (Sum.inr i)))) →
      ↥(fiberGroup f ⊓ sectorGroup (fun i => (e i).isLeft = true)) := fun p =>
    ⟨sumPerm e p.1.val p.2.val, by
      constructor
      · intro i
        obtain ⟨j,rfl⟩ := e.symm.surjective i
        cases j with
        | inl j => simpa using p.1.property j
        | inr j => simpa using p.2.property j
      · intro i
        obtain ⟨j,rfl⟩ := e.symm.surjective i
        cases j <;> simp⟩
  apply Equiv.ofBijective F
  constructor
  · intro p q hpq
    have hh : sumPerm e p.1.val p.2.val = sumPerm e q.1.val q.2.val := congrArg Subtype.val hpq
    have h := @sumPerm_injective n a b e (p.1.val,p.2.val) (q.1.val,q.2.val) hh
    exact Prod.ext (Subtype.ext (congrArg Prod.fst h)) (Subtype.ext (congrArg Prod.snd h))
  · intro g
    let g' : sectorGroup (fun i => (e i).isLeft = true) := ⟨g.val,g.property.2⟩
    refine ⟨(⟨leftRestriction e g', ?_⟩, ⟨rightRestriction e g', ?_⟩), ?_⟩
    · intro i
      dsimp only
      rw [leftRestriction_apply]
      exact g.property.1 _
    · intro i
      dsimp only
      rw [rightRestriction_apply]
      exact g.property.1 _
    · exact Subtype.ext (sumPerm_restrictions e g')

/- Exact independent-block factorization for arbitrary row/column labels. -/
@[simp] lemma staircase_colLen (m j : ℕ) : (staircase m).colLen j = m-j := by
  have hh : ∀ i, i < (staircase m).colLen j ↔ i < m-j := by
    intro i
    rw [← YoungDiagram.mem_iff_lt_colLen, mem_staircase]
    omega
  have h₁ := hh ((staircase m).colLen j)
  have h₂ := hh (m-j)
  omega

end Saxl

end

end OAI


