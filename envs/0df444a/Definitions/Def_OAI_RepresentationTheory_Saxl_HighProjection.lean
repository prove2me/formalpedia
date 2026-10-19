-- Prove2me | Definitions.Def_OAI_RepresentationTheory_Saxl_HighProjection
-- name    : OAI_RepresentationTheory_Saxl_HighProjection
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T22:50:43.484054+00:00
-- url     : https://prove2.me/theorems/df1f59fd-1b55-49c1-8b8b-62ed86d94789
-- title:
--   Same-high projection and cyclic row and column rotations of the staircase
-- statement:
--   For $n\in\mathbb{N}$ write $[n]=\{0,1,\dots,n-1\}$ and let $S_n$ be the symmetric group on $[n]$. A *word* of length $n$ over the alphabet $[d]$ is a map $a:[n]\to[d]$, and $W_{n,d}=\mathbb{C}^{[d]^n}$ is the space of complex functions on words, with standard basis vectors $e_a$ (the indicator function of the word $a$), so that $W_{n,d}\cong(\mathbb{C}^d)^{\otimes n}$. The group $S_n$ acts on $W_{n,d}$ by permuting positions, $(\rho_{n,d}(g)x)(a)=x(a\circ g)$; equivalently $\rho_{n,d}(g)e_a=e_{a\circ g^{-1}}$. For alphabet sizes $d,e$, the product alphabet $[d]\times[e]$ is identified with $[de]$ by $(a,b)\mapsto ae+b$; for a word $w\in[de]^n$ let $w^{L}\in[d]^n$ and $w^{R}\in[e]^n$ be its left and right components, $w_i=w^{L}_i\,e+w^{R}_i$.
--
--   For $m\in\mathbb{N}$ the staircase diagram is $\delta_m=\{(i,j)\in\mathbb{N}^2:i+j<m\}$, with rows of lengths $m,m-1,\dots,1$ and $N_m=|\delta_m|=m(m+1)/2$ cells. Fix $h,s\in\mathbb{N}$ and write $T=T_{h+s}:[N]\to\delta_{h+s}$, $N=N_{h+s}$, for the canonical tableau (the fixed enumeration of the cells of $\delta_{h+s}$ used in the target statement) and $T'=\tau\circ T$ for its transpose, where $\tau(i,j)=(j,i)$. A tableau $t$ (a bijection from positions to the cells of a diagram) has column group $C_t$, the group of position permutations $g$ such that $t(g(i))$ lies in the same column as $t(i)$ for all $i$. The file introduces:
--
--   1. **Translating the high part.** The bijections
--   $$
--   \{(i,j)\in\delta_{h+s}:\ j\ge s\}\to\delta_h,\ (i,j)\mapsto(i,j-s),\qquad \{(i,j)\in\delta_{h+s}:\ i\ge s\}\to\delta_h,\ (i,j)\mapsto(i-s,j).
--   $$
--   2. **Same-high projection.** Call a letter *high* if it is at least $s$. For all $n,d,e,s$, the intertwiner $\Pi_s:W_{n,de}\to W_{n,de}$,
--   $$
--   (\Pi_sz)(w)=\begin{cases}z(w)&\text{if, for every }i\in[n],\ w^{L}_i\ge s\iff w^{R}_i\ge s,\\ 0&\text{otherwise,}\end{cases}
--   $$
--   which keeps exactly the words whose left and right components are high at the same positions.
--   3. **Row rotation.** The permutation $R_{h,s}$ of the cells of $\delta_{h+s}$ given by
--   $$
--   R_{h,s}(i,j)=\begin{cases}(i,\,j+s)&\text{if } j<\max(h-i,0),\\ (i,\,j-\max(h-i,0))&\text{otherwise.}\end{cases}
--   $$
--   It fixes every row $i\ge h$ and rotates each row $i<h$ (of length $h+s-i$) cyclically by $s$ places, $j\mapsto j+s \bmod (h+s-i)$; the cells of row $i$ lying in $\delta_h$ (those with $j<h-i$) go to columns $\ge s$, the others to columns $<s$. Its injectivity is proved and it is then a bijection of the finite cell set.
--   4. **Column rotation.** $K_{h,s}=\tau\circ R_{h,s}\circ\tau$, the same rotation applied to the columns: $(i,j)\mapsto(i+s,j)$ if $i<\max(h-j,0)$ and $(i,j)\mapsto(i-\max(h-j,0),j)$ otherwise.
--   5. **Rotations as position permutations.** $p_R=T^{-1}\circ R_{h,s}\circ T\in S_N$ and $p_K=T^{-1}\circ K_{h,s}\circ T\in S_N$. The permutation $p_R$ preserves the row of every cell, so it lies in the column group $C_{T'}$ of the transposed tableau; $p_K$ preserves columns and lies in $C_T$.
--
--   The staircase $\delta_{h+s}$ is the union of the sub-staircase $\delta_h$ (cells with $i+j<h$) and the band of cells with $h\le i+j<h+s$. With the staircase word $\omega_{h+s}=\Theta(e_{T'}\otimes e_T)\in W_{N,(h+s)^2}$, where $e_t$ is the polytabloid of $t$ and $\Theta(x\otimes y)(w)=x(w^{L})\,y(w^{R})$, the surrounding development uses these objects to show that $\Pi_s\,\omega_{h+s}\neq0$ and that in every word of its support the high letters occupy exactly the positions of the cells of $\delta_h$: the rotated row and column words $(\text{column of }R_{h,s}(T(i)))_i$ and $(\text{row of }K_{h,s}(T(i)))_i$ supply a nonzero coefficient. This is the first step in cutting the staircase into a smaller staircase and a band.
--
--   **Formalization Note** The objects are `highRowEquiv`, `highColEquiv`, `sameHighProjection`, `rotateRowCell` (with `rotateRowCell_injective`), `rotateRow`, `rotateColumn`, `rotateRowPositions` and `rotateColumnPositions`; the last two are elements of the subgroups `columnGroup (stairRowTableau (h+s))` and `columnGroup (stairTableau (h+s))`. Natural-number subtraction is truncated, which is why $\max(h-i,0)$ appears in item 3.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/Saxl/HighProjection.lean

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/Saxl/HighProjection.lean by skeleton subtraction
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

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

open scoped TensorProduct

namespace Saxl
/- Translate the high part of each row to the smaller staircase. -/
def highRowEquiv (h s : ℕ) :
    {x : (staircase (h+s)).cells // s ≤ x.val.2} ≃ (staircase h).cells where
  toFun x := ⟨(x.val.val.1, x.val.val.2 - s), by
    have hx : x.val.val.1 + x.val.val.2 < h+s := mem_staircase.mp x.val.property
    exact mem_staircase.mpr (by have := x.property; omega)⟩
  invFun x := ⟨⟨(x.val.1, x.val.2+s), by
    have hx : x.val.1 + x.val.2 < h := mem_staircase.mp x.property
    exact mem_staircase.mpr (by omega)⟩, by dsimp; omega⟩
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    dsimp
    have := x.property
    ext <;> omega
  right_inv x := by apply Subtype.ext; simp

def highColEquiv (h s : ℕ) :
    {x : (staircase (h+s)).cells // s ≤ x.val.1} ≃ (staircase h).cells where
  toFun x := ⟨(x.val.val.1 - s, x.val.val.2), by
    have hx : x.val.val.1 + x.val.val.2 < h+s := mem_staircase.mp x.val.property
    exact mem_staircase.mpr (by have := x.property; omega)⟩
  invFun x := ⟨⟨(x.val.1+s, x.val.2), by
    have hx : x.val.1 + x.val.2 < h := mem_staircase.mp x.property
    exact mem_staircase.mpr (by omega)⟩, by dsimp; omega⟩
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    dsimp
    have := x.property
    ext <;> omega
  right_inv x := by apply Subtype.ext; simp

/- Local same-high projection in the ordinary pair-letter coordinate space. -/
def sameHighProjection (n d e s : ℕ) :
    Representation.IntertwiningMap (wordRep n (d*e)) (wordRep n (d*e)) where
  toFun z w := if (∀ i, s ≤ (splitLeft w i).val ↔ s ≤ (splitRight w i).val) then z w else 0
  map_add' z y := by ext w; dsimp; split_ifs <;> simp
  map_smul' c z := by ext w; dsimp; split_ifs <;> simp
  isIntertwining' g := by
    apply LinearMap.ext
    intro z
    funext w
    change (if (∀ i, s ≤ (splitLeft w i).val ↔ s ≤ (splitRight w i).val) then z (w ∘ g) else 0) =
      (if (∀ i, s ≤ (splitLeft (w ∘ g) i).val ↔ s ≤ (splitRight (w ∘ g) i).val) then z (w ∘ g) else 0)
    congr 1
    apply propext
    exact (g.forall_congr_right).symm

/- Move low row letters to the band and high row letters to B_h. -/
def rotateRowCell (h s : ℕ) (x : (staircase (h+s)).cells) : (staircase (h+s)).cells :=
  ⟨(x.val.1, if x.val.2 < h - x.val.1 then x.val.2+s else x.val.2-(h-x.val.1)), by
    have hx : x.val.1 + x.val.2 < h+s := mem_staircase.mp x.property
    apply mem_staircase.mpr
    split_ifs <;> omega⟩

lemma rotateRowCell_injective (h s : ℕ) : Function.Injective (rotateRowCell h s) := by
  intro x y he
  have hi0 := congrArg (fun z : (staircase (h+s)).cells => z.val.1) he
  have hi : x.val.1 = y.val.1 := hi0
  have hj := congrArg (fun z : (staircase (h+s)).cells => z.val.2) he
  have hx : x.val.1 + x.val.2 < h+s := mem_staircase.mp x.property
  have hy : y.val.1 + y.val.2 < h+s := mem_staircase.mp y.property
  dsimp [rotateRowCell] at hj
  apply Subtype.ext
  apply Prod.ext hi
  split_ifs at hj <;> omega

def rotateRow (h s : ℕ) : Equiv.Perm (staircase (h+s)).cells :=
  Equiv.ofBijective (rotateRowCell h s) (⟨rotateRowCell_injective h s, Finite.surjective_of_injective (rotateRowCell_injective h s)⟩)

def rotateColumn (h s : ℕ) : Equiv.Perm (staircase (h+s)).cells :=
  ((staircaseSwap (h+s)).trans (rotateRow h s)).trans (staircaseSwap (h+s))

def rotateRowPositions (h s : ℕ) : columnGroup (stairRowTableau (h+s)) :=
  ⟨((stairTableau (h+s)).trans (rotateRow h s)).trans (stairTableau (h+s)).symm, by
    intro i
    change (stairTableau (h+s) ((stairTableau (h+s)).symm (rotateRow h s (stairTableau (h+s) i)))).val.1 = _
    simp only [Equiv.apply_symm_apply]
    rfl⟩

def rotateColumnPositions (h s : ℕ) : columnGroup (stairTableau (h+s)) :=
  ⟨((stairTableau (h+s)).trans (rotateColumn h s)).trans (stairTableau (h+s)).symm, by
    intro i
    change (stairTableau (h+s) ((stairTableau (h+s)).symm (rotateColumn h s (stairTableau (h+s) i)))).val.2 = _
    simp only [Equiv.apply_symm_apply]
    rfl⟩

/- The projected generator is genuinely nonzero for every band width,
without assuming a tensor factorization. -/
end Saxl

end

end OAI


