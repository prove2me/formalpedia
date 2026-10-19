-- Prove2me | Definitions.Def_OAI_RepresentationTheory_Saxl_CoordinateSector
-- name    : OAI_RepresentationTheory_Saxl_CoordinateSector
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T22:52:16.547829+00:00
-- url     : https://prove2.me/theorems/b56d2ebf-43c6-432f-b874-462a0a615d49
-- title:
--   Coordinate projections, sector stabilizers and the two layers of the staircase cut
-- statement:
--   For $n\in\mathbb{N}$ write $[n]=\{0,1,\dots,n-1\}$ and let $S_n$ be the symmetric group on $[n]$. A *word* of length $n$ over the alphabet $[d]$ is a map $a:[n]\to[d]$, and $W_{n,d}=\mathbb{C}^{[d]^n}$ is the space of complex functions on words, with standard basis vectors $e_a$ (the indicator function of the word $a$), so that $W_{n,d}\cong(\mathbb{C}^d)^{\otimes n}$. The group $S_n$ acts on $W_{n,d}$ by permuting positions, $(\rho_{n,d}(g)x)(a)=x(a\circ g)$; equivalently $\rho_{n,d}(g)e_a=e_{a\circ g^{-1}}$.
--
--   A tableau of a Young diagram $\mu$ is a bijection $t$ from positions to the cells $(i,j)$ of $\mu$ (row $i$, column $j$); $r_t$ is its row word (position $\mapsto$ row index of its cell) and $C_t$ its column group (position permutations $g$ with $t(g(i))$ in the same column as $t(i)$ for all $i$). For $m\in\mathbb{N}$ the staircase diagram is $\delta_m=\{(i,j)\in\mathbb{N}^2:i+j<m\}$, with rows of lengths $m,m-1,\dots,1$ and $N_m=|\delta_m|=m(m+1)/2$ cells. Fix $h,s\in\mathbb{N}$ and write $T=T_{h+s}:[N]\to\delta_{h+s}$, $N=N_{h+s}$, for the canonical tableau (the fixed enumeration of the cells of $\delta_{h+s}$ used in the target statement) and $T'=\tau\circ T$ for its transpose, where $\tau(i,j)=(j,i)$. Let $R_{h,s}$ be the permutation of $\delta_{h+s}$ that fixes rows $i\ge h$ and rotates each row $i<h$ cyclically by $s$ places, $(i,j)\mapsto(i,\,j+s \bmod (h+s-i))$, and $K_{h,s}=\tau\circ R_{h,s}\circ\tau$ the analogous column rotation; put $p_R=T^{-1}\circ R_{h,s}\circ T$ and $p_K=T^{-1}\circ K_{h,s}\circ T$ in $S_N$. The file introduces:
--
--   1. **Coordinate projections.** For a predicate $P$ on words, the linear map $\Pi_P$ on $W_{n,d}$ with $(\Pi_Px)(a)=x(a)$ if $P(a)$ holds and $0$ otherwise (no equivariance is claimed; it holds when $P$ is invariant under position permutations).
--   2. **Sector stabilizers.** For a set of positions $D\subseteq[n]$, the subgroup $\operatorname{Stab}(D)=\{g\in S_n:\ g(i)\in D\iff i\in D\ \text{for all } i\}$.
--   3. **Signed alternation.** For a subgroup $G\le S_n$ and a word $a\in[d]^n$, the unnormalized alternating sum
--   $$
--   \operatorname{alt}_G(a)=\sum_{g\in G}\operatorname{sgn}(g)\,\rho_{n,d}(g)\,e_a\in W_{n,d} .
--   $$
--   For example, the polytabloid of a tableau $t$ is $e_t=\operatorname{alt}_{C_t}(r_t)$.
--   4. **High sector of the staircase.** $H_{h,s}=\{i\in[N]:\ T(i)=(i',j')\text{ with }i'+j'<h\}$, the positions whose cell lies in the sub-staircase $\delta_h$.
--   5. **The two layers of the cut.**
--   $$
--   \kappa^{\mathrm{row}}_{h,s}=\operatorname{alt}_{C_{T'}\cap\operatorname{Stab}(H_{h,s})}\big(r_{T'}\circ p_R\big),\qquad
--   \kappa^{\mathrm{col}}_{h,s}=\operatorname{alt}_{C_{T}\cap\operatorname{Stab}(H_{h,s})}\big(r_{T}\circ p_K\big),
--   $$
--   both in $W_{N,\ell}$ with $\ell=\ell(\delta_{h+s})=h+s$. Here $C_{T'}$ is the group of position permutations preserving the row of every cell, $r_{T'}\circ p_R$ assigns to position $i$ the column index of $R_{h,s}(T(i))$, and $r_T\circ p_K$ assigns the row index of $K_{h,s}(T(i))$.
--
--   In the surrounding development these layers describe the same-high projection of the staircase word: if $\omega_{h+s}=\Theta(e_{T'}\otimes e_T)$ is the staircase word (with $\Theta$ the position-wise identification of $W_{N,\ell}\otimes W_{N,\ell}$ with $W_{N,\ell^2}$) and $\Pi_s$ keeps the pair words whose two components are $\ge s$ at the same positions, then $\Pi_s\,\omega_{h+s}=\Theta(\kappa^{\mathrm{row}}_{h,s}\otimes\kappa^{\mathrm{col}}_{h,s})$. Restricting the alternating sums to the sector stabilizer is what makes the later factorization into a sub-staircase part and a band part possible.
--
--   **Formalization Note** The objects are `coordinateProjection` (with the simp lemma `coordinateProjection_apply`), `sectorGroup`, `altWord`, `stairHigh`, `cutRowWord` and `cutColumnWord`; the sign is `signC`, the group $G$ is summed over via a `Fintype` instance obtained from finiteness, and $p_R,p_K$ are `rotateRowPositions h s` and `rotateColumnPositions h s`. The row rotation itself comes from the companion file on the same-high projection, where it is written without a modulus, as $j\mapsto j+s$ for $j<h-i$ and $j\mapsto j-(h-i)$ otherwise; this is the same map.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/Saxl/CoordinateSector.lean

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/Saxl/CoordinateSector.lean by skeleton subtraction
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

namespace OAI

noncomputable section

open scoped TensorProduct

namespace Saxl
/- Coordinate projection; equivariance is asserted only for preserved predicates. -/
def coordinateProjection {n d : ℕ} (P : (Fin n → Fin d) → Prop) :
    Module.End ℂ (WordSpace n d) := by
  classical
  exact {
    toFun := fun x a => if P a then x a else 0
    map_add' := by intros; funext a; by_cases h : P a <;> simp [h]
    map_smul' := by intros; funext a; by_cases h : P a <;> simp [h] }

@[simp] lemma coordinateProjection_apply {n d : ℕ} (P : (Fin n → Fin d) → Prop)
    (x : WordSpace n d) (a : Fin n → Fin d) [Decidable (P a)] :
    coordinateProjection P x a = if P a then x a else 0 := by
  classical
  by_cases h : P a <;> simp [coordinateProjection, h]

/- Permutations preserving a position sector. -/
def sectorGroup {n : ℕ} (D : Fin n → Prop) : Subgroup (Equiv.Perm (Fin n)) where
  carrier := {g | ∀ i, D (g i) ↔ D i}
  one_mem' _ := Iff.rfl
  mul_mem' hg hh i := (hg _).trans (hh i)
  inv_mem' := by
    intro g hg i
    simpa using (hg (g⁻¹ i)).symm

/- The genuine unnormalized signed block alternation. -/
def altWord {n d : ℕ} (G : Subgroup (Equiv.Perm (Fin n))) (a : Fin n → Fin d) :
    WordSpace n d := by
  classical
  letI := Fintype.ofFinite G
  exact ∑ g : G, signC (g : Equiv.Perm (Fin n)) •
    wordRep n d (g : Equiv.Perm (Fin n)) (Pi.single a 1)

/- Keeping a prescribed coloring restricts the alternating group to its
sector stabilizer. This is the finite coset calculation behind block-factorization. -/
end Saxl

namespace Saxl
/- The prescribed high sector in the actual staircase enumeration. -/
def stairHigh (h s : ℕ) (i : Fin (staircase (h+s)).card) : Prop :=
  (stairTableau (h+s) i).val.1 + (stairTableau (h+s) i).val.2 < h

/- The cut's two layers, with their exact retained row and column permutations. -/
def cutRowWord (h s : ℕ) :=
  altWord (columnGroup (stairRowTableau (h+s)) ⊓ sectorGroup (stairHigh h s))
    (rowWord (stairRowTableau (h+s)) ∘ (rotateRowPositions h s : Equiv.Perm _))

def cutColumnWord (h s : ℕ) :=
  altWord (columnGroup (stairTableau (h+s)) ⊓ sectorGroup (stairHigh h s))
    (rowWord (stairTableau (h+s)) ∘ (rotateColumnPositions h s : Equiv.Perm _))

/- Exact sign cancellation in the two retained layers. -/
end Saxl

end

end OAI


