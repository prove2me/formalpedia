-- Prove2me | Definitions.Def_OAI_RepresentationTheory_Saxl_TableauTransport
-- name    : OAI_RepresentationTheory_Saxl_TableauTransport
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T22:47:33.21508+00:00
-- url     : https://prove2.me/theorems/c4e4f084-c25c-4894-afb3-0ed73eb6d73f
-- title:
--   Changing the tableau moves the polytabloid by a position permutation
-- statement:
--   For $n\in\mathbb{N}$ write $[n]=\{0,1,\dots,n-1\}$ and let $S_n$ be the symmetric group on $[n]$. A *word* of length $n$ over the alphabet $[d]$ is a map $a:[n]\to[d]$, and $W_{n,d}=\mathbb{C}^{[d]^n}$ is the space of complex functions on words, with standard basis vectors $e_a$ (the indicator function of the word $a$), so that $W_{n,d}\cong(\mathbb{C}^d)^{\otimes n}$. The group $S_n$ acts on $W_{n,d}$ by permuting positions, $(\rho_{n,d}(g)x)(a)=x(a\circ g)$; equivalently $\rho_{n,d}(g)e_a=e_{a\circ g^{-1}}$.
--
--   A Young diagram $\mu$ is a finite set of cells $(i,j)\in\mathbb{N}^2$ (row $i$, column $j$, both counted from $0$) that is closed under decreasing either coordinate; $\ell(\mu)$ denotes its number of rows. A tableau of shape $\mu$ on $n=|\mu|$ positions is a bijection $t:[n]\to\mu$. Its row word $r_t:[n]\to[\ell(\mu)]$ sends $i$ to the row index of $t(i)$, its column group $C_t\le S_n$ consists of the permutations $g$ such that $t(g(i))$ lies in the same column as $t(i)$ for every $i$, and its polytabloid is
--   $$
--   e_t=\sum_{g\in C_t}\operatorname{sgn}(g)\,\rho_{n,\ell(\mu)}(g)\,e_{r_t}\in W_{n,\ell(\mu)} .
--   $$
--   The Specht module $S^t\subseteq W_{n,\ell(\mu)}$ is the span of the $S_n$-orbit $\{\rho_{n,\ell(\mu)}(g)e_t:g\in S_n\}$.
--
--   Fix two tableaux $s,t:[n]\to\mu$ of the same shape. The file introduces:
--
--   1. **Transition permutation.** $\sigma_{s,t}=t^{-1}\circ s\in S_n$, characterized by $t(\sigma_{s,t}(i))=s(i)$, equivalently $s(\sigma_{s,t}^{-1}(i))=t(i)$, for all $i\in[n]$.
--   2. **Corresponding column groups.** Conjugation $h\mapsto\sigma_{s,t}\,h\,\sigma_{s,t}^{-1}$ is a bijection $C_s\to C_t$, with inverse $h\mapsto\sigma_{s,t}^{-1}h\,\sigma_{s,t}$.
--   3. **Transport of row words and polytabloids.** $r_t=r_s\circ\sigma_{s,t}^{-1}$, and
--   $$
--   e_t=\rho_{n,\ell(\mu)}(\sigma_{s,t})\,e_s .
--   $$
--   4. **Polytabloids of one shape lie in each Specht module of that shape.** $e_t\in S^s$ for all tableaux $s,t$ of shape $\mu$.
--
--   By item 4 (applied in both directions, and since a subrepresentation containing $e_t$ contains its whole orbit span) the Specht subspace $S^t\subseteq W_{n,\ell(\mu)}$ does not depend on the chosen tableau, only on the shape. In the surrounding development this is used, for instance, to see that the polytabloid of the transposed staircase tableau lies in the Specht module of the canonical staircase tableau.
--
--   **Formalization Note** The permutation $\sigma_{s,t}$ is `tableauMove s t` (defined as `s.trans t.symm`), the bijection of item 2 is the `Equiv` `columnMove s t`, and items 1, 3 and 4 are the lemmas `tableauMove_apply`, `tableauMove_inv_apply`, `rowWord_move`, `polytabloid_move` and `polytabloid_mem_all`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/Saxl/TableauTransport.lean

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/Saxl/TableauTransport.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the Saxl mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_Saxl
import Definitions.Def_OAI_RepresentationTheory_Saxl_Basic
import Definitions.Def_OAI_RepresentationTheory_Saxl_Polytabloid
import Definitions.Def_OAI_RepresentationTheory_Saxl_SpechtSubmodule
import Definitions.Def_OAI_RepresentationTheory_Saxl_SpechtDuality

namespace OAI

noncomputable section

open scoped TensorProduct

namespace Saxl
/- A change of tableau enumeration only applies a position permutation. -/
def tableauMove {n : ℕ} {μ : YoungDiagram} (s t : Tableau n μ) : Equiv.Perm (Fin n) :=
  s.trans t.symm

@[simp] lemma tableauMove_apply {n : ℕ} {μ : YoungDiagram} (s t : Tableau n μ) (i : Fin n) :
    t (tableauMove s t i) = s i := by simp [tableauMove]

@[simp] lemma tableauMove_inv_apply {n : ℕ} {μ : YoungDiagram} (s t : Tableau n μ) (i : Fin n) :
    s ((tableauMove s t)⁻¹ i) = t i := by simp [tableauMove, Equiv.Perm.inv_def]

def columnMove {n : ℕ} {μ : YoungDiagram} (s t : Tableau n μ) :
    columnGroup s ≃ columnGroup t where
  toFun h := ⟨tableauMove s t * h.val * (tableauMove s t)⁻¹, by
    intro i
    simp only [Equiv.Perm.mul_apply, tableauMove_apply]
    rw [h.property, tableauMove_inv_apply]⟩
  invFun h := ⟨(tableauMove s t)⁻¹ * h.val * tableauMove s t, by
    intro i
    simp only [Equiv.Perm.mul_apply, tableauMove_inv_apply]
    rw [h.property, tableauMove_apply]⟩
  left_inv h := by apply Subtype.ext; simp [mul_assoc]
  right_inv h := by apply Subtype.ext; simp [mul_assoc]

lemma rowWord_move {n : ℕ} {μ : YoungDiagram} (s t : Tableau n μ) :
    rowWord t = rowWord s ∘ ((tableauMove s t)⁻¹ : Equiv.Perm (Fin n)) := by
  funext i
  apply Fin.ext
  exact congrArg (fun c : μ.cells => c.val.1) (tableauMove_inv_apply s t i).symm

lemma polytabloid_move {n : ℕ} {μ : YoungDiagram} (s t : Tableau n μ) :
    polytabloid t = wordRep n (μ.colLen 0) (tableauMove s t) (polytabloid s) := by
  classical
  let := Fintype.ofFinite (columnGroup s)
  let := Fintype.ofFinite (columnGroup t)
  unfold polytabloid
  rw [map_sum]
  refine (Fintype.sum_equiv (columnMove s t).symm _ _ ?_)
  intro h
  let g := tableauMove s t
  change signC (h : Equiv.Perm (Fin n)) • wordRep n (μ.colLen 0) h.val (Pi.single (rowWord t) 1) =
    wordRep n (μ.colLen 0) g
      (signC ((columnMove s t).symm h).val •
        wordRep n (μ.colLen 0) ((columnMove s t).symm h).val (Pi.single (rowWord s) 1))
  have hs : signC ((columnMove s t).symm h).val = signC h.val := by
    change signC (g⁻¹ * h.val * g) = signC h.val
    rw [map_mul, map_mul, signC_inv]
    calc signC g * signC h.val * signC g = signC h.val * (signC g * signC g) := by ring
         _ = signC h.val := by rw [signC_mul_self, mul_one]
  rw [map_smul, hs]
  congr 1
  rw [← Module.End.mul_apply, ← map_mul]
  change wordRep n (μ.colLen 0) h.val (Pi.single (rowWord t) 1) =
    wordRep n (μ.colLen 0) (g * (g⁻¹ * h.val * g)) (Pi.single (rowWord s) 1)
  have he : g * (g⁻¹ * h.val * g) = h.val * g := by group
  have hv : wordRep n (μ.colLen 0) g (Pi.single (rowWord s) 1) = Pi.single (rowWord t) 1 := by
    rw [wordRep_single, rowWord_move s t]
  rw [he, map_mul, Module.End.mul_apply, hv]

lemma polytabloid_mem_all {n : ℕ} {μ : YoungDiagram} (s t : Tableau n μ) :
    polytabloid t ∈ spechtSub s := by
  rw [polytabloid_move s t]
  exact (spechtSub s).apply_mem_toSubmodule _ (mem_cyclic _ _)

end Saxl

end

end OAI


