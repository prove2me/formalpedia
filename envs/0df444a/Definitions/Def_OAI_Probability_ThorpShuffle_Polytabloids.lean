-- Prove2me | Definitions.Def_OAI_Probability_ThorpShuffle_Polytabloids
-- name    : OAI_Probability_ThorpShuffle_Polytabloids
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-16T03:51:32.517171+00:00
-- url     : https://prove2.me/theorems/6a979436-b3b5-485e-a555-b7f3e8bb7233
-- title:
--   Specht modules of different Young diagrams are not isomorphic
-- statement:
--   This module proves that Specht modules attached to different Young diagrams are non-isomorphic representations of the symmetric group.
--
--   **Setting.** Let $\alpha$ be a finite set and $S_\alpha$ its permutation group. For functions $r,c:\alpha\to\mathbb{N}$:
--
--   - a tabloid of $r$ is a rearrangement $f=r\circ g$ with $g\in S_\alpha$, and $S_\alpha$ acts on tabloids by $(g\cdot f)(x)=f(g^{-1}x)$;
--   - $M_r$ is the space of complex-valued functions on the tabloids of $r$, with indicator vectors $\delta_f$ and the action $(\rho(g)v)(f)=v(g^{-1}\cdot f)$;
--   - $G_c=\{g\in S_\alpha:\ c(g(x))=c(x)\text{ for all }x\}$, and the alternator of $c$ on $M_r$ is
--   $$
--   A_c=\sum_{h\in G_c}\operatorname{sgn}(h)\,\rho(h).
--   $$
--
--   A Young diagram $D$ is a finite set of cells $(i,j)\in\mathbb{N}^2$ (row $i$, column $j$, both counted from $0$) such that $(i,j)\in D$, $i'\le i$ and $j'\le j$ imply $(i',j')\in D$. For a bijection $t:\alpha\to D$ let $r_t,c_t$ be its row and column functions, $\{t\}=r_t$ its base tabloid, $e_t=A_{c_t}\delta_{\{t\}}\in M_{r_t}$ its polytabloid, and $S^D_t=\operatorname{span}_{\mathbb{C}}\{\rho(g)e_t: g\in S_\alpha\}$ its Specht module. Finally let
--   $$
--   n(D)=\sum_{(i,j)\in D} i
--   $$
--   be the sum of the row indices of the cells of $D$.
--
--   For Young diagrams $D,E$ and bijections $t:\alpha\to D$, $u:\alpha\to E$, the module proves:
--
--   1. Every tabloid $f$ of $r$ satisfies $\sum_{x}f(x)=\sum_{x}r(x)$, and $\sum_{x}r_t(x)=n(D)$.
--   2. If a tabloid $f$ of $r$ has $f(x)=f(y)$ for some $x\ne y$ with $c(x)=c(y)$, then $A_c\,\delta_f=0$.
--   3. If $A_c v\ne 0$ for some $v\in M_r$, then some tabloid $f$ of $r$ is injective on every fibre of $c$: $c(x)=c(y)$ and $f(x)=f(y)$ imply $x=y$.
--   4. If some tabloid $f$ of $r_u$ is injective on every column of $t$, then $n(D)\le n(E)$; if moreover $n(D)=n(E)$, then $D=E$.
--   5. If there is an injective $S_\alpha$-equivariant linear map $F:S^D_t\to S^E_u$, then $A_{c_t}v\ne 0$ for some $v\in M_{r_u}$, and consequently $n(D)\le n(E)$.
--   6. If $S^D_t$ and $S^E_u$ are isomorphic as representations of $S_\alpha$, then $D=E$.
--
--   Item 6 is the inequivalence half of the classification of the irreducible representations of the symmetric group: together with the irreducibility of Specht modules it shows that distinct Young diagrams with $|\alpha|$ cells give pairwise non-isomorphic irreducible representations. The integer $n(D)$ serves as a simple monotone statistic: by item 5 an injective intertwiner between Specht modules can only increase it.
--
--   **Formalization Note** The statistic $n(D)$ appears as `∑ z : Cells D, z.val.1`, isomorphisms are `Representation.Equiv`, equivariant maps are `Representation.IntertwiningMap`, and $A_c$ is `PermutationSpace.alternator` applied to the inclusion of `fiberGroup c` and the complex sign. The items above are, in order, `tabloid_sum` and `rowRankSum_tableau`, `collision_zero`, `alternator_nonzero_nocollision`, `rankSum_le_of_nocollision` and `shape_eq_of_nocollision_equal_sum`, `mapped_column_nonzero` and `rankSum_le_of_injective_intertwiner`, and `shape_eq_of_equiv`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ThorpShuffle/Polytabloids.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/ThorpShuffle/Polytabloids.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the ThorpFirstReciprocal mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_ThorpFirstReciprocal
import Definitions.Def_OAI_Probability_ThorpShuffle_Model
import Definitions.Def_OAI_Probability_ThorpShuffle_PairAveraging
import Definitions.Def_OAI_Probability_ThorpShuffle_Walsh
import Definitions.Def_OAI_Probability_ThorpShuffle_Support
import Definitions.Def_OAI_Probability_ThorpShuffle_ConditionalFlow
import Definitions.Def_OAI_Probability_ThorpShuffle_FiniteExpectation
import Definitions.Def_OAI_Probability_ThorpShuffle_WalshFlow
import Definitions.Def_OAI_Probability_ThorpShuffle_FreshCoins
import Definitions.Def_OAI_Probability_ThorpShuffle_HalfHistories
import Definitions.Def_OAI_Probability_ThorpShuffle_NoiseEnergy
import Definitions.Def_OAI_Probability_ThorpShuffle_EnergyDecay
import Definitions.Def_OAI_Probability_ThorpShuffle_MarginalEnergy
import Definitions.Def_OAI_Probability_ThorpShuffle_ConditionalLaw
import Definitions.Def_OAI_Probability_ThorpShuffle_TaggedCompletion
import Definitions.Def_OAI_Probability_ThorpShuffle_Reachability
import Definitions.Def_OAI_Probability_ThorpShuffle_Cyclic
import Definitions.Def_OAI_Probability_ThorpShuffle_Tableaux
import Definitions.Def_OAI_Probability_ThorpShuffle_Specht

namespace OAI

universe uα

noncomputable section

open scoped BigOperators ComplexConjugate InnerProductSpace
open Filter

namespace Thorp.Specht
open scoped Classical

variable {α : Type uα} [Fintype α]

lemma tabloid_sum (r : α → ℕ) (f : Tabloid r) : ∑ x, f.val x = ∑ x, r x := by
  obtain ⟨g, hg⟩ := f.property
  rw [hg]
  exact Equiv.sum_comp g r

lemma collision_zero (r c : α → ℕ) (f : Tabloid r)
    (x y : α) (hxy : x ≠ y) (hc : c x = c y) (hf : f.val x = f.val y) :
    PermutationSpace.alternator (fiberGroup c).subtype
      (complexSign.comp (fiberGroup c).subtype) (EuclideanSpace.single f 1) = 0 := by
  apply PermutationSpace.alternator_single_zero _ _ f (⟨Equiv.swap x y, swap_preserves hc⟩ : fiberGroup c)
  · rw [stabilizes_tabloid_iff]
    exact swap_preserves hf
  · exact complexSign_swap x y hxy

lemma alternator_nonzero_nocollision (r c : α → ℕ)
    (v : EuclideanSpace ℂ (Tabloid r))
    (hv : PermutationSpace.alternator (fiberGroup c).subtype
      (complexSign.comp (fiberGroup c).subtype) v ≠ 0) :
    ∃ f : Tabloid r, ∀ x y, c x = c y → f.val x = f.val y → x = y := by
  by_contra hn
  push Not at hn
  apply hv
  have hexp := (EuclideanSpace.basisFun (Tabloid r) ℂ).sum_repr v
  simp only [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply] at hexp
  rw [← hexp, map_sum]
  apply Finset.sum_eq_zero
  intro f _
  obtain ⟨x, y, hcol, hrow, hne⟩ := hn f
  rw [map_smul, collision_zero r c f x y hne hcol hrow, smul_zero]

lemma rowRankSum_tableau (D : YoungDiagram) (t : α ≃ Thorp.Young.Cells D) :
    ∑ x : α, tableauRow D t x = ∑ z : Thorp.Young.Cells D, z.val.1 :=
  Equiv.sum_comp t (fun z => z.val.1)

lemma rankSum_le_of_nocollision (D E : YoungDiagram)
    (t : α ≃ Thorp.Young.Cells D) (u : α ≃ Thorp.Young.Cells E)
    (f : Tabloid (tableauRow E u))
    (hf : ∀ x y, tableauCol D t x = tableauCol D t y → f.val x = f.val y → x = y) :
    ∑ z : Thorp.Young.Cells D, z.val.1 ≤ ∑ z : Thorp.Young.Cells E, z.val.1 := by
  have hi : ∀ x y : Thorp.Young.Cells D, x.val.2 = y.val.2 →
      f.val (t.symm x) = f.val (t.symm y) → x = y := by
    intro x y hc hr
    apply t.symm.injective
    apply hf _ _ _ hr
    simpa only [tableauCol, Equiv.apply_symm_apply] using hc
  have hh := Thorp.Young.rowRankSum_le D (fun z => f.val (t.symm z)) hi
  rw [Equiv.sum_comp t.symm, tabloid_sum, rowRankSum_tableau] at hh
  exact hh

lemma shape_eq_of_nocollision_equal_sum (D E : YoungDiagram)
    (t : α ≃ Thorp.Young.Cells D) (u : α ≃ Thorp.Young.Cells E)
    (f : Tabloid (tableauRow E u))
    (hf : ∀ x y, tableauCol D t x = tableauCol D t y → f.val x = f.val y → x = y)
    (hs : ∑ z : Thorp.Young.Cells D, z.val.1 = ∑ z : Thorp.Young.Cells E, z.val.1) : D = E := by
  have hi : ∀ x y : Thorp.Young.Cells D, x.val.2 = y.val.2 →
      f.val (t.symm x) = f.val (t.symm y) → x = y := by
    intro x y hc hr
    apply t.symm.injective
    apply hf _ _ _ hr
    simpa only [tableauCol, Equiv.apply_symm_apply] using hc
  have hsum : ∑ z : Thorp.Young.Cells D, f.val (t.symm z) = ∑ z : Thorp.Young.Cells D, z.val.1 := by
    rw [Equiv.sum_comp t.symm, tabloid_sum, rowRankSum_tableau, hs]
  obtain ⟨σ, -, hσ⟩ := Thorp.Young.column_sort D (fun z => f.val (t.symm z)) hi hsum
  obtain ⟨g, hg⟩ := f.property
  apply Thorp.Young.eq_of_rowPreserving D E (((σ.trans t.symm).trans g).trans u)
  intro x
  have hh := hσ x
  rw [hg] at hh
  exact hh

lemma mapped_column_nonzero (D E : YoungDiagram)
    (t : α ≃ Thorp.Young.Cells D) (u : α ≃ Thorp.Young.Cells E)
    (F : Representation.IntertwiningMap (module D t).toRepresentation (module E u).toRepresentation)
    (hF : Function.Injective F) :
    ∃ v : EuclideanSpace ℂ (Tabloid (tableauRow E u)),
      PermutationSpace.alternator (fiberGroup (tableauCol D t)).subtype
        (complexSign.comp (fiberGroup (tableauCol D t)).subtype) v ≠ 0 := by
  let e : (module D t).toSubmodule := ⟨polytabloid D t, self_mem_cyclic _ _⟩
  have he : e ≠ 0 := by
    intro h
    exact polytabloid_ne_zero D t (congrArg Subtype.val h)
  have heig : ∑ h : fiberGroup (tableauCol D t), complexSign h.val •
      (module D t).toRepresentation h.val e = ⟪polytabloid D t, polytabloid D t⟫_ℂ • e := by
    apply Subtype.ext
    simp only [Submodule.coe_sum, Submodule.coe_smul]
    change (∑ h : fiberGroup (tableauCol D t), complexSign h.val •
      tabloidRep D t h.val (polytabloid D t)) = _
    exact (PermutationSpace.alternator_apply _ _ _).symm.trans (columnAlternator_rank_one D t _)
  have hh := congrArg (fun z => (F z : EuclideanSpace ℂ (Tabloid (tableauRow E u)))) heig
  simp only [map_sum, map_smul, F.isIntertwining, Submodule.coe_sum, Submodule.coe_smul] at hh
  refine ⟨F e, ?_⟩
  intro hz
  have heq : PermutationSpace.alternator (fiberGroup (tableauCol D t)).subtype
      (complexSign.comp (fiberGroup (tableauCol D t)).subtype) (F e : EuclideanSpace ℂ (Tabloid (tableauRow E u))) =
      ⟪polytabloid D t, polytabloid D t⟫_ℂ • (F e : EuclideanSpace ℂ (Tabloid (tableauRow E u))) := by
    rw [PermutationSpace.alternator_apply]
    exact hh
  rw [hz] at heq
  rcases smul_eq_zero.mp heq.symm with hs | hs
  · exact polytabloid_ne_zero D t (inner_self_eq_zero.mp hs)
  · have hh' : F e = 0 := Subtype.ext hs
    exact he (hF (by simpa using hh'))

lemma rankSum_le_of_injective_intertwiner (D E : YoungDiagram)
    (t : α ≃ Thorp.Young.Cells D) (u : α ≃ Thorp.Young.Cells E)
    (F : Representation.IntertwiningMap (module D t).toRepresentation (module E u).toRepresentation)
    (hF : Function.Injective F) :
    ∑ z : Thorp.Young.Cells D, z.val.1 ≤ ∑ z : Thorp.Young.Cells E, z.val.1 := by
  obtain ⟨v, hv⟩ := mapped_column_nonzero D E t u F hF
  obtain ⟨f, hf⟩ := alternator_nonzero_nocollision _ _ v hv
  exact rankSum_le_of_nocollision D E t u f hf

theorem shape_eq_of_equiv (D E : YoungDiagram)
    (t : α ≃ Thorp.Young.Cells D) (u : α ≃ Thorp.Young.Cells E)
    (F : Representation.Equiv (module D t).toRepresentation (module E u).toRepresentation) : D = E := by
  have hle := rankSum_le_of_injective_intertwiner D E t u F.toIntertwiningMap F.toLinearEquiv.injective
  have hge := rankSum_le_of_injective_intertwiner E D u t F.symm.toIntertwiningMap F.symm.toLinearEquiv.injective
  obtain ⟨v, hv⟩ := mapped_column_nonzero D E t u F.toIntertwiningMap F.toLinearEquiv.injective
  obtain ⟨f, hf⟩ := alternator_nonzero_nocollision _ _ v hv
  exact shape_eq_of_nocollision_equal_sum D E t u f hf (le_antisymm hle hge)

end Thorp.Specht

end

end OAI


