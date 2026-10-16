-- Prove2me | Definitions.Def_OAI_Probability_ThorpShuffle_LinearExtensions
-- name    : OAI_Probability_ThorpShuffle_LinearExtensions
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-16T03:58:39.844637+00:00
-- url     : https://prove2.me/theorems/d0a1b50b-d9e9-41e1-9d8d-65c1387e15ca
-- title:
--   Linear extensions of finite posets bound Specht dimensions from below
-- statement:
--   This module introduces linear extensions of finite posets and shows that the number of linear extensions of the cell poset of a Young diagram is at most the dimension of the corresponding Specht module.
--
--   Let $A$ be a finite partially ordered set and $[m]=\{0,1,\dots,m-1\}$.
--
--   1. *Linear extensions.* $\mathrm{Ext}(A)$ is the set of bijections $e:A\to[|A|]$ that are strictly increasing: $a<b$ implies $e(a)<e(b)$. Every finite poset has at least one linear extension, i.e. $\mathrm{Ext}(A)\ne\varnothing$.
--   2. *Labelings and Specht dimension.* Let $D$ be a Young diagram, a finite set of cells $(i,j)\in\mathbb{N}^2$ (row $i$, column $j$, both counted from $0$) such that $(i,j)\in D$, $i'\le i$ and $j'\le j$ imply $(i',j')\in D$, with cells ordered componentwise ($(i',j')\le(i,j)$ iff $i'\le i$ and $j'\le j$), and let $t:[n]\to D$ be a bijection. Let $S^D_t$ be the Specht module of $t$: the complex span of the translates $\rho(g)e_t$, $g\in S_n$, of the polytabloid $e_t=\sum_{h\in C_t}\operatorname{sgn}(h)\,\delta_{h\cdot\{t\}}$ in the permutation module on tabloids, where $C_t$ is the group of permutations preserving the columns of $t$ and $\{t\}$ is the row tabloid of $t$. If $I$ is a finite set and $(l_i)_{i\in I}$ is an injective family of strictly increasing bijections $l_i:D\to[n]$, then $|I|\le\dim_{\mathbb{C}}S^D_t$. In particular
--   $$
--   |\mathrm{Ext}(D)|\le\dim_{\mathbb{C}}S^D_t .
--   $$
--   3. *Transposition.* The map $(i,j)\mapsto(j,i)$ is an order isomorphism from the cells of $D$ onto the cells of the conjugate diagram $D^{\mathsf T}=\{(j,i):(i,j)\in D\}$.
--
--   A linear extension of the cell poset of $D$ is exactly a standard Young tableau of shape $D$ (labels increasing along rows and down columns), so item 2 states that the number of standard tableaux is at most the Specht dimension. It turns combinatorial lower bounds on linear extensions, such as binomial coefficients, into lower bounds on Specht degrees, and the transposition isomorphism allows such bounds to be applied to whichever of the first row and the first column is longer.
--
--   **Formalization Note** `Extensions A` is the subtype of `A ≃ Fin (Fintype.card A)` consisting of strictly monotone maps, `extensions_nonempty` gives nonemptiness, `labels_card_le_degree` and `extensions_card_le_degree` are the bounds of item 2 (stated for `t : Fin n ≃ Cells D`, so that $|D|=n$), and `transposeCells D` is the order isomorphism `Cells D ≃o Cells D.transpose`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ThorpShuffle/LinearExtensions.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/ThorpShuffle/LinearExtensions.lean by skeleton subtraction
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
import Definitions.Def_OAI_Probability_ThorpShuffle_Polytabloids
import Definitions.Def_OAI_Probability_ThorpShuffle_Irreducibility
import Definitions.Def_OAI_Probability_ThorpShuffle_Classification

namespace OAI

universe uA uα uI uB

noncomputable section

open scoped BigOperators ComplexConjugate InnerProductSpace
open Filter

namespace Thorp.Young
open scoped Classical

variable (A : Type uA) [Fintype A] [PartialOrder A]

def Extensions := {e : A ≃ Fin (Fintype.card A) // StrictMono e}

instance : Fintype (Extensions A) := inferInstanceAs (Fintype {e : A ≃ Fin (Fintype.card A) // StrictMono e})

lemma extensions_nonempty : Nonempty (Extensions A) := by
  let h : A ≃ LinearExtension A := Equiv.refl A
  let : Fintype (LinearExtension A) := Fintype.ofEquiv A h
  let e := (Fintype.orderIsoFinOfCardEq (LinearExtension A) (Fintype.card_congr h.symm)).symm
  refine ⟨⟨h.trans e.toEquiv, ?_⟩⟩
  exact e.strictMono.comp
    (toLinearExtension.monotone.strictMono_of_injective fun _ _ hh => hh)

end Thorp.Young

namespace Thorp.Specht
open scoped Classical
variable {α : Type uα} [Fintype α]

end Thorp.Specht

namespace Thorp.Young
open scoped Classical
variable (A : Type uA) [Fintype A] [PartialOrder A]

end Thorp.Young

namespace Thorp.Specht
open scoped Classical
variable {n : ℕ} (D : YoungDiagram) (t : Fin n ≃ Thorp.Young.Cells D)

lemma labels_card_le_degree {I : Type uI} [Fintype I]
    (l : I → Thorp.Young.Cells D ≃ Fin n) (hl : ∀ i, StrictMono (l i))
    (hi : Function.Injective l) : Fintype.card I ≤ Module.finrank ℂ (module D t).toSubmodule := by
  let F (i : I) : StandardPerm D t := ⟨t.trans (l i), by
    intro x y hxy
    change l i (t (t.symm x)) < l i (t (t.symm y))
    simpa only [Equiv.apply_symm_apply] using hl i hxy⟩
  have hF : Function.Injective F := by
    intro i j hij
    apply hi
    apply Equiv.ext
    intro x
    have hh := congrArg (fun g : StandardPerm D t => g.val (t.symm x)) hij
    simpa only [F, Equiv.trans_apply, Equiv.apply_symm_apply] using hh
  exact (Fintype.card_le_of_injective F hF).trans (standardPerm_card_le_degree D t)

lemma extensions_card_le_degree :
    Fintype.card (Thorp.Young.Extensions (Thorp.Young.Cells D)) ≤
      Module.finrank ℂ (module D t).toSubmodule := by
  have hc : Fintype.card (Thorp.Young.Cells D) = n := (Fintype.card_congr t.symm).trans (Fintype.card_fin n)
  let c := finCongr hc
  apply labels_card_le_degree D t (fun e => e.val.trans c)
  · intro e x y hxy
    exact e.property hxy
  · intro e f hef
    apply Subtype.ext
    apply Equiv.ext
    intro x
    apply c.injective
    exact congrArg (fun z : Thorp.Young.Cells D ≃ Fin n => z x) hef

end Thorp.Specht

namespace Thorp.Young
open scoped Classical

def transposeCells (D : YoungDiagram) : Cells D ≃o Cells D.transpose where
  toFun x := ⟨x.val.swap, by
    change x.val.swap ∈ D.transpose
    rw [YoungDiagram.mem_transpose, Prod.swap_swap]
    exact x.property⟩
  invFun x := ⟨x.val.swap, (YoungDiagram.mem_transpose.mp x.property)⟩
  left_inv x := by apply Subtype.ext; exact Prod.swap_swap x.val
  right_inv x := by apply Subtype.ext; exact Prod.swap_swap x.val
  map_rel_iff' := by intro x y; exact and_comm

end Thorp.Young

end

end OAI


