-- Prove2me | Definitions.Def_OAI_Combinatorics_ParityLifts_Main
-- name    : OAI_Combinatorics_ParityLifts_Main
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T04:32:17.216484+00:00
-- url     : https://prove2.me/theorems/ae8ae19a-e7f3-4f82-b983-a213ccee14b1
-- title:
--   Pure-left rooted maps into a disjoint union and transport of rooted maps along graph isomorphisms
-- statement:
--   Let $F$ be a rooted test with $k$ roots (a finite vertex set $X_F$ with a symmetric relation $R_F$ and root labels $\rho_F(0),\dots,\rho_F(k-1)$), and let $G$ and $H$ be simple graphs on sets $V$ and $W$, with disjoint union $G\sqcup H$ on $V\sqcup W$. For a simple graph $K$ on $U$ and $x\in U^k$, a map of $F$ into $K$ over $x$ is a map $f:X_F\to U$ with $f(p)f(q)\in E(K)$ whenever $p\,R_F\,q$ and $f(\rho_F(j))=x_j$ for all $j$.
--
--   1. **Pure-left totals.** Let $\iota:V\to V\sqcup W$ be the left inclusion. Pairs $(x,f)$ consisting of a tuple $x\in V^k$ and a map $f$ of $F$ into $G\sqcup H$ over $\iota\circ x$ correspond bijectively to pure-left maps, that is, relation-preserving maps $X_F\to V\sqcup W$ into $G\sqcup H$ sending every root into $V$: one forgets $x$, and recovers it from the values of $f$ at the roots. Consequently, for finite $V$ and $W$,
--   $$
--   \sum_{x\in V^k}\hom_{\iota\circ x}(F,G\sqcup H)=\#\{\text{pure-left maps of }F\text{ into }G\sqcup H\}.
--   $$
--
--   2. **Transport along isomorphisms.** For a graph isomorphism $e$ from $G$ onto a simple graph $K$ on $U$ and for $x\in V^k$, composition with $e$ is a bijection from the maps of $F$ into $G$ over $x$ onto the maps of $F$ into $K$ over $e\circ x$; its inverse is composition with $e^{-1}$.
--
--   Combined with the decomposition of pure-left maps along component masks, these bijections compute the total number of maps of a test whose roots lie entirely on one side of the disjoint union of two graphs; the isomorphism $G\sqcup H\cong H\sqcup G$ reduces the right-hand side to the left-hand case. The parity reduction uses this, for the zero lift and the star lift, to prove the pure version of Weisfeiler–Leman equivalence.
--
--   **Formalization Note** `pureLeftTotalEquiv F G H` is an equivalence between the sigma type of pairs `(x, f)` with `x : Fin k → V` and `f : F.Maps (G.sum H) (Sum.inl ∘ x)` and the type `PureLeftMaps F G H`; `rootedMapsIso F G e x` is an equivalence from `F.Maps G x` to `F.Maps K (e ∘ x)` for `e : G ≃g K`. The displayed count identity follows by taking cardinalities.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/ParityLifts/Main.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/ParityLifts/Main.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the ParityLifts mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_ParityLifts
import Definitions.Def_OAI_Combinatorics_ParityLifts_LiftCounts
import Definitions.Def_OAI_Combinatorics_ParityLifts_WeightedDual
import Definitions.Def_OAI_Combinatorics_ParityLifts_Masses
import Definitions.Def_OAI_Combinatorics_ParityLifts_BaseLabels
import Definitions.Def_OAI_Combinatorics_ParityLifts_BalancedBags
import Definitions.Def_OAI_Combinatorics_ParityLifts_DecompositionCuts
import Definitions.Def_OAI_Combinatorics_ParityLifts_Witnesses
import Definitions.Def_OAI_Combinatorics_ParityLifts_BagTrees
import Definitions.Def_OAI_Combinatorics_ParityLifts_TagSizes
import Definitions.Def_OAI_Combinatorics_ParityLifts_Detection
import Definitions.Def_OAI_Combinatorics_ParityLifts_RankedTrees
import Definitions.Def_OAI_Combinatorics_ParityLifts_RootedTests
import Definitions.Def_OAI_Combinatorics_ParityLifts_GlueTrees
import Definitions.Def_OAI_Combinatorics_ParityLifts_GlueVertices
import Definitions.Def_OAI_Combinatorics_ParityLifts_Rerooting
import Definitions.Def_OAI_Combinatorics_ParityLifts_TestAlgebra
import Definitions.Def_OAI_Combinatorics_ParityLifts_Interpolation
import Definitions.Def_OAI_Combinatorics_ParityLifts_ColorSpan
import Definitions.Def_OAI_Combinatorics_ParityLifts_PureComponents

namespace OAI

namespace ParityWL

open scoped BigOperators

section PureTotals

open scoped Classical

variable {k t : ℕ} (F : RootedTest k t)
variable {V W : Type} (G : SimpleGraph V) (H : SimpleGraph W)

noncomputable def pureLeftTotalEquiv :
    ((x : Fin k → V) × F.Maps (G.sum H) (Sum.inl ∘ x)) ≃ PureLeftMaps F G H where
  toFun f := ⟨f.2.1, fun i => by rw [f.2.2 i]; rfl⟩
  invFun f := ⟨fun i => (f.1.1 (F.roots i)).getLeft (f.2 i),
    ⟨f.1, fun i => (Sum.inl_getLeft _ _).symm⟩⟩
  left_inv f := by
    rcases f with ⟨x, f, hf⟩
    have hx : (fun i => (f.1 (F.roots i)).getLeft (by rw [hf i]; rfl)) = x := by
      funext i
      exact (Sum.getLeft_eq_iff _).mpr (hf i)
    dsimp only
    apply Sigma.ext hx
    apply (Subtype.heq_iff_coe_eq (fun g => by dsimp only; rw [hx])).mpr
    rfl
  right_inv _ := rfl

noncomputable def rootedMapsIso {U : Type} {K : SimpleGraph U} (e : G ≃g K) (x : Fin k → V) :
    F.Maps G x ≃ F.Maps K (e ∘ x) where
  toFun f := ⟨⟨e ∘ f.1.1, fun a b hab => e.map_adj_iff.mpr (f.1.2 a b hab)⟩,
    fun i => congrArg e (f.2 i)⟩
  invFun f := ⟨⟨e.symm ∘ f.1.1, fun a b hab => e.symm.map_adj_iff.mpr (f.1.2 a b hab)⟩,
    fun i => by simpa only [Function.comp_apply, e.symm_apply_apply] using congrArg e.symm (f.2 i)⟩
  left_inv f := by
    apply Subtype.ext
    apply Subtype.ext
    funext a
    exact e.symm_apply_apply _
  right_inv f := by
    apply Subtype.ext
    apply Subtype.ext
    funext a
    exact e.apply_symm_apply _

end PureTotals

end ParityWL

end OAI


