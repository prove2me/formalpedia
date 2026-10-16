-- Prove2me | Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Classes__TwoWayDeterminization
-- name    : OAI_Combinatorics_TwoWayAutomata_Classes__TwoWayDeterminization
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-16T03:38:07.692423+00:00
-- url     : https://prove2.me/theorems/c4bacc5f-6810-492e-9b9b-6947b7fbad4c
-- title:
--   Loop closures of a boundary diagram are idempotent, and no recurrent class is missing relative to the diagram itself
-- statement:
--   Fix $m\in\mathbb N$ and let $[m]=\{0,\dots,m-1\}$. A boundary diagram $e=(F_e,B_e,L_e,R_e)$ is a quadruple of relations on $[m]$ (forward, backward, left-return and right-return traversals of a tape segment). Relations are composed in path order, $(x,z)\in RS$ iff $(x,y)\in R$ and $(y,z)\in S$ for some $y$, and $R^*$ is the reflexive–transitive closure. For a sign $\sigma\in\{+,-\}$ put $T_+(e)=F_e$, $T_-(e)=B_e$, $\Lambda_+(e)=(L_eR_e)^*$, $\Lambda_-(e)=(R_eL_e)^*$ and $\mathrm{Rec}_\sigma(e)=\Lambda_\sigma(e)T_\sigma(e)\Lambda_\sigma(e)$. The signed recurrent classes of $e$ are the pairs $(\sigma,K)$ with $K=\{y:(x,y)\in\mathrm{Rec}_\sigma(e)\text{ and }(y,x)\in\mathrm{Rec}_\sigma(e)\}$ for some $x$ with $(x,x)\in\mathrm{Rec}_\sigma(e)$. For a second diagram $z$, the surviving relation is $U_\sigma(e,z)=\Lambda_\sigma(e)T_\sigma(z)\Lambda_\sigma(e)$, and a class $(\sigma,K)$ of $e$ is missing for $z$ if $(x,x)\notin U_\sigma(e,z)$ for every $x\in K$; $\mathcal M(e,z)$ denotes the set of these classes.
--
--   The module records two basic facts.
--
--   1. **Loop closures are idempotent.** For every diagram $e$ and sign $\sigma$,
--   $$\Lambda_\sigma(e)\,\Lambda_\sigma(e)=\Lambda_\sigma(e).$$
--   2. **Nothing is missing relative to $e$ itself.** For every diagram $e$, $\mathcal M(e,e)=\emptyset$; note that $U_\sigma(e,e)=\mathrm{Rec}_\sigma(e)$ by definition.
--
--   The first fact lets products of loop closures collapse during computations with diagrams. The second is the base case of the bookkeeping of lost classes: when an idempotent diagram $e$ is replaced by another element $z$, the set $\mathcal M(e,z)$ measures which recurrent loops are destroyed, and replacing $e$ by itself destroys none.
--
--   **Formalization Note** The two facts are the simp lemmas `Diagram.loopClosure_comp_self` and `Diagram.missing_self`. Signs are booleans (`true` for $+$), and a signed class is a pair in `Bool × Set (Fin m)`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/TwoWayAutomata/Classes.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/TwoWayAutomata/Classes.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the TwoWayDeterminization mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_TwoWayDeterminization
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Relations__TwoWayDeterminization
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Diagram__TwoWayDeterminization

namespace OAI

namespace TwoWayComplementation

open scoped SetRel

namespace Diagram

@[simp]
theorem loopClosure_comp_self {m : ℕ} (e : Diagram m) (positive : Bool) :
    e.loopClosure positive ○ e.loopClosure positive = e.loopClosure positive :=
  relStar_comp_self _

@[simp]
theorem missing_self {m : ℕ} (e : Diagram m) : e.missing e = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro c ⟨⟨x, hx, hxc⟩, hmissing⟩
  exact hmissing x (hxc ▸ ⟨hx, hx⟩) hx

end Diagram

end TwoWayComplementation

end OAI


