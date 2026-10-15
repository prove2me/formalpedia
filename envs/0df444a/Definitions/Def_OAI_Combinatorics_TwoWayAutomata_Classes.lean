-- Prove2me | Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Classes
-- name    : OAI_Combinatorics_TwoWayAutomata_Classes
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T08:14:49.964081+00:00
-- url     : https://prove2.me/theorems/62b7d35b-30f3-4497-ab3d-448f5bc503e3
-- title:
--   Loop closures are idempotent, and no recurrent class of a diagram is missing relative to itself
-- statement:
--   Let $m\in\mathbb{N}$ and let $e=(e_{\mathrm f},e_{\mathrm b},e_{\mathrm l},e_{\mathrm r})$ be a boundary diagram on $[m]=\{0,\dots,m-1\}$, with the notions of the diagram definitions: the loop closures $\Lambda^+_e=(e_{\mathrm l}e_{\mathrm r})^*$ and $\Lambda^-_e=(e_{\mathrm r}e_{\mathrm l})^*$ (relations compose in path order and $^*$ is the reflexive–transitive closure), and the set $\mathrm{Miss}_e(z)$ of signed recurrent classes $(\pm,C)$ of $e$ such that $(x,x)\notin\Lambda^\pm_e\,z_\pm\,\Lambda^\pm_e$ for every $x\in C$, where $z_+=z_{\mathrm f}$ and $z_-=z_{\mathrm b}$. This file records two facts, valid for every diagram $e$, idempotent or not, and for both signs.
--
--   1. **Loop closures are idempotent:** $\Lambda^\pm_e\,\Lambda^\pm_e=\Lambda^\pm_e$.
--   2. **Nothing is missing from $e$ itself:** $\mathrm{Miss}_e(e)=\emptyset$.
--
--   Item 1 is the instance $R^*R^*=R^*$ that simplifies products of loop closures in later calculations. Item 2 is the base case for comparisons of missing classes: the number of classes of $e$ missing in a diagram $z$ measures how much of the recurrent structure of $e$ is lost when $e$ is replaced by $z$, and it vanishes for $z=e$.
--
--   **Formalization Note** The two facts are the simp lemmas `Diagram.loopClosure_comp_self` and `Diagram.missing_self`; signs are `Bool`, with `true` for $+$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/TwoWayAutomata/Classes.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/TwoWayAutomata/Classes.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the TwoWayComplementation mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_TwoWayComplementation
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Relations
import Definitions.Def_OAI_Combinatorics_TwoWayAutomata_Diagram

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


