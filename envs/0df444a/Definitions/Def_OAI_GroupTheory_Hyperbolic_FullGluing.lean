-- Prove2me | Definitions.Def_OAI_GroupTheory_Hyperbolic_FullGluing
-- name    : OAI_GroupTheory_Hyperbolic_FullGluing
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T06:59:16.526073+00:00
-- url     : https://prove2.me/theorems/986873f4-e93c-4e0c-9056-60e2886fb69d
-- title:
--   Rewording full fillings and pushing their traces forward
-- statement:
--   Two small operations on full fillings of words over an edge alphabet.
--
--   1. **Rewording.** A full filling of a word $w$ is also a full filling of any word $w'$ equal to $w$; the darts, maps and boundary are unchanged.
--   2. **Trace under additive maps.** The trace of a full filling sums a corner function $F:E^3\to M$ over the corners of the non-boundary darts. It is natural in the abelian group $M$: for every additive homomorphism $f:M\to N$,
--   $$
--   f\bigl(\mathrm{trace}(F)\bigr)=\mathrm{trace}\bigl((a,b,c)\mapsto f(F(a,b,c))\bigr).
--   $$
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Hyperbolic/FullGluing.lean

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Hyperbolic/FullGluing.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the TorsionFreeHyperbolic mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_TorsionFreeHyperbolic
import Definitions.Def_OAI_GroupTheory_Hyperbolic_MatrixRank
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Incidence
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Presentation
import Definitions.Def_OAI_GroupTheory_Hyperbolic_WordPaths
import Definitions.Def_OAI_GroupTheory_Hyperbolic_PermutationCycles
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Planarity
import Definitions.Def_OAI_GroupTheory_Hyperbolic_RePairing
import Definitions.Def_OAI_GroupTheory_Hyperbolic_TriangleFilling
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Words
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Dipoles
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Ribbons
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Links
import Definitions.Def_OAI_GroupTheory_Hyperbolic_LiftedFilling
import Definitions.Def_OAI_GroupTheory_Hyperbolic_Spheres
import Definitions.Def_OAI_GroupTheory_Hyperbolic_FullFilling

namespace OAI

namespace Release075.FullFilling
open Equiv PermCycles
attribute [local instance] Classical.propDecidable Classical.decEq
variable {E V M : Type} [AddCommGroup M]
variable {flip : E → E} {color : E → V} {face : E → E → E → Prop}

end Release075.FullFilling

namespace Release075.FullFilling
attribute [local instance] Classical.propDecidable Classical.decEq
variable {E V M : Type} [AddCommGroup M]
variable {flip : E → E} {color : E → V} {face : E → E → E → Prop}

noncomputable abbrev reword {w w' : List E} (D : FullFilling flip color face w)
    (h : w = w') : FullFilling flip color face w' := h ▸ D

end Release075.FullFilling

namespace Release075.FullFilling
open Equiv
attribute [local instance] Classical.propDecidable Classical.decEq
variable {E V M : Type} [AddCommGroup M]
variable {flip : E → E} {color : E → V} {face : E → E → E → Prop}

end Release075.FullFilling

namespace Release075.FullFilling
attribute [local instance] Classical.propDecidable Classical.decEq
variable {E V M N : Type} [AddCommGroup M] [AddCommGroup N]
variable {flip : E → E} {color : E → V} {face : E → E → E → Prop}

theorem trace_map {w : List E} (D : FullFilling flip color face w)
    (F : E → E → E → M) (f : M →+ N) :
    f (D.trace F) = D.trace (fun a b c => f (F a b c)) := by
  unfold trace
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro a _
  split_ifs <;> simp only [map_zero]

end Release075.FullFilling

namespace Release075.TriangleFilling
attribute [local instance] Classical.propDecidable Classical.decEq
variable {E V : Type} {flip : E → E} {color : E → V} {face : E → E → E → Prop}

end Release075.TriangleFilling

end OAI


