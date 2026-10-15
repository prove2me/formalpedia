-- Prove2me | Definitions.Def_OAI_Analysis_SegmentLenses_HeadTests
-- name    : OAI_Analysis_SegmentLenses_HeadTests
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-14T20:57:59.359117+00:00
-- url     : https://prove2.me/theorems/178939ac-b6fc-45bd-a053-bd8677f9221d
-- title:
--   Finite-dimensional head test spaces and restrictions of dual functionals
-- statement:
--   Let $V$ be a set with decidable equality and a segment system. Let $c_{00}(V)$ be the finitely supported real functions on $V$ with the segment norm, $J_V$ its completion, and $J_V^{*}$ the full continuous dual of $J_V$. Fix a finite set $H\subseteq V$.
--
--   1. **Head test space.** The head test space of $H$ is the linear subspace
--   $$
--   c_{00}(H)=\{u\in c_{00}(V):\ u(v)=0\ \text{for all } v\notin H\}
--   $$
--   of tests supported in $H$. It is finite-dimensional, because $u\mapsto(u(v))_{v\in H}$ is an injective linear map into $\mathbb{R}^H$.
--   2. **Restricted functional.** For $x\in J_V^{*}$, the restriction $x|_{c_{00}(H)}$ is the composition of $x$ with the inclusion $c_{00}(H)\hookrightarrow c_{00}(V)\to J_V$. It is a continuous linear functional on the finite-dimensional normed space $c_{00}(H)$.
--
--   Finite dimensionality makes compactness arguments available. For example, it is used to produce unit test vectors supported in $H$ at which a head functional attains its norm.
--
--   **Formalization Note** `headTestSpace H` is a `Submodule ℝ (Test V)`, with the instance `headTestFinite` giving `FiniteDimensional`. `restrictDual H x` is the continuous linear map `x ∘ toComplL ∘ subtypeL`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/SegmentLenses/HeadTests.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/SegmentLenses/HeadTests.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the MidpointLenses mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_MidpointLenses
import Definitions.Def_OAI_Analysis_SegmentLenses_Basic
import Definitions.Def_OAI_Analysis_SegmentLenses_TreeGeometry
import Definitions.Def_OAI_Analysis_SegmentLenses_FiniteLaws
import Definitions.Def_OAI_Analysis_SegmentLenses_Pairing
import Definitions.Def_OAI_Analysis_SegmentLenses_AtomicBalls
import Definitions.Def_OAI_Analysis_SegmentLenses_LawRecovery

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-!
# Common finite norming tests and head localization
-/

noncomputable section

open scoped BigOperators
open Finset

namespace SegmentLenses

section HeadTests
variable {V : Type*} [decidableEqV : DecidableEq V] [SegmentSystem V]

def headTestSpace (H : Finset V) : Submodule ℝ (Test V) where
  carrier := {u | ∀ v ∉ H, u.coeff v = 0}
  zero_mem' := by intro v hv; rfl
  add_mem' := by intro u v hu hv w hw; exact (show u.coeff w + v.coeff w = 0 by rw [hu w hw, hv w hw, add_zero])
  smul_mem' := by intro a u hu w hw; exact (show a * u.coeff w = 0 by rw [hu w hw, mul_zero])

instance headTestFinite (H : Finset V) : FiniteDimensional ℝ (headTestSpace H) := by
  let e : headTestSpace H →ₗ[ℝ] (H → ℝ) :=
    { toFun := fun u v => u.val.coeff v.val
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  apply FiniteDimensional.of_injective e
  intro u v huv
  apply Subtype.ext
  change u.val.coeff = v.val.coeff
  ext w
  by_cases hw : w ∈ H
  · exact congrFun huv ⟨w, hw⟩
  · rw [u.property w hw, v.property w hw]

def restrictDual (H : Finset V) (x : FullDual V) : headTestSpace H →L[ℝ] ℝ :=
  x.comp ((UniformSpace.Completion.toComplL : Test V →L[ℝ] Primal V).comp (headTestSpace H).subtypeL)

end HeadTests

section NormingTest
variable {V : Type*} [DecidableEq V] [PartialOrder V] [LocallyFiniteOrder V] [TreeOrder V]
  [SegmentSystem V] [IntervalSegments V]

end NormingTest

namespace FiniteLaw
variable {Ω : Type*} [Fintype Ω]

end FiniteLaw

section ConeReconstruction
variable {V Ω : Type*} [DecidableEq V] [PartialOrder V] [LocallyFiniteOrder V] [TreeOrder V]
  [SegmentSystem V] [IntervalSegments V] [Fintype Ω]

end ConeReconstruction

end SegmentLenses

end

end OAI


