-- Prove2me | Definitions.Def_RepTheory_TestFunctionActionHom
-- name    : RepTheory_TestFunctionActionHom
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:29.330635+00:00
-- url     : https://prove2.me/theorems/abce06ef-f1a7-53e5-8bcf-b8476f24e990
-- title:
--   Test-function (Hecke) action on a smooth complex representation
-- statement:
--   Throughout, $G$ is a group with a topology and a measurable structure, $V$ a complex vector space, and $\pi : G \to \operatorname{End}_{\mathbb C}(V)$ a monoid homomorphism. [`ModuleAction.ofHom`](../def/RepTheory_TestFunctionActionHom.html#L55) turns such a $\pi$ into a `DistribMulAction` of $G$ on $V$, in which $g$ acts as the endomorphism $\pi(g)$; [`ModuleAction.ofHom_smul`](../def/RepTheory_TestFunctionActionHom.html#L58) records that $g \bullet v = \pi(g)v$ and [`ModuleAction.smulCommClass_ofHom`](../def/RepTheory_TestFunctionActionHom.html#L62) that this action commutes with the complex scalars, $\mathbb{C}$-linearity of each $\pi(g)$. Correspondingly, [`TestFunctionAction.stabilizer_ofHom_eq`](../def/RepTheory_TestFunctionActionHom.html#L84) identifies the stabiliser of $v$ for this action with `repStabilizer π v`, the subgroup $\{g : \pi(g)v = v\}$, so that the project's smoothness predicate `IsSmoothRep π` (openness of every such stabiliser) is equivalent to the statement that every $v \in V$ has open stabiliser for the action (`isSmoothRep_iff_forall_hasOpenStabilizer`, with the one-directional form `hasOpenStabilizer_of_isSmoothRep`).
--
--   The main construction, `heckeSmulHom`, takes a smooth $\pi$ and a measure $\mu$ on $G$ that is finite on compact sets, and produces a $\mathbb{C}$-linear map from [`SchwartzBruhatSpace.testSpace G`](../def/LanglandsTunnell_SchwartzBruhatSpace.html#L17) — the submodule of locally constant, compactly supported functions $G \to \mathbb{C}$ — to $\operatorname{End}_{\mathbb C}(V)$. A test function $\varphi$ is sent to the endomorphism $v \mapsto$ `heckeSmul μ φ v`, the finite-range integral of $g \mapsto \varphi(g)\,\pi(g)v$ against $\mu$: the integrand has finite range and open, hence measurable, fibres, and the integral is the finite sum $\sum_w \mu(\text{fibre over } w)\, w$ with measures read in $\mathbb{C}$ via $\mathbb{R}$. Additivity and $\mathbb{C}$-homogeneity in both $\varphi$ and $v$ make this bilinear. `heckeSmulHom_apply` states the defining formula.
--
--   Two groups of auxiliary statements are proved: for a Haar measure $\mu$ on $G$, an open subgroup has nonzero measure and a compact subgroup has finite measure; and a constant multiple of the indicator function of a subgroup $K$ is invariant under left and right translation by elements of $K$.
--
--   **Relation to Mathlib.** The action attached to $\pi$ is Mathlib's `DistribMulAction.compHom` under a local name. The smoothness predicate, the Schwartz–Bruhat test space and the finite-range integral used to define the test-function action are the project's own: the integral is a finite weighted sum over the fibres of a locally constant compactly supported integrand, so no topology or Bochner integration on $V$ is required.
--
--   **Where it is used.** This supplies the module structure of the Hecke algebra of locally constant compactly supported functions on a smooth complex representation, part of the representation-theoretic input for the Langlands–Tunnell theorem used to establish modularity of the residual representation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_RepTheory_TestFunctionActionHom.lean

import Definitions.Def_RepTheory_TestFunctionAction
import Definitions.Def_LanglandsTunnell_SchwartzBruhatSpace
import Definitions.Def_RepTheory_SmoothAdmissibleSchurCommutant
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.Algebra.GroupWithZero.Action.End
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Complex.Module

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory Set

namespace LevelMeasure

section Mass

variable {G : Type} [Group G] [TopologicalSpace G] [MeasurableSpace G]
variable (μ : Measure G) [μ.IsHaarMeasure]

theorem measure_ne_zero (K : Subgroup G) (hKo : IsOpen (K : Set G)) : μ (K : Set G) ≠ 0 :=
  hKo.measure_ne_zero μ ⟨1, K.one_mem⟩

theorem measure_ne_top (K : Subgroup G) (hKc : IsCompact (K : Set G)) : μ (K : Set G) ≠ ⊤ :=
  hKc.measure_lt_top.ne

end Mass

section Indicator

variable {G : Type} [Group G]

theorem indicator_mul_left (K : Subgroup G) (c : ℂ) {k : G} (hk : k ∈ K) (g : G) :
    (K : Set G).indicator (fun _ => c) (k * g) = (K : Set G).indicator (fun _ => c) g := by
  by_cases hg : g ∈ K
  · rw [indicator_of_mem (K.mul_mem hk hg), indicator_of_mem hg]
  · have : k * g ∉ K := fun h => hg (by simpa using K.mul_mem (K.inv_mem hk) h)
    rw [indicator_of_notMem this, indicator_of_notMem hg]

theorem indicator_mul_right (K : Subgroup G) (c : ℂ) {k : G} (hk : k ∈ K) (g : G) :
    (K : Set G).indicator (fun _ => c) (g * k) = (K : Set G).indicator (fun _ => c) g := by
  by_cases hg : g ∈ K
  · rw [indicator_of_mem (K.mul_mem hg hk), indicator_of_mem hg]
  · have : g * k ∉ K := fun h => hg (by simpa using K.mul_mem h (K.inv_mem hk))
    rw [indicator_of_notMem this, indicator_of_notMem hg]

end Indicator

end LevelMeasure

namespace ModuleAction

variable {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module ℂ V]

abbrev ofHom (π : G →* Module.End ℂ V) : DistribMulAction G V :=
  DistribMulAction.compHom V π

theorem ofHom_smul (π : G →* Module.End ℂ V) (g : G) (v : V) :
    letI := ofHom π
    g • v = π g v := rfl

theorem smulCommClass_ofHom (π : G →* Module.End ℂ V) :
    letI := ofHom π
    SMulCommClass G ℂ V := by
  letI := ofHom π
  exact ⟨fun g c v => ((π g).map_smul c v).symm ▸ rfl⟩

end ModuleAction

open MeasureTheory
open scoped Topology

namespace TestFunctionAction

section Smooth

open FLT.SmoothAdmissibleSchurCommutant

variable {G : Type} [Group G] [TopologicalSpace G] {V : Type} [AddCommGroup V] [Module ℂ V]
variable (π : G →* Module.End ℂ V)

omit [TopologicalSpace G] in

theorem stabilizer_ofHom_eq (v : V) :
    letI := ModuleAction.ofHom π
    MulAction.stabilizer G v = repStabilizer π v := by
  letI := ModuleAction.ofHom π
  ext g
  rfl

theorem isSmoothRep_iff_forall_hasOpenStabilizer :
    letI := ModuleAction.ofHom π
    IsSmoothRep π ↔ ∀ v : V, HasOpenStabilizer G v := by
  letI := ModuleAction.ofHom π
  refine forall_congr' fun v => ?_
  show IsOpen _ ↔ IsOpen _
  rw [stabilizer_ofHom_eq]

theorem hasOpenStabilizer_of_isSmoothRep (hsm : IsSmoothRep π) (v : V) :
    letI := ModuleAction.ofHom π
    HasOpenStabilizer G v :=
  (isSmoothRep_iff_forall_hasOpenStabilizer π).mp hsm v

end Smooth

section Bundle

open FLT.SmoothAdmissibleSchurCommutant

variable {G : Type} [Group G] [TopologicalSpace G] [ContinuousMul G] [MeasurableSpace G]
  [OpensMeasurableSpace G]
variable {V : Type} [AddCommGroup V] [Module ℂ V]

noncomputable def heckeSmulHom (π : G →* Module.End ℂ V) (hsm : IsSmoothRep π) (μ : Measure G)
    [IsFiniteMeasureOnCompacts μ] : SchwartzBruhatSpace.testSpace G →ₗ[ℂ] Module.End ℂ V :=
  letI := ModuleAction.ofHom π
  haveI := ModuleAction.smulCommClass_ofHom π
  have hsm' : ∀ v : V, HasOpenStabilizer G v := hasOpenStabilizer_of_isSmoothRep π hsm
  { toFun := fun φ =>
      { toFun := fun v => heckeSmul μ (φ : G → ℂ) v
        map_add' := fun v w => heckeSmul_add_right μ φ.2.1 φ.2.2 (hsm' v) (hsm' w)
        map_smul' := fun c v => heckeSmul_smul_right μ φ.2.1 φ.2.2 (hsm' v) c }
    map_add' := fun φ ψ => by
      ext v
      exact heckeSmul_add_left μ φ.2.1 φ.2.2 ψ.2.1 ψ.2.2 (hsm' v)
    map_smul' := fun c φ => by
      ext v
      exact heckeSmul_smul_left μ φ.2.1 φ.2.2 (hsm' v) c }

theorem heckeSmulHom_apply (π : G →* Module.End ℂ V) (hsm : IsSmoothRep π) (μ : Measure G)
    [IsFiniteMeasureOnCompacts μ] (φ : SchwartzBruhatSpace.testSpace G) (v : V) :
    heckeSmulHom π hsm μ φ v =
      (letI := ModuleAction.ofHom π; heckeSmul μ (φ : G → ℂ) v) :=
  rfl

end Bundle

end TestFunctionAction


