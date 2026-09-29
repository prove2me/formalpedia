-- Prove2me | Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
-- name    : AutomorphicForm_SmoothAutomorphicFnAt
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.014713+00:00
-- url     : https://prove2.me/theorems/96d84ae4-d182-5fca-a157-ae2ed6e1c2d5
-- title:
--   Finite-adelic smoothness clause for adelic automorphic functions
-- statement:
--   Let $F$ be a number field, $\mathcal{O}_F$ its ring of integers, and $G=\mathrm{GL}_2(\mathbb{A}_F)$ the adelic group `AdelicGL2 (𝓞 F) F`. The module first isolates the subgroup `finiteAdelicGL2Subgroup F`, defined as the kernel of the archimedean projection $\mathrm{GL}_2(\mathbb{A}_F)\to\mathrm{GL}_2(\mathbb{A}_{F,\infty})$ induced by the ring map $\mathbb{A}_F\to\mathbb{A}_{F,\infty}$ (the project's `glArch`): membership is by definition the equation $\mathrm{glArch}(g)=1$, and since $\mathrm{glArch}$ is continuous this subgroup is closed, being the preimage of $\{1\}$. Next, `IsKfSmooth F φ`, for $\varphi:G\to\mathbb{C}$, is defined as the assertion that $\varphi$, viewed as an element of the type synonym `RightTranslationFn` carrying the right-translation action $(g\cdot f)(x)=f(xg)$, is a smooth vector for the restricted action of `finiteAdelicGL2Subgroup F`; unfolding the project's `IsSmoothVector`, this says exactly that the stabiliser $\{k:\mathrm{glArch}(k)=1,\ \varphi(\,\cdot\,k)=\varphi\}$ is open in that subgroup — i.e. $\varphi$ is right-invariant under an open subgroup of the finite-adelic part. No archimedean regularity is asserted.
--
--   The two predicates defined here conjoin this clause to the module's parents: `IsSmoothAutomorphicFnAt F pins ξ φ` is `IsAutomorphicFnAt F pins ξ φ` together with `IsKfSmooth F φ`, and `IsSmoothCuspAutomorphicFnAt F pins ξ φ` is `IsCuspAutomorphicFnAt F pins ξ φ` together with `IsKfSmooth F φ`; here `pins : CarrierPins F` bundles the measurable structures and measures on $G$ and on $\mathbb{A}_F$, a domain $D$, a subgroup $Z\le(\mathbb{A}_F)^\times$ and level and Hecke data, and $\xi:Z\to\mathbb{C}^\times$ is a character.
--
--   The accompanying lemmas are elementary: constant functions are smooth vectors for right translation on any topological group, hence $K_f$-smooth; every vector is smooth for a discrete group, in particular for the trivial subgroup; the zero function satisfies both predicates; the constant function $1$ satisfies the smooth automorphic predicate for the trivial character when $\mu(D)<\infty$, and fails the smooth cuspidal predicate whenever $\nu$ is a probability measure, since then its constant term is $1$.
--
--   **Relation to Mathlib.** Mathlib has no notion of automorphic form on an adelic group; the smooth-vector vocabulary (`IsSmoothVector`, defined as openness of `MulAction.stabilizer`, and the type synonym `RightTranslationFn` with its right-translation `MulAction`) is the project's own, as are the adelic projections used to cut out the finite-adelic subgroup.
--
--   **Where it is used.** These predicates provide the finite-level (right invariance under an open compact subgroup of the finite adeles) clause of the adelic definition of automorphic and cuspidal automorphic functions on $\mathrm{GL}_2(\mathbb{A}_F)$, the setting in which modular forms and their Hecke eigensystems are handled on the automorphic side of the modularity statements used in the proof.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AutomorphicForm_SmoothAutomorphicFnAt.lean

import Definitions.Def_AutomorphicForm_AutomorphicFnAt
import Definitions.Def_RepTheory_SmoothVectors
import Definitions.Def_NumberField_AdelicLevel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open IsDedekindDomain NumberField MeasureTheory Matrix
open FLT.SmoothVectors
open AutomorphicForm

noncomputable section

namespace AutomorphicForm

variable (F : Type) [Field F] [NumberField F]

def finiteAdelicGL2Subgroup : Subgroup (AdelicGL2 (𝓞 F) F) :=
  MonoidHom.ker (NumberField.AdelicLevel.glArch (𝓞 F) F)

theorem mem_finiteAdelicGL2Subgroup_iff (g : AdelicGL2 (𝓞 F) F) :
    g ∈ finiteAdelicGL2Subgroup F ↔ NumberField.AdelicLevel.glArch (𝓞 F) F g = 1 :=
  Iff.rfl

theorem isClosed_finiteAdelicGL2Subgroup :
    IsClosed (finiteAdelicGL2Subgroup F : Set (AdelicGL2 (𝓞 F) F)) := by
  have : finiteAdelicGL2Subgroup F
      = (NumberField.AdelicLevel.glArch (𝓞 F) F) ⁻¹' {1} := by
    ext g; exact Iff.rfl
  rw [this]
  exact (isClosed_singleton).preimage (NumberField.AdelicLevel.continuous_glArch (𝓞 F) F)

def IsKfSmooth (φ : AdelicGL2 (𝓞 F) F → ℂ) : Prop :=
  IsSmoothVector (finiteAdelicGL2Subgroup F)
    (RightTranslationFn.mk φ : RightTranslationFn (AdelicGL2 (𝓞 F) F) ℂ)

theorem isKfSmooth_iff (φ : AdelicGL2 (𝓞 F) F → ℂ) :
    IsKfSmooth F φ ↔
      IsSmoothVector (finiteAdelicGL2Subgroup F) (RightTranslationFn.mk φ) :=
  Iff.rfl

theorem isSmoothVector_rightTranslationFn_const {G : Type*} [Group G] [TopologicalSpace G]
    {M : Type*} (c : M) :
    IsSmoothVector G (RightTranslationFn.mk (fun (_ : G) => c)) := by
  rw [isSmoothVector_iff_isOpen_stabilizer]
  convert isOpen_univ using 2
  rw [Set.eq_univ_iff_forall]
  intro g
  exact MulAction.mem_stabilizer_iff.mpr (RightTranslationFn.ext fun _ => rfl)

theorem isKfSmooth_const (c : ℂ) : IsKfSmooth F (fun _ => c) :=
  (isSmoothVector_rightTranslationFn_const c).restrict_subgroup (finiteAdelicGL2Subgroup F)

theorem isKfSmooth_zero : IsKfSmooth F (fun _ => (0 : ℂ)) := isKfSmooth_const F 0

theorem isSmoothVector_of_discreteTopology {G : Type*} [Group G] [TopologicalSpace G]
    [DiscreteTopology G] {M : Type*} [MulAction G M] (v : M) : IsSmoothVector G v :=
  isOpen_discrete _

theorem isSmoothVector_bot_rightTranslationFn {G : Type*} [Group G] [TopologicalSpace G]
    {M : Type*} (φ : G → M) :
    IsSmoothVector (⊥ : Subgroup G) (RightTranslationFn.mk φ) :=
  isSmoothVector_of_discreteTopology _

def IsSmoothAutomorphicFnAt (pins : CarrierPins F) (ξ : pins.Z →* ℂˣ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) : Prop :=
  IsAutomorphicFnAt F pins ξ φ ∧ IsKfSmooth F φ

def IsSmoothCuspAutomorphicFnAt (pins : CarrierPins F) (ξ : pins.Z →* ℂˣ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) : Prop :=
  IsCuspAutomorphicFnAt F pins ξ φ ∧ IsKfSmooth F φ

theorem isSmoothAutomorphicFnAt_zero (pins : CarrierPins F) (ξ : pins.Z →* ℂˣ) :
    IsSmoothAutomorphicFnAt F pins ξ (fun _ => (0 : ℂ)) :=
  ⟨isAutomorphicFnAt_zero F pins ξ, isKfSmooth_zero F⟩

theorem isSmoothCuspAutomorphicFnAt_zero (pins : CarrierPins F) (ξ : pins.Z →* ℂˣ) :
    IsSmoothCuspAutomorphicFnAt F pins ξ (fun _ => (0 : ℂ)) :=
  ⟨isCuspAutomorphicFnAt_zero F pins ξ, isKfSmooth_zero F⟩

theorem isSmoothAutomorphicFnAt_one_trivial (pins : CarrierPins F)
    (hDfin : @pins.μ pins.D < ⊤) :
    IsSmoothAutomorphicFnAt F pins (1 : pins.Z →* ℂˣ) (fun _ => (1 : ℂ)) :=
  ⟨isAutomorphicFnAt_one_trivial F pins hDfin, isKfSmooth_const F 1⟩

theorem not_isSmoothCuspAutomorphicFnAt_one (pins : CarrierPins F) (ξ : pins.Z →* ℂˣ)
    [@IsProbabilityMeasure _ pins.nS pins.ν] :
    ¬ IsSmoothCuspAutomorphicFnAt F pins ξ (fun _ => (1 : ℂ)) :=
  fun h => not_isCuspAutomorphicFnAt_one F pins ξ h.1

end AutomorphicForm

end


