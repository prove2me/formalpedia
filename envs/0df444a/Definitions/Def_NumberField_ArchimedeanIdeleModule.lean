-- Prove2me | Definitions.Def_NumberField_ArchimedeanIdeleModule
-- name    : NumberField_ArchimedeanIdeleModule
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:29.330635+00:00
-- url     : https://prove2.me/theorems/69ffd5ff-9144-5538-9b1a-98dd4689bee0
-- title:
--   Archimedean idèle module over a number field extension
-- statement:
--   Fix fields $E \subseteq K$ with $K$ an $E$-algebra and an infinite place $w$ of $K$. In the namespace `NumberField.InfPlaceDecomp`, `decomp E K w` is the decomposition subgroup of $w$, namely the stabiliser of $w$ in $K \simeq_{\mathrm{alg}[E]} K$ for Mathlib's action of the $E$-automorphism group on infinite places. The first lemmas record that an automorphism fixing $w$ preserves the absolute value $w$ on the nose (`apply_of_mem`) and is therefore uniformly continuous for the $w$-metric on `WithAbs w.1` (with the general criterion `uniformContinuous_congr_of_forall_eq`: any ring isomorphism preserving an absolute value is an isometry, hence uniformly continuous). Consequently each $\sigma \in D_w$ induces a ring automorphism `actRingEquiv σ` of the completion $K_w$ (`InfinitePlace.Completion`), obtained by functoriality of uniform-space completion; it is continuous, extends $\sigma$ on the image of $K$ (`actRingEquiv_coe`), and is multiplicative and unital in $\sigma$, so assembles into a monoid homomorphism `actHom` $: D_w \to (K_w \simeq_{+*} K_w)$. Scoped instances then register the $D_w$-action on `WithAbs w.1` (given by applying $\sigma$ to the underlying element of $K$) as a distributive, uniformly continuous action, the resulting `MulSemiringAction` of $D_w$ on $K_w$ with `smul_def : σ • x = actRingEquiv σ x`, the induced `MulDistribMulAction` on $K_w^\times$, and finally `localUnits E K w`, the group $K_w^\times$ viewed as an object of `Rep ℤ (decomp E K w)`.
--
--   In the namespace `NumberField.ArchIdele`, with $E, K$ number fields, `above E K v` is a choice, for each infinite place $v$ of $E$, of an infinite place of $K$ restricting to $v$ along $E \to K$ (surjectivity of `comap`, recorded by `comap_above`). The fibre at $v$ is the coinduced representation of `localUnits E K (above E K v)` along the inclusion of $D_{w(v)}$ into $K \simeq_{\mathrm{alg}[E]} K$, and `obj E K` is the product over all infinite places $v$ of $E$ of these fibres, formed with the explicit $\Pi$-construction on `Rep ℤ`: the archimedean idèle module as an integral representation of the $E$-automorphism group of $K$.
--
--   **Relation to Mathlib.** Built on Mathlib's `InfinitePlace`, `WithAbs`, `InfinitePlace.Completion`, `Rep.ofMulDistribMulAction` and `Rep.coind`; the actions of the decomposition group on `WithAbs w.1`, on the completion and on its units are registered as instances scoped to `NumberField.InfPlaceDecomp`, and the archimedean idèle module as a representation is the project's own object.
--
--   **Where it is used.** These modules supply the archimedean half of the $S$-idèle module used in the cohomological treatment of class field theory: coinduction from the decomposition group realises $\prod_{w \mid v} K_w^\times$ factorwise, so that Shapiro's lemma reduces the Tate cohomology of the archimedean idèles to the local groups $\hat H^i(D_w, K_w^\times)$, an input to the first-inequality argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_NumberField_ArchimedeanIdeleModule.lean

import Mathlib
import Definitions.Def_GroupCohomology_RepPi

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField

namespace NumberField.InfPlaceDecomp

section general
variable {K : Type*} [Field K]

theorem uniformContinuous_congr_of_forall_eq (v : AbsoluteValue K ℝ) (f : K ≃+* K) (h : ∀ x, v (f x) = v x) :
    UniformContinuous (WithAbs.congr v v f) :=
  (AddMonoidHomClass.isometry_of_norm (WithAbs.congr v v f) fun x => by
    rw [WithAbs.norm_eq_apply_ofAbs, WithAbs.norm_eq_apply_ofAbs, WithAbs.congr_apply]
    exact h _).uniformContinuous

end general

variable (E K : Type*) [Field E] [Field K] [Algebra E K] (w : InfinitePlace K)

abbrev decomp : Subgroup (K ≃ₐ[E] K) := MulAction.stabilizer (K ≃ₐ[E] K) w

variable {E K w}

theorem apply_of_mem (σ : K ≃ₐ[E] K) (hσ : σ ∈ decomp E K w) (x : K) : w (σ x) = w x := by
  rw [MulAction.mem_stabilizer_iff] at hσ
  conv_lhs => rw [← hσ]
  rw [InfinitePlace.smul_apply, AlgEquiv.symm_apply_apply]

theorem uniformContinuous_congr_of_mem (σ : K ≃ₐ[E] K) (hσ : σ ∈ decomp E K w) :
    UniformContinuous (WithAbs.congr w.1 w.1 (σ : K ≃+* K)) :=
  uniformContinuous_congr_of_forall_eq w.1 (σ : K ≃+* K) (apply_of_mem σ hσ)

noncomputable def actRingEquiv (σ : decomp E K w) : w.Completion ≃+* w.Completion :=
  ((InfinitePlace.Completion.equiv w).trans
    (UniformSpace.Completion.mapRingEquiv (WithAbs.congr w.1 w.1 ((σ : K ≃ₐ[E] K) : K ≃+* K))
      (uniformContinuous_congr_of_mem (σ : K ≃ₐ[E] K) σ.2).continuous
      (by
        rw [WithAbs.congr_symm]
        exact (uniformContinuous_congr_of_mem ((σ⁻¹ : decomp E K w) : K ≃ₐ[E] K) (σ⁻¹).2).continuous))).trans
    (InfinitePlace.Completion.equiv w).symm

theorem actRingEquiv_apply (σ : decomp E K w) (x : w.Completion) :
    (actRingEquiv σ x).toCompletion =
      UniformSpace.Completion.map (WithAbs.congr w.1 w.1 ((σ : K ≃ₐ[E] K) : K ≃+* K)) x.toCompletion :=
  rfl

theorem actRingEquiv_coe (σ : decomp E K w) (x : WithAbs w.1) :
    actRingEquiv σ (x : w.Completion) = ((WithAbs.congr w.1 w.1 ((σ : K ≃ₐ[E] K) : K ≃+* K) x : WithAbs w.1) : w.Completion) := by
  apply InfinitePlace.Completion.ext
  rw [actRingEquiv_apply, InfinitePlace.Completion.coe_toCompletion,
    InfinitePlace.Completion.coe_toCompletion,
    UniformSpace.Completion.map_coe (uniformContinuous_congr_of_mem (σ : K ≃ₐ[E] K) σ.2)]

theorem continuous_actRingEquiv (σ : decomp E K w) : Continuous (actRingEquiv σ) := by
  have : (actRingEquiv σ : w.Completion → w.Completion) =
      InfinitePlace.Completion.ofCompletion ∘
        UniformSpace.Completion.map (WithAbs.congr w.1 w.1 ((σ : K ≃ₐ[E] K) : K ≃+* K)) ∘
        InfinitePlace.Completion.toCompletion :=
    funext fun x => InfinitePlace.Completion.ext (h := actRingEquiv_apply σ x)
  rw [this]
  exact (InfinitePlace.Completion.continuous_ofCompletion w).comp
    (UniformSpace.Completion.continuous_map.comp (InfinitePlace.Completion.continuous_toCompletion w))

theorem actRingEquiv_one : actRingEquiv (1 : decomp E K w) = RingEquiv.refl _ := by
  apply RingEquiv.ext
  intro x
  apply InfinitePlace.Completion.ext
  rw [actRingEquiv_apply]
  change _ = id x.toCompletion
  refine congrFun (UniformSpace.Completion.ext UniformSpace.Completion.continuous_map continuous_id
    fun a => ?_) _
  rw [UniformSpace.Completion.map_coe
    (uniformContinuous_congr_of_mem ((1 : decomp E K w) : K ≃ₐ[E] K) (1 : decomp E K w).2)]
  rfl

theorem actRingEquiv_mul (σ τ : decomp E K w) : actRingEquiv (σ * τ) = (actRingEquiv τ).trans (actRingEquiv σ) := by
  apply RingEquiv.ext
  intro x
  apply InfinitePlace.Completion.ext
  change (actRingEquiv (σ * τ) x).toCompletion = (actRingEquiv σ (actRingEquiv τ x)).toCompletion
  rw [actRingEquiv_apply, actRingEquiv_apply, actRingEquiv_apply]
  refine congrFun (UniformSpace.Completion.ext UniformSpace.Completion.continuous_map
    (UniformSpace.Completion.continuous_map.comp UniformSpace.Completion.continuous_map) fun a => ?_) _
  change _ = UniformSpace.Completion.map _ (UniformSpace.Completion.map _ _)
  rw [UniformSpace.Completion.map_coe (uniformContinuous_congr_of_mem ((σ * τ : decomp E K w) : K ≃ₐ[E] K) (σ * τ).2),
    UniformSpace.Completion.map_coe (uniformContinuous_congr_of_mem (τ : K ≃ₐ[E] K) τ.2),
    UniformSpace.Completion.map_coe (uniformContinuous_congr_of_mem (σ : K ≃ₐ[E] K) σ.2)]
  rfl

noncomputable def actHom : decomp E K w →* (w.Completion ≃+* w.Completion) where
  toFun := actRingEquiv
  map_one' := actRingEquiv_one
  map_mul' σ τ := actRingEquiv_mul σ τ

theorem smul_withAbs_def (σ : decomp E K w) (y : WithAbs w.1) : σ • y = WithAbs.toAbs w.1 ((σ : K ≃ₐ[E] K) y.ofAbs) := rfl

noncomputable scoped instance instMulActionWithAbs : MulAction (decomp E K w) (WithAbs w.1) where
  one_smul y := by rw [smul_withAbs_def]; rfl
  mul_smul σ τ y := by rw [smul_withAbs_def, smul_withAbs_def, smul_withAbs_def]; rfl

noncomputable scoped instance instDistribMulActionWithAbs : DistribMulAction (decomp E K w) (WithAbs w.1) where
  smul_zero σ := by rw [smul_withAbs_def]; show WithAbs.toAbs _ ((σ : K ≃ₐ[E] K) 0) = 0; rw [map_zero]; rfl
  smul_add σ x y := by
    rw [smul_withAbs_def, smul_withAbs_def, smul_withAbs_def]
    show WithAbs.toAbs _ ((σ : K ≃ₐ[E] K) (x.ofAbs + y.ofAbs)) = _
    rw [map_add]; rfl

noncomputable scoped instance instUniformContinuousConstSMul : UniformContinuousConstSMul (decomp E K w) (WithAbs w.1) :=
  ⟨fun σ => uniformContinuous_congr_of_mem (σ : K ≃ₐ[E] K) σ.2⟩

noncomputable scoped instance instMulSemiringAction : MulSemiringAction (decomp E K w) w.Completion where
  smul σ x := actRingEquiv σ x
  one_smul x := by change actRingEquiv 1 x = x; rw [actRingEquiv_one]; rfl
  mul_smul σ τ x := by
    change actRingEquiv (σ * τ) x = actRingEquiv σ (actRingEquiv τ x); rw [actRingEquiv_mul]; rfl
  smul_zero σ := by change actRingEquiv σ 0 = 0; rw [map_zero]
  smul_add σ x y := by change actRingEquiv σ (x + y) = actRingEquiv σ x + actRingEquiv σ y; rw [map_add]
  smul_one σ := by change actRingEquiv σ 1 = 1; rw [map_one]
  smul_mul σ x y := by change actRingEquiv σ (x * y) = actRingEquiv σ x * actRingEquiv σ y; rw [map_mul]

theorem smul_def (σ : decomp E K w) (x : w.Completion) : σ • x = actRingEquiv σ x := rfl

scoped instance instContinuousConstSMul : ContinuousConstSMul (decomp E K w) w.Completion :=
  ⟨fun σ => continuous_actRingEquiv σ⟩

noncomputable scoped instance instMulDistribMulActionUnits : MulDistribMulAction (decomp E K w) (w.Completion)ˣ :=
  Units.mulDistribMulActionRight

noncomputable scoped instance instMulActionUnits : MulAction (decomp E K w) (w.Completion)ˣ :=
  (instMulDistribMulActionUnits (E := E) (K := K) (w := w)).toMulAction

noncomputable scoped instance instSMulUnits : SMul (decomp E K w) (w.Completion)ˣ :=
  (instMulActionUnits (E := E) (K := K) (w := w)).toSMul

theorem coe_smul_units (σ : decomp E K w) (u : (w.Completion)ˣ) : ((σ • u : (w.Completion)ˣ) : w.Completion) = σ • (u : w.Completion) := rfl

variable (E K w) in

noncomputable abbrev localUnits : Rep ℤ (decomp E K w) := Rep.ofMulDistribMulAction (decomp E K w) (w.Completion)ˣ

end NumberField.InfPlaceDecomp

namespace NumberField.ArchIdele

open scoped NumberField.InfPlaceDecomp

variable (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K]

theorem exists_above (v : InfinitePlace E) : ∃ w : InfinitePlace K, w.comap (algebraMap E K) = v :=
  InfinitePlace.comap_surjective v

noncomputable def above (v : InfinitePlace E) : InfinitePlace K := (exists_above E K v).choose

theorem comap_above (v : InfinitePlace E) : (above E K v).comap (algebraMap E K) = v := (exists_above E K v).choose_spec

noncomputable abbrev fibre (v : InfinitePlace E) : Rep ℤ (K ≃ₐ[E] K) :=
  Rep.coind (InfPlaceDecomp.decomp E K (above E K v)).subtype (InfPlaceDecomp.localUnits E K (above E K v))

noncomputable abbrev obj : Rep ℤ (K ≃ₐ[E] K) := GroupCohomology.RepPi.obj (fibre E K)

end NumberField.ArchIdele


