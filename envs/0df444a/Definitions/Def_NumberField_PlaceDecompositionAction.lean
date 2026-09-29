-- Prove2me | Definitions.Def_NumberField_PlaceDecompositionAction
-- name    : NumberField_PlaceDecompositionAction
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:29.330635+00:00
-- url     : https://prove2.me/theorems/8d3faba6-f6d6-5004-ab81-c130a17575c6
-- title:
--   Decomposition group acting on the completion at a finite place
-- statement:
--   Fix a field $E$, a number field $K$ with an $E$-algebra structure, and a height-one prime $w$ of $\mathcal{O}_K$, with its $w$-adic valuation $v_w$ on $K$ (valued in $\mathbb{Z}\cup\{\infty\}$ written multiplicatively as `WithZero (Multiplicative ℤ)`). The abbreviation `decomp E K w` is the decomposition subgroup of $K \simeq_E K$ attached to the valuation subring of $v_w$, i.e. the stabiliser of that subring under the pointwise action of $E$-algebra automorphisms of $K$. The general lemmas of the first section establish the rigidity needed to move this stabiliser condition to the completion: `apply_eq_of_isEquiv_comap` shows that if a $\mathbb{Z}$-valued valuation $v$ on a field $K$ admits a uniformiser and $v$ is equivalent to its pull-back along a ring automorphism $f$, then $v(f x)=v(x)$ for all $x$ (with `le_exp_neg_one_of_lt_one` as the arithmetic step on value groups), and `uniformContinuous_congr_of_forall_eq` shows that a valuation-preserving automorphism is uniformly continuous for the valuation uniformity. Specialising, `isEquiv_comap_of_mem`, `valuation_apply_of_mem` and `uniformContinuous_congr_of_mem` give that every $\sigma \in$ `decomp E K w` satisfies $v_w(\sigma x)=v_w(x)$ and is uniformly continuous on the valued copy `WithVal (w.valuation K)` of $K$.
--
--   The main construction `actRingEquiv` sends $\sigma \in$ `decomp E K w` to the ring automorphism of the $w$-adic completion `w.adicCompletion K` obtained by completing the induced map of valued fields, together with the inverse supplied by $\sigma^{-1}$; `actRingEquiv_coe` identifies its value on elements of $K$ with $\sigma$, `continuous_actRingEquiv` records continuity, and `actRingEquiv_one`, `actRingEquiv_mul` assemble it into the monoid homomorphism `actHom` from `decomp E K w` to the ring automorphisms of `w.adicCompletion K`. `valued_actRingEquiv` shows the action preserves the valuation on the completion, hence by `smul_mem_adicCompletionIntegers_iff` preserves `w.adicCompletionIntegers K`. The remaining declarations package this as scoped instances: multiplicative and distributive actions on `WithVal (w.valuation K)` with uniform continuity of each translate, a `MulSemiringAction` on `w.adicCompletion K` and on its valuation ring, and the resulting actions on the unit groups of both, so that $K_w^{\times}$ and $\mathcal{O}_w^{\times}$ become modules over the decomposition group.
--
--   **Relation to Mathlib.** Built on Mathlib's `ValuationSubring.decompositionSubgroup`, the valued-field congruence `WithVal.congr` and `UniformSpace.Completion.mapRingEquiv`; Mathlib supplies the adic completion `HeightOneSpectrum.adicCompletion` and its valuation ring but no action of the decomposition group on them, which is what is constructed here. The instances are scoped to the `NumberField.PlaceDecomp` namespace rather than made global on Mathlib's carriers.
--
--   **Where it is used.** This supplies the local Galois module at a finite place: the decomposition group at $w$ acting on $K_w$, $K_w^{\times}$, $\mathcal{O}_w$ and $\mathcal{O}_w^{\times}$, which is the basic input for the idèle-theoretic constructions of global class field theory used in the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_NumberField_PlaceDecompositionAction.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField
open scoped Pointwise

namespace NumberField.PlaceDecomp

section general
variable {K : Type*} [Field K] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]

theorem uniformContinuous_congr_of_forall_eq (v : Valuation K Γ₀) (f : K ≃+* K) (h : ∀ x, v (f x) = v x) :
    UniformContinuous (WithVal.congr v v f) := by
  apply uniformContinuous_addMonoidHom_of_continuous
  apply continuous_of_continuousAt_zero (WithVal.congr v v f).toAddMonoidHom
  rw [ContinuousAt, map_zero, (Valued.hasBasis_nhds_zero _ _).tendsto_iff (Valued.hasBasis_nhds_zero _ _)]
  intro γ _
  refine ⟨γ, trivial, fun x hx => ?_⟩
  simp only [Set.mem_setOf_eq] at hx ⊢
  have key : Valued.v ((WithVal.congr v v f).toAddMonoidHom x) = Valued.v x := by
    change Valued.v (WithVal.congr _ _ _ x) = _
    rw [WithVal.congr_apply, WithVal.valued_toVal, ← WithVal.apply_ofVal]
    exact h _
  rw [Valuation.restrict_lt_iff_lt_embedding] at hx ⊢
  rwa [key]

theorem le_exp_neg_one_of_lt_one {t : WithZero (Multiplicative ℤ)} (ht : t < 1) : t ≤ WithZero.exp (-1) := by
  rcases eq_or_ne t 0 with rfl | h0
  · exact zero_le'
  · rw [← WithZero.exp_log h0] at ht ⊢
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at ht
    rw [WithZero.exp_le_exp]
    omega

theorem apply_eq_of_isEquiv_comap (v : Valuation K (WithZero (Multiplicative ℤ))) (f : K ≃+* K)
    (hf : v.IsEquiv (v.comap (f : K →+* K))) (hπ : ∃ π : K, v π = WithZero.exp (-1)) (x : K) : v (f x) = v x := by

  have hle : ∀ a b : K, v a ≤ v b ↔ v (f a) ≤ v (f b) := fun a b => hf a b

  have step1 : ∀ (g : K ≃+* K), (∀ a b : K, v a ≤ v b ↔ v (g a) ≤ v (g b)) → ∀ π : K, v π = WithZero.exp (-1) →
      v (g π) = WithZero.exp (-1) := by
    intro g hg π hπ
    have hπ1 : v π < 1 := by rw [hπ, ← WithZero.exp_zero, WithZero.exp_lt_exp]; omega
    apply le_antisymm
    · apply le_exp_neg_one_of_lt_one
      have : ¬ v (g 1) ≤ v (g π) := fun h => (not_le.2 hπ1) (by simpa using (hg 1 π).2 h)
      simpa using not_le.1 this
    ·
      have hy : v (g (g.symm π)) = WithZero.exp (-1) := by rw [g.apply_symm_apply, hπ]
      have hy1 : v (g.symm π) < 1 := by
        have : ¬ v (g 1) ≤ v (g (g.symm π)) := by
          rw [map_one, map_one, hy, not_le, ← WithZero.exp_zero, WithZero.exp_lt_exp]; omega
        have : ¬ v 1 ≤ v (g.symm π) := fun h => this ((hg _ _).1 h)
        simpa using not_le.1 this
      have := (hg (g.symm π) π).1 ((le_exp_neg_one_of_lt_one hy1).trans hπ.ge)
      rwa [hy] at this
  obtain ⟨π, hvπ⟩ := hπ
  have hfπ : v (f π) = WithZero.exp (-1) := step1 f hle π hvπ

  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · set m : ℤ := WithZero.log (v x) with hm
    have hvx : v x = WithZero.exp m := (WithZero.exp_log ((map_ne_zero v).2 hx)).symm
    have hz : v (π ^ (-m)) = WithZero.exp m := by
      rw [map_zpow₀, hvπ, ← WithZero.exp_zsmul]
      congr 1
      simp
    have hfz : v (f (π ^ (-m))) = WithZero.exp m := by
      rw [map_zpow₀, map_zpow₀, hfπ, ← WithZero.exp_zsmul]
      congr 1
      simp
    have h1 : v (f x) ≤ v (f (π ^ (-m))) := (hle _ _).1 (by rw [hvx, hz])
    have h2 : v (f (π ^ (-m))) ≤ v (f x) := (hle _ _).1 (by rw [hvx, hz])
    rw [hvx]
    exact le_antisymm (h1.trans hfz.le) (hfz.ge.trans h2)

end general

variable (E K : Type*) [Field E] [Field K] [NumberField K] [Algebra E K] (w : HeightOneSpectrum (𝓞 K))

noncomputable abbrev decomp : Subgroup (K ≃ₐ[E] K) := ((w.valuation K).valuationSubring).decompositionSubgroup E

variable {E K w}

theorem isEquiv_comap_of_mem (σ : K ≃ₐ[E] K) (hσ : σ ∈ decomp E K w) :
    (w.valuation K).IsEquiv ((w.valuation K).comap (σ : K →+* K)) := by
  rw [Valuation.isEquiv_iff_val_le_one]
  intro x
  rw [MulAction.mem_stabilizer_iff] at hσ
  have : σ • x ∈ σ • (w.valuation K).valuationSubring ↔ x ∈ (w.valuation K).valuationSubring :=
    ValuationSubring.smul_mem_pointwise_smul_iff
  rw [hσ, Valuation.mem_valuationSubring_iff, Valuation.mem_valuationSubring_iff] at this
  rw [Valuation.comap_apply]
  exact this.symm

theorem valuation_apply_of_mem (σ : K ≃ₐ[E] K) (hσ : σ ∈ decomp E K w) (x : K) :
    w.valuation K (σ x) = w.valuation K x :=
  apply_eq_of_isEquiv_comap (w.valuation K) (σ : K ≃+* K) (isEquiv_comap_of_mem σ hσ) (w.valuation_exists_uniformizer K) x

theorem uniformContinuous_congr_of_mem (σ : K ≃ₐ[E] K) (hσ : σ ∈ decomp E K w) :
    UniformContinuous (WithVal.congr (w.valuation K) (w.valuation K) (σ : K ≃+* K)) :=
  uniformContinuous_congr_of_forall_eq (w.valuation K) (σ : K ≃+* K) (valuation_apply_of_mem σ hσ)

noncomputable def actRingEquiv (σ : decomp E K w) : w.adicCompletion K ≃+* w.adicCompletion K :=
  ((HeightOneSpectrum.adicCompletion.equiv K w).trans
    (UniformSpace.Completion.mapRingEquiv (WithVal.congr (w.valuation K) (w.valuation K) ((σ : K ≃ₐ[E] K) : K ≃+* K))
      (uniformContinuous_congr_of_mem (σ : K ≃ₐ[E] K) σ.2).continuous
      (by
        rw [WithVal.congr_symm]
        exact (uniformContinuous_congr_of_mem ((σ⁻¹ : decomp E K w) : K ≃ₐ[E] K) (σ⁻¹).2).continuous))).trans
    (HeightOneSpectrum.adicCompletion.equiv K w).symm

theorem actRingEquiv_apply (σ : decomp E K w) (x : w.adicCompletion K) :
    (actRingEquiv σ x).toCompletion
      = UniformSpace.Completion.map (WithVal.congr (w.valuation K) (w.valuation K) ((σ : K ≃ₐ[E] K) : K ≃+* K)) x.toCompletion :=
  rfl

theorem actRingEquiv_coe (σ : decomp E K w) (x : WithVal (w.valuation K)) :
    actRingEquiv σ (x : w.adicCompletion K)
      = ((WithVal.congr (w.valuation K) (w.valuation K) ((σ : K ≃ₐ[E] K) : K ≃+* K) x : WithVal (w.valuation K)) : w.adicCompletion K) := by
  apply HeightOneSpectrum.adicCompletion.ext
  rw [actRingEquiv_apply, HeightOneSpectrum.adicCompletion.toCompletion_ofCompletion, HeightOneSpectrum.adicCompletion.toCompletion_ofCompletion,
    UniformSpace.Completion.map_coe (uniformContinuous_congr_of_mem (σ : K ≃ₐ[E] K) σ.2)]

theorem continuous_actRingEquiv (σ : decomp E K w) : Continuous (actRingEquiv σ) := by
  have : (actRingEquiv σ : w.adicCompletion K → w.adicCompletion K)
      = HeightOneSpectrum.adicCompletion.ofCompletion ∘
        UniformSpace.Completion.map (WithVal.congr (w.valuation K) (w.valuation K) ((σ : K ≃ₐ[E] K) : K ≃+* K)) ∘
        HeightOneSpectrum.adicCompletion.toCompletion :=
    funext fun x => HeightOneSpectrum.adicCompletion.ext (h := actRingEquiv_apply σ x)
  rw [this]
  exact (HeightOneSpectrum.adicCompletion.continuous_ofCompletion K w).comp
    (UniformSpace.Completion.continuous_map.comp (HeightOneSpectrum.adicCompletion.continuous_toCompletion K w))

theorem actRingEquiv_one : actRingEquiv (1 : decomp E K w) = RingEquiv.refl _ := by
  apply RingEquiv.ext
  intro x
  apply HeightOneSpectrum.adicCompletion.ext
  rw [actRingEquiv_apply]
  change _ = id x.toCompletion
  refine congrFun (UniformSpace.Completion.ext UniformSpace.Completion.continuous_map continuous_id fun a => ?_) _
  rw [UniformSpace.Completion.map_coe (uniformContinuous_congr_of_mem ((1 : decomp E K w) : K ≃ₐ[E] K) (1 : decomp E K w).2)]
  rfl

theorem actRingEquiv_mul (σ τ : decomp E K w) : actRingEquiv (σ * τ) = (actRingEquiv τ).trans (actRingEquiv σ) := by
  apply RingEquiv.ext
  intro x
  apply HeightOneSpectrum.adicCompletion.ext
  change (actRingEquiv (σ * τ) x).toCompletion = (actRingEquiv σ (actRingEquiv τ x)).toCompletion
  rw [actRingEquiv_apply, actRingEquiv_apply, actRingEquiv_apply]
  refine congrFun (UniformSpace.Completion.ext UniformSpace.Completion.continuous_map
    (UniformSpace.Completion.continuous_map.comp UniformSpace.Completion.continuous_map) fun a => ?_) _
  change _ = UniformSpace.Completion.map _ (UniformSpace.Completion.map _ _)
  rw [UniformSpace.Completion.map_coe (uniformContinuous_congr_of_mem ((σ * τ : decomp E K w) : K ≃ₐ[E] K) (σ * τ).2),
    UniformSpace.Completion.map_coe (uniformContinuous_congr_of_mem (τ : K ≃ₐ[E] K) τ.2),
    UniformSpace.Completion.map_coe (uniformContinuous_congr_of_mem (σ : K ≃ₐ[E] K) σ.2)]
  rfl

noncomputable def actHom : decomp E K w →* (w.adicCompletion K ≃+* w.adicCompletion K) where
  toFun := actRingEquiv
  map_one' := actRingEquiv_one
  map_mul' σ τ := actRingEquiv_mul σ τ

theorem smul_withVal_def (σ : decomp E K w) (y : WithVal (w.valuation K)) :
    σ • y = WithVal.toVal (w.valuation K) ((σ : K ≃ₐ[E] K) y.ofVal) := rfl

noncomputable scoped instance instMulActionWithVal : MulAction (decomp E K w) (WithVal (w.valuation K)) where
  one_smul y := by rw [smul_withVal_def]; rfl
  mul_smul σ τ y := by rw [smul_withVal_def, smul_withVal_def, smul_withVal_def]; rfl

noncomputable scoped instance instDistribMulActionWithVal : DistribMulAction (decomp E K w) (WithVal (w.valuation K)) where
  smul_zero σ := by rw [smul_withVal_def]; show WithVal.toVal _ ((σ : K ≃ₐ[E] K) 0) = 0; rw [map_zero]; rfl
  smul_add σ x y := by
    rw [smul_withVal_def, smul_withVal_def, smul_withVal_def]
    show WithVal.toVal _ ((σ : K ≃ₐ[E] K) (x.ofVal + y.ofVal)) = _
    rw [map_add]; rfl

noncomputable scoped instance instUniformContinuousConstSMul :
    UniformContinuousConstSMul (decomp E K w) (WithVal (w.valuation K)) :=
  ⟨fun σ => uniformContinuous_congr_of_mem (σ : K ≃ₐ[E] K) σ.2⟩

noncomputable scoped instance instMulSemiringAction : MulSemiringAction (decomp E K w) (w.adicCompletion K) where
  smul σ x := actRingEquiv σ x
  one_smul x := by change actRingEquiv 1 x = x; rw [actRingEquiv_one]; rfl
  mul_smul σ τ x := by change actRingEquiv (σ * τ) x = actRingEquiv σ (actRingEquiv τ x); rw [actRingEquiv_mul]; rfl
  smul_zero σ := by change actRingEquiv σ 0 = 0; rw [map_zero]
  smul_add σ x y := by change actRingEquiv σ (x + y) = actRingEquiv σ x + actRingEquiv σ y; rw [map_add]
  smul_one σ := by change actRingEquiv σ 1 = 1; rw [map_one]
  smul_mul σ x y := by change actRingEquiv σ (x * y) = actRingEquiv σ x * actRingEquiv σ y; rw [map_mul]

theorem smul_def (σ : decomp E K w) (x : w.adicCompletion K) : σ • x = actRingEquiv σ x := rfl

noncomputable scoped instance instMulDistribMulActionUnits : MulDistribMulAction (decomp E K w) (w.adicCompletion K)ˣ :=
  Units.mulDistribMulActionRight

set_option synthInstance.maxHeartbeats 200000 in
theorem coe_smul_units (σ : decomp E K w) (u : (w.adicCompletion K)ˣ) : ((σ • u : (w.adicCompletion K)ˣ) : w.adicCompletion K) = σ • (u : w.adicCompletion K) := rfl

section integers

open WithZeroTopology in

theorem valued_actRingEquiv (σ : decomp E K w) (x : w.adicCompletion K) : Valued.v (actRingEquiv σ x) = Valued.v x := by
  have hclosed : IsClosed {y : w.adicCompletion K | Valued.v (actRingEquiv σ y) = Valued.v y} := by
    have : {y : w.adicCompletion K | Valued.v (actRingEquiv σ y) = Valued.v y}
        = {y | Valued.v.restrict (actRingEquiv σ y) = Valued.v.restrict y} :=
      Set.ext fun y => (Valuation.restrict_inj _).symm
    rw [this]
    exact isClosed_eq (Valued.continuous_valuation.comp (continuous_actRingEquiv σ)) Valued.continuous_valuation
  obtain ⟨x, rfl⟩ := HeightOneSpectrum.adicCompletion.ofCompletion_surjective K w x
  refine UniformSpace.Completion.induction_on
    (p := fun y => Valued.v (actRingEquiv σ (.ofCompletion y)) = Valued.v (HeightOneSpectrum.adicCompletion.ofCompletion y : w.adicCompletion K)) x
    (by simpa only [Set.preimage_ofPred_eq] using hclosed.preimage (HeightOneSpectrum.adicCompletion.continuous_ofCompletion K w)) fun a => ?_
  show Valued.v (actRingEquiv σ (a : w.adicCompletion K)) = Valued.v (a : w.adicCompletion K)
  rw [actRingEquiv_coe, HeightOneSpectrum.adicCompletion.valued_ofCompletion, HeightOneSpectrum.adicCompletion.valued_ofCompletion,
    Valued.valuedCompletion_apply, Valued.valuedCompletion_apply, ← WithVal.apply_ofVal, ← WithVal.apply_ofVal,
    WithVal.congr_apply]
  exact valuation_apply_of_mem (σ : K ≃ₐ[E] K) σ.2 a.ofVal

theorem valued_smul (σ : decomp E K w) (x : w.adicCompletion K) : Valued.v (σ • x) = Valued.v x :=
  valued_actRingEquiv σ x

theorem smul_mem_adicCompletionIntegers_iff (σ : decomp E K w) (x : w.adicCompletion K) :
    σ • x ∈ w.adicCompletionIntegers K ↔ x ∈ w.adicCompletionIntegers K := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, HeightOneSpectrum.mem_adicCompletionIntegers, valued_smul]

noncomputable scoped instance instSMulIntegers : SMul (decomp E K w) (w.adicCompletionIntegers K) :=
  ⟨fun σ x => ⟨σ • (x : w.adicCompletion K), (smul_mem_adicCompletionIntegers_iff σ _).2 x.2⟩⟩

theorem coe_smul_integers (σ : decomp E K w) (x : w.adicCompletionIntegers K) :
    ((σ • x : w.adicCompletionIntegers K) : w.adicCompletion K) = σ • (x : w.adicCompletion K) := rfl

set_option synthInstance.maxHeartbeats 200000 in

noncomputable scoped instance instMulSemiringActionIntegers : MulSemiringAction (decomp E K w) (w.adicCompletionIntegers K) :=
  { instSMulIntegers (E := E) (K := K) (w := w) with
    one_smul := fun x => Subtype.ext (by rw [coe_smul_integers, one_smul])
    mul_smul := fun σ τ x => Subtype.ext (by rw [coe_smul_integers, coe_smul_integers, coe_smul_integers, mul_smul])
    smul_zero := fun σ => Subtype.ext (by rw [coe_smul_integers]; exact smul_zero σ)
    smul_add := fun σ x y => Subtype.ext (by rw [coe_smul_integers]; exact smul_add σ (x : w.adicCompletion K) y)
    smul_one := fun σ => Subtype.ext (by rw [coe_smul_integers]; exact smul_one σ)
    smul_mul := fun σ x y => Subtype.ext (by rw [coe_smul_integers]; exact MulSemiringAction.smul_mul σ (x : w.adicCompletion K) y) }

set_option synthInstance.maxHeartbeats 200000 in

noncomputable scoped instance instMulDistribMulActionIntegerUnits : MulDistribMulAction (decomp E K w) (w.adicCompletionIntegers K)ˣ :=
  Units.mulDistribMulActionRight

noncomputable scoped instance instMulActionIntegers : MulAction (decomp E K w) (w.adicCompletionIntegers K) :=
  (instMulSemiringActionIntegers (E := E) (K := K) (w := w)).toMulAction

set_option synthInstance.maxHeartbeats 200000 in
noncomputable scoped instance instSMulUnits : SMul (decomp E K w) (w.adicCompletion K)ˣ :=
  (instMulDistribMulActionUnits (E := E) (K := K) (w := w)).toMulAction.toSMul

set_option synthInstance.maxHeartbeats 200000 in
noncomputable scoped instance instSMulIntegerUnits : SMul (decomp E K w) (w.adicCompletionIntegers K)ˣ :=
  (instMulDistribMulActionIntegerUnits (E := E) (K := K) (w := w)).toMulAction.toSMul

set_option synthInstance.maxHeartbeats 200000 in
noncomputable scoped instance instMulActionUnits : MulAction (decomp E K w) (w.adicCompletion K)ˣ :=
  (instMulDistribMulActionUnits (E := E) (K := K) (w := w)).toMulAction

set_option synthInstance.maxHeartbeats 200000 in
noncomputable scoped instance instMulActionIntegerUnits : MulAction (decomp E K w) (w.adicCompletionIntegers K)ˣ :=
  (instMulDistribMulActionIntegerUnits (E := E) (K := K) (w := w)).toMulAction

end integers

end NumberField.PlaceDecomp


