-- Prove2me | Definitions.Def_NumberField_PlaceTransport
-- name    : NumberField_PlaceTransport
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:29.330635+00:00
-- url     : https://prove2.me/theorems/a637c14a-1595-5d6e-a271-a0c2d5776448
-- title:
--   Galois action on finite places; transport of adic completions
-- statement:
--   Let $E \subseteq K$ be fields with $K$ a number field, and write $w$ for a point of `HeightOneSpectrum (𝓞 K)`, i.e. a nonzero prime $\mathfrak p_w$ of the ring of integers. The scoped instance `instMulActionHeightOneSpectrum` makes $K \simeq_{\mathrm{alg}[E]} K$ act on these primes by $\sigma \cdot w :=$ the comap of $\mathfrak p_w$ along the ring automorphism of $\mathcal O_K$ induced by $\sigma^{-1}$; equivalently $x \in \mathfrak p_{\sigma \cdot w} \iff \sigma^{-1} x \in \mathfrak p_w$, and $\mathfrak p_{\sigma\cdot w}$ is the image $\sigma(\mathfrak p_w)$. The unfolding lemmas record these descriptions, the membership criteria $\sigma x \in \mathfrak p_{\sigma\cdot w}^n \iff x \in \mathfrak p_w^n$, and $\sigma^{-1}\cdot w' = w$ from $\sigma\cdot w = w'$. From this follow the exact valuation compatibilities $v_{\sigma\cdot w}(\sigma r) = v_w(r)$ for $r \in \mathcal O_K$ (`intValuation`) and $v_{\sigma\cdot w}(\sigma x) = v_w(x)$ for $x \in K$.
--
--   A general preliminary shows that a ring isomorphism $f : R \simeq S$ of fields with $v'(f x) = v(x)$, $v$ surjective onto its value monoid, induces a uniformly continuous map of the associated valued fields. Applied to $\sigma$ with data $h : \sigma \cdot w = w'$, completing gives `transport`, a ring isomorphism $K_w \simeq K_{w'}$ of adic completions, characterised on $K$ by $\iota_w x \mapsto \iota_{w'}(\sigma x)$; it is continuous. Using that the closed balls $\{v(y) \le c\}$, $c \neq 0$, are clopen in $K_w$, `valued_transport` proves that the canonical valuations are preserved, whence `transport` preserves the valuation rings and yields ring and group isomorphisms $\mathcal O_w \simeq \mathcal O_{w'}$, $K_w^\times \simeq K_{w'}^\times$ and $\mathcal O_w^\times \simeq \mathcal O_{w'}^\times$. The target is given by a hypothesis $h : \sigma \cdot w = w'$ rather than fixed as $\sigma \cdot w$, so that composites and comparisons are stated without casts.
--
--   **Relation to Mathlib.** Built on Mathlib's `HeightOneSpectrum.comap`, `WithVal.congr` and `UniformSpace.Completion.mapRingEquiv`; the action of $K \simeq_{\mathrm{alg}[E]} K$ on `HeightOneSpectrum (𝓞 K)` is introduced here as a scoped instance rather than a global one on Mathlib's carrier.
--
--   **Where it is used.** These data provide the local ingredient for the Galois action on place-indexed finite (and $S$-)idèle modules of a number field, where an automorphism permutes the finite places and must simultaneously be transported to isomorphisms of the corresponding completions, their valuation rings and unit groups.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_NumberField_PlaceTransport.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField

namespace NumberField.PlaceTransport

section general
variable {R S : Type*} [Field R] [Field S] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]

theorem uniformContinuous_congr_of_forall_eq (v : Valuation R Γ₀) (v' : Valuation S Γ₀) (hv : Function.Surjective v)
    (f : R ≃+* S) (h : ∀ x, v' (f x) = v x) : UniformContinuous (WithVal.congr v v' f) := by
  apply uniformContinuous_addMonoidHom_of_continuous
  apply continuous_of_continuousAt_zero (WithVal.congr v v' f).toAddMonoidHom
  rw [ContinuousAt, map_zero]
  intro s hs
  rw [Filter.mem_map]
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds_zero.1 hs
  obtain ⟨x₀, hx₀⟩ := hv (MonoidWithZeroHom.ValueGroup₀.embedding γ.1)
  have hx₀' : Valued.v.restrict (WithVal.toVal v x₀) ≠ 0 := fun h0 => by
    have h1 := (Valuation.restrict_eq_zero_iff Valued.v).1 h0
    rw [WithVal.valued_toVal, hx₀] at h1
    exact γ.ne_zero (MonoidWithZeroHom.ValueGroup₀.embedding_strictMono.injective (h1.trans (map_zero _).symm))
  refine Valued.mem_nhds_zero.2 ⟨Units.mk0 _ hx₀', fun x hx => hγ ?_⟩
  simp only [Set.mem_setOf_eq, Units.val_mk0, Valuation.restrict_lt_iff, WithVal.valued_toVal, hx₀] at hx
  show Valued.v.restrict (WithVal.congr v v' f x) < γ.1
  rw [Valuation.restrict_lt_iff_lt_embedding, WithVal.congr_apply, WithVal.valued_toVal, h, WithVal.apply_ofVal]
  exact hx

end general

variable (E K : Type*) [Field E] [Field K] [Algebra E K]

noncomputable scoped instance instMulActionHeightOneSpectrum : MulAction (K ≃ₐ[E] K) (HeightOneSpectrum (𝓞 K)) where
  smul σ w := HeightOneSpectrum.comap (MulSemiringAction.toRingEquiv (K ≃ₐ[E] K) (𝓞 K) σ⁻¹ : 𝓞 K →+* 𝓞 K)
    (MulSemiringAction.toRingEquiv (K ≃ₐ[E] K) (𝓞 K) σ⁻¹).surjective w
  one_smul w := HeightOneSpectrum.ext (Ideal.ext fun x => by
    show (MulSemiringAction.toRingEquiv (K ≃ₐ[E] K) (𝓞 K) 1⁻¹) x ∈ w.asIdeal ↔ x ∈ w.asIdeal
    rw [MulSemiringAction.toRingEquiv_apply, inv_one, one_smul])
  mul_smul σ τ w := HeightOneSpectrum.ext (Ideal.ext fun x => by
    show (MulSemiringAction.toRingEquiv (K ≃ₐ[E] K) (𝓞 K) (σ * τ)⁻¹) x ∈ w.asIdeal ↔
      (MulSemiringAction.toRingEquiv (K ≃ₐ[E] K) (𝓞 K) τ⁻¹) ((MulSemiringAction.toRingEquiv (K ≃ₐ[E] K) (𝓞 K) σ⁻¹) x) ∈ w.asIdeal
    rw [MulSemiringAction.toRingEquiv_apply, MulSemiringAction.toRingEquiv_apply, MulSemiringAction.toRingEquiv_apply,
      mul_inv_rev, mul_smul])

variable {E K}

theorem smul_asIdeal (σ : K ≃ₐ[E] K) (w : HeightOneSpectrum (𝓞 K)) :
    (σ • w).asIdeal = w.asIdeal.comap (MulSemiringAction.toRingEquiv (K ≃ₐ[E] K) (𝓞 K) σ⁻¹ : 𝓞 K →+* 𝓞 K) := rfl

theorem mem_smul_asIdeal_iff (σ : K ≃ₐ[E] K) (w : HeightOneSpectrum (𝓞 K)) (x : 𝓞 K) :
    x ∈ (σ • w).asIdeal ↔ σ⁻¹ • x ∈ w.asIdeal := Iff.rfl

theorem smul_mem_smul_asIdeal_iff (σ : K ≃ₐ[E] K) (w : HeightOneSpectrum (𝓞 K)) (x : 𝓞 K) :
    σ • x ∈ (σ • w).asIdeal ↔ x ∈ w.asIdeal := by
  rw [mem_smul_asIdeal_iff, inv_smul_smul]

theorem smul_asIdeal_eq_map (σ : K ≃ₐ[E] K) (w : HeightOneSpectrum (𝓞 K)) :
    (σ • w).asIdeal = Ideal.map ((MulSemiringAction.toRingEquiv (K ≃ₐ[E] K) (𝓞 K) σ : 𝓞 K ≃+* 𝓞 K) : 𝓞 K →+* 𝓞 K) w.asIdeal := by
  rw [Ideal.map_comap_of_equiv]
  ext x
  rw [mem_smul_asIdeal_iff, Ideal.mem_comap, MulSemiringAction.toRingEquiv_symm_apply]

theorem smul_mem_smul_asIdeal_pow_iff (σ : K ≃ₐ[E] K) (w : HeightOneSpectrum (𝓞 K)) (x : 𝓞 K) (n : ℕ) :
    σ • x ∈ (σ • w).asIdeal ^ n ↔ x ∈ w.asIdeal ^ n := by
  rw [smul_asIdeal_eq_map, ← Ideal.map_pow, Ideal.map_comap_of_equiv, Ideal.mem_comap, MulSemiringAction.toRingEquiv_symm_apply,
    inv_smul_smul]

theorem inv_smul_eq_of_smul_eq {σ : K ≃ₐ[E] K} {w w' : HeightOneSpectrum (𝓞 K)} (h : σ • w = w') : σ⁻¹ • w' = w := by
  rw [← h, inv_smul_smul]

variable [NumberField K]

theorem intValuation_smul_apply (σ : K ≃ₐ[E] K) (w : HeightOneSpectrum (𝓞 K)) (r : 𝓞 K) :
    (σ • w).intValuation (σ • r) = w.intValuation r := by
  rcases eq_or_ne r 0 with rfl | hr
  · rw [smul_zero, Valuation.map_zero, Valuation.map_zero]
  · have hσr : σ • r ≠ 0 := fun h0 => hr (by rw [← inv_smul_smul σ r, h0, smul_zero])
    apply le_antisymm
    · obtain ⟨n, hn⟩ : ∃ n : ℕ, w.intValuation r = WithZero.exp (-(n : ℤ)) := ⟨_, w.intValuation_if_neg hr⟩
      rw [hn, HeightOneSpectrum.intValuation_le_pow_iff_mem, smul_mem_smul_asIdeal_pow_iff,
        ← HeightOneSpectrum.intValuation_le_pow_iff_mem, hn]
    · obtain ⟨n, hn⟩ : ∃ n : ℕ, (σ • w).intValuation (σ • r) = WithZero.exp (-(n : ℤ)) := ⟨_, (σ • w).intValuation_if_neg hσr⟩
      rw [hn, HeightOneSpectrum.intValuation_le_pow_iff_mem, ← smul_mem_smul_asIdeal_pow_iff σ,
        ← HeightOneSpectrum.intValuation_le_pow_iff_mem, hn]

theorem valuation_smul_apply (σ : K ≃ₐ[E] K) (w : HeightOneSpectrum (𝓞 K)) (x : K) :
    (σ • w).valuation K (σ x) = w.valuation K x := by
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 K) x
  have h1 : ∀ c : 𝓞 K, σ (algebraMap (𝓞 K) K c) = algebraMap (𝓞 K) K (σ • c) := fun c => rfl
  rw [map_div₀, map_div₀, map_div₀, h1, h1, HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap, intValuation_smul_apply,
    intValuation_smul_apply]

theorem valuation_apply_of_smul_eq {σ : K ≃ₐ[E] K} {w w' : HeightOneSpectrum (𝓞 K)} (h : σ • w = w') (x : K) :
    w'.valuation K (σ x) = w.valuation K x := by
  subst h
  exact valuation_smul_apply σ w x

theorem uniformContinuous_congr_of_smul_eq {σ : K ≃ₐ[E] K} {w w' : HeightOneSpectrum (𝓞 K)} (h : σ • w = w') :
    UniformContinuous (WithVal.congr (w.valuation K) (w'.valuation K) ((σ : K ≃ₐ[E] K) : K ≃+* K)) :=
  uniformContinuous_congr_of_forall_eq (w.valuation K) (w'.valuation K) (w.valuation_surjective K) _ (valuation_apply_of_smul_eq h)

noncomputable def transport (σ : K ≃ₐ[E] K) {w w' : HeightOneSpectrum (𝓞 K)} (h : σ • w = w') :
    w.adicCompletion K ≃+* w'.adicCompletion K :=
  ((HeightOneSpectrum.adicCompletion.equiv K w).trans
    (UniformSpace.Completion.mapRingEquiv (WithVal.congr (w.valuation K) (w'.valuation K) ((σ : K ≃ₐ[E] K) : K ≃+* K))
      (uniformContinuous_congr_of_smul_eq h).continuous
      ((uniformContinuous_congr_of_smul_eq (inv_smul_eq_of_smul_eq h)).continuous.congr fun _ => rfl))).trans
    (HeightOneSpectrum.adicCompletion.equiv K w').symm

theorem transport_apply (σ : K ≃ₐ[E] K) {w w' : HeightOneSpectrum (𝓞 K)} (h : σ • w = w') (x : w.adicCompletion K) :
    (transport σ h x).toCompletion
      = UniformSpace.Completion.map (WithVal.congr (w.valuation K) (w'.valuation K) ((σ : K ≃ₐ[E] K) : K ≃+* K)) x.toCompletion :=
  rfl

theorem transport_coe (σ : K ≃ₐ[E] K) {w w' : HeightOneSpectrum (𝓞 K)} (h : σ • w = w') (x : WithVal (w.valuation K)) :
    transport σ h (x : w.adicCompletion K)
      = ((WithVal.congr (w.valuation K) (w'.valuation K) ((σ : K ≃ₐ[E] K) : K ≃+* K) x : WithVal (w'.valuation K)) : w'.adicCompletion K) := by
  apply HeightOneSpectrum.adicCompletion.ext
  rw [transport_apply, HeightOneSpectrum.adicCompletion.toCompletion_ofCompletion,
    HeightOneSpectrum.adicCompletion.toCompletion_ofCompletion,
    UniformSpace.Completion.map_coe (uniformContinuous_congr_of_smul_eq h)]

theorem continuous_transport (σ : K ≃ₐ[E] K) {w w' : HeightOneSpectrum (𝓞 K)} (h : σ • w = w') : Continuous (transport σ h) := by
  have : (transport σ h : w.adicCompletion K → w'.adicCompletion K)
      = HeightOneSpectrum.adicCompletion.ofCompletion ∘
        UniformSpace.Completion.map (WithVal.congr (w.valuation K) (w'.valuation K) ((σ : K ≃ₐ[E] K) : K ≃+* K)) ∘
        HeightOneSpectrum.adicCompletion.toCompletion :=
    funext fun x => HeightOneSpectrum.adicCompletion.ext (h := transport_apply σ h x)
  rw [this]
  exact (HeightOneSpectrum.adicCompletion.continuous_ofCompletion K w').comp
    (UniformSpace.Completion.continuous_map.comp (HeightOneSpectrum.adicCompletion.continuous_toCompletion K w))

theorem isClopen_setOf_valued_le (w : HeightOneSpectrum (𝓞 K)) {c : WithZero (Multiplicative ℤ)} (hc : c ≠ 0) :
    IsClopen {y : w.adicCompletion K | Valued.v y ≤ c} := by
  obtain ⟨y₁, rfl⟩ := w.valuedAdicCompletion_surjective K c
  have hr : Valued.v.restrict y₁ ≠ 0 := fun h0 => hc ((Valuation.restrict_eq_zero_iff Valued.v).1 h0)
  have : {y : w.adicCompletion K | Valued.v y ≤ Valued.v y₁} = {y | Valued.v.restrict y ≤ Valued.v.restrict y₁} :=
    Set.ext fun y => (Valuation.restrict_le_iff Valued.v (x := y) (y := y₁)).symm
  rw [this]
  exact Valued.isClopen_closedBall (w.adicCompletion K) hr

theorem valued_transport (σ : K ≃ₐ[E] K) {w w' : HeightOneSpectrum (𝓞 K)} (h : σ • w = w') (x : w.adicCompletion K) :
    Valued.v (transport σ h x) = Valued.v x := by

  have key : ∀ c : WithZero (Multiplicative ℤ), c ≠ 0 → ∀ y : w.adicCompletion K, (Valued.v (transport σ h y) ≤ c ↔ Valued.v y ≤ c) := by
    intro c hc y
    have hclosed : IsClosed {y : w.adicCompletion K | Valued.v (transport σ h y) ≤ c ↔ Valued.v y ≤ c} := by
      have h1 : IsClopen {y : w.adicCompletion K | Valued.v (transport σ h y) ≤ c} :=
        (isClopen_setOf_valued_le w' hc).preimage (continuous_transport σ h)
      have h2 : IsClopen {y : w.adicCompletion K | Valued.v y ≤ c} := isClopen_setOf_valued_le w hc
      have : {y : w.adicCompletion K | Valued.v (transport σ h y) ≤ c ↔ Valued.v y ≤ c}
          = ({y | Valued.v (transport σ h y) ≤ c} ∩ {y | Valued.v y ≤ c}) ∪ ({y | Valued.v (transport σ h y) ≤ c}ᶜ ∩ {y | Valued.v y ≤ c}ᶜ) := by
        ext y
        simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_inter_iff, Set.mem_compl_iff]
        tauto
      rw [this]
      exact ((h1.inter h2).union (h1.compl.inter h2.compl)).isClosed
    obtain ⟨y, rfl⟩ := HeightOneSpectrum.adicCompletion.ofCompletion_surjective K w y
    refine UniformSpace.Completion.induction_on
      (p := fun y => Valued.v (transport σ h (.ofCompletion y)) ≤ c ↔
        Valued.v (HeightOneSpectrum.adicCompletion.ofCompletion y : w.adicCompletion K) ≤ c) y
      (by simpa only [Set.preimage_ofPred_eq] using
        hclosed.preimage (HeightOneSpectrum.adicCompletion.continuous_ofCompletion K w)) fun a => ?_
    show Valued.v (transport σ h (a : w.adicCompletion K)) ≤ c ↔ Valued.v (a : w.adicCompletion K) ≤ c
    rw [transport_coe, HeightOneSpectrum.adicCompletion.valued_ofCompletion,
      HeightOneSpectrum.adicCompletion.valued_ofCompletion, Valued.valuedCompletion_apply, Valued.valuedCompletion_apply, ← WithVal.apply_ofVal, ← WithVal.apply_ofVal,
      WithVal.congr_apply, WithVal.ofVal_toVal, AlgEquiv.coe_ringEquiv, valuation_apply_of_smul_eq h]
  rcases eq_or_ne x 0 with rfl | hx
  · rw [map_zero, Valuation.map_zero, Valuation.map_zero]
  · have h0 : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).2 hx
    have h0' : Valued.v (transport σ h x) ≠ 0 := (Valuation.ne_zero_iff _).2 ((map_ne_zero (transport σ h)).2 hx)
    exact le_antisymm ((key _ h0 x).2 le_rfl) ((key _ h0' x).1 le_rfl)

theorem transport_mem_adicCompletionIntegers_iff (σ : K ≃ₐ[E] K) {w w' : HeightOneSpectrum (𝓞 K)} (h : σ • w = w')
    (x : w.adicCompletion K) : transport σ h x ∈ w'.adicCompletionIntegers K ↔ x ∈ w.adicCompletionIntegers K := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, HeightOneSpectrum.mem_adicCompletionIntegers, valued_transport]

set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 800000 in

noncomputable def transportIntegers (σ : K ≃ₐ[E] K) {w w' : HeightOneSpectrum (𝓞 K)} (h : σ • w = w') :
    w.adicCompletionIntegers K ≃+* w'.adicCompletionIntegers K where
  toFun x := ⟨transport σ h x, (transport_mem_adicCompletionIntegers_iff σ h _).2 x.2⟩
  invFun y := ⟨(transport σ h).symm y, (transport_mem_adicCompletionIntegers_iff σ h _).1 (by rw [RingEquiv.apply_symm_apply]; exact y.2)⟩
  left_inv x := Subtype.ext ((transport σ h).symm_apply_apply x)
  right_inv y := Subtype.ext ((transport σ h).apply_symm_apply y)
  map_mul' x y := Subtype.ext (map_mul (transport σ h) (x : w.adicCompletion K) (y : w.adicCompletion K))
  map_add' x y := Subtype.ext (map_add (transport σ h) (x : w.adicCompletion K) (y : w.adicCompletion K))

set_option synthInstance.maxHeartbeats 200000 in
theorem coe_transportIntegers (σ : K ≃ₐ[E] K) {w w' : HeightOneSpectrum (𝓞 K)} (h : σ • w = w') (x : w.adicCompletionIntegers K) :
    ((transportIntegers σ h x : w'.adicCompletionIntegers K) : w'.adicCompletion K) = transport σ h (x : w.adicCompletion K) := rfl

set_option synthInstance.maxHeartbeats 200000 in

noncomputable abbrev transportUnits (σ : K ≃ₐ[E] K) {w w' : HeightOneSpectrum (𝓞 K)} (h : σ • w = w') :
    (w.adicCompletion K)ˣ ≃* (w'.adicCompletion K)ˣ :=
  Units.mapEquiv (transport σ h).toMulEquiv

set_option synthInstance.maxHeartbeats 200000 in

noncomputable abbrev transportIntegerUnits (σ : K ≃ₐ[E] K) {w w' : HeightOneSpectrum (𝓞 K)} (h : σ • w = w') :
    (w.adicCompletionIntegers K)ˣ ≃* (w'.adicCompletionIntegers K)ˣ :=
  Units.mapEquiv (transportIntegers σ h).toMulEquiv

end NumberField.PlaceTransport


