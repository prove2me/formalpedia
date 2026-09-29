-- Prove2me | Definitions.Def_LeopoldtGaloisAction
-- name    : LeopoldtGaloisAction
-- status  : Definition
-- author  : @xuanji
-- created : 2026-09-27T02:46:17.448988+00:00
-- url     : https://prove2.me/theorems/fde15c86-f83f-4b95-a05f-e29edb9b10d9
-- title:
--   Galois action on the semilocal units at $p$
-- statement:
--   Let $K$ be a number field, $p$ a rational prime, and $\mathcal P=\{v\subset\mathcal O_K : v\mid p\}$ the (finite) set of primes of $\mathcal O_K$ above $p$. For $v\in\mathcal P$ write $K_v$ for the $v$-adic completion, $\mathcal O_v$ for its valuation ring, and let
--   $$U=\prod_{v\in\mathcal P}\mathcal O_v^\times$$
--   be the group of semilocal units at $p$ (the object `SemilocalUnits p K` of `Def_LeopoldtDefect`).
--
--   Every field automorphism $\sigma\in\operatorname{Aut}(K/\mathbb Q)$ restricts to a ring automorphism of $\mathcal O_K$ and therefore permutes the primes above $p$: we write $\sigma v$ for the prime with $x\in\sigma v\iff\sigma^{-1}x\in v$. This file defines:
--
--   1. **The prime permutation** $\pi_\sigma:\mathcal P\to\mathcal P$, $v\mapsto\sigma v$ (`Leopoldt.primesOverPerm p K σ`).
--   2. **The local isomorphisms.** Since $|\sigma x|_{\sigma v}=|x|_v$ for all $x\in K$, the map $\sigma:K\to K$ is an isometry from $(K,|\cdot|_v)$ to $(K,|\cdot|_{\sigma v})$ and extends uniquely to a continuous isomorphism of complete fields $\sigma_v:K_v\xrightarrow{\ \sim\ }K_{\sigma v}$, which carries $\mathcal O_v$ onto $\mathcal O_{\sigma v}$ and hence $\mathcal O_v^\times$ onto $\mathcal O_{\sigma v}^\times$ (`Leopoldt.GaloisAction.localRingEquiv`, `localIntegersEquiv`, `localUnitsEquiv`).
--   3. **The Galois action on semilocal units** (`Leopoldt.semilocalGaloisAut p K σ`): the group automorphism of $U$ given by
--   $$(\sigma\cdot x)_w=\sigma_{\sigma^{-1}w}\big(x_{\sigma^{-1}w}\big)\qquad(x=(x_v)_{v\in\mathcal P}\in U,\ w\in\mathcal P).$$
--
--   Equivalently, identifying $\prod_{v\mid p}K_v$ with $K\otimes_{\mathbb Q}\mathbb Q_p$, this is the action of $\sigma\otimes 1$ restricted to the unit group $U$. It is the action of $\operatorname{Gal}(K/\mathbb Q)$ on $K_p$, $U$ and the closure $\overline E$ of the global units which is used throughout the representation-theoretic analysis of the Leopoldt defect.
--
--   **Formalization Note** The local maps are parametrised by any pair of primes $(v,w)$ together with a proof that $w(\sigma x)=v(x)$ for all $x\in K$; the prime $\sigma^{-1}w$ is realised as the comap of $w$ under $\sigma|_{\mathcal O_K}$, and the identity $w(\sigma x)=(\sigma^{-1}w)(x)$ of adic valuations is proved in the file. Continuity, compatibility with the diagonal embedding of global units, the group-action property and stability of $\overline E$ are stated as separate theorems.
-- source:
--   P. Mihăilescu, On CM Z_p-extensions and the Leopoldt conjecture for CM fields, arXiv:1105.4544, §1.1 (Gal(K/Q) acting on K_p = K ⊗ Q_p, U and Ē); J. Neukirch, Algebraic Number Theory, Ch. II §8 (extensions of valuations; conjugate valuations and the isomorphisms K_v ≅ K_{σv})

import Definitions.Def_LeopoldtDefect

/-!
# The Galois action on the semilocal units at `p`

Let `K` be a number field and `σ : K ≃ₐ[ℚ] K` a field automorphism.  Then `σ` permutes the
primes of `𝓞 K` above `p` (`v ↦ σ v`, where `x ∈ σ v ↔ σ⁻¹ x ∈ v`), and for every prime `v`
it is an isometry `(K, |·|_v) → (K, |·|_{σ v})`, hence extends to an isomorphism of complete
valued fields `K_v ≃ K_{σ v}` carrying `𝓞_v` onto `𝓞_{σ v}`.  Collecting these gives an
automorphism of the semilocal unit group `U = ∏_{v ∣ p} 𝓞_v^×`:

  `(σ • x)_w = σ (x_{σ⁻¹ w})`.

This is the action used in Section 1.1 of Mihăilescu, *On CM `ℤ_p`-extensions and the Leopoldt
conjecture for CM fields* (arXiv:1105.4544), where `Gal(K/ℚ)` acts on `K_p = K ⊗_ℚ ℚ_p` and hence
on `U` and `Ē`; see also Neukirch, *Algebraic Number Theory*, Ch. II §8 (extensions of
valuations and the action of automorphisms on completions).
-/

namespace Leopoldt

open NumberField IsDedekindDomain

namespace GaloisAction

section Local

variable {K : Type*} [Field K] [NumberField K]
variable (σ : K ≃ₐ[ℚ] K) (v w : HeightOneSpectrum (𝓞 K))

/-- `σ : K → K` viewed as a ring isomorphism from `K` with the `v`-adic valuation to `K` with the
`w`-adic valuation. -/
noncomputable def withValEquiv : WithVal (v.valuation K) ≃+* WithVal (w.valuation K) :=
  WithVal.congr _ _ (σ : K ≃+* K)

variable {v w}

/-- A ring homomorphism between valuation-topologised `WithVal` rings which preserves the
valuation is uniformly continuous. -/
theorem uniformContinuous_of_valued_eq {v w : HeightOneSpectrum (𝓞 K)}
    (f : WithVal (v.valuation K) →+* WithVal (w.valuation K))
    (hf : ∀ x, Valued.v (f x) = Valued.v x) : UniformContinuous f := by
  refine uniformContinuous_of_continuousAt_zero f ?_
  rw [ContinuousAt, map_zero, (Valued.hasBasis_nhds_zero _ _).tendsto_iff
    (Valued.hasBasis_nhds_zero _ _)]
  intro γ _
  obtain ⟨k, hk⟩ := HeightOneSpectrum.valuation_surjective K v
    (MonoidWithZeroHom.ValueGroup₀.embedding γ.val)
  have hγ : MonoidWithZeroHom.ValueGroup₀.embedding
      γ.val ≠ 0 := by
    exact (map_ne_zero_iff _
      MonoidWithZeroHom.ValueGroup₀.embedding_strictMono.injective).2 γ.ne_zero
  have ha0 : (Valued.v : Valuation (WithVal (v.valuation K)) (WithZero (Multiplicative ℤ))).restrict
      (WithVal.toVal (v.valuation K) k) ≠ 0 := by
    intro h0
    apply hγ
    rw [← hk, ← WithVal.valued_toVal, ← Valuation.embedding_restrict, h0, map_zero]
  refine ⟨Units.mk0 _ ha0, trivial, fun x hx => ?_⟩
  simp only [Set.mem_ofPred_eq, Units.val_mk0, Valuation.restrict_lt_iff_lt_embedding,
    Valuation.embedding_restrict] at hx ⊢
  rw [hf, ← hk, ← WithVal.valued_toVal]
  exact hx

variable (h : ∀ x : K, w.valuation K (σ x) = v.valuation K x)
include h

theorem valued_withValEquiv (x : WithVal (v.valuation K)) :
    Valued.v (withValEquiv σ v w x) = Valued.v x := by
  simp [withValEquiv, WithVal.congr_apply, h]
  rfl

theorem valued_withValEquiv_symm (x : WithVal (w.valuation K)) :
    Valued.v ((withValEquiv σ v w).symm x) = Valued.v x := by
  have := valued_withValEquiv σ h ((withValEquiv σ v w).symm x)
  rw [RingEquiv.apply_symm_apply] at this
  exact this.symm

theorem uniformContinuous_withValEquiv : UniformContinuous (withValEquiv σ v w) :=
  uniformContinuous_of_valued_eq _ (valued_withValEquiv σ h)

theorem uniformContinuous_withValEquiv_symm :
    UniformContinuous (withValEquiv σ v w).symm :=
  uniformContinuous_of_valued_eq _ (valued_withValEquiv_symm σ h)

/-- The isomorphism of completions `(v.valuation K).Completion ≃+* (w.valuation K).Completion`. -/
noncomputable def completionEquiv : (v.valuation K).Completion ≃+* (w.valuation K).Completion :=
  UniformSpace.Completion.mapRingEquiv (withValEquiv σ v w)
    (uniformContinuous_withValEquiv σ h).continuous
    (uniformContinuous_withValEquiv_symm σ h).continuous

/-- The isomorphism of completions `K_v ≃+* K_w` induced by `σ` when `w = σ v`. -/
noncomputable def localRingEquiv : v.adicCompletion K ≃+* w.adicCompletion K :=
  ((HeightOneSpectrum.adicCompletion.equiv K v).trans (completionEquiv σ h)).trans
    (HeightOneSpectrum.adicCompletion.equiv K w).symm

theorem continuous_localRingEquiv : Continuous (localRingEquiv σ h) :=
  (HeightOneSpectrum.adicCompletion.continuous_ofCompletion K w).comp
    (UniformSpace.Completion.continuous_map.comp
      (HeightOneSpectrum.adicCompletion.continuous_toCompletion K v))

theorem continuous_localRingEquiv_symm : Continuous (localRingEquiv σ h).symm :=
  (HeightOneSpectrum.adicCompletion.continuous_ofCompletion K v).comp
    (UniformSpace.Completion.continuous_map.comp
      (HeightOneSpectrum.adicCompletion.continuous_toCompletion K w))

theorem localRingEquiv_coe (k : K) :
    localRingEquiv σ h (k : v.adicCompletion K) = ((σ k : K) : w.adicCompletion K) := by
  show HeightOneSpectrum.adicCompletion.ofCompletion
    (UniformSpace.Completion.map (withValEquiv σ v w)
      ((WithVal.equiv (v.valuation K)).symm k : (v.valuation K).Completion)) = _
  rw [UniformSpace.Completion.map_coe (uniformContinuous_withValEquiv σ h)]
  rfl

theorem localRingEquiv_symm_coe (k : K) :
    (localRingEquiv σ h).symm (k : w.adicCompletion K)
      = ((σ.symm k : K) : v.adicCompletion K) := by
  rw [RingEquiv.symm_apply_eq, localRingEquiv_coe, AlgEquiv.apply_symm_apply]

omit h in
/-- A continuous ring homomorphism of completions which sends `v`-integral elements of `K` to
`w`-integral elements maps `𝓞_v` into `𝓞_w`. -/
theorem mem_integers_of_coe {v w : HeightOneSpectrum (𝓞 K)}
    (g : v.adicCompletion K →+* w.adicCompletion K) (hg : Continuous g)
    (hk : ∀ k : K, v.valuation K k ≤ 1 → Valued.v (g (k : v.adicCompletion K)) ≤ 1)
    (y : v.adicCompletion K) (hy : y ∈ v.adicCompletionIntegers K) :
    g y ∈ w.adicCompletionIntegers K := by
  have hS : IsClosed {z : v.adicCompletion K | Valued.v (g z) ≤ 1} :=
    (Valued.isClosed_integer (w.adicCompletion K)).preimage hg
  have hA : IsOpen ((v.adicCompletionIntegers K : Set (v.adicCompletion K))) :=
    Valued.isOpen_integer (v.adicCompletion K)
  have hkey : (v.adicCompletionIntegers K : Set (v.adicCompletion K)) ∩
      Set.range (algebraMap K (v.adicCompletion K)) ⊆
      {z : v.adicCompletion K | Valued.v (g z) ≤ 1} := by
    rintro z ⟨hz, x, rfl⟩
    have hz' : Valued.v ((x : K) : v.adicCompletion K) ≤ 1 := hz
    rw [HeightOneSpectrum.adicCompletion.valued_coe] at hz'
    exact hk x hz'
  exact hS.closure_subset_iff.mpr hkey
    ((HeightOneSpectrum.denseRange_algebraMap K v).open_subset_closure_inter hA hy)

theorem localRingEquiv_mem_iff (y : v.adicCompletion K) :
    y ∈ v.adicCompletionIntegers K ↔ localRingEquiv σ h y ∈ w.adicCompletionIntegers K := by
  constructor
  · refine mem_integers_of_coe (localRingEquiv σ h).toRingHom (continuous_localRingEquiv σ h)
      (fun k hk => ?_) y
    show Valued.v (localRingEquiv σ h (k : v.adicCompletion K)) ≤ 1
    rw [localRingEquiv_coe, HeightOneSpectrum.adicCompletion.valued_coe, h]
    exact hk
  · intro hy
    have := mem_integers_of_coe (localRingEquiv σ h).symm.toRingHom
      (continuous_localRingEquiv_symm σ h) (fun k hk => ?_) _ hy
    · simpa using this
    show Valued.v ((localRingEquiv σ h).symm (k : w.adicCompletion K)) ≤ 1
    rw [localRingEquiv_symm_coe, HeightOneSpectrum.adicCompletion.valued_coe, ← h,
      AlgEquiv.apply_symm_apply]
    exact hk

/-- The induced isomorphism of local rings of integers `𝓞_v ≃+* 𝓞_w`. -/
noncomputable def localIntegersEquiv :
    v.adicCompletionIntegers K ≃+* w.adicCompletionIntegers K :=
  (localRingEquiv σ h).restrict _ _ (localRingEquiv_mem_iff σ h)

theorem coe_localIntegersEquiv (x : v.adicCompletionIntegers K) :
    ((localIntegersEquiv σ h x : w.adicCompletionIntegers K) : w.adicCompletion K)
      = localRingEquiv σ h (x : v.adicCompletion K) := rfl

/-- The induced isomorphism of local unit groups `𝓞_v^× ≃* 𝓞_w^×`. -/
noncomputable def localUnitsEquiv :
    (v.adicCompletionIntegers K)ˣ ≃* (w.adicCompletionIntegers K)ˣ :=
  Units.mapEquiv (localIntegersEquiv σ h).toMulEquiv

theorem coe_localUnitsEquiv (x : (v.adicCompletionIntegers K)ˣ) :
    (((localUnitsEquiv σ h x : (w.adicCompletionIntegers K)ˣ) :
      w.adicCompletionIntegers K) : w.adicCompletion K)
      = localRingEquiv σ h ((x : v.adicCompletionIntegers K) : v.adicCompletion K) := rfl

end Local

section Primes

variable {K : Type*} [Field K] [NumberField K] (σ : K ≃ₐ[ℚ] K)

/-- The restriction of `σ` to the ring of integers. -/
noncomputable abbrev intEquiv : 𝓞 K ≃+* 𝓞 K := RingOfIntegers.mapRingEquiv (σ : K ≃+* K)

/-- `σ` preserves the ideal `(n)` for every natural number `n`. -/
theorem natCast_mem_iff (n : ℕ) (I : Ideal (𝓞 K)) :
    (n : 𝓞 K) ∈ I.comap (intEquiv σ : 𝓞 K →+* 𝓞 K) ↔ (n : 𝓞 K) ∈ I := by
  rw [Ideal.mem_comap]; simp

/-- Ideals of `𝓞 K` are permuted multiplicatively by `σ`. -/
noncomputable def idealMulEquiv : Ideal (𝓞 K) ≃* Ideal (𝓞 K) where
  toFun I := I.map (intEquiv σ)
  invFun I := I.map (intEquiv σ).symm
  left_inv I := by simp [Ideal.map_symm, Ideal.comap_map_of_bijective _ (intEquiv σ).bijective]
  right_inv I := by
    simp [Ideal.map_symm, Ideal.map_comap_of_surjective _ (intEquiv σ).surjective]
  map_mul' I J := Ideal.map_mul _ I J

theorem intValuation_comap (w : HeightOneSpectrum (𝓞 K)) (a : 𝓞 K) :
    (HeightOneSpectrum.comap (intEquiv σ : 𝓞 K →+* 𝓞 K) (intEquiv σ).surjective w).intValuation a
      = w.intValuation (intEquiv σ a) := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  have ha' : intEquiv σ a ≠ 0 := by simpa using ha
  rw [HeightOneSpectrum.intValuation_eq_exp_neg_multiplicity _ ha,
    HeightOneSpectrum.intValuation_eq_exp_neg_multiplicity _ ha']
  congr 3
  rw [← multiplicity_map_eq (idealMulEquiv σ)]
  congr 1
  · show Ideal.map _ (Ideal.comap _ w.asIdeal) = _
    exact Ideal.map_comap_of_surjective _ (intEquiv σ).surjective _
  · show Ideal.map _ _ = _
    rw [Ideal.map_span, Set.image_singleton]

theorem valuation_comap (w : HeightOneSpectrum (𝓞 K)) (x : K) :
    w.valuation K (σ x) =
      (HeightOneSpectrum.comap (intEquiv σ : 𝓞 K →+* 𝓞 K) (intEquiv σ).surjective w).valuation
        K x := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 K) x
  rw [map_div₀, map_div₀, map_div₀]
  have e : ∀ c : 𝓞 K, σ (algebraMap (𝓞 K) K c) = algebraMap (𝓞 K) K (intEquiv σ c) :=
    fun c => rfl
  rw [e, e, HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap,
    intValuation_comap, intValuation_comap]

end Primes

end GaloisAction

open GaloisAction

variable (p : ℕ) [Fact p.Prime] (K : Type*) [Field K] [NumberField K]

/-- The permutation `v ↦ σ v` of the primes of `𝓞 K` above `p` induced by `σ`; here
`x ∈ σ v ↔ σ⁻¹ x ∈ v`. -/
noncomputable def primesOverPerm (σ : K ≃ₐ[ℚ] K) : PrimesOver p K ≃ PrimesOver p K :=
  (HeightOneSpectrum.equivOfRingEquiv (intEquiv σ)).subtypeEquiv fun v => by
    show _ ↔ (p : 𝓞 K) ∈ Ideal.comap ((intEquiv σ).symm : 𝓞 K →+* 𝓞 K) v.asIdeal
    rw [Ideal.mem_comap]; simp

omit [Fact p.Prime] in
theorem primesOverPerm_apply_asIdeal (σ : K ≃ₐ[ℚ] K) (v : PrimesOver p K) :
    (primesOverPerm p K σ v).1.asIdeal
      = v.1.asIdeal.comap ((intEquiv σ).symm : 𝓞 K →+* 𝓞 K) :=
  rfl

omit [Fact p.Prime] in
theorem primesOverPerm_symm_asIdeal (σ : K ≃ₐ[ℚ] K) (w : PrimesOver p K) :
    ((primesOverPerm p K σ).symm w).1.asIdeal = w.1.asIdeal.comap (intEquiv σ : 𝓞 K →+* 𝓞 K) :=
  rfl

omit [Fact p.Prime] in
theorem valuation_primesOverPerm_symm (σ : K ≃ₐ[ℚ] K) (w : PrimesOver p K) (x : K) :
    w.1.valuation K (σ x) = ((primesOverPerm p K σ).symm w).1.valuation K x :=
  valuation_comap σ w.1 x

/-- The **Galois action on the semilocal units**: for `σ : K ≃ₐ[ℚ] K`, the continuous group
automorphism of `U = ∏_{v ∣ p} 𝓞_v^×` given by `(σ • x)_w = σ(x_{σ⁻¹ w})`, where
`σ : K_{σ⁻¹ w} ≃ K_w` is the isomorphism of completions induced by `σ`. -/
noncomputable def semilocalGaloisAut (σ : K ≃ₐ[ℚ] K) : SemilocalUnits p K ≃* SemilocalUnits p K :=
  ({ toEquiv := (Equiv.piCongrLeft (fun v : PrimesOver p K => (v.1.adicCompletionIntegers K)ˣ)
        (primesOverPerm p K σ).symm).symm
     map_mul' := fun _ _ => rfl } :
      SemilocalUnits p K ≃* ∀ w : PrimesOver p K,
        (((primesOverPerm p K σ).symm w).1.adicCompletionIntegers K)ˣ).trans
  (MulEquiv.piCongrRight fun w =>
    localUnitsEquiv σ (valuation_primesOverPerm_symm p K σ w))

theorem semilocalGaloisAut_apply (σ : K ≃ₐ[ℚ] K) (x : SemilocalUnits p K) (w : PrimesOver p K) :
    semilocalGaloisAut p K σ x w =
      localUnitsEquiv σ (valuation_primesOverPerm_symm p K σ w) (x ((primesOverPerm p K σ).symm w)) :=
  rfl

end Leopoldt


