-- Prove2me | Definitions.Def_ArtinL_Abelian
-- name    : ArtinL_Abelian
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.014713+00:00
-- url     : https://prove2.me/theorems/a913ea7c-b328-5a88-a559-dcad986be5aa
-- title:
--   Abelian Artin L-series, conductors and completed L-functions
-- statement:
--   Throughout, $M/K$ is a Galois extension of number fields and $\psi$ is a monoid homomorphism $\mathrm{Gal}(M/K)\to\mathbb C^\times$; all local data are read off the *chosen* maximal ideal `primeAbove K M v` of $\mathcal O_M$ above a finite place $v$ of $K$ (picked by choice from an existence statement) and the associated arithmetic Frobenius `artinFrob K M v`. For such a $v$, `inertiaGroup K M v` is the inertia subgroup of $\mathrm{Gal}(M/K)$ attached to that prime, and `ramificationGroup K M v i` the one attached to its $(i+1)$-st power, so that the $i=0$ case recovers the inertia group. `IsUnramifiedAt ψ v` says that $\psi$ is trivial on the inertia group; `localValue ψ v` is $\psi(\mathrm{Frob}_v)\in\mathbb C$ in that case and $0$ otherwise; `idealValue ψ I` is the (multiplicative, possibly infinite) product of `localValue ψ v` raised to the multiplicity of $v$ in the factorisation of $I$; `coeff ψ n` is $0$ for $n=0$ and otherwise the sum of `idealValue ψ I` over the finitely many ideals of absolute norm $n$; and `LSeries ψ` is Mathlib's Dirichlet series of this coefficient function. On the conductor side, `swanConductor ψ v` is the rational number $\sum_{i\ge 0}\bigl(\#G_{i+1}/\#G_0\bigr)\cdot[\psi|_{G_{i+1}}\neq 1]$ with $G_j$ the above ramification groups, `conductorExponent ψ v` adds to its natural-number ceiling the indicator of ramification at $v$, and `conductor ψ` is the product of the $v$ raised to these exponents. Archimedean data: `IsPlusAt ψ v` asks, for a place $v$ of $K$, that $\psi$ be trivial on the stabiliser of every infinite place of $M$ above $v$; `nPlus ψ` counts the real places with this property and `nMinus ψ` is the truncated difference $r_1(K)-\mathrm{nPlus}$. `completedLSeries ψ s` is $(|d_K|\,N\mathfrak f(\psi))^{s/2}\Gamma_{\mathbb R}(s)^{n^+}\Gamma_{\mathbb R}(s+1)^{n^-}\Gamma_{\mathbb C}(s)^{r_2(K)}L(s,\psi)$. Separately, for a finite extension $F/k$ and $H\le \mathrm{Gal}(F/k)$, `ofSubgroup H χ` transports a character $\chi$ of $H$ to a character of $\mathrm{Gal}(F/F^H)$ through the Galois correspondence, its value at $\sigma$ being $\chi$ of $\sigma$ viewed as a $k$-algebra automorphism. The remaining lemmas record that the conductor is non-zero with positive absolute norm, that $n^++n^-=r_1(K)$, that values of $\psi$ have modulus $1$, and that all the data attached to $\psi^{-1}$ are the complex conjugates of (resp. equal to, for the conductor and the archimedean counts) those of $\psi$.
--
--   **Relation to Mathlib.** The Dirichlet-series, Gamma-factor, ideal-norm, discriminant and place-counting ingredients, and the inertia subgroup attached to an ideal, are Mathlib's; the abelian Artin local values, ideal values, $L$-series coefficients, Swan conductor, conductor and completed $L$-function assembled from them are the project's own.
--
--   **Where it is used.** These objects supply the one-dimensional (abelian) Artin $L$-functions needed in the Langlands–Tunnell input to the Fermat argument, where $L$-series of characters of subgroups of a Galois group, together with their conductors and completed $L$-functions, are compared with automorphic $L$-series.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_ArtinL_Abelian.lean

import Mathlib
import Definitions.Def_LanglandsTunnell_ArtinFrobenius

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

open NumberField NumberField.InfinitePlace IsDedekindDomain
open scoped Classical

namespace ArtinL.Abelian

section Finite

variable {K M : Type*} [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
  [IsGalois K M]

variable (K M) in

def inertiaGroup (v : HeightOneSpectrum (𝓞 K)) : Subgroup (M ≃ₐ[K] M) :=
  (LanglandsTunnell.P2.Artin.primeAbove K M v).inertia (M ≃ₐ[K] M)

variable (K M) in

def ramificationGroup (v : HeightOneSpectrum (𝓞 K)) (i : ℕ) : Subgroup (M ≃ₐ[K] M) :=
  (LanglandsTunnell.P2.Artin.primeAbove K M v ^ (i + 1)).inertia (M ≃ₐ[K] M)

omit [NumberField M] [IsGalois K M] in
theorem ramificationGroup_zero (v : HeightOneSpectrum (𝓞 K)) :
    ramificationGroup K M v 0 = inertiaGroup K M v := by
  rw [ramificationGroup, zero_add, pow_one, inertiaGroup]

def IsUnramifiedAt (ψ : (M ≃ₐ[K] M) →* ℂˣ) (v : HeightOneSpectrum (𝓞 K)) : Prop :=
  ∀ σ ∈ inertiaGroup K M v, ψ σ = 1

def localValue (ψ : (M ≃ₐ[K] M) →* ℂˣ) (v : HeightOneSpectrum (𝓞 K)) : ℂ :=
  if IsUnramifiedAt ψ v then ((ψ (LanglandsTunnell.P2.Artin.artinFrob K M v) : ℂˣ) : ℂ) else 0

def idealValue (ψ : (M ≃ₐ[K] M) →* ℂˣ) (I : Ideal (𝓞 K)) : ℂ :=
  ∏ᶠ v : HeightOneSpectrum (𝓞 K),
    localValue ψ v ^ (Associates.mk v.asIdeal).count (Associates.mk I).factors

def coeff (ψ : (M ≃ₐ[K] M) →* ℂˣ) (n : ℕ) : ℂ :=
  if n = 0 then 0 else ∑ I ∈ (Ideal.finite_setOf_absNorm_eq (S := 𝓞 K) n).toFinset, idealValue ψ I

def LSeries (ψ : (M ≃ₐ[K] M) →* ℂˣ) (s : ℂ) : ℂ :=
  _root_.LSeries (coeff ψ) s

def swanConductor (ψ : (M ≃ₐ[K] M) →* ℂˣ) (v : HeightOneSpectrum (𝓞 K)) : ℚ :=
  ∑ᶠ i : ℕ,
    (Nat.card (ramificationGroup K M v (i + 1)) : ℚ) / (Nat.card (inertiaGroup K M v) : ℚ) *
      (if ∀ σ ∈ ramificationGroup K M v (i + 1), ψ σ = 1 then 0 else 1)

def conductorExponent (ψ : (M ≃ₐ[K] M) →* ℂˣ) (v : HeightOneSpectrum (𝓞 K)) : ℕ :=
  (if IsUnramifiedAt ψ v then 0 else 1) + ⌈swanConductor ψ v⌉₊

def conductor (ψ : (M ≃ₐ[K] M) →* ℂˣ) : Ideal (𝓞 K) :=
  ∏ᶠ v : HeightOneSpectrum (𝓞 K), v.asIdeal ^ conductorExponent ψ v

end Finite

section Archimedean

variable {K M : Type*} [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]

def IsPlusAt (ψ : (M ≃ₐ[K] M) →* ℂˣ) (v : InfinitePlace K) : Prop :=
  ∀ w : InfinitePlace M, w.comap (algebraMap K M) = v →
    ∀ σ ∈ MulAction.stabilizer (M ≃ₐ[K] M) w, ψ σ = 1

def nPlus (ψ : (M ≃ₐ[K] M) →* ℂˣ) : ℕ :=
  Nat.card {v : InfinitePlace K // v.IsReal ∧ IsPlusAt ψ v}

def nMinus (ψ : (M ≃ₐ[K] M) →* ℂˣ) : ℕ :=
  nrRealPlaces K - nPlus ψ

end Archimedean

section Completed

variable {K M : Type*} [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
  [IsGalois K M]

def completedLSeries (ψ : (M ≃ₐ[K] M) →* ℂˣ) (s : ℂ) : ℂ :=
  ((|(discr K : ℝ)| * (Ideal.absNorm (conductor ψ) : ℝ) : ℝ) : ℂ) ^ (s / 2) *
    Complex.Gammaℝ s ^ nPlus ψ * Complex.Gammaℝ (s + 1) ^ nMinus ψ *
    Complex.Gammaℂ s ^ nrComplexPlaces K * LSeries ψ s

end Completed

section OfSubgroup

variable {k F : Type*} [Field k] [Field F] [Algebra k F] [FiniteDimensional k F]

def ofSubgroup (H : Subgroup (F ≃ₐ[k] F)) (χ : H →* ℂˣ) :
    (F ≃ₐ[IntermediateField.fixedField H] F) →* ℂˣ :=
  χ.comp
    ((MulEquiv.subgroupCongr (IntermediateField.fixingSubgroup_fixedField H)).toMonoidHom.comp
      (IntermediateField.fixingSubgroupEquiv (IntermediateField.fixedField H)).symm.toMonoidHom)

theorem ofSubgroup_apply (H : Subgroup (F ≃ₐ[k] F)) (χ : H →* ℂˣ)
    (σ : F ≃ₐ[IntermediateField.fixedField H] F) :
    ofSubgroup H χ σ =
      χ ⟨σ.restrictScalars k,
        (IntermediateField.fixingSubgroup_fixedField H).le (fun x => σ.commutes x)⟩ :=
  rfl

omit [FiniteDimensional k F] in
theorem restrictScalars_fixingSubgroupEquiv (E : IntermediateField k F) (σ : E.fixingSubgroup) :
    (IntermediateField.fixingSubgroupEquiv E σ).restrictScalars k = σ := by
  ext; rfl

theorem ofSubgroup_fixingSubgroupEquiv (H : Subgroup (F ≃ₐ[k] F)) (χ : H →* ℂˣ) (h : H) :
    ofSubgroup H χ (IntermediateField.fixingSubgroupEquiv (IntermediateField.fixedField H)
      ⟨h, by rw [IntermediateField.fixingSubgroup_fixedField H]; exact h.2⟩) = χ h := by
  rw [ofSubgroup, MonoidHom.comp_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
  rfl

end OfSubgroup

section Basic

variable {K M : Type*} [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
  [IsGalois K M]

@[simp] theorem coeff_zero (ψ : (M ≃ₐ[K] M) →* ℂˣ) : coeff ψ 0 = 0 := by
  simp [coeff]

omit [IsGalois K M] in

theorem conductor_ne_bot (ψ : (M ≃ₐ[K] M) →* ℂˣ) : conductor ψ ≠ ⊥ := by
  unfold conductor
  refine finprod_induction (fun I : Ideal (𝓞 K) => I ≠ ⊥) ?_ (fun I J hI hJ => mul_ne_zero hI hJ)
    (fun v => pow_ne_zero _ v.ne_bot)
  exact one_ne_zero

omit [IsGalois K M] in

theorem absNorm_conductor_pos (ψ : (M ≃ₐ[K] M) →* ℂˣ) : 0 < Ideal.absNorm (conductor ψ) :=
  Nat.pos_of_ne_zero fun h => conductor_ne_bot ψ (Ideal.absNorm_eq_zero_iff.1 h)

omit [NumberField M] [IsGalois K M] in

theorem nPlus_le (ψ : (M ≃ₐ[K] M) →* ℂˣ) : nPlus ψ ≤ nrRealPlaces K := by
  rw [nPlus, nrRealPlaces, ← Nat.card_eq_fintype_card]
  exact Nat.card_mono (Set.toFinite _) fun v hv => hv.1

omit [NumberField M] [IsGalois K M] in

theorem nPlus_add_nMinus (ψ : (M ≃ₐ[K] M) →* ℂˣ) : nPlus ψ + nMinus ψ = nrRealPlaces K := by
  rw [nMinus, Nat.add_sub_cancel' (nPlus_le ψ)]

theorem norm_apply (ψ : (M ≃ₐ[K] M) →* ℂˣ) (σ : M ≃ₐ[K] M) : ‖((ψ σ : ℂˣ) : ℂ)‖ = 1 := by
  have hfin : IsOfFinOrder σ := isOfFinOrder_of_finite σ
  obtain ⟨n, hn, hσ⟩ := hfin.exists_pow_eq_one
  have h1 : ((ψ σ : ℂˣ) : ℂ) ^ n = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← map_pow, hσ, map_one, Units.val_one]
  have h2 : ‖((ψ σ : ℂˣ) : ℂ)‖ ^ n = 1 := by rw [← norm_pow, h1, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').1 h2

theorem coe_inv_apply (ψ : (M ≃ₐ[K] M) →* ℂˣ) (σ : M ≃ₐ[K] M) :
    ((ψ⁻¹ σ : ℂˣ) : ℂ) = starRingEnd ℂ ((ψ σ : ℂˣ) : ℂ) := by
  rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val]
  exact (Complex.inv_eq_conj (norm_apply ψ σ))

omit [NumberField M] [IsGalois K M] in
theorem isUnramifiedAt_inv_iff (ψ : (M ≃ₐ[K] M) →* ℂˣ) (v : HeightOneSpectrum (𝓞 K)) :
    IsUnramifiedAt ψ⁻¹ v ↔ IsUnramifiedAt ψ v := by
  simp [IsUnramifiedAt]

theorem localValue_inv (ψ : (M ≃ₐ[K] M) →* ℂˣ) (v : HeightOneSpectrum (𝓞 K)) :
    localValue ψ⁻¹ v = starRingEnd ℂ (localValue ψ v) := by
  unfold localValue
  rw [isUnramifiedAt_inv_iff]
  split_ifs
  · exact coe_inv_apply ψ _
  · simp

theorem idealValue_inv (ψ : (M ≃ₐ[K] M) →* ℂˣ) (I : Ideal (𝓞 K)) :
    idealValue ψ⁻¹ I = starRingEnd ℂ (idealValue ψ I) := by
  unfold idealValue
  rw [show starRingEnd ℂ (∏ᶠ v : HeightOneSpectrum (𝓞 K),
      localValue ψ v ^ (Associates.mk v.asIdeal).count (Associates.mk I).factors) =
      (starRingAut (R := ℂ)).toMulEquiv (∏ᶠ v : HeightOneSpectrum (𝓞 K),
      localValue ψ v ^ (Associates.mk v.asIdeal).count (Associates.mk I).factors) from rfl,
    MulEquiv.map_finprod]
  exact finprod_congr fun v => by
    rw [localValue_inv, map_pow]
    rfl

omit [IsGalois K M] in
theorem swanConductor_inv (ψ : (M ≃ₐ[K] M) →* ℂˣ) (v : HeightOneSpectrum (𝓞 K)) :
    swanConductor ψ⁻¹ v = swanConductor ψ v := by
  simp [swanConductor]

omit [IsGalois K M] in
theorem conductorExponent_inv (ψ : (M ≃ₐ[K] M) →* ℂˣ) (v : HeightOneSpectrum (𝓞 K)) :
    conductorExponent ψ⁻¹ v = conductorExponent ψ v := by
  rw [conductorExponent, conductorExponent, swanConductor_inv, isUnramifiedAt_inv_iff]

omit [IsGalois K M] in

theorem conductor_inv (ψ : (M ≃ₐ[K] M) →* ℂˣ) : conductor ψ⁻¹ = conductor ψ := by
  simp [conductor, conductorExponent_inv]

omit [NumberField K] [NumberField M] [IsGalois K M] in
theorem isPlusAt_inv_iff (ψ : (M ≃ₐ[K] M) →* ℂˣ) (v : InfinitePlace K) :
    IsPlusAt ψ⁻¹ v ↔ IsPlusAt ψ v := by
  simp [IsPlusAt]

omit [NumberField M] [IsGalois K M] in
theorem nPlus_inv (ψ : (M ≃ₐ[K] M) →* ℂˣ) : nPlus ψ⁻¹ = nPlus ψ := by
  simp [nPlus, isPlusAt_inv_iff]

omit [NumberField M] [IsGalois K M] in
theorem nMinus_inv (ψ : (M ≃ₐ[K] M) →* ℂˣ) : nMinus ψ⁻¹ = nMinus ψ := by
  rw [nMinus, nMinus, nPlus_inv]

theorem coeff_inv (ψ : (M ≃ₐ[K] M) →* ℂˣ) (n : ℕ) :
    coeff ψ⁻¹ n = starRingEnd ℂ (coeff ψ n) := by
  unfold coeff
  split_ifs
  · simp
  · rw [map_sum]
    exact Finset.sum_congr rfl fun I _ => idealValue_inv ψ I

end Basic

end ArtinL.Abelian

end


