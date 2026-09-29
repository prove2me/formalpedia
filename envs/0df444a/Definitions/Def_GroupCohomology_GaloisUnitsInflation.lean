-- Prove2me | Definitions.Def_GroupCohomology_GaloisUnitsInflation
-- name    : GroupCohomology_GaloisUnitsInflation
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:27.528425+00:00
-- url     : https://prove2.me/theorems/46af1cf3-feaf-501b-954e-6a4495ffcd14
-- title:
--   Inflation of 1- and 2-cochains of Galois units
-- statement:
--   Fix fields $K$ and $\Omega$ with $\Omega$ a $K$-algebra, and an intermediate field $L$ of $\Omega/K$ that is normal over $K$. Two maps are defined, both built from the restriction homomorphism $\mathrm{AlgEquiv.restrictNormalHom}\, L \colon (\Omega \simeq_K \Omega) \to (L \simeq_K L)$, $\sigma \mapsto \sigma|_L$, and from the map on unit groups $L^\times \to \Omega^\times$ induced by the structure map $\mathrm{algebraMap}\, L\, \Omega$.
--
--   The first, `unitsInflate₁ L`, sends a function $c$ on $L \simeq_K L$ with values in $\mathrm{Additive}\,L^\times$ to the function $\sigma \mapsto c(\sigma|_L)$ on $\Omega \simeq_K \Omega$ with values in $\mathrm{Additive}\,\Omega^\times$, the value being transported along $L^\times \to \Omega^\times$. The second, `unitsInflate₂ L`, does the same in two variables: a function $f$ on $(L \simeq_K L) \times (L \simeq_K L)$ is sent to $(\sigma,\tau) \mapsto f(\sigma|_L, \tau|_L)$, again with values pushed into $\mathrm{Additive}\,\Omega^\times$. Since the target groups are written additively while the maps on units are multiplicative, both are packaged as $\mathbb{Z}$-linear maps between the corresponding function spaces; thus they are maps of cochain groups in degrees $1$ and $2$ respectively, for the Galois actions on unit groups in Mathlib's additive notation, and no cocycle condition is imposed on the arguments.
--
--   The accompanying lemmas record the defining formulas: `unitsInflate₁_apply` and `unitsInflate₂_apply` give the values at $\sigma$ and at a pair $(\sigma,\tau)$, and `coe_toMul_unitsInflate₁`, `coe_toMul_unitsInflate₂` say that the underlying element of $\Omega$ of an inflated value is the image in $\Omega$ of the underlying element of $L$ of the original value.
--
--   **Relation to Mathlib.** Mathlib supplies the ingredients — `AlgEquiv.restrictNormalHom`, `Units.map`, `Additive` — and inflation maps for group cohomology in general, but these two explicit cochain-level inflation maps for Galois actions on unit groups are the project's own.
--
--   **Where it is used.** The pair consisting of restriction of automorphisms and inclusion of unit groups is compatible with the Galois actions, so these maps carry cocycles to cocycles and induce inflation on cohomology; they are the cochain-level input to the comparison between $H^2(\mathrm{Gal}(L/K), L^\times)$ for finite normal $L/K$ and the continuous second cohomology of $\mathrm{Gal}(\Omega/K)$ with values in $\Omega^\times$, i.e. to the description of the Brauer group of $K$ as a union of relative Brauer groups.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_GroupCohomology_GaloisUnitsInflation.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

namespace groupCohomology

variable {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω] (L : IntermediateField K Ω) [Normal K L]

noncomputable def unitsInflate₁ : ((L ≃ₐ[K] L) → Additive (L)ˣ) →ₗ[ℤ] ((Ω ≃ₐ[K] Ω) → Additive Ωˣ) where
  toFun c σ := Additive.ofMul
    (Units.map (algebraMap L Ω).toMonoidHom (Additive.toMul (c (AlgEquiv.restrictNormalHom L σ))))
  map_add' c c' := by
    funext σ; simp only [RingHom.toMonoidHom_eq_coe, Pi.add_apply, toMul_add, map_mul, ofMul_mul]
  map_smul' n c := by
    funext σ
    simp only [RingHom.toMonoidHom_eq_coe, Pi.smul_apply, toMul_zsmul, map_zpow, ofMul_zpow, eq_intCast, Int.cast_eq]

noncomputable def unitsInflate₂ :
    ((L ≃ₐ[K] L) × (L ≃ₐ[K] L) → Additive (L)ˣ) →ₗ[ℤ] ((Ω ≃ₐ[K] Ω) × (Ω ≃ₐ[K] Ω) → Additive Ωˣ) where
  toFun f p := Additive.ofMul
    (Units.map (algebraMap L Ω).toMonoidHom
      (Additive.toMul (f (AlgEquiv.restrictNormalHom L p.1, AlgEquiv.restrictNormalHom L p.2))))
  map_add' f f' := by
    funext p; simp only [RingHom.toMonoidHom_eq_coe, Pi.add_apply, toMul_add, map_mul, ofMul_mul]
  map_smul' n f := by
    funext p
    simp only [RingHom.toMonoidHom_eq_coe, Pi.smul_apply, toMul_zsmul, map_zpow, ofMul_zpow, eq_intCast, Int.cast_eq]

@[simp] lemma unitsInflate₁_apply (c : (L ≃ₐ[K] L) → Additive (L)ˣ) (σ : Ω ≃ₐ[K] Ω) :
    unitsInflate₁ L c σ = Additive.ofMul
      (Units.map (algebraMap L Ω).toMonoidHom (Additive.toMul (c (AlgEquiv.restrictNormalHom L σ)))) :=
  rfl

@[simp] lemma unitsInflate₂_apply (f : (L ≃ₐ[K] L) × (L ≃ₐ[K] L) → Additive (L)ˣ) (σ τ : Ω ≃ₐ[K] Ω) :
    unitsInflate₂ L f (σ, τ) = Additive.ofMul
      (Units.map (algebraMap L Ω).toMonoidHom
        (Additive.toMul (f (AlgEquiv.restrictNormalHom L σ, AlgEquiv.restrictNormalHom L τ)))) :=
  rfl

lemma coe_toMul_unitsInflate₁ (c : (L ≃ₐ[K] L) → Additive (L)ˣ) (σ : Ω ≃ₐ[K] Ω) :
    ((Additive.toMul (unitsInflate₁ L c σ) : Ωˣ) : Ω)
      = ((Additive.toMul (c (AlgEquiv.restrictNormalHom L σ)) : (L)ˣ) : L) :=
  rfl

lemma coe_toMul_unitsInflate₂ (f : (L ≃ₐ[K] L) × (L ≃ₐ[K] L) → Additive (L)ˣ) (σ τ : Ω ≃ₐ[K] Ω) :
    ((Additive.toMul (unitsInflate₂ L f (σ, τ)) : Ωˣ) : Ω)
      = ((Additive.toMul (f (AlgEquiv.restrictNormalHom L σ, AlgEquiv.restrictNormalHom L τ)) : (L)ˣ) : L) :=
  rfl

end groupCohomology


