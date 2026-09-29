-- Prove2me | Definitions.Def_GaloisRep_Twist
-- name    : GaloisRep_Twist
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:27.528425+00:00
-- url     : https://prove2.me/theorems/f3c5cb5b-3741-5a3e-8bde-97daa6dc537f
-- title:
--   Twisting adic Galois representations by a character
-- statement:
--   Throughout, $A$ is a commutative local ring with maximal ideal $\mathfrak m$ and residue field $A/\mathfrak m$, and $G = \operatorname{Aut}_{\mathbb Q}(\overline{\mathbb Q})$ is the automorphism group of a fixed algebraic closure of $\mathbb Q$. The predicate [`GaloisCharIsAdicContinuous A χ`](../def/GaloisRep_Twist.html#L5), for a monoid homomorphism $\chi : G \to A^\times$, asserts: for every $n$ there is an intermediate field $L$ of $\overline{\mathbb Q}/\mathbb Q$, finite-dimensional over $\mathbb Q$, such that $\chi(\sigma) - 1 \in \mathfrak m^n$ for every $\sigma$ fixing $L$ pointwise. The helper `galoisCharIsAdicContinuous_of_finiteLevel` records that a character which is outright trivial on the pointwise stabiliser of some such $L$ satisfies this. For an adic representation $\rho$ — a free $A$-module $V$ with $\operatorname{rank} 2$ and a homomorphism $G \to \operatorname{End}_A V$ whose orbits are $\mathfrak m$-adically continuous in the sense that, for each $n$, $\rho(\sigma)v - v \in \mathfrak m^n \cdot V$ for all $\sigma$ fixing a suitable finite $L$ — the twist `twist ρ χ hχ` is the adic representation on the same module $V$, with the same rank datum, in which $\sigma$ acts by the scalar multiple $\chi(\sigma)\,\rho(\sigma)$; adic continuity is inherited using the compositum of the two fields produced for $\rho$ and $\chi$. The remaining declarations are computations with this construction: the underlying module and the formula for the action, $\operatorname{tr}(\rho\otimes\chi)(\sigma) = \chi(\sigma)\operatorname{tr}\rho(\sigma)$, $\det(\rho\otimes\chi)(\sigma) = \chi(\sigma)^2 \det \rho(\sigma)$ (rank $2$ entering), and, when every $\chi(\sigma)$ has residue $1$, an explicit equivalence `residualTwistEquiv` of residual representations over $A/\mathfrak m$ whose underlying linear map is the identity of $(A/\mathfrak m)\otimes_A V$, together with the resulting `IsEquiv`. Finally, if $\chi$ is trivial on the inertia subgroups attached to all valuation subrings of $\overline{\mathbb Q}$ lying over a prime $q$, then unramifiedness at $q$, unipotence of inertia at $q$ (the characteristic polynomial of inertia being $(X-1)^2$), and strict ordinarity at $p$ — a decomposition-stable free rank-one line $L$ with inertia acting trivially modulo $L$ and the congruences $x - a z \in (p^n)$ for the scalars on $L$ and modulo $L$ — transfer from $\rho$ to $\rho\otimes\chi$.
--
--   **Relation to Mathlib.** Mathlib has no notion of two-dimensional adic or residual Galois representation; [`GaloisRepAdic`](../def/GaloisRep_Adic.html#L16), the adic continuity predicates and this twisting construction are the project's own, built over Mathlib's local-ring, residue-field, valuation-subring and base-change APIs.
--
--   **Where it is used.** Twisting by a character is used where the deformation-theoretic arguments require adjusting a lift by a character (for instance to normalise a determinant or nebentypus) without changing the residual representation, and the transfer lemmas ensure that the local conditions — unramified outside a finite set, unipotent inertia, strict ordinarity at $p$ — defining the relevant deformation problem are preserved.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_GaloisRep_Twist.lean

import Definitions.Def_GaloisRep_StrictOrdinary

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

def GaloisCharIsAdicContinuous (A : Type) [CommRing A] [IsLocalRing A]
    (χ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Aˣ) : Prop :=
  ∀ n : ℕ, ∃ L : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ L ∧
    ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, (∀ x ∈ L, σ x = x) →
      ((χ σ : Aˣ) : A) - 1 ∈ IsLocalRing.maximalIdeal A ^ n

namespace GaloisRepAdic

variable {A : Type} [CommRing A] [IsLocalRing A]

theorem galoisCharIsAdicContinuous_of_finiteLevel
    (χ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Aˣ)
    (h : ∃ L : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ L ∧
      ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, (∀ x ∈ L, σ x = x) → χ σ = 1) :
    GaloisCharIsAdicContinuous A χ := by
  intro n
  obtain ⟨L, hL, hχ⟩ := h
  refine ⟨L, hL, fun σ hσ => ?_⟩
  rw [hχ σ hσ, Units.val_one, sub_self]
  exact Submodule.zero_mem _

@[reducible] noncomputable def twist (ρ : GaloisRepAdic A)
    (χ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Aˣ)
    (hχ : GaloisCharIsAdicContinuous A χ) : GaloisRepAdic A where
  V := ρ.V
  finrank_eq := ρ.finrank_eq
  ρ := { toFun := fun σ => ((χ σ : Aˣ) : A) • ρ.ρ σ
         map_one' := by rw [map_one, map_one, Units.val_one, one_smul]
         map_mul' := fun σ τ => by
           rw [map_mul, map_mul, Units.val_mul, mul_smul, smul_mul_assoc, mul_smul_comm] }
  isAdicContinuous := by
    intro n
    obtain ⟨L₁, hL₁, h₁⟩ := ρ.isAdicContinuous n
    obtain ⟨L₂, hL₂, h₂⟩ := hχ n
    haveI := hL₁
    haveI := hL₂
    refine ⟨L₁ ⊔ L₂, IntermediateField.finiteDimensional_sup L₁ L₂, fun σ hσ v => ?_⟩
    have hσ₁ : ∀ x ∈ L₁, σ x = x := fun x hx => hσ x ((le_sup_left : L₁ ≤ L₁ ⊔ L₂) hx)
    have hσ₂ : ∀ x ∈ L₂, σ x = x := fun x hx => hσ x ((le_sup_right : L₂ ≤ L₁ ⊔ L₂) hx)
    have hsplit : ((χ σ : Aˣ) : A) • ρ.ρ σ v - v =
        ((χ σ : Aˣ) : A) • (ρ.ρ σ v - v) + (((χ σ : Aˣ) : A) - 1) • v := by
      rw [smul_sub, sub_smul, one_smul, sub_add_sub_cancel]
    show ((χ σ : Aˣ) : A) • ρ.ρ σ v - v ∈ _
    rw [hsplit]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ (h₁ σ hσ₁ v))
      (Submodule.smul_mem_smul (h₂ σ hσ₂) Submodule.mem_top)

variable (ρ : GaloisRepAdic A) (χ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Aˣ)
  (hχ : GaloisCharIsAdicContinuous A χ)

theorem twist_V : (ρ.twist χ hχ).V = ρ.V := rfl

theorem twist_ρ_apply (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    (ρ.twist χ hχ).ρ σ = ((χ σ : Aˣ) : A) • ρ.ρ σ := rfl

theorem twist_ρ_apply_apply (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (v : ρ.V) :
    (ρ.twist χ hχ).ρ σ v = ((χ σ : Aˣ) : A) • ρ.ρ σ v := rfl

theorem trace_twist (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    (ρ.twist χ hχ).trace σ = ((χ σ : Aˣ) : A) * ρ.trace σ := by
  show LinearMap.trace A ρ.V (((χ σ : Aˣ) : A) • ρ.ρ σ) = _
  rw [map_smul, smul_eq_mul]
  rfl

theorem det_twist_ρ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    LinearMap.det ((ρ.twist χ hχ).ρ σ) = ((χ σ : Aˣ) : A) ^ 2 * LinearMap.det (ρ.ρ σ) := by
  show LinearMap.det (((χ σ : Aˣ) : A) • ρ.ρ σ) = _
  rw [LinearMap.det_smul, ρ.finrank_eq]

noncomputable def residualTwistEquiv
    (h1 : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      IsLocalRing.residue A ((χ σ : Aˣ) : A) = 1) :
    ResidualGaloisRep.Equiv (ρ.twist χ hχ).residual ρ.residual where
  toLinearEquiv := LinearEquiv.refl _ _
  map_apply σ x := by
    show ((((χ σ : Aˣ) : A) • ρ.ρ σ).baseChange (IsLocalRing.ResidueField A)) x =
      ((ρ.ρ σ).baseChange (IsLocalRing.ResidueField A)) x
    rw [LinearMap.baseChange_smul, LinearMap.smul_apply,
      ← algebraMap_smul (IsLocalRing.ResidueField A) ((χ σ : Aˣ) : A),
      IsLocalRing.ResidueField.algebraMap_eq, h1 σ, one_smul]

theorem residual_twist_isEquiv
    (h1 : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      IsLocalRing.residue A ((χ σ : Aˣ) : A) = 1) :
    (ρ.twist χ hχ).residual.IsEquiv ρ.residual :=
  ⟨residualTwistEquiv ρ χ hχ h1⟩

theorem isUnramifiedAt_twist {q : ℕ}
    (hq : ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime q →
      ∀ σ ∈ P.inertiaSubgroupIn ℚ, χ σ = 1)
    (h : ρ.IsUnramifiedAt q) : (ρ.twist χ hχ).IsUnramifiedAt q := by
  intro P hP σ hσ
  rw [twist_ρ_apply, hq P hP σ hσ, Units.val_one, one_smul]
  exact h P hP σ hσ

theorem isUnipotentOnInertiaAt_twist {q : ℕ}
    (hq : ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime q →
      ∀ σ ∈ P.inertiaSubgroupIn ℚ, χ σ = 1)
    (h : ρ.IsUnipotentOnInertiaAt q) : (ρ.twist χ hχ).IsUnipotentOnInertiaAt q := by
  intro P hP σ hσ
  have e : (ρ.twist χ hχ).ρ σ = ρ.ρ σ := by
    rw [twist_ρ_apply, hq P hP σ hσ, Units.val_one, one_smul]
  rw [e]
  exact h P hP σ hσ

theorem isStrictOrdinaryAt_twist {p : ℕ}
    (hp : ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime p →
      ∀ σ ∈ P.inertiaSubgroupIn ℚ, χ σ = 1)
    (h : ρ.IsStrictOrdinaryAt p) : (ρ.twist χ hχ).IsStrictOrdinaryAt p := by
  refine ⟨h.1, fun P hP => ?_⟩
  obtain ⟨L, hb, hD, hI, hsc⟩ := h.2 P hP
  refine ⟨L, hb, ?_, ?_, ?_⟩
  · intro σ hσ v hv
    rw [twist_ρ_apply_apply]
    exact L.smul_mem _ (hD σ hσ v hv)
  · intro σ hσ v
    rw [twist_ρ_apply_apply, hp P hP σ hσ, Units.val_one, one_smul]
    exact hI σ hσ v
  · intro σ hσ
    obtain ⟨x, z, hx, hz, hxz⟩ := hsc σ hσ
    refine ⟨((χ σ : Aˣ) : A) * x, ((χ σ : Aˣ) : A) * z, ?_, ?_, ?_⟩
    · intro w hw
      rw [twist_ρ_apply_apply, hx w hw, smul_smul]
    · intro v
      have e : (ρ.twist χ hχ).ρ σ v - (((χ σ : Aˣ) : A) * z) • v =
          ((χ σ : Aˣ) : A) • (ρ.ρ σ v - z • v) := by
        rw [twist_ρ_apply_apply, smul_sub, smul_smul]
      rw [e]
      exact L.smul_mem _ (hz v)
    · intro n a ha
      have e : ((χ σ : Aˣ) : A) * x - (a : A) * (((χ σ : Aˣ) : A) * z) =
          ((χ σ : Aˣ) : A) * (x - (a : A) * z) := by ring
      rw [e]
      exact Ideal.mul_mem_left _ _ (hxz n a ha)

end GaloisRepAdic


