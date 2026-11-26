-- Prove2me | Definitions.Def_ProEtale_Algebra_IntegralLocal
-- name    : ProEtale_Algebra_IntegralLocal
-- status  : Definition
-- author  : @Idealson
-- created : 2026-11-26T17:42:20.711498+00:00
-- url     : https://prove2.me/theorems/2c68236c-5022-4037-a118-a1da7bffc937
-- title:
--   Local rings and integral algebras over henselian local rings; locality of tensor products with purely inseparable residue extensions
-- statement:
--   This file collects lemmas on local rings and integral ring maps, used towards the statement that over a strictly henselian local ring a weakly étale local algebra is the ring itself (Stacks, Tag 097Z). For a local ring $R$ we write $\mathfrak m_R$ for its maximal ideal and $\kappa(R)$ for its residue field.
--
--   Principal results:
--   1. If $R$ is a henselian local ring and $S$ is an integral $R$-algebra which is an integral domain, then $S$ is a local ring.
--   2. A commutative ring whose prime spectrum is nonempty and has at most one point is local.
--   3. If $I \subseteq A$ is contained in the Jacobson radical of $A$ and $A/I$ is local, then $A$ is local.
--   4. If $R \to W$ is a local homomorphism of local rings, the composite $R \to W \to \kappa(W)$ sends every element of $\mathfrak m_R$ to $0$.
--   5. If $R \to S$ is a local, integral homomorphism of local rings, then the residue field extension $\kappa(S)/\kappa(R)$ is algebraic.
--   6. **(Stacks, Tag 092Y.)** Let $R \to S$ and $R \to T$ be local homomorphisms of local rings with $R \to S$ integral. If $\kappa(S)/\kappa(R)$ or $\kappa(T)/\kappa(R)$ is purely inseparable, then
--   $$ S \otimes_R T \text{ is a local ring.} $$
--   (The proof uses that, for a purely inseparable extension $L/\kappa(R)$ and an $R$-field $K$ killed by $\mathfrak m_R$, $L\otimes_R K$ has a one-point spectrum.)
--
--   **Formalization Note** In items 1, 5 and 6 all rings live in a single universe `u`. "Local homomorphism" is `IsLocalHom (algebraMap R S)`, integrality is `Algebra.IsIntegral R S`, and the residue field is `IsLocalRing.ResidueField`. The declarations are `IsLocalRing.of_henselianLocalRing_of_isIntegral_of_isDomain`, `IsLocalRing.of_nonempty_subsingleton_primeSpectrum`, `IsLocalRing.of_isLocalRing_quotient_of_le_jacobson` (hypothesis `I ≤ (⊥ : Ideal A).jacobson`), `IsLocalRing.algebraMap_residueField_eq_zero_of_mem_maximalIdeal`, `Algebra.IsAlgebraic.residueField_of_isIntegral` and `Algebra.isLocalRing_tensorProduct_of_isPurelyInseparable_residueField` (conclusion `IsLocalRing (S ⊗[R] T)`, the disjunctive hypothesis as an `∨`). The module docstring also lists results such as the decomposition of finite algebras over a henselian local ring, which are not part of this file.
-- source:
--   B. Bhatt, P. Scholze, The pro-étale topology for schemes, https://arxiv.org/abs/1309.1198 (v2, 17 Dec 2014); cited in the code: Stacks Project, Tag 097Z; Stacks Project, Tag 092Y. Lean source: idealson-nexources/proetale (fork of chrisflav/proetale by C. Merten, J. Jiang and contributors, Apache-2.0), commit 2983805, file Proetale/Algebra/IntegralLocal.lean (declarations needed by the transplanted proofs, unused ones removed).

/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib
import Mathlib.Algebra.Category.CommAlgCat.Basic
import Mathlib.Algebra.Category.CommAlgCat.FiniteType
import Mathlib.Algebra.Category.Ring.Colimits
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.Algebra.Category.Ring.FinitePresentation
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.CategoryTheory.Limits.Connected
import Mathlib.CategoryTheory.Limits.MorphismProperty
import Mathlib.CategoryTheory.MorphismProperty.Ind
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.Etale.StandardEtale
import Mathlib.RingTheory.Flat.EquationalCriterion
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Polynomial.UniversalFactorizationRing
import Mathlib.RingTheory.RingHom.Etale
import Mathlib.RingTheory.Smooth.NoetherianDescent
import Mathlib.RingTheory.Smooth.StandardSmoothOfFree
import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.RingTheory.Unramified.LocalStructure
import Definitions.Def_ProEtale_FiniteFields_Etale_AlgebraicHenselization
import Definitions.Def_ProEtale_FiniteFields_Etale_IndEtale
import Definitions.Def_ProEtale_FiniteFields_Etale_IndEtaleStructural
import Definitions.Def_ProEtale_Mathlib_FieldTheory_IsSepClosed
import Definitions.Def_ProEtale_Mathlib_RingTheory_Etale_Henselian
import Definitions.Def_ProEtale_Mathlib_RingTheory_Henselian
import Definitions.Def_ProEtale_Mathlib_RingTheory_Henselian_Lib

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option relaxedAutoImplicit false
/-!
# Local rings and integral algebras

This file collects miscellaneous lemmas relating local rings, integral ring
homomorphisms, and Henselian local rings.  These are used in the proof of
[Stacks 097Z](https://stacks.math.columbia.edu/tag/097Z) (over a strictly
Henselian local ring, a weakly étale local algebra is the ring itself).

## Main statements

* `HenselianLocalRing.exists_pi_of_finite` ([Stacks 04GH (1)]
  (https://stacks.math.columbia.edu/tag/04GH)):
  A finite algebra over a Henselian local ring decomposes as a finite product
  of Henselian local rings, each finite over the base.
* `HenselianLocalRing.exists_isIdempotentElem_sub_mem`: over a Henselian local ring `R`,
  idempotents lift modulo any ideal `J` of an integral `R`-algebra `S` with
  `𝔪_R S ≤ J ≤ √(𝔪_R S)`.
* `HenselianLocalRing.of_finite`: a local ring finite over a Henselian local ring is Henselian.
* `IsLocalRing.of_henselianLocalRing_of_isIntegral_of_isDomain`:
  An integral algebra over a Henselian local ring that is an integral domain is local.
* `Algebra.IsAlgebraic.residueField_of_isIntegral`:
  The residue field extension induced by a local integral homomorphism of local rings
  is algebraic.
* `Algebra.isLocalRing_tensorProduct_of_isPurelyInseparable_residueField`
  ([Stacks 092Y](https://stacks.math.columbia.edu/tag/092Y)):
  If `R → S` is local and integral and either `κ(S)/κ(R)` or `κ(T)/κ(R)` is purely
  inseparable, the tensor product `S ⊗[R] T` is a local ring.
-/

universe u

open TensorProduct


namespace IsLocalRing

open Polynomial

/-- An integral algebra over a Henselian local ring that is an integral domain is local. -/
theorem of_henselianLocalRing_of_isIntegral_of_isDomain
    {R S : Type u} [CommRing R] [CommRing S] [HenselianLocalRing R]
    [Algebra R S] [Algebra.IsIntegral R S] [IsDomain S] :
    IsLocalRing S := by
  classical
  refine of_isUnit_or_isUnit_one_sub_self fun a ↦ ?_
  by_contra hcon
  obtain ⟨ha, ha1⟩ := not_or.mp hcon
  -- There exists a monic annihilator of `a`; consider one of minimal degree.
  have hex : ∃ n : ℕ, ∃ F : R[X], F.Monic ∧ aeval a F = 0 ∧ F.natDegree = n := by
    obtain ⟨F, hFm, hFe⟩ := Algebra.IsIntegral.isIntegral (R := R) a
    exact ⟨F.natDegree, F, hFm, by rwa [aeval_def], rfl⟩
  obtain ⟨F, hFm, hFa, hFd⟩ := Nat.find_spec hex
  have hn0 : Nat.find hex ≠ 0 := by
    intro h0
    rw [h0] at hFd
    rw [hFm.natDegree_eq_zero.mp hFd, map_one] at hFa
    exact one_ne_zero hFa
  -- Both `F.eval 0` and `F.eval 1` lie in the maximal ideal of `R`.
  have hev (c : R) (hc : ¬IsUnit (a - algebraMap R S c)) : F.eval c ∈ maximalIdeal R := by
    by_contra hmem
    have hu : IsUnit (F.eval c) := by
      by_contra h2
      exact hmem ((mem_maximalIdeal _).mpr h2)
    obtain ⟨q, hq⟩ := X_sub_C_dvd_sub_C_eval (a := c) (p := F)
    have heq := congrArg (aeval a) hq
    rw [map_sub, hFa, aeval_C, zero_sub, map_mul, map_sub, aeval_X, aeval_C] at heq
    have hdvd : a - algebraMap R S c ∣ algebraMap R S (F.eval c) :=
      ⟨-aeval a q, by rw [mul_neg, ← heq, neg_neg]⟩
    exact hc (isUnit_of_dvd_unit hdvd (hu.map (algebraMap R S)))
  have h0 : F.eval 0 ∈ maximalIdeal R := hev 0 (by simpa using ha)
  have h1 : F.eval 1 ∈ maximalIdeal R := by
    refine hev 1 ?_
    rw [map_one, show a - 1 = -(1 - a) by ring, IsUnit.neg_iff]
    exact ha1
  -- Pass to the residue field and split off the root part at `0`.
  set κ := (maximalIdeal R).ResidueField
  set Fb := F.map (algebraMap R κ) with hFbdef
  have hFbm : Fb.Monic := hFm.map _
  have hFbdeg : Fb.natDegree = Nat.find hex := by rwa [hFbdef, hFm.natDegree_map]
  have hFb0 : Fb.eval 0 = 0 := by
    have hh : Fb.eval (algebraMap R κ 0) = algebraMap R κ (F.eval 0) := by
      rw [hFbdef, eval_map, eval₂_at_apply]
    rw [map_zero] at hh
    rwa [hh, Ideal.algebraMap_residueField_eq_zero]
  have hFb1 : Fb.eval 1 = 0 := by
    have hh : Fb.eval (algebraMap R κ 1) = algebraMap R κ (F.eval 1) := by
      rw [hFbdef, eval_map, eval₂_at_apply]
    rw [map_one] at hh
    rwa [hh, Ideal.algebraMap_residueField_eq_zero]
  have hFbne : Fb ≠ 0 := hFbm.ne_zero
  set ℓ := Fb.rootMultiplicity 0
  set gb := Fb /ₘ (X - C 0) ^ ℓ
  have hsplit : (X - C 0) ^ ℓ * gb = Fb := Fb.pow_mul_divByMonic_rootMultiplicity_eq 0
  have hXC : (X - C (0 : κ)) = X := by rw [map_zero, sub_zero]
  rw [hXC] at hsplit
  have hgbm : gb.Monic := (monic_X_pow ℓ).of_mul_monic_left (by rwa [hsplit])
  have hgb0 : gb.eval 0 ≠ 0 := eval_divByMonic_pow_rootMultiplicity_ne_zero 0 hFbne
  have hℓpos : 0 < ℓ := (rootMultiplicity_pos hFbne).mpr hFb0
  have hgb1 : gb.eval 1 = 0 := by
    have hh := congrArg (eval 1) hsplit
    rwa [eval_mul, eval_pow, eval_X, one_pow, one_mul, hFb1] at hh
  have hgbdeg : gb.natDegree ≠ 0 := by
    intro hdeg0
    rw [hgbm.natDegree_eq_zero.mp hdeg0] at hgb1
    simp at hgb1
  -- `X ^ ℓ` and `gb` are coprime.
  have hcoX : IsCoprime (X : κ[X]) gb := by
    have hXdvd : (X : κ[X]) ∣ gb - C (gb.eval 0) := by
      rw [X_dvd_iff]
      simp [coeff_zero_eq_eval_zero]
    obtain ⟨q, hq⟩ := hXdvd
    refine ⟨-(C (gb.eval 0)⁻¹ * q), C (gb.eval 0)⁻¹, ?_⟩
    have hsub : gb - X * q = C (gb.eval 0) := by
      rw [← hq]
      ring
    calc -(C (gb.eval 0)⁻¹ * q) * X + C (gb.eval 0)⁻¹ * gb
        = C (gb.eval 0)⁻¹ * (gb - X * q) := by ring
      _ = C (gb.eval 0)⁻¹ * C (gb.eval 0) := by rw [hsub]
      _ = 1 := by rw [← C_mul, inv_mul_cancel₀ hgb0, C_1]
  have hcop : IsCoprime ((X : κ[X]) ^ ℓ) gb := hcoX.pow_left
  -- Lift the factorization to `R` and contradict minimality.
  obtain ⟨p₁, p₂, hp₁m, hp₂m, hpe, hr₁, hr₂⟩ :=
    HenselianLocalRing.exists_monic_mul_of_map_eq_mul_of_isCoprime hFm (monic_X_pow ℓ) hgbm hsplit.symm hcop
  have hd₁ : p₁.natDegree = ℓ := by
    rw [← hp₁m.natDegree_map (algebraMap R κ), hr₁, natDegree_X_pow]
  have hd₂ : p₂.natDegree = gb.natDegree := by
    rw [← hp₂m.natDegree_map (algebraMap R κ), hr₂]
  have hsum : ℓ + gb.natDegree = Nat.find hex := by
    rw [← hFbdeg, ← hsplit, natDegree_mul (monic_X_pow ℓ).ne_zero hgbm.ne_zero, natDegree_X_pow]
  have hzero : aeval a p₁ * aeval a p₂ = 0 := by
    rw [← map_mul, ← hpe, hFa]
  rcases mul_eq_zero.mp hzero with hz | hz
  · exact Nat.find_min hex (m := p₁.natDegree) (by omega) ⟨p₁, hp₁m, hz, rfl⟩
  · exact Nat.find_min hex (m := p₂.natDegree) (by omega) ⟨p₂, hp₂m, hz, rfl⟩

/-- A commutative ring with nonempty and subsingleton prime spectrum is local. -/
theorem of_nonempty_subsingleton_primeSpectrum {A : Type*} [CommRing A]
    (h₁ : Nonempty (PrimeSpectrum A)) (h₂ : Subsingleton (PrimeSpectrum A)) :
    IsLocalRing A := by
  obtain ⟨p⟩ := h₁
  have : Nontrivial A :=
    ⟨0, 1, fun e ↦ p.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr (e ▸ p.asIdeal.zero_mem))⟩
  obtain ⟨m, hm⟩ := Ideal.exists_maximal A
  refine IsLocalRing.of_unique_max_ideal ⟨m, hm, fun J hJ ↦ ?_⟩
  exact congrArg PrimeSpectrum.asIdeal (h₂.elim ⟨J, hJ.isPrime⟩ ⟨m, hm.isPrime⟩)

/-- If the quotient `A ⧸ I` is local and `I` is contained in the Jacobson radical of `A`
(equivalently, `I` is contained in every maximal ideal of `A`), then `A` is local. -/
theorem of_isLocalRing_quotient_of_le_jacobson {A : Type*} [CommRing A] (I : Ideal A)
    [IsLocalRing (A ⧸ I)] (hI : I ≤ (⊥ : Ideal A).jacobson) : IsLocalRing A := by
  classical
  have : Nontrivial A := (Ideal.Quotient.mk I).domain_nontrivial
  -- every maximal ideal of `A` contains `I`, hence is the contraction of `𝔪_{A ⧸ I}`
  have key : ∀ Q : Ideal A, Q.IsMaximal →
      Q = (maximalIdeal (A ⧸ I)).comap (Ideal.Quotient.mk I) := by
    intro Q hQ
    have hIQ : I ≤ Q := hI.trans (sInf_le ⟨bot_le, hQ⟩)
    have hmapne : Q.map (Ideal.Quotient.mk I) ≠ ⊤ := by
      intro htop
      have hcm := Ideal.comap_map_of_surjective (Ideal.Quotient.mk I)
        Ideal.Quotient.mk_surjective Q
      rw [htop, Ideal.comap_top] at hcm
      have hker : Ideal.comap (Ideal.Quotient.mk I) ⊥ = I := Ideal.mk_ker
      rw [hker] at hcm
      exact hQ.ne_top (by rw [← sup_eq_left.mpr hIQ, ← hcm])
    have hQle : Q ≤ (maximalIdeal (A ⧸ I)).comap (Ideal.Quotient.mk I) :=
      Ideal.le_comap_map.trans (Ideal.comap_mono (IsLocalRing.le_maximalIdeal hmapne))
    exact hQ.eq_of_le (Ideal.comap_ne_top _ (IsLocalRing.maximalIdeal.isMaximal _).ne_top) hQle
  obtain ⟨M, hM⟩ := Ideal.exists_maximal A
  exact of_unique_max_ideal ⟨M, hM, fun J hJ ↦ by rw [key J hJ, key M hM]⟩

/-- For a local ring `W` with a local homomorphism `R → W` from a local ring `R`, the
composite `R → κ(W)` kills the maximal ideal of `R`. -/
theorem algebraMap_residueField_eq_zero_of_mem_maximalIdeal {R W : Type*} [CommRing R]
    [CommRing W] [IsLocalRing R] [Algebra R W] [IsLocalRing W] [IsLocalHom (algebraMap R W)]
    {x : R} (hx : x ∈ maximalIdeal R) : algebraMap R (ResidueField W) x = 0 := by
  rw [IsScalarTower.algebraMap_apply R W (ResidueField W), ResidueField.algebraMap_eq,
    IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  exact mem_nonunits_iff.mp ((IsLocalRing.mem_maximalIdeal x).mp hx) (IsLocalHom.map_nonunit x hu)

end IsLocalRing

namespace Algebra

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
  [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)]

/-- The residue field extension induced by a local integral homomorphism of local rings is
algebraic. -/
theorem IsAlgebraic.residueField_of_isIntegral [Algebra.IsIntegral R S] :
    Algebra.IsAlgebraic (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S) := by
  -- It suffices to show that `κ(S)` is integral over `R`: since `S` is integral over `R`
  -- and `κ(S)` is integral over `S` (the map `S → κ(S)` is surjective), the composition
  -- `R → S → κ(S)` is integral.  Integrality then descends along the surjection `R → κ(R)`,
  -- so `κ(S)` is integral, hence algebraic, over `κ(R)`.
  have : Algebra.IsIntegral S (IsLocalRing.ResidueField S) :=
    Algebra.isIntegral_of_surjective IsLocalRing.residue_surjective
  have : Algebra.IsIntegral R (IsLocalRing.ResidueField S) := Algebra.IsIntegral.trans S
  have : Algebra.IsIntegral (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S) :=
    Algebra.IsIntegral.tower_top R
  infer_instance

section TensorProduct

open IsLocalRing

/-- If `L` is a purely inseparable extension of the residue field of a local ring `R` and
`K` is an `R`-field killed by the maximal ideal, then `L ⊗[R] K` is a local ring. -/
private theorem isLocalRing_tensorProduct_of_isPurelyInseparable_left
    (R : Type u) [CommRing R] [IsLocalRing R]
    (L K : Type u) [Field L] [Field K] [Algebra R L] [Algebra R K]
    [Algebra (ResidueField R) L] [IsScalarTower R (ResidueField R) L]
    [IsPurelyInseparable (ResidueField R) L]
    (hK : ∀ x ∈ maximalIdeal R, algebraMap R K x = 0) :
    IsLocalRing (L ⊗[R] K) := by
  -- `κ(R) ⊗[R] K ≃ K` since `K` is killed by the maximal ideal.
  let u : ResidueField R →ₐ[R] K :=
    Ideal.Quotient.liftₐ (maximalIdeal R) (Algebra.ofId R K) hK
  let Φ : (ResidueField R) ⊗[R] K →ₐ[R] K := Algebra.TensorProduct.productMap u (AlgHom.id R K)
  have htmul : ∀ z : (ResidueField R) ⊗[R] K, ∃ x : K, z = 1 ⊗ₜ[R] x := by
    intro z
    induction z with
    | zero => exact ⟨0, (TensorProduct.tmul_zero _ _).symm⟩
    | tmul r x =>
      obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective r
      refine ⟨algebraMap R K r * x, ?_⟩
      rw [← ResidueField.algebraMap_eq, Algebra.algebraMap_eq_smul_one,
        TensorProduct.smul_tmul, Algebra.smul_def]
    | add z₁ z₂ h₁ h₂ =>
      obtain ⟨x₁, rfl⟩ := h₁
      obtain ⟨x₂, rfl⟩ := h₂
      exact ⟨x₁ + x₂, (TensorProduct.tmul_add _ _ _).symm⟩
  have hΦ : Function.Bijective Φ := by
    constructor
    · intro z w hzw
      obtain ⟨x, rfl⟩ := htmul z
      obtain ⟨y, rfl⟩ := htmul w
      obtain rfl : x = y := by simpa [Φ] using hzw
      rfl
    · intro x
      exact ⟨1 ⊗ₜ x, by simp [Φ]⟩
  let e : (ResidueField R) ⊗[R] K ≃ₐ[R] K := AlgEquiv.ofBijective Φ hΦ
  have h1 : IsHomeomorph (PrimeSpectrum.comap (Algebra.TensorProduct.map
      (Algebra.ofId (ResidueField R) L) (AlgHom.id R K)).toRingHom) :=
    PrimeSpectrum.isHomeomorph_comap_tensorProductMap_of_isPurelyInseparable
      (K := ResidueField R) (R := R) (S := K) L
  -- `Spec (κ(R) ⊗[R] K)` is a single point: it is homeomorphic to `Spec K`, which is one
  have hsub : Subsingleton (PrimeSpectrum ((ResidueField R) ⊗[R] K)) :=
    ((PrimeSpectrum.isHomeomorph_comap_of_bijective
      e.toRingEquiv.bijective).bijective.surjective).subsingleton
  have hne : Nonempty (PrimeSpectrum ((ResidueField R) ⊗[R] K)) := by
    obtain ⟨q⟩ : Nonempty (PrimeSpectrum K) := inferInstance
    exact ⟨PrimeSpectrum.comap (e.toRingEquiv : _ ≃+* K).toRingHom q⟩
  -- `Spec (L ⊗[R] K) ≅ Spec (κ(R) ⊗[R] K)` since `κ(R) → L` is purely inseparable
  refine IsLocalRing.of_nonempty_subsingleton_primeSpectrum ?_
    (h1.bijective.injective.subsingleton)
  obtain ⟨q⟩ := hne
  obtain ⟨p, -⟩ := h1.bijective.surjective q
  exact ⟨p⟩

variable (R S) in
private theorem isLocalRing_tensorProduct_aux
    (T : Type u) [CommRing T] [Algebra R T] [IsLocalRing T] [IsLocalHom (algebraMap R T)]
    [Algebra.IsIntegral R S]
    (h : IsPurelyInseparable (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S) ∨
        IsPurelyInseparable (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField T)) :
    IsLocalRing (T ⊗[R] S) := by
  classical
  -- the tensor product of the residue fields is local
  have hcase : IsLocalRing ((ResidueField T) ⊗[R] (ResidueField S)) := by
    rcases h with h | h
    · have := h
      have hloc : IsLocalRing ((ResidueField S) ⊗[R] (ResidueField T)) :=
        isLocalRing_tensorProduct_of_isPurelyInseparable_left R (ResidueField S)
          (ResidueField T) fun _ hx ↦
            IsLocalRing.algebraMap_residueField_eq_zero_of_mem_maximalIdeal (W := T) hx
      exact (Algebra.TensorProduct.comm R (ResidueField S)
        (ResidueField T)).toRingEquiv.isLocalRing
    · have := h
      exact isLocalRing_tensorProduct_of_isPurelyInseparable_left R (ResidueField T)
        (ResidueField S) fun _ hx ↦
          IsLocalRing.algebraMap_residueField_eq_zero_of_mem_maximalIdeal (W := S) hx
  -- the two distinguished ideals of the tensor product
  set A := T ⊗[R] S
  let inclS : S →ₐ[R] A := Algebra.TensorProduct.includeRight
  let J₂ : Ideal A := (maximalIdeal S).map inclS
  let J₁ : Ideal A := (maximalIdeal T).map (algebraMap T A)
  -- identify `A ⧸ (J₂ ⊔ J₁)` with `κ(T) ⊗[R] κ(S)`
  let e₁ : T ⊗[R] (ResidueField S) ≃ₐ[R] A ⧸ J₂ :=
    Algebra.TensorProduct.tensorQuotientEquiv R S T (maximalIdeal S)
  let I₁ : Ideal (T ⊗[R] (ResidueField S)) :=
    (maximalIdeal T).map (algebraMap T (T ⊗[R] (ResidueField S)))
  have hcomm : (e₁ : T ⊗[R] (ResidueField S) →+* A ⧸ J₂).comp
      (algebraMap T (T ⊗[R] (ResidueField S)))
      = (Ideal.Quotient.mk J₂).comp (algebraMap T A) := by
    ext t
    exact Algebra.TensorProduct.tensorQuotientEquiv_apply_tmul (R := R) R S T
      (maximalIdeal S) t 1
  have hIJ : J₁.map (Ideal.Quotient.mk J₂)
      = I₁.map (e₁ : T ⊗[R] (ResidueField S) →+* A ⧸ J₂) := by
    rw [Ideal.map_map, Ideal.map_map, hcomm]
  let E₂ : (T ⊗[R] (ResidueField S)) ⧸ I₁ ≃+* (A ⧸ J₂) ⧸ J₁.map (Ideal.Quotient.mk J₂) :=
    Ideal.quotientEquiv I₁ (J₁.map (Ideal.Quotient.mk J₂)) e₁.toRingEquiv hIJ
  let E₃ : (ResidueField T) ⊗[R] (ResidueField S) ≃ₐ[R] (T ⊗[R] (ResidueField S)) ⧸ I₁ :=
    Algebra.TensorProduct.quotientTensorEquiv R (ResidueField S) T (maximalIdeal T)
  let E : (ResidueField T) ⊗[R] (ResidueField S) ≃+* A ⧸ (J₂ ⊔ J₁) :=
    (E₃.toRingEquiv.trans E₂).trans (DoubleQuot.quotQuotEquivQuotSup J₂ J₁)
  have hQuot : IsLocalRing (A ⧸ (J₂ ⊔ J₁)) := E.isLocalRing
  -- every maximal ideal of `A` contains `J₂ ⊔ J₁`
  have hle : ∀ Q : Ideal A, Q.IsMaximal → J₂ ⊔ J₁ ≤ Q := by
    intro Q hQ
    have := hQ.isPrime
    have hT : Q.comap (algebraMap T A) = maximalIdeal T :=
      IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal Q)
    have hR : Q.comap (algebraMap R A) = maximalIdeal R := by
      rw [IsScalarTower.algebraMap_eq R T A, ← Ideal.comap_comap, hT,
        IsLocalRing.maximalIdeal_comap]
    have hScomap : (Q.comap inclS.toRingHom).comap (algebraMap R S) = maximalIdeal R := by
      have hcompS : inclS.toRingHom.comp (algebraMap R S) = algebraMap R A := by
        ext r
        exact inclS.commutes r
      rw [Ideal.comap_comap, hcompS, hR]
    have hSmax : (Q.comap inclS.toRingHom).IsMaximal := by
      refine Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := R)
        (Q.comap inclS.toRingHom) ?_
      rw [hScomap]
      exact IsLocalRing.maximalIdeal.isMaximal R
    have hS : Q.comap inclS.toRingHom = maximalIdeal S := IsLocalRing.eq_maximalIdeal hSmax
    exact sup_le (Ideal.map_le_iff_le_comap.mpr hS.ge) (Ideal.map_le_iff_le_comap.mpr hT.ge)
  -- conclude: `J₂ ⊔ J₁` is below every maximal ideal, and the quotient by it is local
  have := hQuot
  exact IsLocalRing.of_isLocalRing_quotient_of_le_jacobson (J₂ ⊔ J₁)
    (le_sInf fun Q hQ ↦ hle Q hQ.2)

variable (R S) in
/-- Let `R → S` and `R → T` be local ring homomorphisms of local rings, with `R → S`
integral.  If `κ(S)/κ(R)` or `κ(T)/κ(R)` is purely inseparable, the tensor product
`S ⊗[R] T` is a local ring.

[Stacks 092Y](https://stacks.math.columbia.edu/tag/092Y). -/
theorem isLocalRing_tensorProduct_of_isPurelyInseparable_residueField
    (T : Type u) [CommRing T] [Algebra R T] [IsLocalRing T] [IsLocalHom (algebraMap R T)]
    [Algebra.IsIntegral R S]
    (h : IsPurelyInseparable (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S) ∨
        IsPurelyInseparable (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField T)) :
    IsLocalRing (S ⊗[R] T) := by
  have := isLocalRing_tensorProduct_aux R S T h
  exact (Algebra.TensorProduct.comm R T S).toRingEquiv.isLocalRing

end TensorProduct

end Algebra


