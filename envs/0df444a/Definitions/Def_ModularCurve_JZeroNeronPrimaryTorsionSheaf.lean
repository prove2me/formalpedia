-- Prove2me | Definitions.Def_ModularCurve_JZeroNeronPrimaryTorsionSheaf
-- name    : ModularCurve_JZeroNeronPrimaryTorsionSheaf
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.712661+00:00
-- url     : https://prove2.me/theorems/4cb587cf-3278-560c-9a2c-d14f428d56b2
-- title:
--   Eisenstein-primary qm-torsion fppf sheaf data for J0​(p)
-- statement:
--   Fix primes $p$ and $q$. The Eisenstein maximal ideal $\mathfrak P=\mathrm{eisensteinMaximalIdeal}\,p\,q$, the preimage under the Eisenstein character $\mathrm{eisensteinEval}\,p:\mathbb T\to\mathbb Z$ of $(q)$, is recorded as a prime ideal of the Hecke algebra. Two subgroups of `JZero p`, taken with the Hecke-module structure `heckeModuleBar p`, are introduced: `eisensteinPrimaryTorsionBar p q m`, the intersection of the kernel of multiplication by $q^m$ with the supremum over $k$ of the $\mathfrak P^k$-torsion submodules, and `toricEisensteinPrimaryPart p q A hA m`, its intersection with `jZeroToricTorsion p A (q^m)`. A lemma records that the $\mathfrak P^m$-torsion submodule lies in the former, since $q^m\in\mathfrak P^m$. Finally `eisensteinQuotientRationalLocalized p q` is the localisation at $\mathbb T\setminus\mathfrak P$ of the $\mathbb T$-span of the rational classes `eisensteinQuotientRational` in the Eisenstein quotient.
--
--   The structure `JZeroNeronPrimaryTorsionCore p q A hA`, for a valuation subring $A$ of $\overline{\mathbb Q}$ over $p$, packages: abelian sheaves $\mathcal J_m$ on the small fppf site of $\operatorname{Spec}\mathbb Z$; commutative $\mathbb Z$-Hopf algebras $H_m$, flat and of finite type, whose localisations at primes $\ell\neq p$ are finite; additive identifications, natural in $U$, of $\mathcal J_m(U)$ with the convolution group of $\mathbb Z$-algebra maps $H_m\to\Gamma(U,\mathcal O)$; bijections of the convolution groups of $\overline{\mathbb Q}$- and $A$-points of $H_m$ with `eisensteinPrimaryTorsionBar` and `toricEisensteinPrimaryPart`, additive, Galois-equivariant and mutually compatible; maps $\mathcal J_m\to\mathcal J_{m+1}\to Q_m$ forming short exact sequences; and a `JKummerRow q m` over the localised module above whose $H^1_{Jtors}$ term is identified with $H^1$ of $\mathcal J_m$ on the fppf site. `JZeroNeronPrimaryTorsionFFModels` adds finite flat Hopf-algebra models over the localisations $\mathbb Z_{(\ell)}$, $\ell\neq p$, with the same point identifications, together with their reductions modulo $q$ when $q\neq p$. `JZeroNeronPrimaryTorsionInvPins` pins the orders of $H^0$, $H^1$, the index of the toric part and the number of $\overline{\mathbb F_q}$-points as explicit powers of $q$ given by `AdmissibleInvariants q`. The three are bundled as `JZeroNeronPrimaryTorsionSheaf`, and `HasJZeroNeronPrimaryTorsionSheaf p q` asserts such data exist for every $A$ over $p$.
--
--   **Relation to Mathlib.** The small fppf site, sheaves of abelian groups on it and their cohomology are taken from Mathlib (via `Sheaf.H`), as are `Submodule.torsionBySet`, `LocalizedModule`, `HopfAlgebra` and `ShortComplex.ShortExact`; the Eisenstein maximal ideal, the primary-torsion subgroups and all of the Néron torsion-sheaf structures are the project's own.
--
--   **Where it is used.** These structures axiomatise the $\mathfrak P$-primary part of the $q^m$-torsion of the Néron model of $J_0(p)$ together with its finite flat models and the associated Kummer row, the data on which Mazur's Eisenstein-ideal analysis of rational points of $X_0(p)$ rests. The resulting control of torsion feeds the statement [`MazurStepThree`](../def/ModularCurve_MazurStepThree.html#L8) about rational $p$-torsion on integral Weierstrass curves, which is used for the Frey curve attached to a putative solution of Fermat's equation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_ModularCurve_JZeroNeronPrimaryTorsionSheaf.lean

import Mathlib
import Definitions.Def_ModularCurve_JZeroNeronDataPrime
import Definitions.Def_ModularCurve_EisensteinIdeal
import Definitions.Def_ModularCurve_FppfKummerInterface
import Definitions.Def_ModularCurve_MazurStepThreeInputs
import Definitions.Def_AlgebraicGeometry_FppfSiteCohomology
import Definitions.Def_AlgebraicGeometry_FppfCohomologyLES
import Definitions.Def_AlgebraicGeometry_FppfKummerProp17
import Definitions.Def_ModularCurve_JZeroToricTorsion

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

namespace ModularCurve

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme ValuationSubring Opposite

instance eisensteinMaximalIdeal.isPrime (N q : ℕ) [Fact q.Prime] :
    (eisensteinMaximalIdeal N q).IsPrime := by
  have hq : Prime (q : ℤ) := Nat.prime_iff_prime_int.mp Fact.out
  haveI : (Ideal.span {(q : ℤ)}).IsPrime := (Ideal.span_singleton_prime hq.ne_zero).mpr hq
  exact Ideal.IsPrime.comap _

abbrev eisensteinPrimaryTorsionBar (p q m : ℕ) [NeZero p] : AddSubgroup (JZero p) :=
  letI := heckeModuleBar p
  (AddMonoidHom.ker ((q ^ m : ℤ) • AddMonoidHom.id (JZero p))) ⊓
    ⨆ k : ℕ, (Submodule.torsionBySet HeckeAlg (JZero p)
      (↑((eisensteinMaximalIdeal p q) ^ k) : Set HeckeAlg)).toAddSubgroup

abbrev toricEisensteinPrimaryPart (p q : ℕ) [Fact p.Prime]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (_hA : A.LiesOverPrime p) (m : ℕ) :
    AddSubgroup (JZero p) :=
  jZeroToricTorsion p A (q ^ m) ⊓ eisensteinPrimaryTorsionBar p q m

abbrev eisensteinQuotientRationalLocalized (p q : ℕ) [NeZero p] [Fact q.Prime] : Type :=
  letI := heckeModuleBar p
  LocalizedModule (eisensteinMaximalIdeal p q).primeCompl
    ↥(Submodule.span HeckeAlg (eisensteinQuotientRational p (heckeModuleBar p)))

theorem torsionBySet_eisensteinMaximalIdeal_pow_le_eisensteinPrimaryTorsionBar
    (p q m : ℕ) [NeZero p] :
    letI := heckeModuleBar p
    (Submodule.torsionBySet HeckeAlg (JZero p)
      (↑((eisensteinMaximalIdeal p q) ^ m) : Set HeckeAlg)).toAddSubgroup
      ≤ eisensteinPrimaryTorsionBar p q m := by
  letI := heckeModuleBar p
  intro x hx
  refine ⟨?_, ?_⟩
  · have hq : ((q : HeckeAlg) ^ m) ∈ (eisensteinMaximalIdeal p q) ^ m := by
      apply Ideal.pow_mem_pow
      simp [eisensteinMaximalIdeal, Ideal.mem_comap]
    have hx' : ((q : HeckeAlg) ^ m) • x = 0 := (Submodule.mem_torsionBySet_iff _ _).mp hx ⟨_, hq⟩
    change ((q : ℤ) ^ m) • x = 0
    rw [← Int.cast_smul_eq_zsmul HeckeAlg]
    simpa [Int.cast_pow, Int.cast_natCast] using hx'
  · exact AddSubgroup.mem_iSup_of_mem m hx

structure JZeroNeronPrimaryTorsionCore (p q : ℕ) [Fact p.Prime] [Fact q.Prime]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p) where
  𝒥 : ℕ → Sheaf (smallFppfTopology specInt) Ab.{1}
  H : ℕ → Type
  [instCommRing_H : ∀ m, CommRing (H m)]
  [instHopfAlgebra_H : ∀ m, HopfAlgebra ℤ (H m)]
  [instFiniteType_H : ∀ m, Algebra.FiniteType ℤ (H m)]
  [instFlat_H : ∀ m, Module.Flat ℤ (H m)]
  ff_finite : ∀ (m ℓ : ℕ), ℓ.Prime → ℓ ≠ p →
    Module.Finite (GaloisRep.ratLocalizedAt ℓ) (TensorProduct ℤ (GaloisRep.ratLocalizedAt ℓ) (H m))
  sectionsEquiv : ∀ (m : ℕ) (U : specInt.Fppf),
    (𝒥 m).1.obj (op U) ≃+ Additive (WithConv (H m →ₐ[ℤ] Γ(U.left, ⊤)))
  sectionsNat : ∀ (m : ℕ) {U V : specInt.Fppf} (f : U ⟶ V) (s : (𝒥 m).1.obj (op V)),
    ∀ h : H m,
      (Additive.toMul (sectionsEquiv m U ((𝒥 m).1.map f.op s))) h
        = (Scheme.Γ.map f.left.op) ((Additive.toMul (sectionsEquiv m V s)) h)
  genericPoints : ∀ m, WithConv (H m →ₐ[ℤ] AlgebraicClosure ℚ) ≃ ↥(eisensteinPrimaryTorsionBar p q m)
  genericConv : ∀ m, ∀ f g : WithConv (H m →ₐ[ℤ] AlgebraicClosure ℚ),
    genericPoints m (f * g) = genericPoints m f + genericPoints m g
  genericGalois : ∀ m, ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
    ∀ f g : WithConv (H m →ₐ[ℤ] AlgebraicClosure ℚ),
    (∀ h : H m, g h = σ (f h)) →
    ((genericPoints m g : ↥(eisensteinPrimaryTorsionBar p q m)) : JZero p)
      = σ • ((genericPoints m f : ↥(eisensteinPrimaryTorsionBar p q m)) : JZero p)
  Q : ℕ → Sheaf (smallFppfTopology specInt) Ab.{1}
  incl : ∀ m, 𝒥 m ⟶ 𝒥 (m + 1)
  proj : ∀ m, 𝒥 (m + 1) ⟶ Q m
  incl_proj : ∀ m, incl m ≫ proj m = 0
  ses_shortExact : ∀ m, (ShortComplex.mk (incl m) (proj m) (incl_proj m)).ShortExact
  pFibrePoints : ∀ m, WithConv (H m →ₐ[ℤ] ↥A) ≃ ↥(toricEisensteinPrimaryPart p q A hA m)
  pFibreConv : ∀ m, ∀ f g : WithConv (H m →ₐ[ℤ] ↥A),
    pFibrePoints m (f * g) = pFibrePoints m f + pFibrePoints m g
  pFibreGenericCompat : ∀ m, ∀ φ : WithConv (H m →ₐ[ℤ] ↥A),
    ∀ ψ : WithConv (H m →ₐ[ℤ] AlgebraicClosure ℚ),
    (∀ h : H m, ψ h = A.subtype (φ h)) →
    ((pFibrePoints m φ : ↥(toricEisensteinPrimaryPart p q A hA m)) : JZero p)
      = ((genericPoints m ψ : ↥(eisensteinPrimaryTorsionBar p q m)) : JZero p)

  kummerRow : ∀ m, JKummerRow q m (eisensteinQuotientRationalLocalized p q)

  kummerRow_H1Jtors : ∀ m,
    letI := (kummerRow m).instH1Jtors;
    (kummerRow m).H1Jtors ≃+ fppfCohomology specInt (𝒥 m) 1

attribute [instance] JZeroNeronPrimaryTorsionCore.instCommRing_H
  JZeroNeronPrimaryTorsionCore.instHopfAlgebra_H
  JZeroNeronPrimaryTorsionCore.instFiniteType_H JZeroNeronPrimaryTorsionCore.instFlat_H

structure JZeroNeronPrimaryTorsionFFModels (p q : ℕ) [Fact p.Prime] [Fact q.Prime]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (C : JZeroNeronPrimaryTorsionCore p q A hA) where
  Hff : ∀ (_m : ℕ) (ℓ : ℕ), ℓ.Prime → ℓ ≠ p → Type
  [instCommRing_Hff : ∀ m ℓ hℓ hℓp, CommRing (Hff m ℓ hℓ hℓp)]
  [instHopfAlgebra_Hff : ∀ m ℓ hℓ hℓp, HopfAlgebra (GaloisRep.ratLocalizedAt ℓ) (Hff m ℓ hℓ hℓp)]
  [instFinite_Hff : ∀ m ℓ hℓ hℓp, Module.Finite (GaloisRep.ratLocalizedAt ℓ) (Hff m ℓ hℓ hℓp)]
  [instFlat_Hff : ∀ m ℓ hℓ hℓp, Module.Flat (GaloisRep.ratLocalizedAt ℓ) (Hff m ℓ hℓ hℓp)]
  [instCocomm_Hff : ∀ m ℓ hℓ hℓp, Coalgebra.IsCocomm (GaloisRep.ratLocalizedAt ℓ) (Hff m ℓ hℓ hℓp)]
  ffPoints : ∀ m ℓ hℓ hℓp, WithConv (Hff m ℓ hℓ hℓp →ₐ[GaloisRep.ratLocalizedAt ℓ] AlgebraicClosure ℚ)
    ≃ ↥(eisensteinPrimaryTorsionBar p q m)
  ffConv : ∀ m ℓ hℓ hℓp, ∀ f g, ffPoints m ℓ hℓ hℓp (f * g)
    = ffPoints m ℓ hℓ hℓp f + ffPoints m ℓ hℓ hℓp g
  ffGalois : ∀ m ℓ hℓ hℓp, ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
    ∀ f g : WithConv (Hff m ℓ hℓ hℓp →ₐ[GaloisRep.ratLocalizedAt ℓ] AlgebraicClosure ℚ),
    (∀ h, g h = σ (f h)) →
    ((ffPoints m ℓ hℓ hℓp g : ↥(eisensteinPrimaryTorsionBar p q m)) : JZero p)
      = σ • ((ffPoints m ℓ hℓ hℓp f : ↥(eisensteinPrimaryTorsionBar p q m)) : JZero p)
  HffBarQ : ∀ (_m : ℕ), q ≠ p → Type
  [instCommRing_HffBarQ : ∀ m hqp, CommRing (HffBarQ m hqp)]
  [instHopfAlgebra_HffBarQ : ∀ m hqp, HopfAlgebra (ZMod q) (HffBarQ m hqp)]
  [instFinite_HffBarQ : ∀ m hqp, Module.Finite (ZMod q) (HffBarQ m hqp)]
  [instCocomm_HffBarQ : ∀ m hqp, Coalgebra.IsCocomm (ZMod q) (HffBarQ m hqp)]
  ffBarQ_red : ∀ m hqp, Hff m q Fact.out hqp →+* HffBarQ m hqp
  ffBarQ_red_surjective : ∀ m hqp, Function.Surjective (ffBarQ_red m hqp)
  ffBarQ_red_ker : ∀ m hqp, RingHom.ker (ffBarQ_red m hqp)
    = Ideal.span {((q : ℤ) : Hff m q Fact.out hqp)}

attribute [instance] JZeroNeronPrimaryTorsionFFModels.instCommRing_Hff
  JZeroNeronPrimaryTorsionFFModels.instHopfAlgebra_Hff JZeroNeronPrimaryTorsionFFModels.instFinite_Hff
  JZeroNeronPrimaryTorsionFFModels.instFlat_Hff JZeroNeronPrimaryTorsionFFModels.instCocomm_Hff
  JZeroNeronPrimaryTorsionFFModels.instCommRing_HffBarQ JZeroNeronPrimaryTorsionFFModels.instHopfAlgebra_HffBarQ
  JZeroNeronPrimaryTorsionFFModels.instFinite_HffBarQ JZeroNeronPrimaryTorsionFFModels.instCocomm_HffBarQ

structure JZeroNeronPrimaryTorsionInvPins (p q : ℕ) [Fact p.Prime] [Fact q.Prime]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (C : JZeroNeronPrimaryTorsionCore p q A hA) (F : JZeroNeronPrimaryTorsionFFModels p q A hA C) where
  inv : ℕ → AdmissibleInvariants q
  h0_pin : ∀ m, Nat.card (fppfCohomology specInt (C.𝒥 m) 0) = q ^ (inv m).h0
  h1_pin : ∀ m, Nat.card (fppfCohomology specInt (C.𝒥 m) 1) = q ^ (inv m).h1
  δ_pin : ∀ m, Nat.card ↥(eisensteinPrimaryTorsionBar p q m)
    = q ^ (inv m).δ * Nat.card ↥(toricEisensteinPrimaryPart p q A hA m)
  α_pin : ∀ m, ∀ hqp : q ≠ p,
    Nat.card (WithConv (F.HffBarQ m hqp →ₐ[ZMod q] AlgebraicClosure (ZMod q))) = q ^ (inv m).α

structure JZeroNeronPrimaryTorsionSheaf (p q : ℕ) [Fact p.Prime] [Fact q.Prime]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p) where
  core : JZeroNeronPrimaryTorsionCore p q A hA
  ffModels : JZeroNeronPrimaryTorsionFFModels p q A hA core
  invPins : JZeroNeronPrimaryTorsionInvPins p q A hA core ffModels

def HasJZeroNeronPrimaryTorsionSheaf (p q : ℕ) [Fact p.Prime] [Fact q.Prime] : Prop :=
  ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p),
    Nonempty (JZeroNeronPrimaryTorsionSheaf p q A hA)

section Falseprobe

end Falseprobe

end ModularCurve

end


