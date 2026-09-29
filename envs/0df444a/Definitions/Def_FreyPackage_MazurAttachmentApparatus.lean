-- Prove2me | Definitions.Def_FreyPackage_MazurAttachmentApparatus
-- name    : FreyPackage_MazurAttachmentApparatus
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.503845+00:00
-- url     : https://prove2.me/theorems/325232ab-e25e-50fb-b203-a82a25aee62d
-- title:
--   Hecke-ideal and residual matrix-representation data for Mazur's principle
-- statement:
--   Throughout, `HeckeAlg` is the polynomial ring $\mathbb{Z}[T_\ell : \ell \text{ prime}]$ (with `heckeGen` $\ell$ the variable $T_\ell$), `JZero M` is the degree-zero divisor class group of the base-changed modular function field of level $M$ over $\overline{\mathbb{Q}}$, and `mazurGaloisGroup` abbreviates $\mathrm{Aut}_{\mathbb{Q}}(\overline{\mathbb{Q}})$ for $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ`. Five predicates on an ideal $\mathfrak m \subseteq$ `HeckeAlg` are introduced. `EigenformIdealData P M g 𝔪` is a structure whose fields assert that $\mathfrak m$ is maximal, contains $p$, is not eventually Eisenstein (no finite set $S$ of primes with $T_\ell - (\ell+1) \in \mathfrak m$ for all $\ell \notin S$), and satisfies $T_\ell - b \in \mathfrak m$ whenever an integer $b$ equals the $\ell$-th $q$-expansion coefficient of $g$. `IdealGoodPrimeCurveCongruence p M W 𝔪` asserts $T_\ell - a_\ell(W) \in \mathfrak m$ for every prime $\ell$ of good reduction for the chosen integral Weierstrass model $W$ with $\ell \nmid M$, $\ell \neq p$, where $a_\ell(W)$ is the Frobenius trace of that model. `IsAttachedMatrixRep 𝔪 Sρ ρmat` says of a monoid homomorphism $\rho$ into $2\times2$ matrices over `HeckeAlg`$/\mathfrak m$ (invertibility is not imposed) that for each prime $\ell \notin S_\rho$, each valuation subring $A$ of $\overline{\mathbb{Q}}$ lying over $\ell$ and each $\sigma$ that is a Frobenius at $\ell$ for $A$, $\operatorname{tr}\rho(\sigma) = T_\ell \bmod \mathfrak m$ and $\det\rho(\sigma) = \ell \bmod \mathfrak m$; adding openness of $\ker\rho$ gives `IsAttachedMatrixRepWithOpenKer`. `AttachedRepUnramifiedAtQ q 𝔪` quantifies over all such $\rho$ with open kernel: if $q$ is a unit mod $\mathfrak m$, then $\rho$ is trivial on the inertia subgroup of every $A$ over $q$ and $\det\rho(\mathrm{Frob}_q) = q$. `CurveAttachmentMatrixData P q N 𝔪` posits a matrix representation $\rho$ and an element $c$ with: the trace and determinant conditions at primes not dividing $Nqp$; irreducibility, in the form that the only $\rho$-stable submodules of $(\mathbb{T}/\mathfrak m)^2$ are $\bot$ and $\top$; $\rho(c)^2 = 1$ and $\det\rho(c) = -1$; and a Galois number field $F \subseteq \overline{\mathbb{Q}}$ with $\mathrm{Gal}(\overline{\mathbb{Q}}/F)$ contained both in $\ker\rho$ and in the subgroup fixing the $\mathfrak m$-torsion of `JZero (N*q)` pointwise.
--
--   `MazurPerWitnessIdealSupplyFamily P q` packages these: for every level $N$ with $q \nmid N$, assuming the $p$-torsion representation of the Frey curve is irreducible in the sense of having no proper nonzero Galois-stable $\mathbb{Z}/p$-submodule and is unramified at $q$, then for every weight-two cusp form $g$ on $\Gamma_0(Nq)$ and maximal ideal $\mathfrak m_w \ni p$ of the integral closure of $\mathbb{Z}$ in $\mathbb{C}$ exhibiting $g$ as a congruent witness for the integral Frey model, with $a_q(g)^2 = 1$ (the project's `IsNewAt q`), and given the Hecke input and commutation hypotheses at level $Nq$, there is an ideal $\mathfrak m$ satisfying all four conditions above together with non-vanishing of the $\mathfrak m$-torsion in `JZero (N*q)`, the Hecke action being the one induced by the correspondences.
--
--   **Relation to Mathlib.** Mathlib has no abstract Hecke algebra, no residual Hecke eigenvalue ideals and no notion of a Galois representation attached to such an ideal; these are the project's own notions, built on Mathlib's `MvPolynomial`, `Ideal.Quotient`, `Matrix (Fin 2) (Fin 2)` and `AlgEquiv.restrictNormalHom`, and on the project's decomposition/inertia and Frobenius predicates for valuation subrings.
--
--   **Where it is used.** These predicates supply the input data for the formalisation of Mazur's principle, the level-lowering step that removes the auxiliary prime $q$ from the level of a weight-two form congruent to the Frey curve; the conclusions recorded here (non-Eisenstein maximal ideal, congruences with the Frey Frobenius traces, unramifiedness at $q$ of the attached residual representation, irreducibility and oddness, and non-vanishing of the $\mathfrak m$-torsion in the Jacobian) are exactly what that argument consumes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_FreyPackage_MazurAttachmentApparatus.lean

import Mathlib
import Definitions.Def_FLTPrelim_FreyPackage
import Definitions.Def_FreyPackage_LevelRaising
import Definitions.Def_FreyPackage_GaloisRep
import Definitions.Def_GaloisRep_GlobalUnramifiedAt
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_ModularCurve_HeckeInputsAll
import Definitions.Def_ModularCurve_MazurPrincipleCore

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

namespace FreyPackage

open ModularCurve
open scoped CongruenceSubgroup

abbrev mazurGaloisGroup : Type := AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ

structure EigenformIdealData (P : FreyPackage) (M : ℕ) (g : CuspForm (CongruenceSubgroup.Gamma0 M) 2)
    (𝔪 : Ideal HeckeAlg) : Prop where
  hmax : 𝔪.IsMaximal
  hpmem : ((P.p : ℕ) : HeckeAlg) ∈ 𝔪
  heis : ¬ IsEventuallyEisenstein 𝔪
  heigen : ∀ (ℓ : Nat.Primes) (b : ℤ), (algebraMap ℤ ℂ b = ModularFormClass.qCoeff g ℓ) →
    heckeGen ℓ - MvPolynomial.C b ∈ 𝔪

def IdealGoodPrimeCurveCongruence (p M : ℕ) (W : WeierstrassCurve ℤ) (𝔪 : Ideal HeckeAlg) : Prop :=
  ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), W.IsGoodPrimeFor ℓ → ¬ ℓ ∣ M → ℓ ≠ p →
    heckeGen ⟨ℓ, hℓ⟩ - MvPolynomial.C (W.apOfModel ℓ : ℤ) ∈ 𝔪

def IsAttachedMatrixRep (𝔪 : Ideal HeckeAlg) (Sρ : Finset ℕ)
    (ρmat : mazurGaloisGroup →* Matrix (Fin 2) (Fin 2) (HeckeAlg ⧸ 𝔪)) : Prop :=
  ∀ ℓ : ℕ, (hℓ : ℓ.Prime) → ℓ ∉ Sρ →
    ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
      ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ ℓ →
        Ideal.Quotient.mk 𝔪 (heckeGen ⟨ℓ, hℓ⟩) = (ρmat σ).trace ∧
        Ideal.Quotient.mk 𝔪 ((ℓ : HeckeAlg)) = (ρmat σ).det

def IsAttachedMatrixRepWithOpenKer (𝔪 : Ideal HeckeAlg) (Sρ : Finset ℕ)
    (ρmat : mazurGaloisGroup →* Matrix (Fin 2) (Fin 2) (HeckeAlg ⧸ 𝔪)) : Prop :=
  IsAttachedMatrixRep 𝔪 Sρ ρmat ∧ IsOpen (ρmat.ker : Set mazurGaloisGroup)

def AttachedRepUnramifiedAtQ (q : ℕ) (𝔪 : Ideal HeckeAlg) : Prop :=
  ∀ (Sρ : Finset ℕ) (ρmat : mazurGaloisGroup →* Matrix (Fin 2) (Fin 2) (HeckeAlg ⧸ 𝔪)),
    IsAttachedMatrixRepWithOpenKer 𝔪 Sρ ρmat → IsUnit ((q : ℕ) : HeckeAlg ⧸ 𝔪) →
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime q →
        (∀ σ ∈ A.inertiaSubgroupIn ℚ, ρmat σ = 1) ∧
        ∀ frob : mazurGaloisGroup, A.IsFrobeniusAt frob q → (ρmat frob).det = ((q : ℕ) : HeckeAlg ⧸ 𝔪)

def CurveAttachmentMatrixData (P : FreyPackage) (q N : ℕ) [NeZero q] [NeZero N]
    [Module HeckeAlg (JZero (N * q))] (𝔪 : Ideal HeckeAlg) : Prop :=
  ∃ (ρmat : mazurGaloisGroup →* Matrix (Fin 2) (Fin 2) (HeckeAlg ⧸ 𝔪))
    (c : mazurGaloisGroup),
    (∀ ℓ : ℕ, (hℓ : ℓ.Prime) → ℓ ∉ ((N * q) * P.p).primeFactors →
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ ℓ →
          (ρmat σ).trace = Ideal.Quotient.mk 𝔪 (heckeGen ⟨ℓ, hℓ⟩))
    ∧ (∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ ((N * q) * P.p).primeFactors →
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
        ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ ℓ →
          (ρmat σ).det = ((ℓ : ℕ) : HeckeAlg ⧸ 𝔪))
    ∧ (∀ Wsub : Submodule (HeckeAlg ⧸ 𝔪) (Fin 2 → HeckeAlg ⧸ 𝔪),
        (∀ g, ∀ v ∈ Wsub, (ρmat g).mulVec v ∈ Wsub) → Wsub = ⊥ ∨ Wsub = ⊤)
    ∧ ρmat c * ρmat c = 1
    ∧ (ρmat c).det = -1
    ∧ ∃ (F : Type) (_ : Field F) (_ : NumberField F) (_ : IsGalois ℚ F)
        (_ : Algebra F (AlgebraicClosure ℚ)) (_ : IsScalarTower ℚ F (AlgebraicClosure ℚ)),
        (AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := AlgebraicClosure ℚ) F).ker ≤ ρmat.ker
        ∧ (AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := AlgebraicClosure ℚ) F).ker ≤
             fixingSubgroup mazurGaloisGroup
               (heckeTorsion (JZero (N * q)) 𝔪 : Set (JZero (N * q)))

def MazurPerWitnessIdealSupplyFamily (P : FreyPackage) (q : ℕ) [NeZero q] : Prop :=
  ∀ (N : ℕ) [NeZero N], ¬ q ∣ N →
    WeierstrassCurve.Affine.Point.GaloisRepIsIrreducible (K := AlgebraicClosure ℚ) ℚ P.freyCurve P.p →
    GlobalGaloisRep.IsUnramifiedAt P.freyGaloisRep q →
    ∀ (g : CuspForm (CongruenceSubgroup.Gamma0 (N * q)) 2) (𝔪w : Ideal (integralClosure ℤ ℂ)),
      P.IsCongruentWitness (N * q) g (freyCurveInt P) 𝔪w → g.IsNewAt q →
      HeckeInputsAll (N * q) → HeckeOperatorsCommuteBar (N * q) →
      ∃ 𝔪 : Ideal HeckeAlg,
        P.EigenformIdealData (N * q) g 𝔪 ∧
        IdealGoodPrimeCurveCongruence P.p (N * q) (freyCurveInt P) 𝔪 ∧
        AttachedRepUnramifiedAtQ q 𝔪 ∧
        (letI := heckeModuleBar (N * q)
         P.CurveAttachmentMatrixData q N 𝔪 ∧ heckeTorsion (JZero (N * q)) 𝔪 ≠ ⊥)

end FreyPackage

end


