-- Prove2me | Definitions.Def_FreyPackage_EigenformResidualAttachment
-- name    : FreyPackage_EigenformResidualAttachment
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.503845+00:00
-- url     : https://prove2.me/theorems/04a88731-703e-5988-9faf-466dbdddef9e
-- title:
--   Residual Galois representations attached to eigenforms of level M
-- statement:
--   The module defines a single predicate, `EigenformResidualAttachmentAt P M`, on a Frey package $P=(a,b,c,p)$ and a natural number $M$. It asserts: for every weight-$2$ cusp form $g$ on $\Gamma_0(M)$ which is a normalised eigenform in the project's sense (first $q$-coefficient $1$, multiplicativity of $q$-coefficients at coprime indices, and the two prime-power recursions according to whether the prime divides the level), and for every maximal ideal $\mathfrak m$ of $\mathrm{integralClosure}\,\mathbb Z\,\mathbb C$ (the ring of all algebraic integers in $\mathbb C$) containing the image of $p$, there exist: a field $K$ carrying a $\mathbb Z/p$-algebra structure, a $K$-vector space $V$ with a representation $\rho$ of $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$, realised as the group of $\mathbb Q$-algebra automorphisms of `AlgebraicClosure ℚ`, a ring homomorphism $\psi$ from the algebraic integers to $K$, and a number field $F$, Galois over $\mathbb Q$ and embedded in $\overline{\mathbb Q}$ compatibly over $\mathbb Q$, subject to four conditions: (i) $\mathfrak m\subseteq\ker\psi$, so $\psi$ is a residue map at $\mathfrak m$; (ii) $\dim_K V=2$; (iii) the kernel of the restriction homomorphism $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)\to\mathrm{Gal}(F/\mathbb Q)$ lies in the intersection of $\ker\rho$ with the kernel of the action of $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$ on the $p$-torsion of the Frey curve over $\overline{\mathbb Q}$ (the monoid homomorphism `galoisRepModuleEnd`), i.e. both representations factor through $\mathrm{Gal}(F/\mathbb Q)$; (iv) for every prime $\ell\nmid M$ with $\ell\neq p$, every valuation subring $A$ of $\overline{\mathbb Q}$ in which $\ell$ is a non-unit, and every $\tau$ that is a Frobenius at $\ell$ for $A$ (in the decomposition subgroup, acting as $x\mapsto x^{\ell}$ on the residue field of $A$), one has $\mathrm{tr}\,\rho(\tau)=\psi(a)$ for some algebraic integer $a$ whose complex value is the $\ell$-th $q$-coefficient of $g$, and $\det\rho(\tau)=\ell$ in $K$.
--
--   Note what is not required: no irreducibility of $\rho$, and no congruence relating $\rho$ to the mod-$p$ representation of the Frey curve — condition (iii) only forces the two to be trivial on a common open normal subgroup, so that both are determined by their values on $\mathrm{Gal}(F/\mathbb Q)$. The module also installs a classical decidable-equality instance on `AlgebraicClosure ℚ`, needed for the torsion-module machinery.
--
--   **Relation to Mathlib.** Cusp forms, $\Gamma_0(M)$, `Representation`, `LinearMap.trace`/`det` and valuation subrings with their decomposition subgroups are Mathlib's; the normalised-eigenform structure, the $q$-coefficient function, the Galois action on the $p$-torsion of a Weierstrass curve and [`ValuationSubring.IsFrobeniusAt`](../def/EllipticCurve_FrobeniusTrace.html#L51) are the project's own definitions, and the attachment predicate itself has no Mathlib counterpart.
--
--   **Where it is used.** The predicate is the interface through which the phrase "the mod-$p$ representation arises from level $M$" is used in the level-lowering step: it packages, for each eigenform of level $M$ and each maximal ideal above $p$, a two-dimensional residual representation with prescribed Frobenius traces and determinants, together with a common finite Galois field of definition for it and for the mod-$p$ representation of the Frey curve, as required for density arguments comparing the two.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_FreyPackage_EigenformResidualAttachment.lean

import Mathlib.RepresentationTheory.Basic
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.FieldTheory.Galois.Basic
import Definitions.Def_FLTPrelim_ModularRep
import Definitions.Def_FLTPrelim_FreyPackage
import Definitions.Def_EllipticCurve_FrobeniusTrace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open WeierstrassCurve WeierstrassCurve.Affine.Point
open scoped CongruenceSubgroup

namespace FreyPackage

noncomputable local instance instDecEqQbarCongruenceRecovery :
    DecidableEq (AlgebraicClosure ℚ) := Classical.decEq _

def EigenformResidualAttachmentAt (P : FreyPackage) (M : ℕ) : Prop :=
  ∀ (g : CuspForm (CongruenceSubgroup.Gamma0 M) 2), g.IsNormalizedEigenform →
    ∀ (𝔪 : Ideal (integralClosure ℤ ℂ)), 𝔪.IsMaximal → (P.p : integralClosure ℤ ℂ) ∈ 𝔪 →
      ∃ (K : Type) (_ : Field K) (_ : Algebra (ZMod P.p) K)
        (V : Type) (_ : AddCommGroup V) (_ : Module K V)
        (ρ : Representation K (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) V)
        (ψ : integralClosure ℤ ℂ →+* K)
        (F : Type) (_ : Field F) (_ : NumberField F) (_ : IsGalois ℚ F)
        (_ : Algebra F (AlgebraicClosure ℚ)) (_ : IsScalarTower ℚ F (AlgebraicClosure ℚ)),
        𝔪 ≤ RingHom.ker ψ ∧
        Module.finrank K V = 2 ∧
        (AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := AlgebraicClosure ℚ) F).ker ≤
          (galoisRepModuleEnd (S := ℚ) (K := AlgebraicClosure ℚ) P.freyCurve P.p).ker ⊓
            ρ.ker ∧
        (∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ M → ℓ ≠ P.p →
          ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
            ∀ τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt τ ℓ →
              ∃ a : integralClosure ℤ ℂ, (a : ℂ) = ModularFormClass.qCoeff g ℓ ∧
                LinearMap.trace K V (ρ τ) = ψ a) ∧
        (∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ M → ℓ ≠ P.p →
          ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
            ∀ τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt τ ℓ →
              LinearMap.det (ρ τ) = (ℓ : K))

end FreyPackage


