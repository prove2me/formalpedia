-- Prove2me | Definitions.Def_FreyPackage_EigenformRealizationSupplyField
-- name    : FreyPackage_EigenformRealizationSupplyField
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.503845+00:00
-- url     : https://prove2.me/theorems/f1be58b3-8426-5273-9c54-2b66b21207ed
-- title:
--   Supply predicate: residual eigenform realizations with field coefficients
-- statement:
--   Fix a Frey package $P$ (integers $a,b,c$ and a prime $p\ge 5$ with $a^p+b^p=c^p$, $\gcd(a,b)=1$, $a\equiv 3 \bmod 4$, $b$ even) and a level $M$. `ESMasterAttachmentSupplyField P M J` is a predicate on an abstract carrier $J$ that is an abelian group, a module over the project's Hecke algebra `HeckeAlg` (the polynomial ring $\mathbb{Z}[T_\ell : \ell \text{ prime}]$, with `heckeGen` the variable at $\ell$), and is equipped with an action of $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$, realised as $\overline{\mathbb{Q}}$-algebra automorphisms of `AlgebraicClosure ℚ`. No compatibility between the Hecke and Galois actions is assumed. It asserts: for every weight-$2$ cusp form $g$ on $\Gamma_0(M)$ satisfying the project's `IsNormalizedEigenform` (first $q$-coefficient $1$, multiplicativity at coprime indices, and the usual prime-power recursions, with or without the $p\mid N$ Euler factor), and for every maximal ideal $\mathfrak{m}$ of the algebraic integers $\overline{\mathbb{Z}} =$ `integralClosure ℤ ℂ` containing $p$, there exist a field $k$, a ring homomorphism $\varphi:$ `HeckeAlg` $\to k$, a $k$-vector space $V$, a function $\pi : J \to V$, a homomorphism $\rho$ from the Galois group to $\mathrm{GL}_k(V)$, a ring homomorphism $\psi : \overline{\mathbb{Z}} \to k$, and a Galois number field $F$ embedded in $\overline{\mathbb{Q}}$ over $\mathbb{Q}$, such that: $p = 0$ in $k$; $(k,\varphi,V,\pi,\rho)$ is an `IsResidualRealization` of $J$ at $p$, i.e. $\dim_k V = 2$ and $\pi$ is additive, Galois-equivariant via $\rho$ and Hecke-semilinear via $\varphi$ on the $p$-torsion $\{x : p\cdot x = 0\}$, whose image spans $V$; $\det \rho(\sigma) = \ell$ in $k$ for every Frobenius $\sigma$ at a place over any prime $\ell \nmid Mp$; $\mathfrak{m} \subseteq \ker\psi$; for each prime $\ell \nmid Mp$ the $\ell$-th $q$-coefficient of $g$ is an algebraic integer $a$ with $\varphi(T_\ell) = \psi(a)$; and the kernel of restriction $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q}) \to \mathrm{Gal}(F/\mathbb{Q})$ lies in $\ker\rho$ and in the kernel of the $P.p$-torsion representation of the Frey curve, so both factor through $\mathrm{Gal}(F/\mathbb{Q})$. The conjunct $p = 0$ in $k$ follows from the other clauses but is recorded. `EigenformRealizationSupplyFieldAt P M` is this predicate for $J =$ `JZero M`, the degree-zero divisor class group of the base-changed modular function field of level $M$, with its Hecke module structure taken as an instance hypothesis; the accompanying lemma is the definitional unfolding.
--
--   **Relation to Mathlib.** Mathlib supplies `CuspForm`, `CongruenceSubgroup.Gamma0`, $q$-expansion coefficients and `integralClosure ℤ ℂ`; the Hecke algebra here is the project's free polynomial ring on the primes rather than a Mathlib Hecke algebra, and `IsNormalizedEigenform`, `IsResidualRealization`, `CyclotomicDeterminant` and `JZero` (a degree-zero divisor class group of a function field, not an abelian variety) are the project's own notions. The coefficient field $k$ is not required to be finite.
--
--   **Where it is used.** This is the hypothesis supplying, for each normalised weight-$2$ eigenform of level $M$ and each maximal ideal of $\overline{\mathbb{Z}}$ above $p$, a two-dimensional mod-$p$ Galois representation with cyclotomic determinant realised on the $p$-torsion of the level-$M$ Jacobian, whose Hecke eigenvalues reduce the $q$-coefficients of the form. It is the Eichler–Shimura input on which the comparison with the mod-$p$ representation of the Frey curve, and hence the Frey–Serre–Ribet part of the argument, rests.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_FreyPackage_EigenformRealizationSupplyField.lean

import Definitions.Def_ModularCurve_ResidualRealization
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_FLTPrelim_ModularRep

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Module LinearMap CongruenceSubgroup
open ModularCurve
open WeierstrassCurve WeierstrassCurve.Affine.Point
open scoped WeierstrassCurve.Affine

namespace FreyPackage

def ESMasterAttachmentSupplyField (P : FreyPackage) (M : ℕ)
    (J : Type*) [AddCommGroup J] [Module HeckeAlg J]
    [DistribMulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) J] : Prop :=
  ∀ (g : CuspForm (Gamma0 M) 2), g.IsNormalizedEigenform →
    ∀ (𝔪 : Ideal (integralClosure ℤ ℂ)), 𝔪.IsMaximal → (P.p : integralClosure ℤ ℂ) ∈ 𝔪 →
      ∃ (k : Type) (_ : Field k) (φ : HeckeAlg →+* k)
        (V : Type) (_ : AddCommGroup V) (_ : Module k V)
        (π : J → V)
        (ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* (V ≃ₗ[k] V))
        (ψ : integralClosure ℤ ℂ →+* k)
        (F : Type) (_ : Field F) (_ : NumberField F) (_ : IsGalois ℚ F)
        (_ : Algebra F (AlgebraicClosure ℚ)) (_ : IsScalarTower ℚ F (AlgebraicClosure ℚ)),
        ((P.p : k) = 0) ∧
        IsResidualRealization P.p J k φ V π ρ ∧
        CyclotomicDeterminant M P.p ρ ∧
        𝔪 ≤ RingHom.ker ψ ∧
        (∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ¬ ℓ ∣ M * P.p → ∃ a : integralClosure ℤ ℂ,
          (a : ℂ) = ModularFormClass.qCoeff g ℓ ∧ φ (heckeGen ⟨ℓ, hℓ⟩) = ψ a) ∧
        (AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := AlgebraicClosure ℚ) F).ker ≤
          (galoisRepModuleEnd (S := ℚ) (K := AlgebraicClosure ℚ) P.freyCurve P.p).ker ⊓
            ρ.ker

def EigenformRealizationSupplyFieldAt (P : FreyPackage) (M : ℕ)
    [Module HeckeAlg (JZero M)] : Prop :=
  ESMasterAttachmentSupplyField P M (JZero M)

theorem eigenformRealizationSupplyFieldAt_iff_eSMasterAttachmentSupplyField
    {P : FreyPackage} {M : ℕ} [Module HeckeAlg (JZero M)] :
    P.EigenformRealizationSupplyFieldAt M ↔ ESMasterAttachmentSupplyField P M (JZero M) :=
  Iff.rfl

end FreyPackage


