-- Prove2me | Definitions.Def_ModularCurve_TwoNewEigenformIdeal
-- name    : ModularCurve_TwoNewEigenformIdeal
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.712661+00:00
-- url     : https://prove2.me/theorems/361af46b-e37d-53af-ae55-5bfb87daecd3
-- title:
--   Eigensystem ideals of forms new at two primes
-- statement:
--   Both notions are phrased over the project's abstract Hecke algebra `HeckeAlg`, the polynomial ring $\mathbb{Z}[X_\ell : \ell \text{ prime}]$ on generators indexed by the primes, and use `eigenIdeal a`, the kernel of the $\mathbb{Z}$-algebra map $\mathrm{aeval}\,a$ sending $X_\ell \mapsto a_\ell$.
--
--   `IsTwoNewEigenformIdeal M q q' 𝔪` asserts the existence of a weight-two cusp form $f$ for $\Gamma_0(M)$ together with: a proof that $f$ is a normalised eigenform in the project's sense (first $q$-expansion coefficient $1$, multiplicativity of the coefficients on coprime indices, and the two prime-power recursions $a_{p^{r+2}} = a_p a_{p^{r+1}} - p\,a_{p^r}$ for $p \nmid M$ and $a_{p^{r+2}} = a_p a_{p^{r+1}}$ for $p \mid M$); proofs that $f$ is new at $q$ and at $q'$, where `IsNewAt` is the condition $a_q^2 = 1$ on the relevant coefficient; a finite field $k$; a subring $\mathcal{O} \subseteq \mathbb{C}$ containing $a_\ell(f)$ for every prime $\ell$; and a ring homomorphism $\varphi : \mathcal{O} \to k$; such that $\mathfrak{m}$ is exactly the kernel of the map $X_\ell \mapsto \varphi(a_\ell(f))$. Thus $\mathfrak{m}$ is the ideal cutting out a residual eigensystem attached to such an $f$, with the residue field and the reduction map existentially quantified rather than fixed.
--
--   `TwoNewEigensystemsFactor M q q' Y`, for an abelian group $Y$ with a `HeckeAlg`-module structure, asserts that for every normalised weight-two eigenform $f$ of level $\Gamma_0(M)$ with $a_q^2 = 1$ and $a_{q'}^2 = 1$, the annihilator of $Y$ in `HeckeAlg` is contained in the kernel of $X_\ell \mapsto a_\ell(f) \in \mathbb{C}$. Equivalently, every polynomial Hecke relation holding on $Y$ also holds on each such complex eigensystem, so that each of these eigensystems factors through the image of `HeckeAlg` in $\mathrm{End}(Y)$.
--
--   **Relation to Mathlib.** Mathlib has weight-two cusp forms for $\Gamma_0(M)$ and $q$-expansion coefficients, but no Hecke algebra, eigensystem ideal or newness notion; these are the project's own, with the Hecke algebra modelled as a free polynomial ring on the primes and eigensystems as $\mathbb{Z}$-algebra maps out of it.
--
--   **Where it is used.** These predicates package the eigensystems that arise in the level-raising step: $\mathfrak{m}$ records a residual eigensystem coming from a form of level $\Gamma_0(M)$ (intended with $M = Nqq'$) new at the two primes $q$ and $q'$, while `TwoNewEigensystemsFactor` expresses that a given Hecke module $Y$ sees all such eigensystems.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_ModularCurve_TwoNewEigenformIdeal.lean

import Definitions.Def_HeckeGalois_EichlerShimura
import Definitions.Def_FLTPrelim_Modularity
import Definitions.Def_FreyPackage_LevelRaising

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace ModularCurve

def IsTwoNewEigenformIdeal (M q q' : ℕ) (𝔪 : Ideal HeckeAlg) : Prop :=
  ∃ (f : CuspForm (CongruenceSubgroup.Gamma0 M) 2) (_ : f.IsNormalizedEigenform)
    (_ : f.IsNewAt q) (_ : f.IsNewAt q')
    (k : Type) (_ : Field k) (_ : Finite k) (𝒪 : Subring ℂ)
    (h𝒪 : ∀ ℓ : Nat.Primes, ModularFormClass.qCoeff f ℓ ∈ 𝒪) (φ : 𝒪 →+* k),
      𝔪 = eigenIdeal (fun ℓ => φ ⟨ModularFormClass.qCoeff f ℓ, h𝒪 ℓ⟩)

def TwoNewEigensystemsFactor (M q q' : ℕ) (Y : Type*) [AddCommGroup Y] [Module HeckeAlg Y] :
    Prop :=
  ∀ (f : CuspForm (CongruenceSubgroup.Gamma0 M) 2), f.IsNormalizedEigenform →
    f.IsNewAt q → f.IsNewAt q' →
      Module.annihilator HeckeAlg Y ≤
        RingHom.ker (MvPolynomial.aeval (R := ℤ)
          (fun ℓ : Nat.Primes => ModularFormClass.qCoeff f ℓ))

end ModularCurve


