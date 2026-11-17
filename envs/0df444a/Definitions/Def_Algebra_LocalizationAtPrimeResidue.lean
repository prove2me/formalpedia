-- Prove2me | Definitions.Def_Algebra_LocalizationAtPrimeResidue
-- name    : Algebra_LocalizationAtPrimeResidue
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-11-16T17:59:53.086197+00:00
-- url     : https://prove2.me/theorems/a804c9ba-1e94-499b-a15a-015640d4a6b7
-- title:
--   Residue algebras after localization at a maximal ideal
-- statement:
--   Let $k$ be a commutative ring, let $A$ be a commutative $k$-algebra, and let $p$ be a maximal ideal of $A$. The file defines a $k$-algebra equivalence $$A/p ≃_k κ(A_p).$$ When $k$ is a field and a $k$-algebra map $e:A→k$ has kernel $p$, it also defines $κ(A_p)≃_k k$. These identifications make the residue field of a local ring at a rational evaluation point carry the correct constant-field action.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
noncomputable section

namespace IsLocalization.AtPrime

/-- Localization at a maximal ideal preserves its residue algebra over constants. -/
def residueAlgEquiv {k A : Type*} [CommRing k] [CommRing A] [Algebra k A]
    (p : Ideal A) [p.IsMaximal] :
    (A ⧸ p) ≃ₐ[k] IsLocalRing.ResidueField (Localization.AtPrime p) :=
  AlgEquiv.ofRingEquiv
    (f := equivQuotMaximalIdeal p (Localization.AtPrime p))
    (fun a => by
      change equivQuotMaximalIdeal p (Localization.AtPrime p)
          (Ideal.Quotient.mk p (algebraMap k A a)) =
        Ideal.Quotient.mk (IsLocalRing.maximalIdeal (Localization.AtPrime p))
          (algebraMap k (Localization.AtPrime p) a)
      rw [equivQuotMaximalIdeal_apply_mk]
      congr 1)

/-- The local residue algebra at a rational evaluation point is the constant field. -/
def rationalPointResidueAlgEquiv {k A : Type*} [Field k] [CommRing A] [Algebra k A]
    (e : A →ₐ[k] k) (p : Ideal A) [p.IsMaximal]
    (hp : RingHom.ker e.toRingHom = p) :
    IsLocalRing.ResidueField (Localization.AtPrime p) ≃ₐ[k] k := by
  subst p
  exact (residueAlgEquiv (k := k) (RingHom.ker e.toRingHom)).symm.trans
    (Ideal.quotientKerAlgEquivOfSurjective (fun a =>
      ⟨algebraMap k A a, e.commutes a⟩))

end IsLocalization.AtPrime


