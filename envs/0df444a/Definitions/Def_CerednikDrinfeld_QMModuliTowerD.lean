-- Prove2me | Definitions.Def_CerednikDrinfeld_QMModuliTowerD
-- name    : CerednikDrinfeld_QMModuliTowerD
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.503845+00:00
-- url     : https://prove2.me/theorems/4683b927-9deb-5d57-a375-f47b9a99173b
-- title:
--   Quaternionic moduli tower witness over Z[1/D]
-- statement:
--   This module defines the structure [`CerednikDrinfeld.QM.ModuliTowerWitnessD`](../def/CerednikDrinfeld_QMModuliTowerD.html#L15), a bundle of data and compatibilities witnessing that a scheme $\pi_X : X \to \operatorname{Spec}\mathbb{Z}[1/D]$ (the localisation of $\mathbb{Z}$ away from $D$), together with a tower of function fields, is a moduli space for fake elliptic curves with extra level structure. The ambient parameters are: a $\mathbb{Z}$-submodule $\Lambda$ of $\mathbb{H}[\mathbb{Q},a,b]$, naturals $N$, $D$ and primes $q$, $q'$; a field $\bar F$ over $\overline{\mathbb{Q}}$; the morphism $\pi_X$ and a geometric point $\bar s : \operatorname{Spec}\overline{\mathbb{Q}} \to \operatorname{Spec}\mathbb{Z}[1/D]$; a moduli map `pt` sending, for each commutative ring $S$ and each $s : \operatorname{Spec} S \to \operatorname{Spec}\mathbb{Z}[1/D]$, a fake elliptic curve over $S$ to an $X$-point over $s$; a `CurveModel` $\mathfrak{M}$ for $\bar F/\overline{\mathbb{Q}}$ with a morphism $e_{\mathfrak M}$ from its curve to the fibre $X \times_{\mathbb{Z}[1/D]} \overline{\mathbb{Q}}$; actions `gal`, `galT` of $\operatorname{Aut}_{\mathbb{Q}}(\overline{\mathbb{Q}})$ by semilinear automorphisms on $\bar F$ and on the fields $F_\ell$ of a Hecke tower $\mathbb{T}$ indexed by the primes $\ell \neq q,q'$; and $\overline{\mathbb{Q}}$-linear semilinear automorphisms $W$, $W_{\mathbb{T}}$, two at each level.
--
--   The fields assign to every place $P$ of $\bar F$ a fake elliptic curve $\mathrm{rep}(P)$ of level $N$ over $\overline{\mathbb{Q}}$, and to every place of $F_\ell$ a fake elliptic curve with an extra level-$\ell$ subgroup, the latter assignment being a bijection onto isomorphism classes (`repT_surjective`, `repT_injective`). Further fields record: that the $X$-point of $\mathrm{rep}(P)$ is the $\overline{\mathbb{Q}}$-point of $\mathfrak{M}$ attached to $P$ followed by $e_{\mathfrak M}$ and the projection to $X$; that the two legs $\varphi(\ell,0)$, $\varphi(\ell,1)$ of the tower correspond to forgetting the extra level and to quotienting by it by an $\ell$-isogeny; that `gal`, `galT` act on $\overline{\mathbb{Q}}$ through $\sigma$ and that $\mathrm{rep}$, $\mathrm{repT}$ are equivariant, the level-$\ell$ case being spelled out as a pullback square along $\operatorname{Spec}\sigma$ compatible with the group law, the $\Lambda$-action and both level subschemes; and that $W_0$, $W_1$ (resp. their tower analogues) realise Atkin–Lehner quotients at $q$ and $q'$, the kernel being cut out by the elements $m \in \Lambda$ with $m\bar m$ a rational multiple of $q$ (resp. $q'$). The structure differs from `ModuliTowerWitness` only in that the base is $\operatorname{Spec}\mathbb{Z}[1/D]$ for the extra parameter $D$ instead of $\operatorname{Spec}\mathbb{Z}[1/Nqq']$; the Hecke index type is the same.
--
--   **Relation to Mathlib.** Mathlib has no notion of fake elliptic curves, Shimura-curve moduli, Hecke towers or Atkin–Lehner quotients in this scheme-theoretic form; these, as well as the notions `Place`, `CurveModel` and `SemilinearAut` used here, are the project's own, built on Mathlib's scheme theory (smooth and proper morphisms, pullbacks, closed immersions) and quaternion algebras.
--
--   **Where it is used.** The witness packages the moduli interpretation of a tower of quaternionic Shimura curves, with its Hecke correspondences, Galois action and Atkin–Lehner involutions, in a form that can be fed to the Čerednik–Drinfeld uniformisation and thence to the comparison of torsion in Jacobians used for level lowering in the Frey–Serre–Ribet part of the argument. It is a definition only: nothing is asserted here, and instances of the structure are supplied elsewhere.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_CerednikDrinfeld_QMModuliTowerD.lean

import Definitions.Def_CerednikDrinfeld_QMModuliPropsD
import Definitions.Def_CerednikDrinfeld_QMModuliTower

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsDedekindDomain AlgebraicCurve
open scoped Quaternion TensorProduct NumberField

namespace CerednikDrinfeld.QM

variable {a b : ℚ}

structure ModuliTowerWitnessD (Λ : Submodule ℤ ℍ[ℚ, a, b]) (N q q' D : ℕ) [Fact q.Prime] [Fact q'.Prime]
    (Fbar : Type) [Field Fbar] [Algebra (AlgebraicClosure ℚ) Fbar]
    (X : Scheme.{0}) (πX : X ⟶ Spec (CommRingCat.of (Localization.Away ((D : ℕ) : ℤ))))
    (sbar : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Spec (CommRingCat.of (Localization.Away ((D : ℕ) : ℤ))))
    (pt : ∀ (S : Type) [CommRing S]
      (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of (Localization.Away ((D : ℕ) : ℤ)))),
      FakeEllipticCurve Λ N S → SchemeHomOver s πX)
    (𝔐 : AlgebraicCurve.CurveModel (AlgebraicClosure ℚ) Fbar) (e𝔐 : 𝔐.C ⟶ CategoryTheory.Limits.pullback πX sbar)
    (gal : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* SemilinearAut (AlgebraicClosure ℚ) Fbar)
    (𝕋 : HeckeTower.TowerData q q' Fbar)
    (galT : ∀ ℓ : HeckeTower.AwayPrime q q', (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* SemilinearAut (AlgebraicClosure ℚ) (𝕋.F ℓ))
    (W : Fin 2 → SemilinearAut (AlgebraicClosure ℚ) Fbar)
    (WT : ∀ ℓ : HeckeTower.AwayPrime q q', Fin 2 → SemilinearAut (AlgebraicClosure ℚ) (𝕋.F ℓ)) : Type 1 where

  rep : Place (AlgebraicClosure ℚ) Fbar → FakeEllipticCurve Λ N (AlgebraicClosure ℚ)

  pt_rep : ∀ P : Place (AlgebraicClosure ℚ) Fbar,
    (pt _ sbar (rep P)).1 = (𝔐.pointEquivPlace.symm P).1 ≫ e𝔐 ≫ CategoryTheory.Limits.pullback.fst πX sbar

  repT : ∀ ℓ : HeckeTower.AwayPrime q q',
    Place (AlgebraicClosure ℚ) (𝕋.F ℓ) → FakeEllipticCurve.WithExtraLevel Λ N (ℓ.1 : ℕ) (AlgebraicClosure ℚ)

  repT_surjective : ∀ (ℓ : HeckeTower.AwayPrime q q') (u : FakeEllipticCurve.WithExtraLevel Λ N (ℓ.1 : ℕ) (AlgebraicClosure ℚ)),
    ∃ P : Place (AlgebraicClosure ℚ) (𝕋.F ℓ), FakeEllipticCurve.WithExtraLevel.Iso (repT ℓ P) u

  repT_injective : ∀ (ℓ : HeckeTower.AwayPrime q q') (P Q : Place (AlgebraicClosure ℚ) (𝕋.F ℓ)),
    FakeEllipticCurve.WithExtraLevel.Iso (repT ℓ P) (repT ℓ Q) → P = Q

  gal_base : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
    SemilinearAut.baseAut (gal σ) = (σ : AlgebraicClosure ℚ ≃+* AlgebraicClosure ℚ)

  galT_base : ∀ (ℓ : HeckeTower.AwayPrime q q') (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ),
    SemilinearAut.baseAut (galT ℓ σ) = (σ : AlgebraicClosure ℚ ≃+* AlgebraicClosure ℚ)

  W_base : ∀ (i : Fin 2) (c : AlgebraicClosure ℚ), SemilinearAut.baseAut (W i) c = c

  WT_base : ∀ (ℓ : HeckeTower.AwayPrime q q') (i : Fin 2) (c : AlgebraicClosure ℚ), SemilinearAut.baseAut (WT ℓ i) c = c

  restrict_zero : ∀ (ℓ : HeckeTower.AwayPrime q q') (P : Place (AlgebraicClosure ℚ) (𝕋.F ℓ)),
    FakeEllipticCurve.IsLevelRestrict (repT ℓ P) (rep (P.restrictAlong (𝕋.φ (ℓ, 0)) (𝕋.integral (ℓ, 0))))

  restrict_one : ∀ (ℓ : HeckeTower.AwayPrime q q') (P : Place (AlgebraicClosure ℚ) (𝕋.F ℓ)),
    FakeEllipticCurve.IsLevelIsogeny (ℓ.1 : ℕ) (repT ℓ P) (rep (P.restrictAlong (𝕋.φ (ℓ, 1)) (𝕋.integral (ℓ, 1))))

  gal_rep : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (P : Place (AlgebraicClosure ℚ) Fbar),
    ∃ E : FakeEllipticCurve Λ N (AlgebraicClosure ℚ),
      FakeEllipticCurve.IsPullback (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ) (rep P) E ∧
        FakeEllipticCurve.Iso E (rep (gal σ • P))

  galT_rep : ∀ (ℓ : HeckeTower.AwayPrime q q') (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (P : Place (AlgebraicClosure ℚ) (𝕋.F ℓ)),
    ∃ (u : FakeEllipticCurve.WithExtraLevel Λ N (ℓ.1 : ℕ) (AlgebraicClosure ℚ)) (g : u.1.A ⟶ (repT ℓ P).1.A)
      (hg : CategoryTheory.IsPullback g u.1.f (repT ℓ P).1.f
        (Spec.map (CommRingCat.ofHom (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)))),
      (∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (Q Q' : SchemeHomOver t' u.1.f),
        (u.1.L.mul t' Q Q').1 ≫ g =
          ((repT ℓ P).1.L.mul (t' ≫ Spec.map (CommRingCat.ofHom (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)))
            ⟨Q.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, Q.2]⟩
            ⟨Q'.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, Q'.2]⟩).1) ∧
      (∀ x : ↥Λ, u.1.act x ≫ g = g ≫ (repT ℓ P).1.act x) ∧
      (∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ))) (Q : SchemeHomOver t' u.1.f),
        (FactorsThrough u.1.lev Q → ∃ Q₀ : T ⟶ (repT ℓ P).1.C, Q₀ ≫ (repT ℓ P).1.lev = Q.1 ≫ g) ∧
        (FactorsThrough u.2.levK Q → ∃ Q₀ : T ⟶ (repT ℓ P).2.K, Q₀ ≫ (repT ℓ P).2.levK = Q.1 ≫ g)) ∧
      FakeEllipticCurve.WithExtraLevel.Iso u (repT ℓ (galT ℓ σ • P))

  W_zero_rep : ∀ P : Place (AlgebraicClosure ℚ) Fbar, (rep P).IsAtkinLehnerQuotient q (rep (W 0 • P))

  W_one_rep : ∀ P : Place (AlgebraicClosure ℚ) Fbar, (rep P).IsAtkinLehnerQuotient q' (rep (W 1 • P))

  WT_zero_rep : ∀ (ℓ : HeckeTower.AwayPrime q q') (P : Place (AlgebraicClosure ℚ) (𝕋.F ℓ)),
    FakeEllipticCurve.WithExtraLevel.IsAtkinLehnerQuotient q (repT ℓ P) (repT ℓ (WT ℓ 0 • P))

  WT_one_rep : ∀ (ℓ : HeckeTower.AwayPrime q q') (P : Place (AlgebraicClosure ℚ) (𝕋.F ℓ)),
    FakeEllipticCurve.WithExtraLevel.IsAtkinLehnerQuotient q' (repT ℓ P) (repT ℓ (WT ℓ 1 • P))

end CerednikDrinfeld.QM

end


