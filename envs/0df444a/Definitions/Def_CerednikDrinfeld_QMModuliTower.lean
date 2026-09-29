-- Prove2me | Definitions.Def_CerednikDrinfeld_QMModuliTower
-- name    : CerednikDrinfeld_QMModuliTower
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.503845+00:00
-- url     : https://prove2.me/theorems/bb417bed-6d52-556d-ba06-0202489640dd
-- title:
--   Moduli tower witnesses for fake elliptic curves over Qˉ​
-- statement:
--   Fix a quaternion algebra $\mathbb H[\mathbb Q,a,b]$, a $\mathbb Z$-submodule $\Lambda$ of it, a level $N$ and primes $q,q'$. The structure [`CerednikDrinfeld.QM.ModuliTowerWitness`](../def/CerednikDrinfeld_QMModuliTower.html#L16) is indexed by: a field $\bar F$ over $\bar{\mathbb Q}$; a scheme $X$ with a morphism $\pi_X$ to $\operatorname{Spec}\mathbb Z[1/(Nqq')]$ together with the point $\bar s:\operatorname{Spec}\bar{\mathbb Q}\to\operatorname{Spec}\mathbb Z[1/(Nqq')]$; a rule `pt` assigning to each ring $S$, each $S$-point $s$ of the base and each object of `FakeEllipticCurve Λ N S` an $S$-point of $X$ over $s$; a curve model $\mathfrak M$ of $\bar F/\bar{\mathbb Q}$ (an integral proper smooth relative-dimension-one scheme whose function field is identified with $\bar F$, with a bijection between its closed points and the places of $\bar F$) and a morphism $e_{\mathfrak M}$ from $\mathfrak M.C$ to $X\times_{\mathbb Z[1/(Nqq')]}\operatorname{Spec}\bar{\mathbb Q}$; semilinear-automorphism-valued actions `gal`, `galT` of $\operatorname{Aut}(\bar{\mathbb Q}/\mathbb Q)$ on $\bar F$ and on the fields of a tower datum $\mathbb T$ (for each prime $\ell\notin\{q,q'\}$ a curve field $\mathbb T.F_\ell$ over $\bar{\mathbb Q}$ with two finite integral $\bar{\mathbb Q}$-embeddings $\varphi_{\ell,0},\varphi_{\ell,1}$ of $\bar F$); and semilinear automorphisms $W_0,W_1$ of $\bar F$ and $WT_{\ell,0},WT_{\ell,1}$ of $\mathbb T.F_\ell$.
--
--   A witness consists of: a fake elliptic curve $\mathrm{rep}\,P$ over $\bar{\mathbb Q}$ for each place $P$ of $\bar F$, whose moduli point under `pt` is exactly the $\bar{\mathbb Q}$-point of $X$ obtained from $P$ through $\mathfrak M.\mathrm{pointEquivPlace}^{-1}$, then $e_{\mathfrak M}$, then the first projection; for each $\ell$ a map $\mathrm{repT}_\ell$ from places of $\mathbb T.F_\ell$ to pairs $(E,K)$ with $K$ an extra level at $\ell$ (a $\Lambda$-stable closed subgroup scheme of $E$, killed by $\ell$, finite flat of fibre rank $\ell^2$ and geometrically $(\mathbb Z/\ell)^2$, meeting the level-$N$ structure only in the identity), which is bijective onto isomorphism classes; the requirements that `gal σ` and `galT ℓ σ` induce $\sigma$ on $\bar{\mathbb Q}$ and that the $W$'s and $WT$'s are $\bar{\mathbb Q}$-linear; that restriction along $\varphi_{\ell,0}$ corresponds to forgetting $K$ (an isomorphism of the underlying fake elliptic curves) and restriction along $\varphi_{\ell,1}$ to the $\ell$-isogeny with kernel $K$ (a pair of maps composing to the $\Lambda$-action of $\ell$ in both orders, compatible with group law, $\Lambda$-action and level-$N$ structure); Galois equivariance of $\mathrm{rep}$ and $\mathrm{repT}$, the latter spelled out as a pullback square along $\operatorname{Spec}\sigma$ whose comparison morphism respects the relative group law and the $\Lambda$-action and carries the level-$N$ and extra-level subschemes forward; and that $W_0,W_1$ (resp. $WT_{\ell,0},WT_{\ell,1}$) move places to Atkin–Lehner quotients at $q$, $q'$, where the kernel of the quotient map is characterised as the points annihilated by all $m\in\Lambda$ with $m\,\bar m$ an integer multiple of $q$ (resp. $q'$). All of these conditions are fields of the structure, so a witness is data satisfying a congruence-by-congruence list of moduli-theoretic identities on a chosen model, not an abstract equivalence of moduli problems.
--
--   **Relation to Mathlib.** Mathlib has no notion of fake elliptic curves with quaternionic multiplication, of their level structures, or of Shimura-curve Hecke towers; these, together with the project's [`AlgebraicCurve.Place`](../def/AlgebraicCurve_DivisorClassGroup.html#L22), `CurveModel`, `SemilinearAut` and `HeckeTower.TowerData`, are the project's own. Only the underlying scheme-theoretic apparatus (schemes, pullbacks, closed immersions, finite flat morphisms, valuation subrings) is Mathlib's.
--
--   **Where it is used.** The structure is the interface through which the places of a Shimura curve over $\bar{\mathbb Q}$ and of the fields of its Hecke tower are read as moduli of fake elliptic curves, so that the tower maps become the two degeneracy maps of an $\ell$-isogeny correspondence and the distinguished involutions become Atkin–Lehner quotients at $q$ and $q'$. It is used in the Čerednik–Drinfeld part of the development, where Hecke and Galois action on the Jacobian of such a curve are compared with their modular-curve counterparts.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_CerednikDrinfeld_QMModuliTower.lean

import Definitions.Def_CerednikDrinfeld_QMModuliProps
import Definitions.Def_CerednikDrinfeld_HeckeTower
import Definitions.Def_AlgebraicCurve_CurveModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsDedekindDomain AlgebraicCurve
open scoped Quaternion TensorProduct NumberField

namespace CerednikDrinfeld.QM

variable {a b : ℚ}

structure ModuliTowerWitness (Λ : Submodule ℤ ℍ[ℚ, a, b]) (N q q' : ℕ) [Fact q.Prime] [Fact q'.Prime]
    (Fbar : Type) [Field Fbar] [Algebra (AlgebraicClosure ℚ) Fbar]
    (X : Scheme.{0}) (πX : X ⟶ Spec (CommRingCat.of (Localization.Away ((N * q * q' : ℕ) : ℤ))))
    (sbar : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Spec (CommRingCat.of (Localization.Away ((N * q * q' : ℕ) : ℤ))))
    (pt : ∀ (S : Type) [CommRing S]
      (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of (Localization.Away ((N * q * q' : ℕ) : ℤ)))),
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


