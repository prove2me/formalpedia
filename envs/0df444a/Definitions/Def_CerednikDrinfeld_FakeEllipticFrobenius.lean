-- Prove2me | Definitions.Def_CerednikDrinfeld_FakeEllipticFrobenius
-- name    : CerednikDrinfeld_FakeEllipticFrobenius
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.014713+00:00
-- url     : https://prove2.me/theorems/03829d54-a266-50b6-bf9a-227aebe26fac
-- title:
--   Frobenius–Verschiebung data for fake elliptic curves
-- statement:
--   Throughout, $a,b\in\mathbb Q$, $\Lambda$ is a $\mathbb Z$-submodule of the quaternion algebra $\mathbb H[\mathbb Q,a,b]$, $N$ a natural number, $S$ a commutative ring of characteristic a prime $\ell$, and $E$, $E_\ell$ are fake elliptic curves over $S$ with $\Lambda$-action and level-$N$ structure in the sense of `FakeEllipticCurve` (a smooth proper group scheme $f\colon A\to\operatorname{Spec} S$ with two-dimensional fibres, a relative group law $L$ on points, a $\Lambda$-action `act` and a closed level subscheme `lev`).
--
--   The structure `FrobeniusVerschiebungData ℓ E Eℓ` packages, as data together with the required identities as fields: a morphism $\mathrm{pr}\colon A_\ell\to A$ exhibiting $E_\ell$ as the base change of $E$ along the ring Frobenius $x\mapsto x^{\ell}$ of $S$ (the square with $\mathrm{pr}$, the structure morphisms and $\operatorname{Spec}$ of the Frobenius is cartesian), compatible with the group laws on points, with the $\Lambda$-actions ($\mathrm{act}_x$ followed by $\mathrm{pr}$ equals $\mathrm{pr}$ followed by $\mathrm{act}_x$) and carrying points of `Eℓ.lev` into `E.lev`; morphisms $F\colon A\to A_\ell$ and $V\colon A_\ell\to A$ over $S$ which are homomorphisms for the relative group laws on $T$-points for every scheme $T$ over $\operatorname{Spec} S$, commute with the $\Lambda$-action, preserve the level structures in the respective directions, and satisfy $V\circ F=[\ell]$ and $F\circ V=[\ell]$ on points, where $[\ell]$ is $\ell$-fold iteration of the group law `nsmulPt`, not the action of $\ell\in\Lambda$; and finally the identification of $F$ followed by $\mathrm{pr}$ with absolute Frobenius: for every commutative ring $B$ of characteristic $\ell$ and every $x\colon\operatorname{Spec} B\to A$, one has $\mathrm{pr}\circ F\circ x=x\circ\operatorname{Spec}(\mathrm{frobenius}\,B\,\ell)$.
--
--   The accompanying declarations are: `isPullback`, extracting from a datum the predicate `FakeEllipticCurve.IsPullback` for the Frobenius of $S$; `FPt` and `VPt`, viewing $F$ and $V$ as points over the respective structure morphisms; `HasFrobeniusVerschiebung`, the existence of such a datum; and `IsFrobeniusKernel`, asserting for a pair $u=(E,K)$ with extra level $\ell$-structure `levK` and a datum for $(E,E_\ell)$ that, on $T$-points for all $T$, a point factors through `levK` exactly when its image under $F$ is the identity point — i.e. the extra level is the kernel of $F$, expressed relationally on points.
--
--   **Relation to Mathlib.** The Frobenius ring endomorphism is Mathlib's `frobenius`; fake elliptic curves, their relative group laws on points and the Frobenius–Verschiebung vocabulary above are the project's own notions, with no Mathlib counterpart.
--
--   **Where it is used.** These notions supply the characteristic-$\ell$ vocabulary for the point-level Eichler–Shimura congruence on the Shimura curve attached to an indefinite quaternion algebra: over a field of characteristic $\ell$, extra level structures of order $\ell^2$ on a fake elliptic curve are compared with the kernel of the relative Frobenius and with the fibres of the Verschiebung. Nothing here asserts existence of a datum; that is abelian-scheme input used elsewhere.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_CerednikDrinfeld_FakeEllipticFrobenius.lean

import Mathlib.Algebra.CharP.Frobenius
import Definitions.Def_CerednikDrinfeld_QMModuliProps

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open scoped Quaternion

namespace CerednikDrinfeld.QM.FakeEllipticCurve

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {S : Type u} [CommRing S]

structure FrobeniusVerschiebungData (ℓ : ℕ) [Fact ℓ.Prime] [CharP S ℓ] (E Eℓ : FakeEllipticCurve Λ N S) : Type u where

  pr : Eℓ.A ⟶ E.A

  pr_isPullback : CategoryTheory.IsPullback pr Eℓ.f E.f (Spec.map (CommRingCat.ofHom (frobenius S ℓ)))

  pr_mul : ∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t' Eℓ.f),
    (Eℓ.L.mul t' P Q).1 ≫ pr =
      (E.L.mul (t' ≫ Spec.map (CommRingCat.ofHom (frobenius S ℓ)))
        ⟨P.1 ≫ pr, by rw [Category.assoc, pr_isPullback.w, ← Category.assoc, P.2]⟩
        ⟨Q.1 ≫ pr, by rw [Category.assoc, pr_isPullback.w, ← Category.assoc, Q.2]⟩).1

  pr_act : ∀ x : ↥Λ, Eℓ.act x ≫ pr = pr ≫ E.act x

  pr_lev : ∀ {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t' Eℓ.f),
    FactorsThrough Eℓ.lev P → ∃ P₀ : T ⟶ E.C, P₀ ≫ E.lev = P.1 ≫ pr

  F : E.A ⟶ Eℓ.A

  F_over : F ≫ Eℓ.f = E.f

  V : Eℓ.A ⟶ E.A

  V_over : V ≫ E.f = Eℓ.f

  F_hom : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t E.f),
    mapPt F F_over (E.L.mul t P Q) = Eℓ.L.mul t (mapPt F F_over P) (mapPt F F_over Q)

  V_hom : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t Eℓ.f),
    mapPt V V_over (Eℓ.L.mul t P Q) = E.L.mul t (mapPt V V_over P) (mapPt V V_over Q)

  F_act : ∀ x : ↥Λ, E.act x ≫ F = F ≫ Eℓ.act x

  V_act : ∀ x : ↥Λ, Eℓ.act x ≫ V = V ≫ E.act x

  F_lev : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E.f),
    FactorsThrough E.lev P → FactorsThrough Eℓ.lev (mapPt F F_over P)

  V_lev : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t Eℓ.f),
    FactorsThrough Eℓ.lev P → FactorsThrough E.lev (mapPt V V_over P)

  V_F : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t E.f),
    mapPt V V_over (mapPt F F_over P) = nsmulPt E.L t ℓ P

  F_V : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (Q : SchemeHomOver t Eℓ.f),
    mapPt F F_over (mapPt V V_over Q) = nsmulPt Eℓ.L t ℓ Q

  F_frobenius : ∀ (B : Type u) [CommRing B] [CharP B ℓ] (x : Spec (CommRingCat.of B) ⟶ E.A),
    x ≫ F ≫ pr = Spec.map (CommRingCat.ofHom (frobenius B ℓ)) ≫ x

namespace FrobeniusVerschiebungData

variable {ℓ : ℕ} [Fact ℓ.Prime] [CharP S ℓ] {E Eℓ : FakeEllipticCurve Λ N S}

theorem isPullback (D : FrobeniusVerschiebungData ℓ E Eℓ) : IsPullback (frobenius S ℓ) E Eℓ :=
  ⟨D.pr, D.pr_isPullback, D.pr_mul, D.pr_act, D.pr_lev⟩

def FPt (D : FrobeniusVerschiebungData ℓ E Eℓ) : SchemeHomOver E.f Eℓ.f := ⟨D.F, D.F_over⟩

def VPt (D : FrobeniusVerschiebungData ℓ E Eℓ) : SchemeHomOver Eℓ.f E.f := ⟨D.V, D.V_over⟩

end FrobeniusVerschiebungData

def HasFrobeniusVerschiebung (ℓ : ℕ) [Fact ℓ.Prime] [CharP S ℓ] (E Eℓ : FakeEllipticCurve Λ N S) : Prop :=
  Nonempty (FrobeniusVerschiebungData ℓ E Eℓ)

def IsFrobeniusKernel {ℓ : ℕ} [Fact ℓ.Prime] [CharP S ℓ] {Eℓ : FakeEllipticCurve Λ N S}
    (u : WithExtraLevel Λ N ℓ S) (D : FrobeniusVerschiebungData ℓ u.1 Eℓ) : Prop :=
  ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t u.1.f),
    FactorsThrough u.2.levK P ↔ mapPt D.F D.F_over P = Eℓ.L.one t

end CerednikDrinfeld.QM.FakeEllipticCurve

end


