-- Prove2me | Definitions.Def_FormalGroup_PointTransport
-- name    : FormalGroup_PointTransport
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.503845+00:00
-- url     : https://prove2.me/theorems/96629b8b-8bf9-5f43-bb1d-db312624aeaf
-- title:
--   Homomorphisms and isomorphisms of formal group laws; base change
-- statement:
--   Throughout, $R$ is a commutative ring and $F$, $G$ are formal group laws over $R$ in Mathlib's sense, each given by its two-variable power series `toPowerSeries` in `MvPowerSeries (Fin 2) R`. The helper [`FormalGroup.LawHom.substX i φ`](../def/FormalGroup_PointTransport.html#L12) is the substitution of the variable $X_i$ ($i \in \{0,1\}$) into a one-variable series $φ$, i.e. $φ(X_i)$ regarded as an element of $R[[X_0,X_1]]$.
--
--   [`FormalGroup.LawHom F G`](../def/FormalGroup_PointTransport.html#L15) is a structure whose data is a single power series `series` $= φ \in R[[Z]]$, together with two fields that are propositions: $φ$ has vanishing constant coefficient, and the compatibility $φ(F(X_0,X_1)) = G(φ(X_0), φ(X_1))$ holds in $R[[X_0,X_1]]$, the left side being the substitution of $F$'s series into $φ$ and the right side the substitution of the pair $(φ(X_0), φ(X_1))$ into $G$'s series. Thus the axioms of a homomorphism are carried as fields of the structure. [`FormalGroup.LawIso F G`](../def/FormalGroup_PointTransport.html#L24) extends this by the further requirement that the linear coefficient $\mathrm{coeff}_1 φ$ be a unit of $R$; invertibility of $φ$ under substitution is therefore not part of the data.
--
--   The action on points is `LawHom.app`: for a commutative $R$-algebra $A$ equipped with a uniform structure, `φ.app x` is the evaluation `evalSeries φ.series x`, namely $\mathrm{eval}_2$ of $φ$ along `algebraMap R A` at $x$, with $R$ given the discrete uniformity. `LawHom.appAdic φ I x` is the same evaluation performed in the uniform structure attached to an ideal $I \subseteq A$.
--
--   Finally, [`FormalGroup.IsBaseChange F f G`](../def/FormalGroup_PointTransport.html#L41), for a ring homomorphism $f : R \to S$ and a formal group law $G$ over $S$, is the relation asserting the equality of series $G(X_0,X_1) = f_*F(X_0,X_1)$, where $f_*$ applies $f$ to coefficients. It is a predicate on a pair of given laws, not a construction of $G$ from $F$.
--
--   **Relation to Mathlib.** Built on Mathlib's `FormalGroup` (a one-dimensional formal group law presented by its series in `MvPowerSeries (Fin 2) R`); the homomorphism and isomorphism structures are the project's own, kept under the names `LawHom`/`LawIso`, and carry no identity, composition or inverse as data.
--
--   **Where it is used.** This vocabulary supports the transport arguments for Drinfeld level structures on formal groups: isomorphisms of Weierstrass models induce isomorphisms of the associated formal group laws, Drinfeld bases are carried along such isomorphisms, and the universal property of the Lubin–Tate deformation ring with Drinfeld level structure is phrased using `LawIso` together with the base-change relation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_FormalGroup_PointTransport.lean

import Mathlib
import Definitions.Def_FormalGroup_NSeries

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

namespace FormalGroup

variable {R : Type*} [CommRing R]

def LawHom.substX (i : Fin 2) (φ : PowerSeries R) : MvPowerSeries (Fin 2) R :=
  PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries (Fin 2) R) φ

structure LawHom (F G : FormalGroup R) where

  series : PowerSeries R

  constantCoeff_series : PowerSeries.constantCoeff series = 0

  comm : PowerSeries.subst F.toPowerSeries series =
    MvPowerSeries.subst ![LawHom.substX 0 series, LawHom.substX 1 series] G.toPowerSeries

structure LawIso (F G : FormalGroup R) extends LawHom F G where

  isUnit_coeff_one : IsUnit (PowerSeries.coeff 1 series)

namespace LawHom

variable {F G : FormalGroup R}

def app {A : Type*} [CommRing A] [UniformSpace A] [Algebra R A] (φ : LawHom F G) (x : A) : A :=
  FormalGroup.evalSeries φ.series x

def appAdic {A : Type*} [CommRing A] [Algebra R A] (φ : LawHom F G) (I : Ideal A) (x : A) : A :=
  letI : WithIdeal A := ⟨I⟩
  φ.app x

end LawHom

def IsBaseChange (F : FormalGroup R) {S : Type*} [CommRing S] (f : R →+* S) (G : FormalGroup S) : Prop :=
  G.toPowerSeries = MvPowerSeries.map f F.toPowerSeries

end FormalGroup

end


