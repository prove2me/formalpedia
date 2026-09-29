-- Prove2me | Definitions.Def_GoodReductionJacobian_BareDeformation
-- name    : GoodReductionJacobian_BareDeformation
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:27.528425+00:00
-- url     : https://prove2.me/theorems/9f2d176d-5ff2-521f-aefd-a918809bf64e
-- title:
--   Bare deformations of schemes with a relative group law
-- statement:
--   Fix a commutative ring $S$, a scheme $A_S$ with a structure morphism $f_S : A_S \to \operatorname{Spec} S$ carrying a relative group law $L_S$, and a commutative ring $B$ with $S$ a $B$-algebra. Here a relative group law on a morphism $f : A \to \operatorname{Spec} R$ is the project's functor-of-points datum: a group structure (multiplication, unit, inverse, with associativity, unit laws, left inverse) on the sections $\{P : T \to A \mid P \text{ followed by } f = t\}$ for every $t : T \to \operatorname{Spec} R$, natural in $T$. A term of `BareDeformation fₛ Lₛ B` consists of: a scheme $A$ with $f : A \to \operatorname{Spec} B$; a relative group law $L$ on $f$ which is commutative (its multiplication is symmetric at every $t$); the bundle `AbelianSchemePropertyBundle B f`, asserting that $f$ is smooth and proper, that each fibre $f^{-1}(s)$ of the underlying map of spaces is connected, and that a relative group law on $f$ exists; a morphism $g : A_S \to A$ such that the square formed by $g$, $f_S$, $f$ and $\operatorname{Spec}$ of $B \to S$ is cartesian, so $A_S$ is the base change of $A$ along $B \to S$; and a field `hom` asserting that $g$ is a homomorphism on points, namely that for all $t : T \to \operatorname{Spec} S$ and sections $P, Q$ of $f_S$ over $t$, multiplying in $L_S$ and then composing with $g$ agrees with multiplying the composites $P$-then-$g$, $Q$-then-$g$ in $L$ over the induced base point.
--
--   Two such deformations $D$, $D'$ are declared `IsIso` when some scheme isomorphism $e : D.A \cong D'.A$ satisfies $e$ followed by $D'.f$ equal to $D.f$ and $D.g$ followed by $e$ equal to $D'.g$; no compatibility with the group laws or unit sections is demanded. Finally, `LiftsCoordinates` relates formal coordinate systems: for [`FormalCoordinates`](../def/WeierstrassCurve_ZeroComponentReduction.html#L28) $\theta_S$ of $f_S$ and $\theta$ of $D.f$ in $d$ variables, it asserts that for every ring $B''$ that is simultaneously a $B$-algebra and an $S$-algebra compatibly, and every $d$-tuple $s$ of nilpotent elements of $B''$, the morphism $\theta_S(B'', s)$ followed by $g$ equals $\theta(B'', s)$.
--
--   **Relation to Mathlib.** Mathlib supplies `Smooth`, `IsProper` and `IsPullback`, used in the conditions above, but has no notion of abelian scheme or of deformation of one; the group structure is carried by the project's functorial `RelativeGroupLaw` rather than by monoid-object structure in the category of schemes.
--
--   **Where it is used.** These structures package the deformation-theoretic objects attached to an abelian scheme over a base ring: a lift of a given scheme-with-group-law along a ring homomorphism $B \to S$, together with the relation used to state that formal coordinates on the lift reduce to given ones, as required for Serre–Tate style comparisons in the good-reduction analysis of Jacobians.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_GoodReductionJacobian_BareDeformation.lean

import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_FormalGroupAlongSection

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NeronModelInfra

namespace GoodReductionJacobian

structure BareDeformation {S : Type} [CommRing S] {Aₛ : Scheme.{0}} (fₛ : Aₛ ⟶ Spec (CommRingCat.of S))
    (Lₛ : RelativeGroupLaw S fₛ) (B : Type) [CommRing B] [Algebra B S] : Type 1 where

  A : Scheme.{0}

  f : A ⟶ Spec (CommRingCat.of B)

  L : RelativeGroupLaw B f

  comm : L.IsCommutative

  bundle : AbelianSchemePropertyBundle B f

  g : Aₛ ⟶ A

  cart : IsPullback g fₛ f (Spec.map (CommRingCat.ofHom (algebraMap B S)))

  hom : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P Q : SchemeHomOver t fₛ),
    (Lₛ.mul t P Q).1 ≫ g =
      (L.mul (t ≫ Spec.map (CommRingCat.ofHom (algebraMap B S)))
        ⟨P.1 ≫ g, by rw [Category.assoc, cart.w, ← Category.assoc, P.2]⟩
        ⟨Q.1 ≫ g, by rw [Category.assoc, cart.w, ← Category.assoc, Q.2]⟩).1

namespace BareDeformation

variable {S : Type} [CommRing S] {Aₛ : Scheme.{0}} {fₛ : Aₛ ⟶ Spec (CommRingCat.of S)} {Lₛ : RelativeGroupLaw S fₛ}
  {B : Type} [CommRing B] [Algebra B S]

def IsIso (D D' : BareDeformation fₛ Lₛ B) : Prop :=
  ∃ e : D.A ≅ D'.A, e.hom ≫ D'.f = D.f ∧ D.g ≫ e.hom = D'.g

def LiftsCoordinates {d : ℕ} (D : BareDeformation fₛ Lₛ B)
    (θₛ : RelativeGroupLaw.FormalCoordinates fₛ d) (θ : RelativeGroupLaw.FormalCoordinates D.f d) : Prop :=
  ∀ (B'' : Type) [CommRing B''] [Algebra B B''] [Algebra S B''] [IsScalarTower B S B''] (s : Fin d → B''),
    (∀ i, IsNilpotent (s i)) → (θₛ B'' s).1 ≫ D.g = (θ B'' s).1

end BareDeformation

end GoodReductionJacobian

end


