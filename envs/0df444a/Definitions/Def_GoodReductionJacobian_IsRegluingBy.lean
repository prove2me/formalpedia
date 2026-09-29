-- Prove2me | Definitions.Def_GoodReductionJacobian_IsRegluingBy
-- name    : GoodReductionJacobian_IsRegluingBy
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:27.528425+00:00
-- url     : https://prove2.me/theorems/a98f31c1-399e-50bc-8e9d-c177278613c4
-- title:
--   Regluing relation between two bare deformations along a cover
-- statement:
--   Fix a ring $S$, a scheme $A_S$ with a morphism $f_S : A_S \to \operatorname{Spec} S$ and a relative group law $L_S$ on $f_S$, and a ring $B$ with $S$ a $B$-algebra. A `BareDeformation` $D$ of $(f_S, L_S)$ to $B$ consists of a scheme $D.A$ with a structural morphism $D.f : D.A \to \operatorname{Spec} B$, a commutative relative group law $D.L$ on $D.f$ together with the bundle of properties (smooth, proper, connected fibres, group law present), a morphism $D.g : A_S \to D.A$ exhibiting $f_S$ as the base change of $D.f$ along $\operatorname{Spec} S \to \operatorname{Spec} B$, and the compatibility of $D.g$ with the two group laws on points.
--
--   Given two such deformations $D_0$ and $D$, an ordered affine open cover $\mathcal U$ of $D_0.A$ (finite linearly ordered index set, affine opens $U_i$ covering $D_0.A$), and for each strictly increasing pair $s = (i<j)$, written as an element of `𝒰.Idx 1`, a self-isomorphism $\tau_s$ of the open subscheme $U_s = U_i \cap U_j$, the predicate `IsRegluingBy D₀ 𝒰 τ D` asserts three things. First, each $\tau_s$ is a morphism over $\operatorname{Spec} B$: composing $\tau_s$ with the inclusion of $U_s$ followed by $D_0.f$ gives back that inclusion followed by $D_0.f$. Second, each $\tau_s$ fixes the part coming from $A_S$: the restriction $D_0.g \mid_{U_s} : D_0.g^{-1}(U_s) \to U_s$ followed by $\tau_s$ equals itself. Third, there exists a family of morphisms $\iota_i : U_i \to D.A$ which are open immersions, satisfy $\iota_i$ followed by $D.f$ equals the inclusion of $U_i$ followed by $D_0.f$, are jointly surjective on underlying points, are compatible with the comparison morphisms ($D_0.g \mid_{U_i}$ followed by $\iota_i$ equals the inclusion $D_0.g^{-1}(U_i) \to A_S$ followed by $D.g$), and are glued by $\tau$: for $s=(i<j)$, the inclusion $U_s \subseteq U_i$ followed by $\iota_i$ equals $\tau_s$ followed by the inclusion $U_s \subseteq U_j$ followed by $\iota_j$.
--
--   Thus the regluing is recorded as a relation between two given deformations rather than as a construction of a glued scheme; no cocycle condition on $\tau$ is imposed, and the relation constrains $D$ only through $D.A$, $D.f$ and $D.g$, not through its group law.
--
--   **Relation to Mathlib.** Mathlib provides gluing data for schemes and affine open covers, but no notion of a deformation of a scheme with a relative group law nor of regluing one by transition automorphisms; `BareDeformation`, `Scheme.OrderedAffineCover` (a cover with a finite linearly ordered index set, for alternating Čech indices) and `IsRegluingBy` are the project's own. The restriction notations $f \mid_U$ and $f^{-1}U$ and the morphism `homOfLE` between open subschemes are Mathlib's.
--
--   **Where it is used.** The predicate belongs to the project's treatment of abelian schemes over a base ring, in particular Jacobians with good reduction: it compares two lifts of the same situation along the base change $B \to S$, which is the form in which lifts along nilpotent thickenings and the resulting effect on the associated formal group are analysed.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_GoodReductionJacobian_IsRegluingBy.lean

import Definitions.Def_GoodReductionJacobian_BareDeformation
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NeronModelInfra

namespace GoodReductionJacobian.BareDeformation

variable {S : Type} [CommRing S] {Aₛ : Scheme.{0}} {fₛ : Aₛ ⟶ Spec (CommRingCat.of S)} {Lₛ : RelativeGroupLaw S fₛ}
  {B : Type} [CommRing B] [Algebra B S]

def IsRegluingBy (D₀ : BareDeformation fₛ Lₛ B) (𝒰 : D₀.A.OrderedAffineCover)
    (τ : ∀ s : 𝒰.Idx 1, ((↑(𝒰.inter s) : Scheme.{0}) ≅ ↑(𝒰.inter s)))
    (D : BareDeformation fₛ Lₛ B) : Prop :=

  (∀ s : 𝒰.Idx 1, (τ s).hom ≫ (𝒰.inter s).ι ≫ D₀.f = (𝒰.inter s).ι ≫ D₀.f) ∧

  (∀ s : 𝒰.Idx 1, (D₀.g ∣_ 𝒰.inter s) ≫ (τ s).hom = D₀.g ∣_ 𝒰.inter s) ∧

  ∃ ι : ∀ i : 𝒰.ι, (↑(𝒰.U i) : Scheme.{0}) ⟶ D.A,
    (∀ i, IsOpenImmersion (ι i)) ∧
    (∀ i, ι i ≫ D.f = (𝒰.U i).ι ≫ D₀.f) ∧
    (∀ x : D.A, ∃ (i : 𝒰.ι) (y : ↑(𝒰.U i)), (ι i).base y = x) ∧
    (∀ i, (D₀.g ∣_ 𝒰.U i) ≫ ι i = (D₀.g ⁻¹ᵁ 𝒰.U i).ι ≫ D.g) ∧
    (∀ s : 𝒰.Idx 1,
      D₀.A.homOfLE (𝒰.inter_le s 0) ≫ ι (s.1 0) = (τ s).hom ≫ D₀.A.homOfLE (𝒰.inter_le s 1) ≫ ι (s.1 1))

end GoodReductionJacobian.BareDeformation

end


