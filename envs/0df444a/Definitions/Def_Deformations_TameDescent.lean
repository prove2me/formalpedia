-- Prove2me | Definitions.Def_Deformations_TameDescent
-- name    : Deformations_TameDescent
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.503845+00:00
-- url     : https://prove2.me/theorems/6d515f2f-7a14-5b13-a9c6-9fbc524237b1
-- title:
--   Descent of a character along a surjection of groups
-- statement:
--   The module fixes groups $G$ and $\Delta$ and a commutative ring $A$, and defines a single object, [`TaylorWiles.tameDescentChar`](../def/Deformations_TameDescent.html#L9). Its data are a group homomorphism $\pi \colon G \to \Delta$, a proof that $\pi$ is surjective, a character $\chi \colon G \to A^\times$ (a homomorphism into the unit group of $A$), and a proof that $\chi$ is trivial on every element of $\ker \pi$. From these it produces a homomorphism $\Delta \to A^\times$. The construction is the expected one: the hypothesis on $\ker\pi$ lets $\chi$ be factored through the quotient group $G / \ker \pi$ (Mathlib's `QuotientGroup.lift`), and surjectivity of $\pi$ gives the first-isomorphism equivalence $G/\ker\pi \simeq \Delta$ (`QuotientGroup.quotientKerEquivOfSurjective`); the defined character is the inverse of that equivalence, viewed as a homomorphism $\Delta \to G/\ker\pi$, followed by the factored character. Thus, by construction, the resulting character $\xi$ satisfies $\xi(\pi g) = \chi(g)$ for all $g \in G$, and it is the unique character of $\Delta$ with this property, since $\pi$ is surjective. The definition is noncomputable, the inverse of the equivalence being obtained from the surjectivity hypothesis rather than from an explicit section. No hypothesis relating $\pi$, $\chi$ or $A$ to arithmetic is imposed: this is pure group theory, the arithmetic input being supplied at the points of use, where the trivialty of $\chi$ on $\ker\pi$ has to be established.
--
--   **Relation to Mathlib.** Built entirely from Mathlib's `QuotientGroup.lift` and `QuotientGroup.quotientKerEquivOfSurjective`; it packages the universal property of a surjection of groups as a named construction, and introduces no notion absent from Mathlib.
--
--   **Where it is used.** In the Taylor–Wiles argument this is applied at an auxiliary prime $q$ with $G$ an inertia group at $q$, $\Delta$ its tame quotient of $q$-power order used to index the level structure, and $\chi$ a diagonal character of the local restriction of the universal deformation; the descended character of $\Delta$ is what makes the deformation ring an algebra over the group ring of $\Delta_Q$ and feeds into the construction of the diamond characters.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_Deformations_TameDescent.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

namespace TaylorWiles

variable {G Δ A : Type*} [Group G] [Group Δ] [CommRing A]

noncomputable def tameDescentChar (π : G →* Δ) (hπ : Function.Surjective π) (χ : G →* Aˣ)
    (hχ : ∀ g ∈ π.ker, χ g = 1) : Δ →* Aˣ :=
  (QuotientGroup.lift π.ker χ hχ).comp
    (MulEquiv.symm (QuotientGroup.quotientKerEquivOfSurjective π hπ) : Δ →* G ⧸ π.ker)

end TaylorWiles


