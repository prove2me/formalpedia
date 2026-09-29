-- Prove2me | Definitions.Def_MvFormalGroup_Deformation
-- name    : MvFormalGroup_Deformation
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:29.330635+00:00
-- url     : https://prove2.me/theorems/a9570135-9850-5bfe-9f9e-18435d48742c
-- title:
--   Deformations of multivariate formal group laws along a ring map
-- statement:
--   Fix a commutative ring $S$, a natural number $d$, a $d$-dimensional formal group law $G_0$ over $S$ (an element of [`MvFormalGroup d S`](../def/MvFormalGroup_BasicV2.html#L15): a family of $d$ power series in the $2d$ variables indexed by `Fin d ⊕ Fin d` with vanishing constant term, with the coefficient of each linear variable $X_{\mathrm{inl}\,j}$ and $X_{\mathrm{inr}\,j}$ in the $i$-th series equal to $\delta_{ij}$, satisfying the associativity identity under substitution; commutativity is a separate class and is not imposed), and a commutative ring $B$ with an algebra structure $B \to S$. A `Deformation G₀ B` is a structure with two fields: a formal group law $F$ over $B$ of the same dimension $d$, and the requirement `map_eq` that pushing $F$ forward coefficientwise along $\mathrm{algebraMap}_{B,S}$ — the law `F.map (algebraMap B S)`, obtained by applying `MvPowerSeries.map` to each component — is *equal* to $G_0$. So the reduction condition is an equality of laws, not merely an isomorphism with $G_0$; nothing is assumed about $B \to S$ (no surjectivity, nilpotence, local or Artinian hypotheses).
--
--   For two deformations $D, D'$ the predicate `IsIso D D'` asserts the existence of a homomorphism $\varphi$ of formal group laws $D.F \to D'.F$ over $B$ (a [`MvFormalGroup.Hom`](../def/MvFormalGroup_BasicV2.html#L71), i.e. $d$ power series in $d$ variables without constant term intertwining the two group laws) which admits a two-sided inverse homomorphism $\psi$ with respect to `Hom.comp` and `Hom.id`, and which reduces over $S$ to the identity: for each $i$, the image of $\varphi$'s $i$-th component under `MvPowerSeries.map (algebraMap B S)` is the variable $X_i$. Thus `IsIso` is strict isomorphism of deformations, expressed as a relation rather than a chosen datum; it is not proved here to be an equivalence relation. Finally, `refl G₀` is the deformation of $G_0$ to $S$ itself given by $F = G_0$.
--
--   **Relation to Mathlib.** Mathlib has no notion of deformation of a formal group law; the structure [`MvFormalGroup`](../def/MvFormalGroup_BasicV2.html#L15) of multivariate formal group laws and this deformation layer are the project's own, built on Mathlib's substitution calculus for `MvPowerSeries`.
--
--   **Where it is used.** These notions supply the objects of the deformation functor of a formal group law: the set of deformations to $B$ modulo strict isomorphism, which for $S$ the residue field of an Artinian local $B$ is the deformation space in Schlessinger's sense. They are used by the modules on lifting formal group laws (Serre–Tate and Lubin–Tate style arguments) and on tangent-space bounds for formal groups of finite height.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_MvFormalGroup_Deformation.lean

import Definitions.Def_MvFormalGroup_BasicV2

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

namespace MvFormalGroup

@[ext]
structure Deformation {S : Type} [CommRing S] {d : ℕ} (G₀ : MvFormalGroup d S)
    (B : Type) [CommRing B] [Algebra B S] : Type where

  F : MvFormalGroup d B

  map_eq : F.map (algebraMap B S) = G₀

namespace Deformation

variable {S : Type} [CommRing S] {d : ℕ} {G₀ : MvFormalGroup d S} {B : Type} [CommRing B] [Algebra B S]

def IsIso (D D' : Deformation G₀ B) : Prop :=
  ∃ φ : MvFormalGroup.Hom D.F D'.F,
    (∃ ψ : MvFormalGroup.Hom D'.F D.F, ψ.comp φ = MvFormalGroup.Hom.id D.F ∧ φ.comp ψ = MvFormalGroup.Hom.id D'.F) ∧
    ∀ i : Fin d, MvPowerSeries.map (algebraMap B S) (φ.toPowerSeries i) = MvPowerSeries.X i

def refl (G₀ : MvFormalGroup d S) : Deformation G₀ S where
  F := G₀
  map_eq := by
    ext i n
    simp [MvFormalGroup.map, Algebra.algebraMap_self]

end Deformation

end MvFormalGroup

end


