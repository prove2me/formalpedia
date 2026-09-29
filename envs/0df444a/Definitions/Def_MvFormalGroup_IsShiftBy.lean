-- Prove2me | Definitions.Def_MvFormalGroup_IsShiftBy
-- name    : MvFormalGroup_IsShiftBy
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:29.330635+00:00
-- url     : https://prove2.me/theorems/eb0a3c45-be3f-54d0-b8b7-589d14dac882
-- title:
--   Shifting a formal group deformation by a first-order class
-- statement:
--   Fix a local ring $B$ with residue field $k=\mathrm{ResidueField}(B)$ and a $B$-algebra $B_1$. The context also fixes a group $V$ carrying compatible $k$- and $B$-module structures (the $B$-action factoring through $k$ by a scalar-tower assumption) together with a $B$-linear map $\iota : V \to B$, a $d$-dimensional formal group law $F$ over $B$, and a $k$-linear map $w$ from the $k$-dual of $V$ to the first-order deformation space $t$ of the reduction $F\otimes_B k$; such a $w$ is the chosen spelling of an element of $V\otimes_k t$. Here $t =$ `firstOrderDeformationSpace` is the quotient of the space `firstOrderCocycles` of $k$-linear combinations of $\varepsilon$-parts of commutative deformations of $F\otimes_B k$ over the dual numbers $k[\varepsilon]$ by its intersection with `firstOrderCoboundaries`, the span of those $\varepsilon$-parts of commutative deformations that are strictly isomorphic to a deformation with vanishing $\varepsilon$-part; a `Deformation` of a law $G_0$ over $S$ to a base $B$ is a structure consisting of a law over $B$ together with the equation that its coefficientwise image in $S$ is $G_0$.
--
--   For two lifts $G, G'$ of $F\otimes_B B_1$ to $B$, the predicate `IsShiftBy` asserts the existence of finitely many $v_i \in V$, cocycles $z_i$ in `firstOrderCocycles` of $F\otimes_B k$, and $d$-tuples $\tilde z_i$ of power series in $2d$ variables over $B$ reducing coefficientwise to $z_i$, such that $w(\xi) = \sum_i \xi(v_i)\,[z_i]$ for every $\xi$ in the dual of $V$ and, componentwise as power series over $B$, $G' = G + \sum_i \iota(v_i)\,\tilde z_i$. Thus the relation is stated on chosen representatives, with the representing data $(v_i, z_i, \tilde z_i)$ quantified existentially inside, rather than as a group action defined once and for all.
--
--   **Relation to Mathlib.** Built on Mathlib's multivariate power series and their substitution operation; the multi-dimensional formal group laws, their deformations, the first-order cocycles/coboundaries and this shift relation are the project's own definitions.
--
--   **Where it is used.** The predicate records, for a small extension $B \to B_1$ with $\iota$ presenting the relevant ideal of $B$, how the tangent space of the reduction acts on the set of lifts of a formal group law, in the shape needed for the deformation theory of formal groups attached to abelian schemes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_MvFormalGroup_IsShiftBy.lean

import Mathlib
import Definitions.Def_MvFormalGroup_FirstOrderDeformation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

namespace MvFormalGroup.Deformation

open IsLocalRing

def IsShiftBy {B : Type} [CommRing B] [IsLocalRing B] {B₁ : Type} [CommRing B₁] [Algebra B B₁]
    (V : Type) [AddCommGroup V] [Module (ResidueField B) V] [Module B V] [IsScalarTower B (ResidueField B) V]
    (ι : V →ₗ[B] B) {d : ℕ} (F : MvFormalGroup d B)
    (w : Module.Dual (ResidueField B) V →ₗ[ResidueField B] firstOrderDeformationSpace (F.map (residue B)))
    (G G' : Deformation (F.map (algebraMap B B₁)) B) : Prop :=
  ∃ (n : ℕ) (v : Fin n → V) (z : Fin n → ↥(firstOrderCocycles (F.map (residue B))))
    (zl : Fin n → Fin d → MvPowerSeries (Fin d ⊕ Fin d) B),
    (∀ i l, MvPowerSeries.map (residue B) (zl i l) = (z i : Fin d → MvPowerSeries (Fin d ⊕ Fin d) (ResidueField B)) l) ∧
    (∀ ξ : Module.Dual (ResidueField B) V, w ξ = ∑ i, ξ (v i) • Submodule.Quotient.mk (z i)) ∧
    (∀ l, G'.F.toPowerSeries l = G.F.toPowerSeries l + ∑ i, ι (v i) • zl i l)

end MvFormalGroup.Deformation

end


