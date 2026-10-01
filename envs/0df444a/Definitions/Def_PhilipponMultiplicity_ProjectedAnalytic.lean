-- Prove2me | Definitions.Def_PhilipponMultiplicity_ProjectedAnalytic
-- name    : PhilipponMultiplicity_ProjectedAnalytic
-- status  : Definition
-- author  : @tomasz
-- created : 2026-10-01T10:32:03.802835+00:00
-- url     : https://prove2.me/theorems/facf9b7b-3681-47d9-8012-a171e44019da
-- title:
--   The analytic parametrization induced by coordinate projection
-- statement:
--   For a nonempty selection $I$ of factors of an embedded group product $G$, define a section $\sigma:G_I\to G$ by inserting the identity in every omitted factor. It satisfies
--   $$
--   \pi\sigma=\mathrm{id},\qquad \sigma(0)=0.
--   $$
--   Given an analytic subgroup parametrization $A$, define its projected parametrization on the same parameter ball by
--   $$
--   B(z)=\pi(A(z)).
--   $$
--   For a translated base point $y\in G_I$, its homogeneous coordinate lift is the restriction of the original lift of $A$ at $\sigma(y)$ to the retained coordinate blocks. The constructor verifies the local homomorphism identities, analyticity, power-series representation on the original ball, and representation of the translated projected points. This is an explicit construction, with no assumed contact, codimension, rank, or vanishing conclusion.
-- source:
--   Auxiliary tangent-space statement for the coordinate-projection treatment of zero multidegrees in P. Philippon, Lemmes de zéros dans les groupes algébriques commutatifs, Bulletin de la SMF 114 (1986), pp.360–361, Corollary 2.3; analytic subgroup and contact conventions on pp.357–358. This is a supporting formalization lemma, not a separately numbered theorem of the paper. https://numdam.org/articles/10.24033/bsmf.2060/

import Definitions.Def_PhilipponMultiplicity_FactorProjection

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators Topology
open Filter
noncomputable section

namespace PhilipponMultiplicity.GroupFactorSelection
universe u
variable {K : Type u} [NontriviallyNormedField K] {G : EmbeddedGroupProduct K}
variable (s : GroupFactorSelection G)

/-- Insert the identity in the factors omitted by the selection. -/
def sectionPoint (y : s.group.Point) : G.Point := fun i =>
  if hi : i ∈ s.val then
    (Equiv.piCongrLeft (fun i : s.val => (G.factor i.val).Point) s.indexEquiv y) ⟨i,hi⟩
  else 0

theorem project_sectionPoint (y : s.group.Point) : s.project (s.sectionPoint y) = y := by
  funext i
  change (if hi : s.index i ∈ s.val then _ else _) = y i
  have hi : s.index i ∈ s.val := (s.indexEquiv i).property
  rw [dif_pos hi]
  change (Equiv.piCongrLeft (fun i : s.val => (G.factor i.val).Point) s.indexEquiv y)
    (s.indexEquiv i) = y i
  simp

theorem sectionPoint_zero : s.sectionPoint 0 = 0 := by
  funext i
  by_cases hi : i ∈ s.val
  · change (if hi : i ∈ s.val then _ else _) = 0
    rw [dif_pos hi]
    have hz : (Equiv.piCongrLeft (fun i : s.val => (G.factor i.val).Point)
        s.indexEquiv) 0 = fun _ => 0 := by
      funext j
      obtain ⟨k,rfl⟩ := s.indexEquiv.surjective j
      simp
    rw [hz]
  · simp only [sectionPoint,dif_neg hi,Pi.zero_apply]

/-- The projected parametrization uses the original parameter ball. Its
translated lifts restrict the original lifts at the identity section. -/
def projectedAnalytic (A : AnalyticSubgroup G) : AnalyticSubgroup s.group where
  parameterDimension := A.parameterDimension
  parameterDimension_pos := A.parameterDimension_pos
  radius := A.radius
  radius_pos := A.radius_pos
  domain := A.domain
  domain_eq_ball := A.domain_eq_ball
  domain_open := A.domain_open
  zero_mem := A.zero_mem
  map z := s.project (A.map z)
  map_zero := by rw [A.map_zero,map_zero]
  map_add x y h := by rw [A.map_add x y h,map_add]
  lift y z v := A.lift (s.sectionPoint y) z (s.coordinateIndex v)
  lift_analytic y v := A.lift_analytic _ _
  base_series v := by
    rw [s.sectionPoint_zero]
    exact A.base_series (s.coordinateIndex v)
  base_represents z i := by
    rw [s.sectionPoint_zero]
    exact A.base_represents z (s.index i)
  lift_represents y := by
    filter_upwards [A.lift_represents (s.sectionPoint y)] with z hz
    obtain ⟨hz,hr⟩ := hz
    refine ⟨hz,?_⟩
    intro i
    obtain ⟨hn,he⟩ := hr (s.index i)
    refine ⟨hn,?_⟩
    change _ = s.group.embedding (s.project (s.sectionPoint y + A.map ⟨z,hz⟩)) i at he
    rw [map_add,s.project_sectionPoint] at he
    exact he

end PhilipponMultiplicity.GroupFactorSelection


