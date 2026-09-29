-- Prove2me | Definitions.Def_GroupCohomology_ContinuousUnramifiedLevelInflation
-- name    : GroupCohomology_ContinuousUnramifiedLevelInflation
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:27.528425+00:00
-- url     : https://prove2.me/theorems/64fa6f93-153e-5706-97e1-b085c6413a09
-- title:
--   Inflation into the S-level continuous H2
-- statement:
--   The setting is a group $G$ together with a level map $r\colon G\to\operatorname{Gal}(\overline{\mathbb Q}/\mathbb Q)$, a commutative ring $k$, a $k$-linear representation $M$ of $G$, a finite set $S$ of rational primes, and an intermediate field $F$ of $\overline{\mathbb Q}/\mathbb Q$ normal over $\mathbb Q$; write $U_F = r^{-1}(\mathrm{Gal}(\overline{\mathbb Q}/F))$ for the preimage under $r$ of the fixing subgroup of $F$, a normal subgroup of $G$. The standing hypothesis `hF` is `F.IsUnramifiedOutside S`, i.e. $F$ is finite over $\mathbb Q$ and, for every prime $q\notin S$ and every valuation subring of $\overline{\mathbb Q}$ lying over $q$, its inertia subgroup over $\mathbb Q$ is contained in the fixing subgroup of $F$.
--
--   The cochain-level inflation maps `levelInflate₁ r M F` and `levelInflate₂ r M F` send a function on $G/U_F$ (respectively on $(G/U_F)^2$) with values in the $U_F$-invariants $M^{U_F}$, viewed as a representation of $G/U_F$, to the function $g\mapsto y(\bar g)$ (respectively $(g,h)\mapsto x(\bar g,\bar h)$) with values in $M$. The lemmas here record that these land in the $S$-level objects: `levelInflate₁ y` is $S$-level constant with witness field $F$ itself, the inflation of a $2$-cocycle lies in `levelCocyclesSr₂ r S M` (the intersection of $2$-cocycles with the $S$-level $2$-cochains), and the inflation of $d_{12}y$ equals $d_{12}$ of the inflation of $y$, hence lies in `levelCoboundariesSr₂ r S M` (the image of the $S$-level $1$-cochains under $d_{12}$).
--
--   From this, `levelInflateCocyclesSr₂` is the $k$-linear map from $2$-cocycles of $M^{U_F}$ over $G/U_F$ to `levelCocyclesSr₂ r S M`, with `coe_levelInflateCocyclesSr₂` identifying its underlying function with `levelInflate₂`; it kills $2$-coboundaries modulo the $S$-level coboundaries. Consequently `continuousH2SrInflation r S M F hF` is a $k$-linear map
--   $$H^2\big(G/U_F,\;M^{U_F}\big)\longrightarrow \mathrm{continuousH2Sr}\,r\,S\,M,$$
--   where the target is the quotient of the $S$-level $2$-cocycles by the $S$-level $2$-coboundaries; it is obtained by factoring the above through the identification of $H^2$ with $2$-cocycles modulo the image of the cycles map, and `continuousH2SrInflation_H2π` states the characterising identity $\mathrm{inf}_F(\pi x) = \pi_S(\mathrm{levelInflateCocyclesSr₂}\,x)$ on $2$-cocycles $x$.
--
--   **Relation to Mathlib.** Mathlib supplies the inhomogeneous $2$-cocycles and $2$-coboundaries, $H^2$ with its projection and its identification with cocycles modulo the cycles map, and the quotient-to-invariants representation; the $S$-level cochain conditions, the quotient `continuousH2Sr` and the inflation map into it are the project's own, and are not Mathlib's inflation map for a normal subgroup.
--
--   **Where it is used.** These maps form the inflation system used to describe the $S$-level continuous $H^2$ of a level map as a colimit of the ordinary $H^2$ of the finite quotients $G/U_F$ over fields $F$ unramified outside $S$, which is how second-cohomology obstruction classes are handled in the deformation-theoretic part of the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_GroupCohomology_ContinuousUnramifiedLevelInflation.lean

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevel
import Definitions.Def_GroupCohomology_LevelSubgroup
import Definitions.Def_GroupCohomology_ContinuousH2Inflation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory

noncomputable section
namespace groupCohomology

section A0
variable {k G : Type} [CommRing k] [Group G] (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (S : Finset Nat.Primes)
  (M : Rep.{0} k G) (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [Normal ℚ F]

omit [Normal ℚ F] in
private lemma coe_mul_eq_of_mem' {g s : G} (hs : r s ∈ F.fixingSubgroup) :
    ((g * s : G) : G ⧸ F.fixingSubgroup.comap r) = (g : G ⧸ F.fixingSubgroup.comap r) := by
  rw [QuotientGroup.eq]; simpa using (F.fixingSubgroup.comap r).inv_mem hs

lemma levelInflate₁_mem_levelCochainsSr₁ (hF : F.IsUnramifiedOutside S) (y : (G ⧸ F.fixingSubgroup.comap r) → M.quotientToInvariants _) :
    levelInflate₁ r M F y ∈ levelCochainsSr₁ r S M :=
  ⟨F, hF, fun g s hs => by simp only [levelInflate₁_apply, coe_mul_eq_of_mem' r F hs]⟩

lemma levelInflate₂_mem_levelCocyclesSr₂ (hF : F.IsUnramifiedOutside S)
    {x : (G ⧸ F.fixingSubgroup.comap r) × (G ⧸ F.fixingSubgroup.comap r) → M.quotientToInvariants _}
    (hx : x ∈ cocycles₂ (M.quotientToInvariants (F.fixingSubgroup.comap r))) :
    levelInflate₂ r M F x ∈ levelCocyclesSr₂ r S M :=
  ⟨levelInflate₂_mem_cocycles₂ hx, ⟨F, hF, fun g g' s s' hs hs' => by
    simp only [levelInflate₂_apply, coe_mul_eq_of_mem' r F hs, coe_mul_eq_of_mem' r F hs']⟩⟩

lemma levelInflate₂_mem_levelCoboundariesSr₂ (hF : F.IsUnramifiedOutside S)
    {x : (G ⧸ F.fixingSubgroup.comap r) × (G ⧸ F.fixingSubgroup.comap r) → M.quotientToInvariants _}
    (hx : x ∈ coboundaries₂ (M.quotientToInvariants (F.fixingSubgroup.comap r))) :
    levelInflate₂ r M F x ∈ levelCoboundariesSr₂ r S M := by
  obtain ⟨y, rfl⟩ := hx
  exact (mem_levelCoboundariesSr₂_iff r S M _).2 ⟨levelInflate₁ r M F y, levelInflate₁_mem_levelCochainsSr₁ r S M F hF y, (levelInflate₂_d₁₂ y).symm⟩

def levelInflateCocyclesSr₂ (hF : F.IsUnramifiedOutside S) :
    cocycles₂ (M.quotientToInvariants (F.fixingSubgroup.comap r)) →ₗ[k] ↥(levelCocyclesSr₂ r S M) :=
  ((levelInflate₂ r M F).comp (Submodule.subtype _)).codRestrict _ fun x => levelInflate₂_mem_levelCocyclesSr₂ r S M F hF x.2

lemma coe_levelInflateCocyclesSr₂ (hF : F.IsUnramifiedOutside S) (x : cocycles₂ (M.quotientToInvariants (F.fixingSubgroup.comap r))) :
    (levelInflateCocyclesSr₂ r S M F hF x : G × G → M) = levelInflate₂ r M F x := rfl

lemma continuousH2Srπ_levelInflateCocyclesSr₂_eq_zero (hF : F.IsUnramifiedOutside S)
    {x : cocycles₂ (M.quotientToInvariants (F.fixingSubgroup.comap r))}
    (hx : (x : _ → _) ∈ coboundaries₂ (M.quotientToInvariants (F.fixingSubgroup.comap r))) :
    continuousH2Srπ r S M (levelInflateCocyclesSr₂ r S M F hF x) = 0 :=
  (continuousH2Srπ_eq_zero_iff r S M _).2 (levelInflate₂_mem_levelCoboundariesSr₂ r S M F hF hx)

def continuousH2SrInflation (hF : F.IsUnramifiedOutside S) :
    H2 (M.quotientToInvariants (F.fixingSubgroup.comap r)) →ₗ[k] continuousH2Sr r S M :=
  (Submodule.liftQ _ (continuousH2Srπ r S M ∘ₗ levelInflateCocyclesSr₂ r S M F hF) (by
      rintro x ⟨y, rfl⟩
      exact continuousH2Srπ_levelInflateCocyclesSr₂_eq_zero r S M F hF ⟨y, rfl⟩))
    ∘ₗ (H2Iso (M.quotientToInvariants (F.fixingSubgroup.comap r))).hom.hom

lemma continuousH2SrInflation_H2π (hF : F.IsUnramifiedOutside S) (x : cocycles₂ (M.quotientToInvariants (F.fixingSubgroup.comap r))) :
    continuousH2SrInflation r S M F hF (H2π _ x) = continuousH2Srπ r S M (levelInflateCocyclesSr₂ r S M F hF x) := by
  have h := π_comp_H2Iso_hom_apply (M.quotientToInvariants (F.fixingSubgroup.comap r)) ((isoCocycles₂ _).inv x)
  simp only [Iso.inv_hom_id_apply] at h
  have e : (H2Iso (M.quotientToInvariants (F.fixingSubgroup.comap r))).hom.hom (H2π _ x)
      = (LinearMap.range (shortComplexH2 (M.quotientToInvariants (F.fixingSubgroup.comap r))).moduleCatToCycles).mkQ x :=
    Eq.trans rfl h
  have key : ∀ z, z = (LinearMap.range (shortComplexH2 (M.quotientToInvariants (F.fixingSubgroup.comap r))).moduleCatToCycles).mkQ x →
      (LinearMap.range (shortComplexH2 (M.quotientToInvariants (F.fixingSubgroup.comap r))).moduleCatToCycles).liftQ
          (continuousH2Srπ r S M ∘ₗ levelInflateCocyclesSr₂ r S M F hF)
          (by rintro x ⟨y, rfl⟩; exact continuousH2Srπ_levelInflateCocyclesSr₂_eq_zero r S M F hF ⟨y, rfl⟩) z
        = continuousH2Srπ r S M (levelInflateCocyclesSr₂ r S M F hF x) := by
    rintro _ rfl; rfl
  exact key _ e

end A0

end groupCohomology
end


