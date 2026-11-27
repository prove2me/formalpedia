-- Prove2me | Definitions.Def_AlgebraicGeometry_EtaleAdditiveCohomologyBaseChangeMap
-- name    : AlgebraicGeometry_EtaleAdditiveCohomologyBaseChangeMap
-- status  : Definition
-- author  : @tomasz
-- created : 2026-11-27T04:19:21.018533+00:00
-- url     : https://prove2.me/theorems/4c9857ba-df66-57f0-99d8-911c0b2cdc48
-- title:
--   The linear map on additive étale cohomology under field extension
-- statement:
--   The canonical additive-cohomology restriction is linear over the original field and gives a canonical scalar-extension map.
-- source:
--   Stacks Project, Lemma 59.63.6, https://stacks.math.columbia.edu/tag/0A3P.

import Definitions.Def_AlgebraicGeometry_EtaleArtinSchreierNaturality
import Mathlib.RingTheory.TensorProduct.Finite

noncomputable section

section

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 950000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PhilipponEtaleAdditiveStructureSheaf (sheaf frobenius cohomologyModule frobenius_cohomology_smul)
open PhilipponArtinSchreierBaseChange
open PhilipponArtinSchreierCohomology (artinSchreier_surjective mem_artinSchreierKernel_iff)
open PhilipponArtinSchreierKernel (constantIsoKernel)
open PhilipponEtaleAcyclicCohomology (pullbackConstantIso)
open PhilipponEtalePrimeTorsionComparison (restrict)
open PhilipponEtaleSmallSite (pullbackAdjunction pullbackSheaves)


namespace PhilipponEtaleCharacteristicComparison

open scoped TensorProduct

universe u

private abbrev Ab (X : Scheme.{u}) := Sheaf X.smallEtaleTopology AddCommGrpCat.{u}
private abbrev primeCoefficients (p : ℕ) := AddCommGrpCat.of (ULift.{u} (ZMod p))

abbrev restrictedModule {K E : Type u} [Field K] [Field E] [Algebra K E]
    {Y : Scheme.{u}} (s : Y ⟶ Spec (.of E)) (q : ℕ) : Module K ((sheaf Y).H q) :=
  letI := cohomologyModule s q
  Module.compHom ((sheaf Y).H q) (algebraMap K E)

theorem restrictedModule_isScalarTower {K E : Type u} [Field K] [Field E] [Algebra K E]
    {Y : Scheme.{u}} (s : Y ⟶ Spec (.of E)) (q : ℕ) :
    letI := cohomologyModule s q
    letI := restrictedModule (K := K) s q
    IsScalarTower K E ((sheaf Y).H q) := by
  let := cohomologyModule s q
  let := restrictedModule (K := K) s q
  exact IsScalarTower.of_algebraMap_smul fun _ _ => rfl

/-- The canonical structure-sheaf restriction, linear over the smaller field. -/
def linearComparison {K E : Type u} [Field K] [Field E] [Algebra K E]
    {X Y : Scheme.{u}} (a : Y ⟶ X) (r : X ⟶ Spec (.of K)) (s : Y ⟶ Spec (.of E))
    (h : a ≫ r = s ≫ Spec.map (CommRingCat.ofHom (algebraMap K E))) (q : ℕ) :
    letI := cohomologyModule r q
    letI := restrictedModule (K := K) s q
    (sheaf X).H q →ₗ[K] (sheaf Y).H q := by
  let := cohomologyModule r q
  let := restrictedModule (K := K) s q
  exact { structureCohomologyComparison a q with
    map_smul' := structureCohomologyComparison_smul a r s (algebraMap K E) h q }

/-- Flat base change for the canonical map on additive étale cohomology in degree `q`. -/
def IsAdditiveCohomologyBaseChangeInDegree {K E : Type u} [Field K] [Field E] [Algebra K E]
    {X Y : Scheme.{u}} (a : Y ⟶ X) (r : X ⟶ Spec (.of K)) (s : Y ⟶ Spec (.of E))
    (h : a ≫ r = s ≫ Spec.map (CommRingCat.ofHom (algebraMap K E))) (q : ℕ) : Prop :=
  letI := cohomologyModule r q
  letI := cohomologyModule s q
  letI := restrictedModule (K := K) s q
  letI := restrictedModule_isScalarTower (K := K) s q
  IsBaseChange E (linearComparison a r s h q)

/-- Flat base change for the canonical map on additive étale cohomology in all degrees. -/
def IsAdditiveCohomologyBaseChange {K E : Type u} [Field K] [Field E] [Algebra K E]
    {X Y : Scheme.{u}} (a : Y ⟶ X) (r : X ⟶ Spec (.of K)) (s : Y ⟶ Spec (.of E))
    (h : a ≫ r = s ≫ Spec.map (CommRingCat.ofHom (algebraMap K E))) : Prop :=
  ∀ q : ℕ, IsAdditiveCohomologyBaseChangeInDegree a r s h q

/-- If additive cohomology vanishes on both schemes, its canonical map satisfies base change. -/
theorem isBaseChange_of_subsingleton {K E : Type u} [Field K] [Field E] [Algebra K E]
    {X Y : Scheme.{u}} (a : Y ⟶ X) (r : X ⟶ Spec (.of K)) (s : Y ⟶ Spec (.of E))
    (h : a ≫ r = s ≫ Spec.map (CommRingCat.ofHom (algebraMap K E))) (q : ℕ)
    [Subsingleton ((sheaf X).H q)] [Subsingleton ((sheaf Y).H q)] :
    IsAdditiveCohomologyBaseChangeInDegree a r s h q := by
  let := cohomologyModule r q
  let := cohomologyModule s q
  let := restrictedModule (K := K) s q
  let := restrictedModule_isScalarTower (K := K) s q
  change IsBaseChange E (linearComparison a r s h q)
  unfold IsBaseChange IsTensorProduct
  exact ⟨fun _ _ _ => Subsingleton.elim _ _, fun x => ⟨0, Subsingleton.elim _ x⟩⟩


end PhilipponEtaleCharacteristicComparison

end

end


