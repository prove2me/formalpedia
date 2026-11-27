-- Prove2me | Definitions.Def_AlgebraicGeometry_EtaleArtinSchreierSequenceMap
-- name    : AlgebraicGeometry_EtaleArtinSchreierSequenceMap
-- status  : Definition
-- author  : @tomasz
-- created : 2026-11-27T06:09:10.456278+00:00
-- url     : https://prove2.me/theorems/dc286a3c-de67-4d49-87be-f589e4ae455d
-- title:
--   The Artin–Schreier short exact sequence under field extension
-- statement:
--   Inverse image along a field extension maps the Artin–Schreier sequence to the sequence on the extended scheme, compatibly with the constant sheaf comparison.
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

def artinSchreierSequence {K : Type u} [Field K] {X : Scheme.{u}}
    (r : X ⟶ Spec (.of K)) {p : ℕ} (hp : p.Prime) (hK : (p : K) = 0) :
    ShortComplex (Ab X) :=
  ShortComplex.mk (PhilipponArtinSchreierKernel.inclusion r hp hK)
    (frobenius r hp hK - 𝟙 (sheaf X))
    (by simp only [PhilipponArtinSchreierKernel.inclusion, Category.assoc, kernel.condition, comp_zero])

theorem artinSchreierSequence_shortExact {K : Type u} [Field K] {X : Scheme.{u}}
    (r : X ⟶ Spec (.of K)) {p : ℕ} (hp : p.Prime) (hK : (p : K) = 0) :
    (artinSchreierSequence r hp hK).ShortExact := by
  let g := frobenius r hp hK - 𝟙 (sheaf X)
  let T := ShortComplex.mk (kernel.ι g) g (kernel.condition g)
  let : Sheaf.IsLocallySurjective g := PhilipponArtinSchreierEtaleCover.locally_surjective r hp hK
  have hT : T.ShortExact := { exact := ShortComplex.exact_kernel g }
  let e := constantIsoKernel r hp hK
  let i : T ≅ artinSchreierSequence r hp hK := ShortComplex.isoMk e.symm
    (Iso.refl _) (Iso.refl _)
    (by change e.inv ≫ (e.hom ≫ kernel.ι g) = kernel.ι g ≫ 𝟙 _; simp)
    (by simp [T, g, artinSchreierSequence])
  exact ShortComplex.shortExact_of_iso i hT

def artinSchreierMap {K E : Type u} [Field K] [Field E] [Algebra K E]
    {X Y : Scheme.{u}} (a : Y ⟶ X) (r : X ⟶ Spec (.of K)) (s : Y ⟶ Spec (.of E))
    (h : a ≫ r = s ≫ Spec.map (CommRingCat.ofHom (algebraMap K E)))
    {p : ℕ} (hp : p.Prime) (hK : (p : K) = 0) (hE : (p : E) = 0) :
    (artinSchreierSequence r hp hK).map (pullbackSheaves a) ⟶ artinSchreierSequence s hp hE where
  τ₁ := (pullbackConstantIso a).hom.app (primeCoefficients p)
  τ₂ := structureComparison a
  τ₃ := structureComparison a
  comm₁₂ := (inclusion_baseChange a r s (algebraMap K E) h hp hK hE).symm
  comm₂₃ := by
    let L := pullbackSheaves a
    let : L.Additive := (pullbackAdjunction a).left_adjoint_additive
    change structureComparison a ≫ (frobenius s hp hE - 𝟙 (sheaf Y)) =
      L.map (frobenius r hp hK - 𝟙 (sheaf X)) ≫ structureComparison a
    rw [L.map_sub, L.map_id, Preadditive.comp_sub, Preadditive.sub_comp,
      structureComparison_frobenius a r s hp hK hE, Category.comp_id, Category.id_comp]


end PhilipponEtaleCharacteristicComparison

end

end


