-- Prove2me | Definitions.Def_Formalism_QuotientMetricDivisors_LatticeGlueUnique
-- name    : Formalism_QuotientMetricDivisors_LatticeGlueUnique
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:08:50.260806+00:00
-- url     : https://prove2.me/theorems/50644951-a700-42ff-b8cd-8e9edc1b4066
-- title:
--   Lattice Glue Unique
-- statement:
--   Definitions and structural lemmas for Lattice Glue Unique, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/QuotientMetricDivisors/LatticeGlueUnique.lean

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_Statement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix
noncomputable section
namespace Formalism.DivisionValues
def glueLat {K : Type} [Field K] [NumberField K] {D : ℕ}
    (L : HeightOneSpectrum (𝓞 K) → Submodule (𝓞 K) (Fin D → K)) : Submodule (𝓞 K) (Fin D → K) :=
  ⨅ w : HeightOneSpectrum (𝓞 K), Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (L w)
def LatticeGlue : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (D : ℕ) (L0 : Submodule (𝓞 K) (Fin D → K))
    (L : HeightOneSpectrum (𝓞 K) → Submodule (𝓞 K) (Fin D → K)),
    Submodule.IsLattice K L0 → (∀ w, Submodule.IsLattice K (L w)) →
    {w : HeightOneSpectrum (𝓞 K) |
      Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (L w) ≠ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal L0}.Finite →
    Submodule.IsLattice K (glueLat L) ∧
      ∀ w : HeightOneSpectrum (𝓞 K),
        Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (glueLat L) = Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (L w)
def LatticeGlueUnique : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (D : ℕ) (R R' : Submodule (𝓞 K) (Fin D → K)),
    ((∀ w : HeightOneSpectrum (𝓞 K),
      Formalism.HermitianLatticesTheory.localization₂ w.asIdeal R = Formalism.HermitianLatticesTheory.localization₂ w.asIdeal R') → R = R') ∧
    ((∀ w : HeightOneSpectrum (𝓞 K),
      Formalism.HermitianLatticesTheory.localization₂ w.asIdeal R ≤ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal R') → R ≤ R') ∧
    glueLat (fun _ => R) = R
def LatticeGlueIndep : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (D : ℕ) (L0 L1 : Submodule (𝓞 K) (Fin D → K)),
    Submodule.IsLattice K L0 → Submodule.IsLattice K L1 →
    ∀ S : Set (HeightOneSpectrum (𝓞 K)), S.Finite →
    ∃! R : Submodule (𝓞 K) (Fin D → K), Submodule.IsLattice K R ∧
      (∀ w ∈ S, Formalism.HermitianLatticesTheory.localization₂ w.asIdeal R = Formalism.HermitianLatticesTheory.localization₂ w.asIdeal L1) ∧
      (∀ w ∉ S, Formalism.HermitianLatticesTheory.localization₂ w.asIdeal R = Formalism.HermitianLatticesTheory.localization₂ w.asIdeal L0)
def LatticeGlueSemi : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (D : ℕ),
    (∀ (L0 : Submodule (𝓞 K) (Fin D → K))
      (L : HeightOneSpectrum (𝓞 K) → Submodule (𝓞 K) (Fin D → K)),
      Submodule.IsLattice K L0 → (∀ w, Submodule.IsLattice K (L w)) →
      (∀ w, L (conjPl w) = L w) →
      {w : HeightOneSpectrum (𝓞 K) |
        Formalism.HermitianLatticesTheory.loc (K := K) w.asIdeal (L w) ≠ Formalism.HermitianLatticesTheory.loc (K := K) w.asIdeal L0}.Finite →
      Submodule.IsLattice K (glueLat L) ∧
      (∀ w : HeightOneSpectrum (𝓞 K),
        Formalism.HermitianLatticesTheory.loc (K := K) w.asIdeal (glueLat L) = Formalism.HermitianLatticesTheory.loc (K := K) w.asIdeal (L w)) ∧
      glueLat L = ⨅ w : HeightOneSpectrum (𝓞 K), Formalism.HermitianLatticesTheory.loc (K := K) w.asIdeal (L w)) ∧
    (∀ R R' : Submodule (𝓞 K) (Fin D → K),
      (∀ w : HeightOneSpectrum (𝓞 K),
        Formalism.HermitianLatticesTheory.loc (K := K) w.asIdeal R = Formalism.HermitianLatticesTheory.loc (K := K) w.asIdeal R') → R = R')
def StepBGlue : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (D : ℕ)
    (Tup : Type) (μ0 : Tup) (μ : HeightOneSpectrum (𝓞 K) → Tup), (∀ w, μ (conjPl w) = μ w) →
    {w | μ w ≠ μ0}.Finite →
    ∀ (abelian₂ : Tup → Submodule (𝓞 K) (Fin D → K)), (∀ t, Submodule.IsLattice K (abelian₂ t)) →
    ∀ (ι : Tup → Matrix (Fin D) (Fin D) K), (∀ t, IsUnit (ι t).det) →
    (∃! R : Submodule (𝓞 K) (Fin D → K), ∀ w : HeightOneSpectrum (𝓞 K),
      Formalism.HermitianLatticesTheory.localization₂ w.asIdeal R = Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (matLat (ι (μ w)) (abelian₂ (μ w)))) ∧
    ∀ R : Submodule (𝓞 K) (Fin D → K),
      (∀ w : HeightOneSpectrum (𝓞 K),
        Formalism.HermitianLatticesTheory.localization₂ w.asIdeal R = Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (matLat (ι (μ w)) (abelian₂ (μ w)))) →
      Submodule.IsLattice K R ∧
      R = glueLat (fun w => matLat (ι (μ w)) (abelian₂ (μ w))) ∧
      (∀ w : HeightOneSpectrum (𝓞 K), Formalism.HermitianLatticesTheory.loc (K := K) w.asIdeal R =
        Formalism.HermitianLatticesTheory.loc (K := K) w.asIdeal (matLat (ι (μ w)) (abelian₂ (μ w)))) ∧
      {w : HeightOneSpectrum (𝓞 K) | Formalism.HermitianLatticesTheory.localization₂ w.asIdeal R ≠
        Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (matLat (ι μ0) (abelian₂ μ0))}.Finite
def DivIntoDualGlue : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (D : ℕ)
    (Tup : Type) (μ0 : Tup) (μ : HeightOneSpectrum (𝓞 K) → Tup), {w | μ w ≠ μ0}.Finite →
    ∀ (n : Tup → ℕ) (M : ∀ t, Submodule (𝓞 K) (Fin (n t) → K)),
    (∀ t, Submodule.IsLattice K (M t)) →
    ∀ (π : ∀ t, Matrix (Fin D) (Fin (n t)) K), (∀ t, Function.Surjective (π t).mulVec) →
    ∀ (ι : Tup → Matrix (Fin D) (Fin D) K), (∀ t, IsUnit (ι t).det) →
    ∃! R : Submodule (𝓞 K) (Fin D → K), Submodule.IsLattice K R ∧
      ∀ w : HeightOneSpectrum (𝓞 K), Formalism.HermitianLatticesTheory.localization₂ w.asIdeal R =
        Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (matLat (ι (μ w)) (matLat (π (μ w)) (M (μ w))))
end Formalism.DivisionValues


