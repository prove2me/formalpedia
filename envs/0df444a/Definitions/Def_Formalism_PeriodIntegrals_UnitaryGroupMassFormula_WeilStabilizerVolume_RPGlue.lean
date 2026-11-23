-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_RPGlue
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_RPGlue
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:15:37.348663+00:00
-- url     : https://prove2.me/theorems/5733d23d-a04f-4306-b3b3-dcd74508fde2
-- title:
--   RPGlue
-- statement:
--   Definitions and structural lemmas for RPGlue, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/RPGlue.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_RestrProdSt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_TopoPolish
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicLocalCompactness_AdeleLC
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.VolStabW
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
  Topology Filter
open scoped TensorProduct RestrictedProduct
namespace RestrictedProductGluing
open PositiveNearLattice
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] [FiniteDimensional F E]
  {M a d : ℕ} (b : Module.Basis (Fin d) F E)
def good : Set ((Fin a → Fin M → Ainf F ⊗[F] E) ×
    (∀ v : HeightOneSpectrum (𝓞 F), Fin a → Fin M → Fv F v ⊗[F] E)) :=
  {p | ∀ᶠ v in cofinite, p.2 v ∈ latV b v}
def mkAf (x : ∀ v : HeightOneSpectrum (𝓞 F), Fv F v)
    (h : ∀ᶠ v in cofinite, x v ∈ v.adicCompletionIntegers F) : Af F :=
  (⟨x, h⟩ : Πʳ v : HeightOneSpectrum (𝓞 F), [v.adicCompletion F, v.adicCompletionIntegers F])
open Classical in

def finAd (p : (Fin a → Fin M → Ainf F ⊗[F] E) ×
    (∀ v : HeightOneSpectrum (𝓞 F), Fin a → Fin M → Fv F v ⊗[F] E)) (i : Fin a) (j : Fin M)
    (k : Fin d) : Af F :=
  if h : p ∈ good b then
    mkAf (fun v => crd b (Fv F v) (p.2 v i j) k)
      ((show ∀ᶠ v in cofinite, p.2 v ∈ latV b v from h).mono fun _ hv => hv i j k)
  else 0
def crdA (p : (Fin a → Fin M → Ainf F ⊗[F] E) ×
    (∀ v : HeightOneSpectrum (𝓞 F), Fin a → Fin M → Fv F v ⊗[F] E)) (i : Fin a) (j : Fin M)
    (k : Fin d) : AF F :=
  pairA F (crd b (Ainf F) (p.1 i j) k) (finAd b p i j k)
def glue (p : (Fin a → Fin M → Ainf F ⊗[F] E) ×
    (∀ v : HeightOneSpectrum (𝓞 F), Fin a → Fin M → Fv F v ⊗[F] E)) :
    Fin a → Fin M → AF F ⊗[F] E :=
  fun i j => (Algebra.TensorProduct.basis (AF F) b).equivFun.symm (fun k => crdA b p i j k)
def coeA (x : Af F) : ∀ v : HeightOneSpectrum (𝓞 F), Fv F v := fun v => evalV F v x
end RestrictedProductGluing
end PI.VolStabW


