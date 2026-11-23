-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_ProdFormulaEOf
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_ProdFormulaEOf
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:27:15.959789+00:00
-- url     : https://prove2.me/theorems/7c2895d6-c2ec-4ab4-b9ed-4e7e5bc1fe9d
-- title:
--   Prod Formula EOf
-- statement:
--   Definitions and structural lemmas for Prod Formula EOf, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProductFormulaHaar/ProdFormulaEOf.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ProdFormulaE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_ResCharIff
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_BasisEApply
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_DenEqOneOfForallPadicNormLeOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open IsDedekindDomain NumberField MeasureTheory ValuativeRel Formalism.MainNotions.S.Loc
namespace PI.ProdFormulaE.Top
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {sig : E →ₐ[F] E}
theorem transport {K : Type} [Field K] [TopologicalSpace K] {m : ℕ} (ℓ : ℕ) (h : m = ℓ)
    [Fact m.Prime] [Fact ℓ.Prime] [Algebra ℚ_[m] K] (hc : Continuous (algebraMap ℚ_[m] K))
    (hf : FiniteDimensional ℚ_[m] K) :
    ∃ A : Algebra ℚ_[ℓ] K, Continuous (@algebraMap ℚ_[ℓ] K _ _ A) ∧
      @FiniteDimensional ℚ_[ℓ] K _ _ A.toModule ∧
      ∀ (w : K) (a : ℚ), ‖@Algebra.trace ℚ_[ℓ] K _ _ A w - (a : ℚ_[ℓ])‖ =
        ‖Algebra.trace ℚ_[m] K w - (a : ℚ_[m])‖ := by
  subst h
  exact ⟨inferInstance, hc, hf, fun _ _ => rfl⟩
theorem transport_at (L : ∀ p : HeightOneSpectrum (𝓞 F), LocAt F E sig p) (q : ℕ) [Fact q.Prime]
    (i : {p : HeightOneSpectrum (𝓞 F) // resChar p = q}) :
    ∃ A : Algebra ℚ_[q] (L i.1).Fp, Continuous (@algebraMap ℚ_[q] (L i.1).Fp _ _ A) ∧
      @FiniteDimensional ℚ_[q] (L i.1).Fp _ _ A.toModule ∧
      ∀ (w : (L i.1).Fp) (a : ℚ), ‖@Algebra.trace ℚ_[q] (L i.1).Fp _ _ A w - (a : ℚ_[q])‖ =
        (haveI := (L i.1).ellPrime
         ‖Algebra.trace ℚ_[resChar i.1] (L i.1).Fp w - (a : ℚ_[resChar i.1])‖) :=
  haveI := (L i.1).ellPrime
  transport q i.2 (L i.1).qlCont (L i.1).qlFin
def fam (L : ∀ p : HeightOneSpectrum (𝓞 F), LocAt F E sig p) (q : ℕ) [Fact q.Prime] :
    Tr.LocFam F q {p : HeightOneSpectrum (𝓞 F) // resChar p = q} where
  P i := i.1
  K i := (L i.1).Fp
  fld _ := inferInstance
  vr _ := inferInstance
  top _ := inferInstance
  lf i := (L i.1).lf
  cz i := (L i.1).char0
  alg i := (transport_at L q i).choose
  cont i := (transport_at L q i).choose_spec.1
  fin i := (transport_at L q i).choose_spec.2.1
  ιF i := (L i.1).ιF
  dense i := (L i.1).dense
  val i := (L i.1).val
end PI.ProdFormulaE.Top
end


