-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_BasisEApply
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ProductFormulaHaar_BasisEApply
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:18:29.697251+00:00
-- url     : https://prove2.me/theorems/d2e111ea-05d9-40b7-ac01-6d5f646468a7
-- title:
--   Basis EApply
-- statement:
--   Definitions and structural lemmas for Basis EApply, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/ProductFormulaHaar/BasisEApply.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ProdFormulaE
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open IsDedekindDomain NumberField Formalism.MainNotions.S.Loc
namespace PI.ProdFormulaE.Base
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {sig : E →ₐ[F] E} {p : HeightOneSpectrum (𝓞 F)}
theorem finrank_pos (L : LocAt F E sig p) : 0 < Module.finrank L.Fp L.Ep := by
  rw [L.rank]; norm_num
theorem finite (L : LocAt F E sig p) : Module.Finite L.Fp L.Ep :=
  Module.finite_of_finrank_pos (finrank_pos L)
theorem ιE_smul (L : LocAt F E sig p) (a : F) (y : E) : L.ιE (a • y) = L.ιF a • L.ιE y := by
  rw [Algebra.smul_def, map_mul, L.compat, Algebra.smul_def]
theorem ιE_eq_sum (L : LocAt F E sig p) {ι : Type*} [Fintype ι] (b : Module.Basis ι F E) (y : E) :
    L.ιE y = ∑ i, L.ιF (b.repr y i) • L.ιE (b i) := by
  conv_lhs => rw [← b.sum_repr y]
  rw [map_sum]
  exact Finset.sum_congr rfl fun i _ => ιE_smul L _ _
theorem span_basis (L : LocAt F E sig p) {ι : Type*} [Fintype ι] (b : Module.Basis ι F E) :
    Submodule.span L.Fp (Set.range (L.ιE ∘ b)) = ⊤ := by
  rw [eq_top_iff, ← L.span, Submodule.span_le]
  rintro _ ⟨y, rfl⟩
  rw [ιE_eq_sum L b y]
  exact Submodule.sum_mem _ fun i _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
def basisE (L : LocAt F E sig p) {ι : Type*} [Fintype ι] (b : Module.Basis ι F E)
    (h : Module.finrank F E = 2) : Module.Basis ι L.Fp L.Ep :=
  haveI := finite L
  basisOfTopLeSpanOfCardEqFinrank (L.ιE ∘ b) (span_basis L b).ge
    (by rw [L.rank, ← h, Module.finrank_eq_card_basis b])
end PI.ProdFormulaE.Base
end


