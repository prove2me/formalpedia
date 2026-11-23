-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ModelBaseTrivModels
-- name    : Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ModelBaseTrivModels
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:27:19.860211+00:00
-- url     : https://prove2.me/theorems/fa68b085-1814-4eb0-8052-b6be99c861b3
-- title:
--   Model Base Triv Models
-- statement:
--   Definitions and structural lemmas for Model Base Triv Models, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ModelBaseTrivModels.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_OpenRowsFree
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_ModelFamilies
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.PeriodRowsCompare
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {g : ℕ}
  {e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)} {F : GlobalTheory.IndefiniteRowSideFullHecke.ModelFamilies.FamAt Xo c σ e} {r : ℕ}
def modelsEquiv (F : GlobalTheory.IndefiniteRowSideFullHecke.ModelFamilies.FamAt Xo c σ e) (r : ℕ) :
    Rows.ModelsOf F r ≃ GlobalTheory.IndefiniteRowSideFullHecke.ModelFamilies.ModelsOf F r where
  toFun M := ⟨M.X, M.φ⟩
  invFun M := ⟨M.X, M.φ⟩
  left_inv _ := rfl
  right_inv _ := rfl
def trivChar (X : Data E r) : Data E r :=
  { X with
    χ := fun _ _ => 1
    χ_mul := fun _ _ _ _ _ => (one_mul 1).symm
    χ_add := fun _ _ _ _ => (one_mul 1).symm
    χ_fin := fun _ => ⟨1, one_pos, fun _ _ => one_pow 1⟩ }
def trivModels (M : GlobalTheory.IndefiniteRowSideFullHecke.ModelFamilies.ModelsOf F r) : Rows.ModelsOf F r :=
  ⟨fun k => trivChar (M.X k), M.φ⟩
end GlobalTheory.PeriodRowsCompare


