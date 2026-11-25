-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_HeisenbergCocycleMemCentre
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_HeisenbergCocycleMemCentre
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-25T12:12:42.535625+00:00
-- url     : https://prove2.me/theorems/065487a5-0241-4f4f-9f96-2a6e629f9bcd
-- title:
--   Heisenberg Cocycle Mem Centre
-- statement:
--   Definitions and structural lemmas for Heisenberg Cocycle Mem Centre, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/LevelSplitting/HeisenbergCocycleMemCentre.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_UnipotentRadicalActionFormula
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_NCDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LevelSplitting_ToMatrixLin
import Theorems.Thm_PI_LevelKSplit_W_NCH_pWp_apply
import Theorems.Thm_PI_LevelKSplit_W_NCH_pWp_isWp
import Theorems.Thm_PI_LevelKSplit_W_NCH_sL_uni
import Theorems.Thm_PI_LevelKSplit_W_SemiG_Dat_pX_apply
import Theorems.Thm_PI_LevelKSplit_W_SemiG_Dat_pXv_apply
import Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_pX_apply
import Theorems.Thm_PI_VolSemiDirect_W_PG_Dat_pXv_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.LevelKSplit.W.NCH
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub PI.VolSemiDirect.W PI.VolSemiDirect.W.PG
  PI.VolSemiDirect.W.PG.Dat
open scoped TensorProduct Matrix
section Gen
variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] {r : ℕ} {D : Dat A n r}
def sMat (D : Dat A n r) (half : A) (y : Fin r → n → A) : Matrix n n A :=
  LinearMap.toMatrix' (sL D half y)
end Gen
section R
variable {F E : Type} [Field F] [Field E] [Algebra F E] {R : Type} [CommRing R] [Algebra F R]
  {σ : E →ₐ[F] E} {M : ℕ} {J : Matrix (Fin M) (Fin M) E} {r : ℕ} {P : Frame E M r} {T : F}
theorem pWp_eq (x : Fin M → R ⊗[F] E) :
    PI.LevelKSplit.W.NC.pWp R σ J P x = pWp (datR R σ J P T) x := by
  rw [pWp_apply, pX_apply, pXv_apply]
  rfl
theorem yH_eq (g : HA R σ J) (a : Fin r) :
    PI.LevelKSplit.W.NC.yH R σ J P g a =
      pWp (datR R σ J P T) (lin R σ J g ((datR R σ J P T).f a)) :=
  pWp_eq _
theorem hJi (hJ : IsHermND σ J) : (J⁻¹).map (inclR (F := F) R) * JR R J = 1 := by
  rw [JR, ← Matrix.map_mul, Matrix.nonsing_inv_mul J (isUnit_iff_ne_zero.2 hJ.2)]
  exact Matrix.map_one _ (map_zero _) (map_one _)
section Sec
variable (hJ : IsHermND σ J) (H : (datR R σ J P T).Hyp) {half : R ⊗[F] E}
  (hh : Half (datR R σ J P T) half)
include hJ H hh
theorem sMat_uj {y : Fin r → Fin M → R ⊗[F] E} (hy : ∀ a, IsWp (datR R σ J P T) (y a)) :
    Formalism.UG.cT (sigR R σ) (sMat (datR R σ J P T) half y) * JR R J * sMat (datR R σ J P T) half y =
      JR R J :=
  PI.LevelKSplit.W.SemiA.uj_of_uni _ _ _ fun x x' => by
    rw [sMat, LinearMap.toMatrix'_mulVec, LinearMap.toMatrix'_mulVec]
    exact sL_uni H hy hh x x'
theorem sMat_linv {y : Fin r → Fin M → R ⊗[F] E} (hy : ∀ a, IsWp (datR R σ J P T) (y a)) :
    (J⁻¹).map (inclR (F := F) R) * Formalism.UG.cT (sigR R σ) (sMat (datR R σ J P T) half y) * JR R J *
      sMat (datR R σ J P T) half y = 1 := by
  have e : (J⁻¹).map (inclR (F := F) R) * Formalism.UG.cT (sigR R σ) (sMat (datR R σ J P T) half y) *
      JR R J * sMat (datR R σ J P T) half y = (J⁻¹).map (inclR (F := F) R) *
      (Formalism.UG.cT (sigR R σ) (sMat (datR R σ J P T) half y) * JR R J *
        sMat (datR R σ J P T) half y) := by
    simp only [Matrix.mul_assoc]
  rw [e, sMat_uj hJ H hh hy, hJi hJ]
def sU {y : Fin r → Fin M → R ⊗[F] E} (hy : ∀ a, IsWp (datR R σ J P T) (y a)) :
    GL (Fin M) (R ⊗[F] E) where
  val := sMat (datR R σ J P T) half y
  inv := (J⁻¹).map (inclR (F := F) R) * Formalism.UG.cT (sigR R σ) (sMat (datR R σ J P T) half y) *
    JR R J
  val_inv := mul_eq_one_comm.2 (sMat_linv hJ H hh hy)
  inv_val := sMat_linv hJ H hh hy
theorem sU_mem {y : Fin r → Fin M → R ⊗[F] E} (hy : ∀ a, IsWp (datR R σ J P T) (y a)) :
    sU hJ H hh hy ∈ HR R σ J := by
  first
  | exact sMat_uj hJ H hh hy
  | (simp only [HR]; exact sMat_uj hJ H hh hy)
  | (simp [HR, sU]; exact sMat_uj hJ H hh hy)
def sHG {y : Fin r → Fin M → R ⊗[F] E} (hy : ∀ a, IsWp (datR R σ J P T) (y a)) : HA R σ J :=
  ⟨sU hJ H hh hy, sU_mem hJ H hh hy⟩
theorem isWp_yH (g : HA R σ J) (a : Fin r) :
    IsWp (datR R σ J P T) (PI.LevelKSplit.W.NC.yH R σ J P g a) := by
  rw [yH_eq (T := T)]
  exact pWp_isWp H _
end Sec
end R
end PI.LevelKSplit.W.NCH


