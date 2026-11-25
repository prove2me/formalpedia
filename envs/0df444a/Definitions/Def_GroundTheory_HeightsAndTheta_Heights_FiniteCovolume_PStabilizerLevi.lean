-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PStabilizerLevi
-- name    : GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PStabilizerLevi
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T09:22:43.232856+00:00
-- url     : https://prove2.me/theorems/25b7e6bd-3a14-5cb3-9a32-7f0a2a59863a
-- title:
--   PStabilizer Levi
-- statement:
--   Definitions and structural lemmas for PStabilizer Levi, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FiniteCovolume/PStabilizerLevi.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PStabilizerLeviPlaces
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_StabilizerLevi_conjT_eq_f4f7b197f2a7
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_StabilizerLevi_frame_0d474e499bcf
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_StabilizerLevi_gramAt_complement_0681a8dddbea
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_StabilizerLevi_leftInv_mul_24167f725f84
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_StabilizerLevi_leviProj_mul_2dfedc9dd00d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_StabilizerLevi_leviProj_unitary_03bc851e798c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_StabilizerLevi_leviSec_mulVec_of_8771abea5030
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_StabilizerLevi_leviSec_mul_ac9cb8ce7cd9
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_StabilizerLevi_leviSec_one_91b9f3a7494d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_StabilizerLevi_leviSec_unitary_c1fb52bd7931
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_mem_archUnitary_0eab686fdef0

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GroundTheory.Heights₂.Heights.FiniteCovolume
open NumberField GroundTheory.Automorphic Module Matrix Topology
noncomputable section
set_option linter.unusedSectionVars false
namespace StabilizerLevi
variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]
def mat {h : HermitianForm F E W} {v : Basis ι E W} (g : archUnitary h v) (w : InfinitePlace E) :
    Matrix ι ι ℂ :=
  ((g : InfinitePlace E → GL ι ℂ) w : Matrix ι ι ℂ)
section Mat
variable {h : HermitianForm F E W} {v : Basis ι E W}
theorem mat_mul (g g' : archUnitary h v) (w : InfinitePlace E) :
    mat (g * g') w = mat g w * mat g' w := rfl
theorem mat_one (w : InfinitePlace E) : mat (1 : archUnitary h v) w = 1 := rfl
theorem mat_mul_inv (g : archUnitary h v) (w : InfinitePlace E) : mat g w * mat g⁻¹ w = 1 := by
  rw [← mat_mul, mul_inv_cancel, mat_one]
theorem mat_inv_mul (g : archUnitary h v) (w : InfinitePlace E) : mat g⁻¹ w * mat g w = 1 := by
  rw [← mat_mul, inv_mul_cancel, mat_one]
theorem unitary_mat (g : archUnitary h v) (w : InfinitePlace E) :
    (mat g w)ᴴ * gramAt h v w * mat g w = gramAt h v w := by
  have := mem_archUnitary.1 g.2 w
  rwa [conjT_eq] at this
end Mat
variable {h : HermitianForm F E W} {v : Basis ι E W} {x₀ w₀ : W} {n : ℕ}
  (hp : IsHyperbolicPair h x₀ w₀) {h' : HermitianForm F E (hypComplement h x₀ w₀)}
  (hh' : ∀ x y, h'.toSesq x y = h.toSesq x y) {v' : Basis (Fin n) E (hypComplement h x₀ w₀)}
abbrev bMat (v : Basis ι E W) (v' : Basis (Fin n) E (hypComplement h x₀ w₀)) (w : InfinitePlace E) :
    Matrix ι (Fin n) ℂ :=
  colMat v (fun k => (v' k : W)) w
include hp hh'
theorem q_mul (g g' : archUnitary h v) (hg : g ∈ vecFixGroup h v x₀)
    (hg' : g' ∈ vecFixGroup h v x₀) (w : InfinitePlace E) :
    leviProj (gramAt h v w) (bMat v v' w) (mat (g * g') w) =
      leviProj (gramAt h v w) (bMat v v' w) (mat g w) *
        leviProj (gramAt h v w) (bMat v v' w) (mat g' w) := by
  obtain ⟨hH, hG, hBX, hBY, hXX, hYY, hXY, hspan⟩ := frame v hp h' hh' v' w
  rw [mat_mul]
  exact leviProj_mul hH hG hBX hBY hXX hYY hXY hspan (unitary_mat g w) (hg w) (unitary_mat g' w)
    (hg' w)
theorem q_one (w : InfinitePlace E) :
    leviProj (gramAt h v w) (bMat v v' w) (mat (1 : archUnitary h v) w) = 1 := by
  obtain ⟨hH, hG, -⟩ := frame v hp h' hh' v' w
  rw [mat_one, leviProj, Matrix.mul_one]
  exact leftInv_mul hG
def qUnit (g : vecFixGroup h v x₀) (w : InfinitePlace E) : GL (Fin n) ℂ where
  val := leviProj (gramAt h v w) (bMat v v' w) (mat (g : archUnitary h v) w)
  inv := leviProj (gramAt h v w) (bMat v v' w) (mat ((g⁻¹ : vecFixGroup h v x₀) : archUnitary h v) w)
  val_inv := by
    rw [← q_mul hp hh' _ _ g.2 (g⁻¹).2, ← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one,
      q_one hp hh']
  inv_val := by
    rw [← q_mul hp hh' _ _ (g⁻¹).2 g.2, ← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one,
      q_one hp hh']
theorem qUnit_mem (g : vecFixGroup h v x₀) :
    (fun w => qUnit hp hh' (v' := v') g w) ∈ archUnitary h' v' := by
  rw [mem_archUnitary]
  intro w
  obtain ⟨hH, hG, hBX, hBY, hXX, hYY, hXY, hspan⟩ := frame v hp h' hh' v' w
  rw [conjT_eq]
  change (leviProj (gramAt h v w) (bMat v v' w) (mat (g : archUnitary h v) w))ᴴ * gramAt h' v' w *
    leviProj (gramAt h v w) (bMat v v' w) (mat (g : archUnitary h v) w) = gramAt h' v' w
  rw [gramAt_complement v h' hh' v' w]
  exact leviProj_unitary hH hG hBX hBY hXX hYY hXY hspan (unitary_mat _ w) (g.2 w)
def qHom : vecFixGroup h v x₀ →* archUnitary h' v' where
  toFun g := ⟨fun w => qUnit hp hh' g w, qUnit_mem hp hh' g⟩
  map_one' := Subtype.ext (funext fun w => Units.ext (q_one hp hh' w))
  map_mul' g g' := Subtype.ext (funext fun w => Units.ext (q_mul hp hh' _ _ g.2 g'.2 w))
def iUnit (m : archUnitary h' v') (w : InfinitePlace E) : GL ι ℂ where
  val := leviSec (gramAt h v w) (bMat v v' w) (mat m w)
  inv := leviSec (gramAt h v w) (bMat v v' w) (mat m⁻¹ w)
  val_inv := by
    obtain ⟨hH, hG, -⟩ := frame v hp h' hh' v' w
    rw [← leviSec_mul hG, mat_mul_inv, leviSec_one]
  inv_val := by
    obtain ⟨hH, hG, -⟩ := frame v hp h' hh' v' w
    rw [← leviSec_mul hG, mat_inv_mul, leviSec_one]
theorem iUnit_mem (m : archUnitary h' v') : (fun w => iUnit hp hh' (v := v) m w) ∈ archUnitary h v := by
  rw [mem_archUnitary]
  intro w
  obtain ⟨hH, hG, -⟩ := frame v hp h' hh' v' w
  rw [conjT_eq]
  change (leviSec (gramAt h v w) (bMat v v' w) (mat m w))ᴴ * gramAt h v w *
    leviSec (gramAt h v w) (bMat v v' w) (mat m w) = gramAt h v w
  refine leviSec_unitary hH hG _ ?_
  rw [← gramAt_complement v h' hh' v' w]
  exact unitary_mat m w
theorem iUnit_mem_vecFixGroup (m : archUnitary h' v') :
    (⟨fun w => iUnit hp hh' (v := v) m w, iUnit_mem hp hh' m⟩ : archUnitary h v) ∈ vecFixGroup h v x₀ := by
  intro w
  obtain ⟨hH, hG, hBX, -⟩ := frame v hp h' hh' v' w
  exact leviSec_mulVec_of hBX _
def iHom : archUnitary h' v' →* vecFixGroup h v x₀ where
  toFun m := ⟨⟨fun w => iUnit hp hh' (v := v) m w, iUnit_mem hp hh' m⟩, iUnit_mem_vecFixGroup hp hh' m⟩
  map_one' := Subtype.ext (Subtype.ext (funext fun w => Units.ext (by
    change leviSec (gramAt h v w) (bMat v v' w) (mat (1 : archUnitary h' v') w) = 1
    rw [mat_one, leviSec_one])))
  map_mul' m m' := Subtype.ext (Subtype.ext (funext fun w => Units.ext (by
    obtain ⟨hH, hG, -⟩ := frame v hp h' hh' v' w
    change leviSec (gramAt h v w) (bMat v v' w) (mat (m * m') w) =
      leviSec (gramAt h v w) (bMat v v' w) (mat m w) * leviSec (gramAt h v w) (bMat v v' w) (mat m' w)
    rw [mat_mul, leviSec_mul hG])))
end StabilizerLevi
open StabilizerLevi
variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]
end
end GroundTheory.Heights₂.Heights.FiniteCovolume


