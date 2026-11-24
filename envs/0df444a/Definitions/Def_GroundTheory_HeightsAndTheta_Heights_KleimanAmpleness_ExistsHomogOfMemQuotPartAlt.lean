-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_ExistsHomogOfMemQuotPartAlt
-- name    : GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_ExistsHomogOfMemQuotPartAlt
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:10:19.238944+00:00
-- url     : https://prove2.me/theorems/10c7229f-b020-452a-a550-fe0e41d9f544
-- title:
--   Exists Homog Of Mem Quot Part Alt
-- statement:
--   Definitions and structural lemmas for Exists Homog Of Mem Quot Part Alt, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/ExistsHomogOfMemQuotPartAlt.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_ImportsTerTer
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (Cell cellMon CechC cellRes faceSign cechD locPart cechCc mIdealOver mConeMapOver
  quotPart)
noncomputable section
namespace CellLocEval
set_option linter.unusedSectionVars false
variable {S : Type} [CommRing S] {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
section Homog
end Homog
section Eval
variable {Ω : Type} [Field Ω] [Algebra S Ω] (y : (Σ k, ι k) → Ω)
theorem aeval_eq_zero_of_mem {f : MRingOver S ι} (hf : f ∈ mIdealOver S y) : aeval y f = 0 := by
  have h : (MvPolynomial.eval (fun _ : K => (1 : Ω))).comp (mConeMapOver S y).toRingHom =
      (aeval y : MRingOver S ι →ₐ[S] Ω).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [mConeMapOver, MvPolynomial.algebraMap_apply]
    · intro p
      simp [mConeMapOver]
  have h2 := RingHom.congr_fun h f
  simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at h2
  rw [← h2, show mConeMapOver S y f = 0 from (RingHom.mem_ker).mp hf, map_zero]
def ev0 : (MRingOver S ι ⧸ mIdealOver S y) →ₐ[S] Ω :=
  Ideal.Quotient.liftₐ (mIdealOver S y) (aeval y) (fun _ hf => aeval_eq_zero_of_mem y hf)
theorem evalAtPoint_mk (p : MRingOver S ι) : ev0 y (Ideal.Quotient.mk (mIdealOver S y) p) = aeval y p := rfl
theorem evalAtPoint_smul (r : MRingOver S ι) (m : MRingOver S ι ⧸ mIdealOver S y) :
    ev0 y (r • m) = aeval y r * ev0 y m := by
  obtain ⟨m, rfl⟩ := Ideal.Quotient.mk_surjective m
  show ev0 y (Ideal.Quotient.mk _ (r * m)) = _
  rw [evalAtPoint_mk, evalAtPoint_mk, map_mul]
variable {y}
theorem aeval_ne_zero_of_mem {I : ∀ k, Finset (ι k)} (hI : CellMeets y I) {t : MRingOver S ι}
    (ht : t ∈ cellMon S I) : aeval y t ≠ 0 := by
  unfold ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.cellMon at ht
  induction ht using Submonoid.closure_induction with
  | mem x hx =>
    obtain ⟨k, i, hi, rfl⟩ := hx
    rw [aeval_X]
    exact hI k i hi
  | one => simp
  | mul x z _ _ hx hz => rw [map_mul]; exact mul_ne_zero hx hz
variable (y)
def ev (I : ∀ k, Finset (ι k)) (hI : CellMeets y I)
    (x : LocalizedModule (cellMon S I) (MRingOver S ι ⧸ mIdealOver S y)) : Ω :=
  LocalizedModule.liftOn x (fun p => ev0 y p.1 / aeval y (p.2 : MRingOver S ι)) (by
    rintro ⟨a, s⟩ ⟨b, t⟩ ⟨u, hu⟩
    simp only [Submonoid.smul_def] at hu
    have h := congrArg (ev0 y) hu
    rw [evalAtPoint_smul, evalAtPoint_smul, evalAtPoint_smul, evalAtPoint_smul] at h
    have hu0 := aeval_ne_zero_of_mem hI u.2
    have hs0 := aeval_ne_zero_of_mem hI s.2
    have ht0 := aeval_ne_zero_of_mem hI t.2
    dsimp only
    rw [div_eq_div_iff hs0 ht0]
    have h' := mul_left_cancel₀ hu0 h
    linear_combination h')
theorem ev_mk (I : ∀ k, Finset (ι k)) (hI : CellMeets y I) (m : MRingOver S ι ⧸ mIdealOver S y)
    (s : cellMon S I) : ev y I hI (LocalizedModule.mk m s) = ev0 y m / aeval y (s : MRingOver S ι) :=
  LocalizedModule.liftOn_mk _ _ _
def evLin (I : ∀ k, Finset (ι k)) (hI : CellMeets y I) :
    LocalizedModule (cellMon S I) (MRingOver S ι ⧸ mIdealOver S y) →ₗ[S] Ω where
  toFun := ev y I hI
  map_add' x x' := by
    induction x using LocalizedModule.induction_on with
    | h m s =>
      induction x' using LocalizedModule.induction_on with
      | h m' s' =>
        have hs0 := aeval_ne_zero_of_mem hI s.2
        have hs0' := aeval_ne_zero_of_mem hI s'.2
        rw [LocalizedModule.mk_add_mk, ev_mk, ev_mk, ev_mk]
        simp only [Submonoid.smul_def, map_add, evalAtPoint_smul, Submonoid.coe_mul, map_mul]
        field_simp
  map_smul' s x := by
    induction x using LocalizedModule.induction_on with
    | h m t =>
      rw [LocalizedModule.smul'_mk, ev_mk, ev_mk, map_smul, smul_div_assoc, RingHom.id_apply]
open Classical in

def evMap (I : ∀ k, Finset (ι k)) :
    LocalizedModule (cellMon S I) (MRingOver S ι ⧸ mIdealOver S y) →ₗ[S] Ω :=
  if h : CellMeets y I then evLin y I h else 0
end Eval
section Rep
variable {V : Ideal (MRingOver S ι)}
end Rep
section Parts
variable {Ω : Type} [Field Ω] [Algebra S Ω] (y : (Σ k, ι k) → Ω)
end Parts
section Res
variable {Ω : Type} [Field Ω] [Algebra S Ω] {y : (Σ k, ι k) → Ω}
end Res
end CellLocEval
end
end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization


