-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SmoothAddSmul
-- name    : Development_AbelianVarietyTheory_Proofs_FoundationProofs_SmoothAddSmul
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-24T14:17:03.974243+00:00
-- url     : https://prove2.me/theorems/b505da2a-5c15-46f2-9ba6-5e285a333c45
-- title:
--   Smooth Add Smul
-- statement:
--   Definitions and structural lemmas for Smooth Add Smul, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/SmoothAddSmul.lean

import Mathlib
import Definitions.Def_Formalism_FormalDegreeBessel_StatementIO
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_QuotientSettingHolds
import Theorems.Thm_Formalism_REAL_complex_parts_mem_lie_algebra_holds
import Theorems.Thm_Formalism_REAL_rdLinV
import Theorems.Thm_Formalism_REAL_rdSmoothV

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ContDiff
noncomputable section
namespace GlobalTheory.CapelliCentral
open Formalism.REAL Formalism.QuantumDeterminants
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ} {ε : Fin n → Bool} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
open Matrix in
open scoped ContDiff in
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in
variable {n : ℕ} {ε : Fin n → Bool} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] in
theorem _root_.GlobalTheory.CapelliCentral.smooth_congr {f f' : Matrix (Fin n) (Fin n) ℂ → E}
    (hf : _root_.Formalism.REAL.SmoothOnGV ε f) (h : ∀ g, _root_.Formalism.REAL.inUJ ε g → f' g = f g) : _root_.Formalism.REAL.SmoothOnGV ε f' := by
  intro g₀ hg₀
  obtain ⟨U, F, hU, hgU, hF, hfF⟩ := hf g₀ hg₀
  exact ⟨U, F, hU, hgU, hF, fun g hg hgG => (h g hgG).trans (hfF g hg hgG)⟩
open Matrix in
open scoped ContDiff in
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in
variable {n : ℕ} {ε : Fin n → Bool} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] in
theorem _root_.GlobalTheory.CapelliCentral.smooth_add_smul {f f' : Matrix (Fin n) (Fin n) ℂ → E} (hf : _root_.Formalism.REAL.SmoothOnGV ε f)
    (hf' : _root_.Formalism.REAL.SmoothOnGV ε f') (c : ℂ) : _root_.Formalism.REAL.SmoothOnGV ε (fun x => f x + c • f' x) := by
  intro g₀ hg₀
  obtain ⟨U, F, hU, hgU, hF, hfF⟩ := hf g₀ hg₀
  obtain ⟨U', F', hU', hgU', hF', hfF'⟩ := hf' g₀ hg₀
  refine ⟨U ∩ U', fun x => F x + c • F' x, hU.inter hU', ⟨hgU, hgU'⟩,
    (hF.mono Set.inter_subset_left).add ((hF'.mono Set.inter_subset_right).const_smul c),
    fun g hg hgG => ?_⟩
  show f g + c • f' g = F g + c • F' g
  rw [hfF g hg.1 hgG, hfF' g hg.2 hgG]
open Matrix in
open scoped ContDiff in
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in
variable {n : ℕ} {ε : Fin n → Bool} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] in
theorem _root_.GlobalTheory.CapelliCentral.smooth_zero :
    _root_.Formalism.REAL.SmoothOnGV ε (fun _ : Matrix (Fin n) (Fin n) ℂ => (0 : E)) := by
  intro g₀ _
  exact ⟨Set.univ, fun _ => 0, isOpen_univ, trivial, contDiffOn_const, fun _ _ _ => rfl⟩
open Matrix in
open scoped ContDiff in
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in
variable {n : ℕ} {ε : Fin n → Bool} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] in
theorem _root_.GlobalTheory.CapelliCentral.eab_smooth {f : Matrix (Fin n) (Fin n) ℂ → E}
    (hf : _root_.Formalism.REAL.SmoothOnGV ε f) (a b : Fin n) : _root_.Formalism.REAL.SmoothOnGV ε (_root_.Formalism.REAL.EabV ε a b f) := by
  obtain ⟨hP, hQ, -, -⟩ := _root_.Formalism.REAL.complex_parts_mem_lie_algebra_holds n ε (Matrix.single a b 1)
  have h1 := _root_.Formalism.REAL.rdSmoothV n ε E f _ hf hP
  have h2 := _root_.Formalism.REAL.rdSmoothV n ε E f _ hf hQ
  have h3 := _root_.GlobalTheory.CapelliCentral.smooth_add_smul h1 h2 Complex.I
  exact _root_.GlobalTheory.CapelliCentral.smooth_congr h3 (fun g _ => rfl)
open Matrix in
open scoped ContDiff in
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in
variable {n : ℕ} {ε : Fin n → Bool} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] in
theorem _root_.GlobalTheory.CapelliCentral.eab_add_smul {f f' : Matrix (Fin n) (Fin n) ℂ → E}
    (hf : _root_.Formalism.REAL.SmoothOnGV ε f) (hf' : _root_.Formalism.REAL.SmoothOnGV ε f') (c : ℂ) (a b : Fin n)
    {g : Matrix (Fin n) (Fin n) ℂ} (hg : _root_.Formalism.REAL.inUJ ε g) :
    _root_.Formalism.REAL.EabV ε a b (fun x => f x + c • f' x) g = _root_.Formalism.REAL.EabV ε a b f g + c • _root_.Formalism.REAL.EabV ε a b f' g := by
  obtain ⟨hP, hQ, -, -⟩ := _root_.Formalism.REAL.complex_parts_mem_lie_algebra_holds n ε (Matrix.single a b 1)
  have e1 := (_root_.Formalism.REAL.rdLinV n ε E f f' _ _ 0 c g hf hf' hP hP hg).2.2
  have e2 := (_root_.Formalism.REAL.rdLinV n ε E f f' _ _ 0 c g hf hf' hQ hQ hg).2.2
  show _root_.Formalism.REAL.EcV ε _ _ g = _root_.Formalism.REAL.EcV ε _ _ g + c • _root_.Formalism.REAL.EcV ε _ _ g
  unfold _root_.Formalism.REAL.EcV
  rw [e1, e2]
  simp only [smul_add, smul_comm Complex.I c]
  abel
open Matrix in
open scoped ContDiff in
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in
variable {n : ℕ} {ε : Fin n → Bool} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] in
theorem _root_.GlobalTheory.CapelliCentral.eab_zero (a b : Fin n) (g : Matrix (Fin n) (Fin n) ℂ) :
    _root_.Formalism.REAL.EabV ε a b (fun _ => (0 : E)) g = 0 := by
  simp [_root_.Formalism.REAL.EabV, _root_.Formalism.REAL.EcV, _root_.Formalism.REAL.RdV]
open Classical in

def cut (ε : Fin n → Bool) (f : Matrix (Fin n) (Fin n) ℂ → E) : Matrix (Fin n) (Fin n) ℂ → E :=
  fun g => if inUJ ε g then f g else 0
open Matrix in
open scoped ContDiff in
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in
variable {n : ℕ} {ε : Fin n → Bool} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] in
theorem _root_.GlobalTheory.CapelliCentral.cut_of_mem (f : Matrix (Fin n) (Fin n) ℂ → E)
    {g : Matrix (Fin n) (Fin n) ℂ} (hg : _root_.Formalism.REAL.inUJ ε g) :
    _root_.GlobalTheory.CapelliCentral.cut ε f g = f g := by
  unfold _root_.GlobalTheory.CapelliCentral.cut
  rw [if_pos hg]
open Matrix in
open scoped ContDiff in
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in
variable {n : ℕ} {ε : Fin n → Bool} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] in
theorem _root_.GlobalTheory.CapelliCentral.cut_of_not_mem (f : Matrix (Fin n) (Fin n) ℂ → E)
    {g : Matrix (Fin n) (Fin n) ℂ} (hg : ¬ _root_.Formalism.REAL.inUJ ε g) :
    _root_.GlobalTheory.CapelliCentral.cut ε f g = 0 := by
  unfold _root_.GlobalTheory.CapelliCentral.cut
  rw [if_neg hg]
def smoothSpace (ε : Fin n → Bool) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] :
    Submodule ℂ (Matrix (Fin n) (Fin n) ℂ → E) where
  carrier := {f | SmoothOnGV ε f ∧ ∀ g, ¬ inUJ ε g → f g = 0}
  zero_mem' := ⟨smooth_zero, fun _ _ => rfl⟩
  add_mem' := by
    rintro f f' ⟨h1, h2⟩ ⟨h3, h4⟩
    refine ⟨smooth_congr (smooth_add_smul h1 h3 1) (fun g _ => by simp), fun g hg => ?_⟩
    simp [h2 g hg, h4 g hg]
  smul_mem' := by
    rintro c f ⟨h1, h2⟩
    refine ⟨smooth_congr (smooth_add_smul smooth_zero h1 c) (fun g _ => by simp), fun g hg => ?_⟩
    simp [h2 g hg]
def mk (f : Matrix (Fin n) (Fin n) ℂ → E) (hf : SmoothOnGV ε f) : smoothSpace ε E :=
  ⟨cut ε f, smooth_congr hf (fun _ hg => cut_of_mem f hg), fun _ hg => cut_of_not_mem f hg⟩
open Matrix in
open scoped ContDiff in
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in
variable {n : ℕ} {ε : Fin n → Bool} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] in
theorem _root_.GlobalTheory.CapelliCentral.mk_apply (f : Matrix (Fin n) (Fin n) ℂ → E)
    (hf : _root_.Formalism.REAL.SmoothOnGV ε f) {g : Matrix (Fin n) (Fin n) ℂ} (hg : _root_.Formalism.REAL.inUJ ε g) :
    (_root_.GlobalTheory.CapelliCentral.mk f hf).1 g = f g :=
  _root_.GlobalTheory.CapelliCentral.cut_of_mem f hg
open Matrix in
open scoped ContDiff in
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in
variable {n : ℕ} {ε : Fin n → Bool} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] in
theorem _root_.GlobalTheory.CapelliCentral.ext_on {F F' : _root_.GlobalTheory.CapelliCentral.smoothSpace ε E}
    (h : ∀ g, _root_.Formalism.REAL.inUJ ε g → F.1 g = F'.1 g) : F = F' := by
  apply Subtype.ext
  funext g
  by_cases hg : _root_.Formalism.REAL.inUJ ε g
  · exact h g hg
  · rw [F.2.2 g hg, F'.2.2 g hg]
def eabEnd (ε : Fin n → Bool) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (a b : Fin n) :
    Module.End ℂ (smoothSpace ε E) where
  toFun F := mk (EabV ε a b F.1) (eab_smooth F.2.1 a b)
  map_add' F F' := by
    apply ext_on
    intro g hg
    have := eab_add_smul F.2.1 F'.2.1 1 a b hg
    simp only [one_smul] at this
    rw [mk_apply _ _ hg, Submodule.coe_add, Submodule.coe_add, Pi.add_apply, mk_apply _ _ hg,
      mk_apply _ _ hg]
    exact this
  map_smul' c F := by
    apply ext_on
    intro g hg
    have := eab_add_smul smooth_zero F.2.1 c a b hg
    simp only [zero_add, eab_zero] at this
    rw [mk_apply _ _ hg, Submodule.coe_smul, Submodule.coe_smul, Pi.smul_apply, mk_apply _ _ hg]
    exact this
end GlobalTheory.CapelliCentral
namespace GlobalTheory
open Formalism.REAL Formalism.QuantumDeterminants CapelliCentral
end GlobalTheory


