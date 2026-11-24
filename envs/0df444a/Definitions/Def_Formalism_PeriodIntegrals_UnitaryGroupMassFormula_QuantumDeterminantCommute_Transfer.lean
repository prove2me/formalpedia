-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuantumDeterminantCommute_Transfer
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuantumDeterminantCommute_Transfer
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-24T14:44:50.249696+00:00
-- url     : https://prove2.me/theorems/9f456b9f-7b84-40fb-8d66-338f9e480db9
-- title:
--   Transfer
-- statement:
--   Definitions and structural lemmas for Transfer, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/QuantumDeterminantCommute/Transfer.lean

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuantumDeterminantCommute_Development
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
noncomputable section
namespace QmCapCommW
abbrev Pt (k r : ℕ) (i : Fin (r + 1)) (D : Set (Mx k r)) : Type := {g : Mx k r // g ∈ Glev k r i ∩ D}
open Classical in

def ext0 {k r : ℕ} {i : Fin (r + 1)} {D : Set (Mx k r)} {E : Type} [Zero E] (φ : Pt k r i D → E) : Mx k r → E :=
  fun g => if h : g ∈ Glev k r i ∩ D then φ ⟨g, h⟩ else 0
section Core
variable {k r : ℕ} {i : Fin (r + 1)} {D : Set (Mx k r)} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
lemma extension_by_zero_apply {φ : Pt k r i D → E} {g : Mx k r} (hg : g ∈ Glev k r i ∩ D) : ext0 φ g = φ ⟨g, hg⟩ := by
  simp only [ext0, dif_pos hg]
lemma matrixExtendByZero_add (φ ψ : Pt k r i D → E) : ext0 (φ + ψ) = fun h => ext0 φ h + (1 : ℂ) • ext0 ψ h := by
  funext h
  simp only [ext0]
  split_ifs <;> simp
lemma extendByZeroOffSubset_smul_apply (c : ℂ) (φ : Pt k r i D → E) : ext0 (c • φ) = fun h => (fun _ => (0 : E)) h + c • ext0 φ h := by
  funext h
  simp only [ext0]
  split_ifs <;> simp
lemma matrixExtendByZero_zero : ext0 (0 : Pt k r i D → E) = fun _ => 0 := by
  funext h
  simp only [ext0]
  split_ifs <;> simp
lemma smooth_congr (hD : IsOpen D) {f f' : Mx k r → E} (h : ∀ g ∈ Glev k r i ∩ D, f g = f' g)
    (hf : SmoothLev k r i D f) : SmoothLev k r i D f' := by
  intro g₀ hg₀
  obtain ⟨U, F, hU, hgU, hF, hfF⟩ := hf g₀ hg₀
  refine ⟨U ∩ D, F, hU.inter hD, ⟨hgU, hg₀.2⟩, hF.mono Set.inter_subset_left, fun g hg hgl => ?_⟩
  rw [← h g ⟨hgl, hg.2⟩]
  exact hfF g hg.1 hgl
lemma smooth_zero : SmoothLev k r i D (fun _ : Mx k r => (0 : E)) := fun _ _ => ⟨Set.univ, fun _ => 0, isOpen_univ, trivial, contDiffOn_const, fun _ _ _ => rfl⟩
lemma smooth_lin {f f' : Mx k r → E} (hf : SmoothLev k r i D f) (hf' : SmoothLev k r i D f') (c : ℂ) :
    SmoothLev k r i D (fun g => f g + c • f' g) := by
  intro g₀ hg₀
  obtain ⟨U1, F1, hU1, hg1, hF1, hf1⟩ := hf g₀ hg₀
  obtain ⟨U2, F2, hU2, hg2, hF2, hf2⟩ := hf' g₀ hg₀
  refine ⟨U1 ∩ U2, fun g => F1 g + c • F2 g, hU1.inter hU2, ⟨hg1, hg2⟩,
    (hF1.mono Set.inter_subset_left).add ((hF2.mono Set.inter_subset_right).const_smul c),
    fun g hg hgl => ?_⟩
  show f g + c • f' g = F1 g + c • F2 g
  rw [hf1 g hg.1 hgl, hf2 g hg.2 hgl]
variable (k r i D E) in

def SS : Submodule ℂ (Pt k r i D → E) where
  carrier := {φ | SmoothLev k r i D (ext0 φ)}
  add_mem' {φ ψ} hφ hψ := by
    show SmoothLev k r i D (ext0 (φ + ψ))
    rw [matrixExtendByZero_add]; exact smooth_lin hφ hψ 1
  zero_mem' := by
    show SmoothLev k r i D (ext0 (0 : Pt k r i D → E))
    rw [matrixExtendByZero_zero]; exact smooth_zero
  smul_mem' c φ hφ := by
    show SmoothLev k r i D (ext0 (c • φ))
    rw [extendByZeroOffSubset_smul_apply]; exact smooth_lin smooth_zero hφ c
lemma eh_zero (a b : Fin (2 * r + k + 1)) (g : Mx k r) : EH k r a b (fun _ : Mx k r => (0 : E)) g = 0 := by
  simp [EH, EabH, RdV]
def TT (a b : Fin (mdim k r i)) (φ : Pt k r i D → E) : Pt k r i D → E :=
  fun p => EH k r (posL k r i a) (posL k r i b) (ext0 φ) p.1
lemma TT_mem (hP : EabPres) (hD : IsOpen D) {φ : Pt k r i D → E} (hφ : φ ∈ SS k r i D E) (a b : Fin (mdim k r i)) :
    TT a b φ ∈ SS k r i D E := by
  have h1 := (hP E k r 0 i D a b (ext0 φ) (ext0 φ) 0 hD hφ hφ).1
  refine smooth_congr hD (fun g hg => ?_) h1
  exact (extension_by_zero_apply (φ := TT a b φ) hg).symm
lemma TT_add (hP : EabPres) (hD : IsOpen D) {φ ψ : Pt k r i D → E} (hφ : φ ∈ SS k r i D E)
    (hψ : ψ ∈ SS k r i D E) (a b : Fin (mdim k r i)) : TT a b (φ + ψ) = TT a b φ + TT a b ψ := by
  funext p
  have h3 := (hP E k r 0 i D a b (ext0 φ) (ext0 ψ) 1 hD hφ hψ).2.2 p.1 p.2
  show EH k r (posL k r i a) (posL k r i b) (ext0 (φ + ψ)) p.1 =
    EH k r (posL k r i a) (posL k r i b) (ext0 φ) p.1 + EH k r (posL k r i a) (posL k r i b) (ext0 ψ) p.1
  rw [matrixExtendByZero_add, h3, one_smul]
lemma TT_smul (hP : EabPres) (hD : IsOpen D) {φ : Pt k r i D → E} (hφ : φ ∈ SS k r i D E) (c : ℂ)
    (a b : Fin (mdim k r i)) : TT a b (c • φ) = c • TT a b φ := by
  funext p
  have h3 := (hP E k r 0 i D a b (fun _ => (0 : E)) (ext0 φ) c hD smooth_zero hφ).2.2 p.1 p.2
  try dsimp only at h3
  show EH k r (posL k r i a) (posL k r i b) (ext0 (c • φ)) p.1 =
    c • EH k r (posL k r i a) (posL k r i b) (ext0 φ) p.1
  rw [extendByZeroOffSubset_smul_apply]
  try dsimp only
  rw [h3, eh_zero, zero_add]
def EE (hP : EabPres) (hD : IsOpen D) (a b : Fin (mdim k r i)) : Module.End ℂ (SS k r i D E) where
  toFun x := ⟨TT a b x.1, TT_mem hP hD x.2 a b⟩
  map_add' x y := Subtype.ext (TT_add hP hD x.2 y.2 a b)
  map_smul' c x := Subtype.ext (TT_smul hP hD x.2 c a b)
def Rep (F : Mx k r → E) (φ : Pt k r i D → E) : Prop := ∀ g (hg : g ∈ Glev k r i ∩ D), F g = φ ⟨g, hg⟩
end Core
end QmCapCommW


