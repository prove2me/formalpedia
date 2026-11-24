-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TorusInvariance_Development
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TorusInvariance_Development
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-24T14:24:54.129206+00:00
-- url     : https://prove2.me/theorems/9272da25-f9df-4bd4-8bb9-8af1e35cc1cd
-- title:
--   Development
-- statement:
--   Definitions and structural lemmas for Development, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/TorusInvariance/Development.lean

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped ContDiff
noncomputable section
namespace Formalism.FourierDecayAlt.Q.TInvW
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
def blk {k r : ℕ} (i : Fin (r + 1)) (g : Mx k r) : Matrix (Fin (mdim k r i)) (Fin (mdim k r i)) ℂ :=
  fun a b => g (posL k r i a) (posL k r i b)
def StepS : Prop :=
  ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (i : Fin (r + 1)), inWb k r z →
    (1 : Mx k r) ∈ Slev k r z i ∧ ∀ s ∈ Slev k r z i, s ∈ Glev k r i ∧ s *ᵥ fvec k r z i = fvec k r z i
def StepGrp : Prop :=
  ∀ (k r : ℕ) (i : Fin (r + 1)), ∀ g ∈ Glev k r i, ∀ h ∈ Glev k r i, g * h ∈ Glev k r i
def StepVec : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (i : Fin (r + 1)), inWb k r z → inWb k r z' →
    (∀ s ∈ Slev k r z i, ∀ g : Mx k r, yv k r z i (s * g) = yv k r z i g ∧ ybv k r z i (s * g) = ybv k r z i g) ∧
    ∀ s' ∈ Slev k r z' i,
      blk i s' * blk i s'⁻¹ = 1 ∧ blk i s'⁻¹ * blk i s' = 1 ∧
      blk i s' *ᵥ xv k r z' i = xv k r z' i ∧ xbv k r z' i ᵥ* blk i s'⁻¹ = xbv k r z' i ∧
      ∀ g ∈ Glev k r i, yv k r z i g = blk i s' *ᵥ yv k r z i (g * s') ∧
        ybv k r z i g = ybv k r z i (g * s') ᵥ* blk i s'⁻¹
def StepCongr : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (k r : ℕ) (i : Fin (r + 1)) (D : Set (Mx k r))
    (a b : Fin (mdim k r i)) (f f' : Mx k r → E) (g : Mx k r), IsOpen D → g ∈ Glev k r i ∩ D →
    (∀ x ∈ Glev k r i ∩ D, f x = f' x) →
    EH k r (posL k r i a) (posL k r i b) f g = EH k r (posL k r i a) (posL k r i b) f' g
def StepRight : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (k r : ℕ) (i : Fin (r + 1)) (D : Set (Mx k r))
    (a b : Fin (mdim k r i)) (f : Mx k r → E) (s' g : Mx k r), IsOpen D → SmoothLev k r i D f →
    s' ∈ Glev k r i → g ∈ Glev k r i → g * s' ∈ D →
    EH k r (posL k r i a) (posL k r i b) (fun x => f (x * s')) g =
      ∑ c, ∑ d, (blk i s'⁻¹ c a * blk i s' b d) • EH k r (posL k r i c) (posL k r i d) f (g * s')
def StepRSm : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (k r : ℕ) (i : Fin (r + 1)) (D : Set (Mx k r))
    (f : Mx k r → E) (s' : Mx k r), s' ∈ Glev k r i → (∀ g ∈ Glev k r i ∩ D, g * s' ∈ D) →
    SmoothLev k r i D f → SmoothLev k r i D (fun x => f (x * s'))
section Alg
variable {A : Type*} [Ring A] [Algebra ℂ A] {n : ℕ}
end Alg
section Model
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {k r : ℕ} {i : Fin (r + 1)} {D : Set (Mx k r)}
abbrev Pt (k r : ℕ) (i : Fin (r + 1)) (D : Set (Mx k r)) : Type := {g : Mx k r // g ∈ Glev k r i ∩ D}
open Classical in

def ext (k r : ℕ) (i : Fin (r + 1)) (D : Set (Mx k r)) (φ : Pt k r i D → E) : Mx k r → E :=
  fun g => if h : g ∈ Glev k r i ∩ D then φ ⟨g, h⟩ else 0
lemma ext_at {φ : Pt k r i D → E} {g : Mx k r} (hg : g ∈ Glev k r i ∩ D) : ext k r i D φ g = φ ⟨g, hg⟩ := by
  unfold ext
  rw [dif_pos hg]
lemma lev_congr (hD : IsOpen D) {f f' : Mx k r → E} (h : ∀ g ∈ Glev k r i ∩ D, f g = f' g)
    (hf : SmoothLev k r i D f) : SmoothLev k r i D f' := by
  intro g₀ hg₀
  obtain ⟨U, F, hU, hgU, hF, hfF⟩ := hf g₀ hg₀
  refine ⟨U ∩ D, F, hU.inter hD, ⟨hgU, hg₀.2⟩, hF.mono Set.inter_subset_left, fun g hg hgG => ?_⟩
  rw [← h g ⟨hgG, hg.2⟩, hfF g hg.1 hgG]
lemma lev_zero : SmoothLev k r i D (fun _ : Mx k r => (0 : E)) := fun _ _ => ⟨Set.univ, fun _ => 0, isOpen_univ, trivial, contDiffOn_const, fun _ _ _ => rfl⟩
lemma lev_add {f f' : Mx k r → E} (hf : SmoothLev k r i D f) (hf' : SmoothLev k r i D f') :
    SmoothLev k r i D (fun g => f g + f' g) := by
  intro g₀ hg₀
  obtain ⟨U, F, hU, hgU, hF, hfF⟩ := hf g₀ hg₀
  obtain ⟨U', F', hU', hgU', hF', hfF'⟩ := hf' g₀ hg₀
  refine ⟨U ∩ U', fun g => F g + F' g, hU.inter hU', ⟨hgU, hgU'⟩,
    (hF.mono Set.inter_subset_left).add (hF'.mono Set.inter_subset_right), fun g hg hgG => ?_⟩
  show f g + f' g = F g + F' g
  rw [hfF g hg.1 hgG, hfF' g hg.2 hgG]
lemma lev_smul {f : Mx k r → E} (c : ℂ) (hf : SmoothLev k r i D f) :
    SmoothLev k r i D (fun g => c • f g) := by
  intro g₀ hg₀
  obtain ⟨U, F, hU, hgU, hF, hfF⟩ := hf g₀ hg₀
  refine ⟨U, fun g => c • F g, hU, hgU, hF.const_smul c, fun g hg hgG => ?_⟩
  show c • f g = c • F g
  rw [hfF g hg hgG]
variable (E k r i D) in

def Sm : Submodule ℂ (Pt k r i D → E) where
  carrier := {φ | SmoothLev k r i D (ext k r i D φ)}
  add_mem' {φ ψ} hφ hψ := by
    have e : ext k r i D (φ + ψ) = fun g => ext k r i D φ g + ext k r i D ψ g := by
      funext g; unfold ext; split_ifs <;> simp
    show SmoothLev k r i D (ext k r i D (φ + ψ))
    rw [e]; exact lev_add hφ hψ
  zero_mem' := by
    have e : ext k r i D (0 : Pt k r i D → E) = fun _ => 0 := by
      funext g; unfold ext; split_ifs <;> simp
    show SmoothLev k r i D (ext k r i D (0 : Pt k r i D → E))
    rw [e]; exact lev_zero
  smul_mem' c φ hφ := by
    have e : ext k r i D (c • φ) = fun g => c • ext k r i D φ g := by
      funext g; unfold ext; split_ifs <;> simp
    show SmoothLev k r i D (ext k r i D (c • φ))
    rw [e]; exact lev_smul c hφ
def Rep (F : Mx k r → E) (φ : Pt k r i D → E) : Prop :=
  ∀ g (hg : g ∈ Glev k r i ∩ D), F g = φ ⟨g, hg⟩
def Tf (a b : Fin (mdim k r i)) (φ : Pt k r i D → E) : Pt k r i D → E :=
  fun p => EH k r (posL k r i a) (posL k r i b) (ext k r i D φ) p.1
lemma eh_zero (a b : Fin (2 * r + k + 1)) (g : Mx k r) :
    EH k r a b (fun _ : Mx k r => (0 : E)) g = 0 := by
  simp [EabH, RdV]
section Ops
variable (hP : EabPres) (hC : StepCongr) (hD : IsOpen D)
include hP hC hD
lemma Tf_mem {φ : Pt k r i D → E} (hφ : φ ∈ Sm E k r i D) (a b : Fin (mdim k r i)) :
    Tf a b φ ∈ Sm E k r i D := by
  have hφ' : SmoothLev k r i D (ext k r i D φ) := hφ
  have h1 := (hP E k r (fun _ => 0) i D a b (ext k r i D φ) (ext k r i D φ) 0 hD hφ' hφ').1
  show SmoothLev k r i D (ext k r i D (Tf a b φ))
  exact lev_congr hD (fun g hg => (ext_at (φ := Tf a b φ) hg).symm) h1
lemma Tf_add {φ ψ : Pt k r i D → E} (hφ : φ ∈ Sm E k r i D) (hψ : ψ ∈ Sm E k r i D)
    (a b : Fin (mdim k r i)) : Tf a b (φ + ψ) = Tf a b φ + Tf a b ψ := by
  have hφ' : SmoothLev k r i D (ext k r i D φ) := hφ
  have hψ' : SmoothLev k r i D (ext k r i D ψ) := hψ
  funext p
  have e : ext k r i D (φ + ψ) = fun x => ext k r i D φ x + (1 : ℂ) • ext k r i D ψ x := by
    funext g; unfold ext; split_ifs <;> simp
  have h3 := (hP E k r (fun _ => 0) i D a b (ext k r i D φ) (ext k r i D ψ) 1 hD hφ' hψ').2.2 p.1 p.2
  show EH k r (posL k r i a) (posL k r i b) (ext k r i D (φ + ψ)) p.1 =
    EH k r (posL k r i a) (posL k r i b) (ext k r i D φ) p.1 + EH k r (posL k r i a) (posL k r i b) (ext k r i D ψ) p.1
  rw [e, h3, one_smul]
lemma Tf_smul {φ : Pt k r i D → E} (hφ : φ ∈ Sm E k r i D) (c : ℂ)
    (a b : Fin (mdim k r i)) : Tf a b (c • φ) = c • Tf a b φ := by
  have hφ' : SmoothLev k r i D (ext k r i D φ) := hφ
  funext p
  have e : ext k r i D (c • φ) = fun x => (0 : E) + c • ext k r i D φ x := by
    funext g; unfold ext; split_ifs <;> simp
  have h3 := (hP E k r (fun _ => 0) i D a b (fun _ => (0 : E)) (ext k r i D φ) c hD lev_zero hφ').2.2 p.1 p.2
  show EH k r (posL k r i a) (posL k r i b) (ext k r i D (c • φ)) p.1 =
    c • EH k r (posL k r i a) (posL k r i b) (ext k r i D φ) p.1
  rw [e, h3, eh_zero, zero_add]
def Ealg (a b : Fin (mdim k r i)) : Module.End ℂ (Sm E k r i D) where
  toFun x := ⟨Tf a b x.1, Tf_mem hP hC hD x.2 a b⟩
  map_add' x y := Subtype.ext (Tf_add hP hC hD x.2 y.2 a b)
  map_smul' c x := Subtype.ext (Tf_smul hP hC hD x.2 c a b)
variable {s' : Mx k r} (hs' : ∀ g ∈ Glev k r i ∩ D, g * s' ∈ Glev k r i ∩ D)
def Rf (φ : Pt k r i D → E) : Pt k r i D → E := fun p => φ ⟨p.1 * s', hs' p.1 p.2⟩
variable (hRS : StepRSm) (hs'G : s' ∈ Glev k r i)
include hRS hs'G
lemma Rf_mem {φ : Pt k r i D → E} (hφ : φ ∈ Sm E k r i D) : Rf hs' φ ∈ Sm E k r i D := by
  have hφ' : SmoothLev k r i D (ext k r i D φ) := hφ
  have h1 := hRS E k r i D (ext k r i D φ) s' hs'G (fun g hg => (hs' g hg).2) hφ'
  show SmoothLev k r i D (ext k r i D (Rf hs' φ))
  refine lev_congr hD (fun g hg => ?_) h1
  show ext k r i D φ (g * s') = ext k r i D (Rf hs' φ) g
  rw [ext_at hg, ext_at (hs' g hg)]
  rfl
def RL : Module.End ℂ (Sm E k r i D) where
  toFun x := ⟨Rf hs' x.1, Rf_mem hP hC hD hs' hRS hs'G x.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
end Ops
end Model
end Formalism.FourierDecayAlt.Q.TInvW


