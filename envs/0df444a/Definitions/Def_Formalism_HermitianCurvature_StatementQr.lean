-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_StatementQr
-- name    : Formalism_HermitianCurvature_StatementQr
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-24T15:54:58.610225+00:00
-- url     : https://prove2.me/theorems/321b5a86-d895-429f-8efd-8d99f6bc4a45
-- title:
--   Statement Qr
-- statement:
--   Definitions and structural lemmas for Statement Qr, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/StatementQr.lean

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_Good_comp
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_at
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_smooth_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_smooth_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_smooth_zero

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
namespace Formalism.FourierDecayAlt.Qr
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
def eps {t : ℕ} (i q : Fin t) : ℤ := if i.val < q.val then 1 else -1
def IsVec {A : Type*} [Ring A] {t : ℕ} (E : Fin t → Fin t → A) (y : Fin t → A) : Prop :=
  ∀ a b c, E a b * y c - y c * E a b = if a = c then -y b else 0
def IsCov {A : Type*} [Ring A] {t : ℕ} (E : Fin t → Fin t → A) (η : Fin t → A) : Prop :=
  ∀ a b c, E a b * η c - η c * E a b = if b = c then η a else 0
def Commute2 {A : Type*} [Ring A] {t : ℕ} (y η : Fin t → A) : Prop :=
  (∀ a b, y a * y b = y b * y a) ∧ (∀ a b, η a * η b = η b * η a) ∧ ∀ a b, y a * η b = η b * y a
def QJacobi : Prop :=
  ∀ (A : Type) [Ring A] [Algebra ℂ A] (t : ℕ) (E : Fin t → Fin t → A), GlRel E →
    ∀ (u : ℂ) (i q j p : Fin t),
      qminor E (skip1 i) (skip1 j) (u + 1) * qminor E (skip1 q) (skip1 p) u -
          qminor E (skip1 q) (skip1 j) (u + 1) * qminor E (skip1 i) (skip1 p) u =
        if i = q ∨ j = p then 0 else
          ((eps i q * eps j p : ℤ) : A) *
            (qdet E (u + 1) * qminor E (skip2 (min i q) (max i q)) (skip2 (min j p) (max j p)) u)
def DetVec : Prop :=
  ∀ (A : Type) [Ring A] [Algebra ℂ A] (t : ℕ) (E : Fin t → Fin t → A) (y : Fin t → A), GlRel E → IsVec E y →
    ∀ (w : ℂ) (j : Fin t),
      qdet E w * y j = y j * qdet E w -
        ∑ l : Fin t, (((-1 : ℤ) ^ ((j : ℕ) + (l : ℕ)) : ℤ) : A) * (y l * qminor E (skip1 j) (skip1 l) w)
def MinorCov : Prop :=
  ∀ (A : Type) [Ring A] [Algebra ℂ A] (t : ℕ) (E : Fin t → Fin t → A) (η : Fin t → A), GlRel E → IsCov E η →
    ∀ (u : ℂ) (q p i : Fin t),
      qminor E (skip1 q) (skip1 p) u * η i - η i * qminor E (skip1 q) (skip1 p) u =
        if i = p then 0 else ∑ a : Fin t, if a = q then 0 else
          ((eps a q * eps i p * (-1) ^ ((a : ℕ) + (i : ℕ)) : ℤ) : A) *
            (qminor E (skip2 (min a q) (max a q)) (skip2 (min i p) (max i p)) u * η a)
def chY {A : Type*} [Ring A] [Algebra ℂ A] {t : ℕ} (E : Fin t → Fin t → A) (u : ℂ) (y : Fin t → A) (ξ : Fin t → ℂ) : A :=
  ∑ i : Fin t, ∑ j : Fin t, ((-1 : ℂ) ^ ((i : ℕ) + (j : ℕ)) * ξ i) • (y j * qminor E (skip1 i) (skip1 j) u)
def chX {A : Type*} [Ring A] [Algebra ℂ A] {t : ℕ} (E : Fin t → Fin t → A) (u : ℂ) (x : Fin t → ℂ) (η : Fin t → A) : A :=
  ∑ i : Fin t, ∑ j : Fin t, ((-1 : ℂ) ^ ((i : ℕ) + (j : ℕ)) * x j) • (η i * qminor E (skip1 i) (skip1 j) u)
def chYY {A : Type*} [Ring A] [Algebra ℂ A] {t : ℕ} (E : Fin t → Fin t → A) (u : ℂ) (y η : Fin t → A) : A :=
  ∑ i : Fin t, ∑ j : Fin t, ((-1 : ℂ) ^ ((i : ℕ) + (j : ℕ))) • (η i * y j * qminor E (skip1 i) (skip1 j) u)
def ch2 {A : Type*} [Ring A] [Algebra ℂ A] {t : ℕ} (E : Fin t → Fin t → A) (u : ℂ) (y : Fin t → A) (x : Fin t → ℂ)
    (η : Fin t → A) (ξ : Fin t → ℂ) : A :=
  ∑ i : Fin t, ∑ i' : Fin t, ∑ j : Fin t, ∑ j' : Fin t,
    if i < i' ∧ j < j' then
      ((-1 : ℂ) ^ ((i : ℕ) + (i' : ℕ) + (j : ℕ) + (j' : ℕ))) •
        ((ξ i' • η i - ξ i • η i') * (x j' • y j - x j • y j') * qminor E (skip2 i i') (skip2 j j') u)
    else 0
def AlgDetBasis : Prop :=
  ∀ (A : Type) [Ring A] [Algebra ℂ A] (t : ℕ) (E : Fin t → Fin t → A) (y η : Fin t → A), GlRel E → IsVec E y →
    IsCov E η → Commute2 y η → ∀ (u : ℂ) (p q : Fin t),
      qdet E (u + 1) * ch2 E (u - 1) y (Pi.single p 1) η (Pi.single q 1) +
          chY E (u + 1) y (Pi.single q 1) * chX E (u - 1) (Pi.single p 1) η =
        chYY E u y η * chatA E u (Pi.single p 1) (Pi.single q 1)
def AlgDet : Prop :=
  ∀ (A : Type) [Ring A] [Algebra ℂ A] (t : ℕ) (E : Fin t → Fin t → A) (y η : Fin t → A), GlRel E → IsVec E y →
    IsCov E η → Commute2 y η → ∀ (u : ℂ) (x ξ : Fin t → ℂ),
      qdet E (u + 1) * ch2 E (u - 1) y x η ξ + chY E (u + 1) y ξ * chX E (u - 1) x η =
        chYY E u y η * chatA E u x ξ
section Ring
variable (k r : ℕ) (i : Fin (r + 1)) (D : Set (Mx k r)) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E]
def SV : Submodule ℂ (Mx k r → E) where
  carrier := {φ | SmoothLev k r i D φ ∧ ∀ g, g ∉ Glev k r i ∩ D → φ g = 0}
  add_mem' := fun {a b} ha hb => ⟨Qx2.smooth_add ha.1 hb.1, fun g hg => by
    show a g + b g = 0
    rw [ha.2 g hg, hb.2 g hg, add_zero]⟩
  zero_mem' := ⟨Qx2.smooth_zero, fun _ _ => rfl⟩
  smul_mem' := fun c {a} ha => ⟨Qx2.smooth_smul ha.1 c, fun g hg => by
    show c • a g = 0
    rw [ha.2 g hg, smul_zero]⟩
variable {k r i D E}
open Classical in

def cutF (k r : ℕ) (i : Fin (r + 1)) (D : Set (Mx k r)) (f : Mx k r → E) : Mx k r → E :=
  fun g => if g ∈ Glev k r i ∩ D then f g else 0
theorem cutF_of_mem {f : Mx k r → E} {g : Mx k r} (hg : g ∈ Glev k r i ∩ D) : cutF k r i D f g = f g := by
  unfold cutF
  exact if_pos hg
theorem cutF_of_not_mem {f : Mx k r → E} {g : Mx k r} (hg : g ∉ Glev k r i ∩ D) : cutF k r i D f g = 0 := by
  unfold cutF
  exact if_neg hg
theorem cutF_smooth (hD : IsOpen D) {f : Mx k r → E} (hf : SmoothLev k r i D f) :
    SmoothLev k r i D (cutF k r i D f) := by
  intro g₀ hg₀
  obtain ⟨U, F, hU, hgU, hF, hfF⟩ := hf g₀ hg₀
  refine ⟨U ∩ D, F, hU.inter hD, ⟨hgU, hg₀.2⟩, hF.mono Set.inter_subset_left, fun g hg hgl => ?_⟩
  rw [cutF_of_mem ⟨hgl, hg.2⟩]
  exact hfF g hg.1 hgl
theorem cutF_mem (hD : IsOpen D) {f : Mx k r → E} (hf : SmoothLev k r i D f) : cutF k r i D f ∈ SV k r i D E :=
  ⟨cutF_smooth hD hf, fun _ hg => cutF_of_not_mem hg⟩
def mkV (hD : IsOpen D) (f : Mx k r → E) (hf : SmoothLev k r i D f) : SV k r i D E := ⟨cutF k r i D f, cutF_mem hD hf⟩
theorem SV_ext {φ ψ : SV k r i D E} (h : ∀ g ∈ Glev k r i ∩ D, φ.1 g = ψ.1 g) : φ = ψ := by
  apply Subtype.ext
  funext g
  by_cases hg : g ∈ Glev k r i ∩ D
  · exact h g hg
  · rw [φ.2.2 g hg, ψ.2.2 g hg]
open Classical in

def opV (k r : ℕ) (i : Fin (r + 1)) (D : Set (Mx k r)) (T : (Mx k r → E) → Mx k r → E) : Module.End ℂ (SV k r i D E) :=
  if h : IsOpen D ∧ Qx2.Good k r i D T then
    { toFun := fun φ => ⟨cutF k r i D (T φ.1), cutF_mem h.1 (h.2.sm _ φ.2.1)⟩
      map_add' := fun φ ψ => SV_ext fun g hg => by
        show cutF k r i D (T (φ.1 + ψ.1)) g = cutF k r i D (T φ.1) g + cutF k r i D (T ψ.1) g
        rw [cutF_of_mem hg, cutF_of_mem hg, cutF_of_mem hg]
        have := h.2.lin φ.1 ψ.1 1 φ.2.1 ψ.2.1 g hg
        simp only [one_smul] at this
        exact this
      map_smul' := fun c φ => SV_ext fun g hg => by
        show cutF k r i D (T (c • φ.1)) g = c • cutF k r i D (T φ.1) g
        rw [cutF_of_mem hg, cutF_of_mem hg]
        have h0 := h.2.lin (fun _ => 0) φ.1 c Qx2.smooth_zero φ.2.1 g hg
        have h1 := h.2.lin (fun _ => 0) (fun _ => 0) 1 Qx2.smooth_zero Qx2.smooth_zero g hg
        simp only [one_smul, add_zero, left_eq_add] at h1
        simp only [zero_add] at h0
        rw [h1, zero_add] at h0
        exact h0 }
  else 0
def EV (k r : ℕ) (i : Fin (r + 1)) (D : Set (Mx k r)) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E]
    (a b : Fin (mdim k r i)) : Module.End ℂ (SV k r i D E) :=
  opV k r i D fun f => EH k r (posL k r i a) (posL k r i b) f
def mulF (c : Mx k r → ℂ) (f : Mx k r → E) : Mx k r → E := fun g => c g • f g
def yV (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (i : Fin (r + 1)) (D : Set (Mx k r)) (E : Type) [NormedAddCommGroup E]
    [NormedSpace ℂ E] (c : Fin (mdim k r i)) : Module.End ℂ (SV k r i D E) :=
  opV k r i D (mulF fun g => yv k r z i g c)
def etaV (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (i : Fin (r + 1)) (D : Set (Mx k r)) (E : Type) [NormedAddCommGroup E]
    [NormedSpace ℂ E] (c : Fin (mdim k r i)) : Module.End ℂ (SV k r i D E) :=
  opV k r i D (mulF fun g => ybv k r z i g c)
end Ring
def MulGood : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (i : Fin (r + 1))
    (D : Set (Mx k r)) (c : Fin (mdim k r i)),
    Qx2.Good k r i D (mulF (E := E) fun g => yv k r z i g c) ∧ Qx2.Good k r i D (mulF (E := E) fun g => ybv k r z i g c)
def BridgeRel : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (i : Fin (r + 1))
    (D : Set (Mx k r)), IsOpen D →
    GlRel (EV k r i D E) ∧ IsVec (EV k r i D E) (yV k r z i D E) ∧ IsCov (EV k r i D E) (etaV k r z i D E) ∧
      Commute2 (yV k r z i D E) (etaV k r z i D E)
def BridgeMinor : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (k r : ℕ) (i : Fin (r + 1)) (D : Set (Mx k r)), IsOpen D →
    ∀ (t : ℕ) (a b : Fin t → Fin (mdim k r i)) (u : ℂ) (φ : SV k r i D E), ∀ g ∈ Glev k r i ∩ D,
      (qminor (EV k r i D E) a b u φ).1 g = qminorOp (EH k r) (posL k r i ∘ a) (posL k r i ∘ b) u φ.1 g
def tV (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (i : Fin (r + 1)) (D : Set (Mx k r)) (E : Type) [NormedAddCommGroup E]
    [NormedSpace ℂ E] (Y : ℂ) : Fin 2 → Fin 2 → Module.End ℂ (SV k r i D E) :=
  fun p q =>
    match p, q with
    | 0, 0 => qdet (EV k r i D E) (uC k r i Y)
    | 0, 1 => -chX (EV k r i D E) (uC k r i Y - 1) (xv k r z' i) (etaV k r z i D E)
    | 1, 0 => -chY (EV k r i D E) (uC k r i Y) (yV k r z i D E) (xbv k r z' i)
    | 1, 1 => -ch2 (EV k r i D E) (uC k r i Y - 1) (yV k r z i D E) (xv k r z' i) (etaV k r z i D E) (xbv k r z' i)
def BridgeT : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (i : Fin (r + 1))
    (D : Set (Mx k r)) (hD : IsOpen D) (f : Mx k r → E) (hf : SmoothLev k r i D f) (Y : ℂ) (p q : Fin 2),
    SmoothLev k r i D (tL k r z z' i Y p q f) ∧
      ∀ g ∈ Glev k r i ∩ D, tL k r z z' i Y p q f g = (tV k r z z' i D E Y p q (mkV hD f hf)).1 g
def ChatFrame : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (k r : ℕ) (D : Set (Mx k r)), IsOpen D →
    ∀ (x : Fin (2 * r + k + 1) → ℂ) (Bs : Fin k → Fin (2 * r + k + 1) → ℂ), inWb k r x → herm (Hpk k r) x x ≠ 0 →
    IsFrameOf k r [x] Bs → ∀ (u : ℂ) (φ : SV k r (Fin.last r) D E), ∀ g ∈ Glev k r (Fin.last r) ∩ D,
      (chatA (EV k r (Fin.last r) D E) u (fun j => x (posL k r (Fin.last r) j))
          (fun j => herm (Hpk k r) (bvec (posL k r (Fin.last r) j)) x) φ).1 g =
        herm (Hpk k r) x x • capR k r Bs u φ.1 g
def CapRGood : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (k r m : ℕ) (i : Fin (r + 1)) (D : Set (Mx k r)), IsOpen D →
    ∀ (Bs : Fin m → Fin (2 * r + k + 1) → ℂ), (∀ a, inWb k r (Bs a)) → ∀ w : ℂ,
      Qx2.Good k r i D (capR (E := E) k r Bs w)
def LeftRightSwap : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (k r m : ℕ) (i : Fin (r + 1)) (D : Set (Mx k r)), IsOpen D →
    ∀ (Bs : Fin m → Fin (2 * r + k + 1) → ℂ), (∀ a, inWb k r (Bs a)) → ∀ (w : ℂ) (F : Mx k r → E),
    SmoothLev k r i D F → ∀ g₀ ∈ Glev k r i ∩ D,
      capR k r (fun a => g₀⁻¹ *ᵥ Bs a) w F g₀ = capLft k r Bs w F g₀
def OneParamDiff : Prop :=
  ∀ (W : Type) [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W] (φ : ℝ → (W →L[ℂ] W)),
    φ 0 = 1 → (∀ s t, φ (s + t) = (φ s).comp (φ t)) → Continuous φ →
    ∃ A : W →L[ℂ] W, ∀ t, HasDerivAt φ ((φ t).comp A) t
end Formalism.FourierDecayAlt.Qr


