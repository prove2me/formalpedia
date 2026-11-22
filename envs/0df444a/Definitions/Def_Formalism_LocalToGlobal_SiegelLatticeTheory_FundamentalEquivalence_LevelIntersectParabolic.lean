-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FundamentalEquivalence_LevelIntersectParabolic
-- name    : Formalism_LocalToGlobal_SiegelLatticeTheory_FundamentalEquivalence_LevelIntersectParabolic
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:23:36.795318+00:00
-- url     : https://prove2.me/theorems/7d10eadc-1b3a-4d15-9dc8-779a23650f11
-- title:
--   Level Intersect Parabolic
-- statement:
--   Definitions and structural lemmas for Level Intersect Parabolic, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/FundamentalEquivalence/LevelIntersectParabolic.lean

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Bridge
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.L2.SG.Sub
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain
open scoped TensorProduct
section Grp
variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)
def ratV (x : Fin n → E) : Fin n → R ⊗[F] E := fun i => inclR R (x i)
def spanR {m : ℕ} (Y : Fin m → Fin n → E) (s : Set (Fin m)) :
    Submodule (R ⊗[F] E) (Fin n → R ⊗[F] E) :=
  Submodule.span (R ⊗[F] E) ((fun a => ratV (F := F) R (Y a)) '' s)
def lin (g : HA R σ J) : (Fin n → R ⊗[F] E) →ₗ[R ⊗[F] E] (Fin n → R ⊗[F] E) :=
  Matrix.mulVecLin ((HA.mat R σ J g : GL (Fin n) (R ⊗[F] E)) : Matrix (Fin n) (Fin n) (R ⊗[F] E))
theorem lin_mul (g h : HA R σ J) (x : Fin n → R ⊗[F] E) :
    lin R σ J (g * h) x = lin R σ J g (lin R σ J h x) := by
  simp only [lin, Matrix.mulVecLin_apply]
  show ((HA.mat R σ J g * HA.mat R σ J h : GL (Fin n) (R ⊗[F] E)) :
    Matrix (Fin n) (Fin n) (R ⊗[F] E)).mulVec x = _
  rw [Units.val_mul, ← Matrix.mulVec_mulVec]
theorem lin_one (x : Fin n → R ⊗[F] E) : lin R σ J 1 x = x := by
  simp only [lin, Matrix.mulVecLin_apply]
  show ((1 : GL (Fin n) (R ⊗[F] E)) : Matrix (Fin n) (Fin n) (R ⊗[F] E)).mulVec x = x
  simp
theorem lin_inv_lin (g : HA R σ J) (x : Fin n → R ⊗[F] E) : lin R σ J g⁻¹ (lin R σ J g x) = x := by
  rw [← lin_mul, inv_mul_cancel, lin_one]
theorem lin_lin_inv (g : HA R σ J) (x : Fin n → R ⊗[F] E) : lin R σ J g (lin R σ J g⁻¹ x) = x := by
  rw [← lin_mul, mul_inv_cancel, lin_one]
def stabT {a : ℕ} (X : Fin a → Fin n → E) : Subgroup (HA R σ J) :=
  MulAction.stabilizer (HA R σ J) (ratTup (F := F) R X)
def UniC {m : ℕ} (Y : Fin m → Fin n → E) (g : HA R σ J) : Prop :=
  ∀ b : Fin m, lin R σ J g (ratV (F := F) R (Y b)) - ratV (F := F) R (Y b) ∈ spanR (F := F) R Y {a | a < b}
section UniLemmas
variable {R σ J}
variable {m : ℕ} {Y : Fin m → Fin n → E} {g : HA R σ J}
theorem uni_map_le (hg : UniC R σ J Y g) (s : Set (Fin m))
    (hs : ∀ b ∈ s, ∀ a, a < b → a ∈ s) :
    (spanR (F := F) R Y s).map (lin R σ J g) ≤ spanR (F := F) R Y s := by
  unfold spanR
  rw [Submodule.map_span, Submodule.span_le]
  rintro _ ⟨_, ⟨b, hb, rfl⟩, rfl⟩
  have h1 : Submodule.span (R ⊗[F] E) ((fun a => ratV (F := F) R (Y a)) '' {a | a < b}) ≤
      Submodule.span (R ⊗[F] E) ((fun a => ratV (F := F) R (Y a)) '' s) :=
    Submodule.span_mono (Set.image_mono fun a ha => hs b hb a ha)
  have h2 : ratV (F := F) R (Y b) ∈
      Submodule.span (R ⊗[F] E) ((fun a => ratV (F := F) R (Y a)) '' s) :=
    Submodule.subset_span ⟨b, hb, rfl⟩
  have := Submodule.add_mem _ (h1 (hg b)) h2
  simpa using this
theorem uni_sub_mem (hg : UniC R σ J Y g) (s : Set (Fin m)) (t : Set (Fin m))
    (hs : ∀ b ∈ s, ∀ a, a < b → a ∈ t) (w : Fin n → R ⊗[F] E) (hw : w ∈ spanR (F := F) R Y s) :
    lin R σ J g w - w ∈ spanR (F := F) R Y t := by
  have key : spanR (F := F) R Y s ≤
      (spanR (F := F) R Y t).comap (lin R σ J g - LinearMap.id) := by
    unfold spanR
    rw [Submodule.span_le]
    rintro _ ⟨b, hb, rfl⟩
    simp only [SetLike.mem_coe, Submodule.mem_comap, LinearMap.sub_apply, LinearMap.id_apply]
    exact Submodule.span_mono (Set.image_mono fun a ha => hs b hb a ha) (hg b)
  simpa using key hw
theorem uni_le_map (hg : UniC R σ J Y g) (s : Set (Fin m))
    (hs : ∀ b ∈ s, ∀ a, a < b → a ∈ s) :
    spanR (F := F) R Y s ≤ (spanR (F := F) R Y s).map (lin R σ J g) := by
  unfold spanR
  rw [Submodule.span_le]
  rintro _ ⟨b, hb, rfl⟩
  induction b using WellFoundedLT.induction with
  | _ b ih =>
  have hmem : ratV (F := F) R (Y b) ∈
      Submodule.span (R ⊗[F] E) ((fun a => ratV (F := F) R (Y a)) '' s) :=
    Submodule.subset_span ⟨b, hb, rfl⟩
  have h1 := Submodule.mem_map_of_mem (f := lin R σ J g) hmem
  have h2 : Submodule.span (R ⊗[F] E) ((fun a => ratV (F := F) R (Y a)) '' {a | a < b}) ≤
      (Submodule.span (R ⊗[F] E) ((fun a => ratV (F := F) R (Y a)) '' s)).map (lin R σ J g) := by
    rw [Submodule.span_le]
    rintro _ ⟨a, ha, rfl⟩
    exact ih a ha (hs b hb a ha)
  have := Submodule.sub_mem _ h1 (h2 (hg b))
  simpa using this
end UniLemmas
def uniFlag {m : ℕ} (Y : Fin m → Fin n → E) : Subgroup (HA R σ J) where
  carrier := {g | UniC R σ J Y g}
  one_mem' := by
    intro b
    simp [lin_one]
  mul_mem' := by
    intro g h hg hh b
    simp only [Set.mem_ofPred_eq] at *
    have hdc : ∀ c ∈ {a : Fin m | a < b}, ∀ a, a < c → a ∈ {a : Fin m | a < b} :=
      fun c hc a ha => lt_trans ha hc
    have h1 : lin R σ J g (lin R σ J h (ratV (F := F) R (Y b)) - ratV (F := F) R (Y b)) ∈ spanR (F := F) R Y {a | a < b} :=
      uni_map_le hg _ hdc (Submodule.mem_map_of_mem (hh b))
    have h2 := hg b
    rw [lin_mul]
    have := Submodule.add_mem _ h1 h2
    rw [map_sub] at this
    simpa using this
  inv_mem' := by
    intro g hg b
    simp only [Set.mem_ofPred_eq] at *
    have hdc : ∀ c ∈ {a : Fin m | a ≤ b}, ∀ a, a < c → a ∈ {a : Fin m | a ≤ b} :=
      fun c hc a ha => le_trans ha.le hc
    have hy : ratV (F := F) R (Y b) ∈ (spanR (F := F) R Y {a | a ≤ b}).map (lin R σ J g) :=
      uni_le_map hg _ hdc (Submodule.subset_span ⟨b, le_refl b, rfl⟩)
    obtain ⟨w, hw, hwy⟩ := hy
    have hw' : lin R σ J g⁻¹ (ratV (F := F) R (Y b)) = w := by
      rw [← hwy, lin_inv_lin]
    rw [hw', ← hwy]
    have := uni_sub_mem hg {a | a ≤ b} {a | a < b}
      (fun c hc a ha => lt_of_lt_of_le ha hc) w hw
    have := Submodule.neg_mem _ this
    simpa using this
end Grp
structure Frame (E : Type) (n r : ℕ) where

  e : Fin r → Fin n → E

  f : Fin r → Fin n → E

  z : Fin n → E
section Frames
variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)
def Frame.IsStd {r : ℕ} (P : Frame E n r) (T : F) : Prop :=
  (∀ a b, hE σ J (P.e a) (P.e b) = 0) ∧ (∀ a b, hE σ J (P.f a) (P.f b) = 0) ∧
  (∀ a b, hE σ J (P.e a) (P.f b) = if a = b then 1 else 0) ∧
  (∀ a, hE σ J (P.e a) P.z = 0) ∧ (∀ a, hE σ J (P.f a) P.z = 0) ∧
  hE σ J P.z P.z = algebraMap F E (-T) ∧ T ≠ 0
def F0 {r : ℕ} (P : Frame E n r) : Fin (r + 1) → Fin n → E := Fin.snoc P.e P.z
def tupH {r : ℕ} (P : Frame E n r) : Fin (r + 1 + r) → Fin n → E := Fin.append (F0 P) P.f
def S0 {r : ℕ} (P : Frame E n r) : Subgroup (HA R σ J) := stabT R σ J (F0 P)
def Ssub {r : ℕ} (P : Frame E n r) : Subgroup (HA R σ J) := uniFlag R σ J (F0 P)
def Hsub {r : ℕ} (P : Frame E n r) : Subgroup (HA R σ J) := stabT R σ J (tupH P)
def InXperp {r : ℕ} (P : Frame E n r) (v : Fin n → R ⊗[F] E) : Prop :=
  ∀ a, hR R σ J (ratV (F := F) R (P.e a)) v = 0
variable {R σ J}
theorem hR_add_left (x x' y : Fin n → R ⊗[F] E) :
    hR R σ J (x + x') y = hR R σ J x y + hR R σ J x' y := by
  simp only [hR, Formalism.UG.hform, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]
theorem hR_smul_left (c : R ⊗[F] E) (x y : Fin n → R ⊗[F] E) :
    hR R σ J (c • x) y = sigR R σ c * hR R σ J x y := by
  simp only [hR, Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum, mul_assoc]
theorem hR_zero_left (y : Fin n → R ⊗[F] E) : hR R σ J 0 y = 0 := by
  simp [hR, Formalism.UG.hform]
theorem hform_eq_dotProduct_mulVec {A : Type} [CommRing A] {k : ℕ} (τ : A →+* A)
    (K : Matrix (Fin k) (Fin k) A) (x y : Fin k → A) :
    Formalism.UG.hform τ K x y = dotProduct (fun i => τ (x i)) (K.mulVec y) := by
  simp [Formalism.UG.hform, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
theorem hR_lin (g : HA R σ J) (x y : Fin n → R ⊗[F] E) :
    hR R σ J (lin R σ J g x) (lin R σ J g y) = hR R σ J x y := by
  set M := ((HA.mat R σ J g : GL (Fin n) (R ⊗[F] E)) : Matrix (Fin n) (Fin n) (R ⊗[F] E))
    with hM
  have hg : Matrix.transpose (M.map (sigR R σ)) * JR R J * M = JR R J := g.2
  simp only [hR, lin, Matrix.mulVecLin_apply, hform_eq_dotProduct_mulVec, ← hM]
  have hσ : (fun i => sigR R σ ((M.mulVec x) i)) =
      (M.map (sigR R σ)).mulVec (fun i => sigR R σ (x i)) := by
    funext i
    simp [Matrix.mulVec, dotProduct, map_sum]
  rw [hσ, ← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
    Matrix.mulVec_mulVec, hg]
theorem hR_span_perp {r : ℕ} (P : Frame E n r) (v : Fin n → R ⊗[F] E) (hv : InXperp R σ J P v)
    (x : Fin n → R ⊗[F] E) (hx : x ∈ spanR (F := F) R P.e Set.univ) : hR R σ J x v = 0 := by
  unfold spanR at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, -, rfl⟩ := hx
    exact hv a
  | zero => exact hR_zero_left v
  | add x y _ _ hx hy => rw [hR_add_left, hx, hy, add_zero]
  | smul c x _ hx => rw [hR_smul_left, hx, mul_zero]
variable (R σ J)
def Nsub {r : ℕ} (P : Frame E n r) : Subgroup (HA R σ J) where
  carrier := {g | UniC R σ J P.e g ∧
    ∀ v, InXperp R σ J P v → lin R σ J g v - v ∈ spanR (F := F) R P.e Set.univ}
  one_mem' := by
    refine ⟨(uniFlag R σ J P.e).one_mem, fun v _ => ?_⟩
    simp [lin_one]
  mul_mem' := by
    rintro g h ⟨hg1, hg2⟩ ⟨hh1, hh2⟩
    refine ⟨(uniFlag R σ J P.e).mul_mem hg1 hh1, fun v hv => ?_⟩
    have h1 : lin R σ J g (lin R σ J h v - v) ∈ spanR (F := F) R P.e Set.univ :=
      uni_map_le hg1 Set.univ (fun _ _ _ _ => Set.mem_univ _)
        (Submodule.mem_map_of_mem (hh2 v hv))
    have := Submodule.add_mem _ h1 (hg2 v hv)
    rw [map_sub] at this
    rw [lin_mul]
    simpa using this
  inv_mem' := by
    rintro g ⟨hg1, hg2⟩
    refine ⟨(uniFlag R σ J P.e).inv_mem hg1, fun v hv => ?_⟩
    have hw : InXperp R σ J P (lin R σ J g⁻¹ v) := by
      intro a
      have hx : lin R σ J g (ratV (F := F) R (P.e a)) ∈ spanR (F := F) R P.e Set.univ :=
        uni_map_le hg1 Set.univ (fun _ _ _ _ => Set.mem_univ _)
          (Submodule.mem_map_of_mem (Submodule.subset_span ⟨a, Set.mem_univ _, rfl⟩))
      rw [← hR_lin g, lin_lin_inv]
      exact hR_span_perp P v hv _ hx
    have := Submodule.neg_mem _ (hg2 _ hw)
    rw [lin_lin_inv] at this
    simpa using this
def FrameUnipotentSubgroup {r : ℕ} (P : Frame E n r) : Subgroup (HA R σ J) := Nsub R σ J P ⊓ S0 R σ J P
end Frames
section Level
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)
def compV (v : HeightOneSpectrum (𝓞 F)) : GL (Fin n) (Af F ⊗[F] E) →* GL (Fin n) (Fv F v ⊗[F] E) :=
  Formalism.UG.bc (Algebra.TensorProduct.map (evalV F v) (AlgHom.id F E)).toRingHom
def latLoc (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E)) :
    Submodule (v.adicCompletionIntegers F) (Fin n → Fv F v ⊗[F] E) :=
  Submodule.span (v.adicCompletionIntegers F) (ratV (F := F) (Fv F v) '' Λ)
def Kloc (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E)) :
    Subgroup (GL (Fin n) (Fv F v ⊗[F] E)) where
  carrier := {g | ∀ x, x ∈ latLoc (E := E) v Λ ↔
    Matrix.mulVec (g : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) x ∈ latLoc (E := E) v Λ}
  one_mem' := by intro x; simp
  mul_mem' := by
    intro a b ha hb x
    simp only [Units.val_mul, ← Matrix.mulVec_mulVec]
    exact (hb x).trans (ha _)
  inv_mem' := by
    intro g hg x
    have := hg (Matrix.mulVec ((g⁻¹ : GL (Fin n) (Fv F v ⊗[F] E)) : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) x)
    rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec] at this
    exact this.symm
def incAf : HA (Af F) σ J →* GL (Fin n) (Af F ⊗[F] E) := (HR (Af F) σ J).subtype
def Kf (Λ : Set (Fin n → E)) : Subgroup (HA (Af F) σ J) :=
  ⨅ v : HeightOneSpectrum (𝓞 F), (Kloc v Λ).comap ((compV v).comp (incAf σ J))
def KS {r : ℕ} (P : Frame E n r) (Λ : Set (Fin n → E)) : Subgroup (HA (Af F) σ J) :=
  Ssub (Af F) σ J P ⊓ Kf σ J Λ
def KH {r : ℕ} (P : Frame E n r) (Λ : Set (Fin n → E)) : Subgroup (HA (Af F) σ J) :=
  Hsub (Af F) σ J P ⊓ Kf σ J Λ
def NO {r : ℕ} (P : Frame E n r) (Λ : Set (Fin n → E)) : Subgroup (HA (Af F) σ J) :=
  Nsub (Af F) σ J P ⊓ Kf σ J Λ
def levelIntersectParabolic {r : ℕ} (P : Frame E n r) (Λ : Set (Fin n → E)) : Subgroup (HA (Af F) σ J) :=
  S0 (Af F) σ J P ⊓ Kf σ J Λ
end Level
end Formalism.L2.SG.Sub


