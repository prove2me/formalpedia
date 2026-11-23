-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
-- name    : Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ChartGen
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T03:17:10.237514+00:00
-- url     : https://prove2.me/theorems/8f2b33ae-1cf3-46f1-8e9f-019a838968ce
-- title:
--   Chart Gen
-- statement:
--   Definitions and structural lemmas for Chart Gen, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/SemilocalFrames/ChartGen.lean

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementMass
import Definitions.Def_Formalism_FlagUnipotentLattices_CardSubmodulesAndLinearEquivBounds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Matrix
open scoped ENNReal Classical
namespace GlobalTheory.Mass
def orbSum (G : Type*) [Group G] {α : Type*} [MulAction G α] (X : Set α) (N : α → ℝ≥0∞) : ℝ≥0∞ :=
  ∑' q : {q : MulAction.orbitRel.Quotient G α // Quotient.out q ∈ X},
    ((ENat.card (MulAction.stabilizer G (Quotient.out q.1)) : ℕ∞) : ℝ≥0∞)⁻¹ * N (Quotient.out q.1)
def orbMass (G : Type*) [Group G] {α : Type*} [MulAction G α] (X : Set α) : ℝ≥0∞ :=
  orbSum G X fun _ => 1
def Stable (G : Type*) [Group G] {α : Type*} [MulAction G α] (X : Set α) : Prop :=
  ∀ (g : G), ∀ x ∈ X, g • x ∈ X
section Act
variable {R K V : Type*} [CommRing R] [Field K] [StarRing K] [Algebra R K]
  [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
instance latAct (h : V →ₗ⋆[K] V →ₗ[K] K) : MulAction (Formalism.HermitianLatticesTheory.isom h) (Submodule R V) where
  smul g L := Formalism.HermitianLatticesTheory.gmap (g : V ≃ₗ[K] V) L
  one_smul L := by
    ext x
    change x ∈ Formalism.HermitianLatticesTheory.gmap (1 : V ≃ₗ[K] V) L ↔ _
    simp [Formalism.HermitianLatticesTheory.gmap]
  mul_smul a b L := by
    ext x
    change x ∈ Formalism.HermitianLatticesTheory.gmap ((a : V ≃ₗ[K] V) * (b : V ≃ₗ[K] V)) L ↔
      x ∈ Formalism.HermitianLatticesTheory.gmap (a : V ≃ₗ[K] V) (Formalism.HermitianLatticesTheory.gmap (b : V ≃ₗ[K] V) L)
    simp [Formalism.HermitianLatticesTheory.gmap]
def gaG (h : V →ₗ⋆[K] V →ₗ[K] K) (A B : Submodule R V) : Subgroup (Formalism.HermitianLatticesTheory.isom h) where
  carrier := {γ | (∀ x, (γ : V ≃ₗ[K] V) x ∈ A ↔ x ∈ A) ∧ (∀ x, (γ : V ≃ₗ[K] V) x ∈ B ↔ x ∈ B) ∧
    ∀ x ∈ A, (γ : V ≃ₗ[K] V) x - x ∈ B}
  one_mem' := ⟨fun _ => Iff.rfl, fun _ => Iff.rfl, fun x _ => by simp⟩
  mul_mem' := by
    rintro a b ⟨a1, a2, a3⟩ ⟨b1, b2, b3⟩
    refine ⟨fun x => (a1 _).trans (b1 x), fun x => (a2 _).trans (b2 x), fun x hx => ?_⟩
    have e : ((a * b : Formalism.HermitianLatticesTheory.isom h) : V ≃ₗ[K] V) x - x =
        ((a : V ≃ₗ[K] V) ((b : V ≃ₗ[K] V) x) - (b : V ≃ₗ[K] V) x) + ((b : V ≃ₗ[K] V) x - x) := by
      simp
    rw [e]
    exact B.add_mem (a3 _ ((b1 x).2 hx)) (b3 x hx)
  inv_mem' := by
    rintro a ⟨a1, a2, a3⟩
    have e : ∀ x, (a : V ≃ₗ[K] V) (((a⁻¹ : Formalism.HermitianLatticesTheory.isom h) : V ≃ₗ[K] V) x) = x := fun x => by
      simp
    refine ⟨fun x => ?_, fun x => ?_, fun x hx => ?_⟩
    · rw [← a1, e]
    · rw [← a2, e]
    · have hy : ((a⁻¹ : Formalism.HermitianLatticesTheory.isom h) : V ≃ₗ[K] V) x ∈ A := by rw [← a1, e]; exact hx
      have := a3 _ hy
      rw [e] at this
      simpa using B.neg_mem this
def lieL (h : V →ₗ⋆[K] V →ₗ[K] K) (A B : Submodule R V) : AddSubgroup (V →ₗ[K] V) where
  carrier := {X | (∀ x y, h (X x) y + h x (X y) = 0) ∧ ∀ x ∈ A, X x ∈ B}
  zero_mem' := ⟨fun x y => by simp, fun x _ => by simp⟩
  add_mem' := by
    rintro X Y ⟨h1, h2⟩ ⟨k1, k2⟩
    refine ⟨fun x y => ?_, fun x hx => B.add_mem (h2 x hx) (k2 x hx)⟩
    have a := h1 x y
    have b := k1 x y
    simp only [LinearMap.add_apply, map_add]
    linear_combination a + b
  neg_mem' := by
    rintro X ⟨h1, h2⟩
    refine ⟨fun x y => ?_, fun x hx => B.neg_mem (h2 x hx)⟩
    have a := h1 x y
    simp only [LinearMap.neg_apply, map_neg]
    linear_combination -a
def primeTo (d : R) : Submonoid R where
  carrier := {s | ∀ P : Ideal R, P.IsMaximal → d ∈ P → s ∉ P}
  one_mem' := fun P hP _ h1 => hP.ne_top ((Ideal.eq_top_iff_one P).2 h1)
  mul_mem' := fun ha hb P hP hd hab =>
    (hP.isPrime.mem_or_mem hab).elim (ha P hP hd) (hb P hP hd)
def locD {W : Type*} [AddCommGroup W] [Module R W] (d : R) (L : Submodule R W) : Submodule R W :=
  Formalism.HermitianLatticesTheory.locS (primeTo d) L
def scl {W : Type*} [AddCommGroup W] [Module R W] (c : R) (L : Submodule R W) : Submodule R W :=
  L.map (LinearMap.lsmul R W c)
def gaD (h : V →ₗ⋆[K] V →ₗ[K] K) (d c : R) (M : Submodule R V) : Subgroup (Formalism.HermitianLatticesTheory.isom h) :=
  gaG h (locD d (Formalism.HermitianLatticesTheory.dual h M)) (scl c (locD d M))
def stabD (h : V →ₗ⋆[K] V →ₗ[K] K) (d : R) (M : Submodule R V) : Subgroup (Formalism.HermitianLatticesTheory.isom h) :=
  MulAction.stabilizer (Formalism.HermitianLatticesTheory.isom h) (locD d M)
def agreeD (h : V →ₗ⋆[K] V →ₗ[K] K) (d : R) (M : Submodule R V) : Set (Submodule R V) :=
  {N | N ∈ Formalism.HermitianLatticesTheory.genus h M ∧ locD d N = locD d M}
def idxN {W : Type*} [AddCommGroup W] [Module R W] (A B : Submodule R W) : ℕ :=
  B.toAddSubgroup.relIndex A.toAddSubgroup
def discN (h : V →ₗ⋆[K] V →ₗ[K] K) (M : Submodule R V) : ℕ := idxN (Formalism.HermitianLatticesTheory.dual h M) M
def IsIntLat (h : V →ₗ⋆[K] V →ₗ[K] K) (M : Submodule R V) : Prop :=
  Submodule.IsLattice K M ∧ Formalism.HermitianLatticesTheory.IsIntegralLat h M
def IsMaxLat (h : V →ₗ⋆[K] V →ₗ[K] K) (M : Submodule R V) : Prop :=
  IsIntLat h M ∧ ∀ N : Submodule R V, IsIntLat h N → M ≤ N → N = M
def badP (h : V →ₗ⋆[K] V →ₗ[K] K) (M : Submodule R V) : Set (Ideal R) :=
  {P | P.IsMaximal ∧ ¬ Formalism.HermitianLatticesTheory.IsUnimodularAt h P M}
def hRes (h : V →ₗ⋆[K] V →ₗ[K] K) (U : Submodule K V) : U →ₗ⋆[K] U →ₗ[K] K := h.domRestrict₁₂ U U
def latIn (U : Submodule K V) (M : Submodule R V) : Submodule R U :=
  M.comap (U.subtype.restrictScalars R)
def perp (h : V →ₗ⋆[K] V →ₗ[K] K) (U : Submodule K V) : Submodule K V := ⨅ x ∈ U, LinearMap.ker (h x)
def latsDisc (h : V →ₗ⋆[K] V →ₗ[K] K) (n : ℕ) : Set (Submodule R V) :=
  {M | IsIntLat h M ∧ discN h M = n}
def primSp (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule R V) (j n : ℕ) : Set (Submodule K V) :=
  {U | Module.finrank K U = j ∧ discN (hRes h U) (latIn U L) = n}
end Act
def PD {K V : Type*} [Field K] [StarRing K] [AddCommGroup V] [Module K V] (h : V →ₗ⋆[K] V →ₗ[K] K) : Prop :=
  ∀ τ : K →+* ℂ, ∀ x : V, x ≠ 0 → 0 < (τ (h x x)).re
def qIn {K : Type*} [Field K] [NumberField K] (P : Ideal (𝓞 K)) : ℕ := Nat.sqrt (Ideal.absNorm P)
def lamMax {K V : Type*} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K) (M : Submodule (𝓞 K) V) : ℝ :=
  ∏ᶠ P ∈ badP h M, ((qIn P : ℝ) ^ Module.finrank K V - (-1) ^ Module.finrank K V) / ((qIn P : ℝ) + 1)
def ChartGen (A : Type) [CommRing A] [StarRing A] : Prop :=
  ∀ (j : ℕ) (S : Matrix (Fin j) (Fin j) A), Sᴴ = S → ∀ Q : Matrix (Fin j) (Fin j) A → Prop,
    (∀ (Y : Matrix (Fin j) (Fin j) A) (θ : A), θ + star θ = 1 → Formalism.HermitianLatticeCounting.LatticeSumBounds.Phi S Y = 0 →
      IsUnit (1 + θ • (S * Y)).det → Q Y) →
    (∀ Y Y', Q Y → Q Y' → Q (Y + Y' + Y * S * Y')) →
    ∀ Y, Formalism.HermitianLatticeCounting.LatticeSumBounds.Phi S Y = 0 → Q Y
end GlobalTheory.Mass


