-- Prove2me | Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
-- name    : CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T09:29:04.140228+00:00
-- url     : https://prove2.me/theorems/1fc1f51e-7331-421d-a6c9-b0e0d1b20f13
-- title:
--   St Sandwich
-- statement:
--   Definitions and structural lemmas for St Sandwich, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/RealGroups/UnitaryAdmissibility/ArchimedeanUnitaryDual/StSandwich.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace CompanionTheory.Rg.FlB
section Defs
variable {L : Type} [NontriviallyNormedField L] {V : Type} [AddCommGroup V] [Module L V]
def IsInv (s : L →+* L) : Prop := (∀ x, s (s x) = x) ∧ (∀ x, ‖s x‖ = ‖x‖) ∧ ∃ x, s x ≠ x
def IsHerm (s : L →+* L) (h : V → V → L) : Prop :=
  (∀ x y z, h x (y + z) = h x y + h x z) ∧ (∀ (a : L) x y, h x (a • y) = a * h x y) ∧ (∀ x y, h y x = s (h x y)) ∧
    ∀ x, (∀ y, h x y = 0) → x = 0
def IsDelta (s : L →+* L) (δ : L) : Prop :=
  δ ≠ 0 ∧ (∀ a : L, (∀ x : L, ‖x‖ ≤ 1 → ‖a * x + s (a * x)‖ ≤ 1) ↔ ‖a‖ ≤ ‖δ‖) ∧ ∃ c : L, ‖c‖ ≤ 1 ∧ c * δ + s (c * δ) = 1
def IsLat (L : Type) [NontriviallyNormedField L] [Module L V] (Λ : AddSubgroup V) : Prop :=
  ∃ (m : ℕ) (b : Module.Basis (Fin m) L V), ∀ x, x ∈ Λ ↔ ∀ i, ‖b.repr x i‖ ≤ 1
def IsMax (h : V → V → L) (Λ : AddSubgroup V) : Prop :=
  IsLat L Λ ∧ (∀ x ∈ Λ, ‖h x x‖ ≤ 1) ∧ ∀ Λ' : AddSubgroup V, IsLat L Λ' → (∀ x ∈ Λ', ‖h x x‖ ≤ 1) → Λ ≤ Λ' → Λ' = Λ
def IsFrame (h : V → V → L) (δ : L) {l : ℕ} (e f : Fin l → V) (W : Submodule L V) : Prop :=
  (∀ i j, h (e i) (e j) = 0) ∧ (∀ i j, h (f i) (f j) = 0) ∧ (∀ i j, h (e i) (f j) = if i = j then δ else 0) ∧
    (∀ w ∈ W, ∀ i, h (e i) w = 0 ∧ h (f i) w = 0) ∧ (∀ w ∈ W, h w w = 0 → w = 0) ∧
    ∀ x, ∃ (a b : Fin l → L), ∃ w ∈ W, x = ∑ i, a i • e i + ∑ i, b i • f i + w
def IsAdapted (h : V → V → L) {l : ℕ} (e f : Fin l → V) (W : Submodule L V) (u : Fin l → L) (Λ : AddSubgroup V) : Prop :=
  ∀ (a b : Fin l → L), ∀ w ∈ W, (∑ i, a i • e i + ∑ i, b i • f i + w ∈ Λ ↔
    (∀ i, ‖a i‖ ≤ ‖u i‖) ∧ (∀ i, ‖b i‖ ≤ ‖u i‖⁻¹) ∧ ‖h w w‖ ≤ 1)
def IsIso (h : V → V → L) (g : V ≃ₗ[L] V) : Prop := ∀ x y, h (g x) (g y) = h x y
def IsCong (Λ : AddSubgroup V) (π : L) (g : V ≃ₗ[L] V) : Prop := ∀ x ∈ Λ, ∃ y ∈ Λ, g x - x = π • y
def IsTor (s : L →+* L) {l : ℕ} (e f : Fin l → V) (W : Submodule L V) (u : Fin l → L) (t : V ≃ₗ[L] V) : Prop :=
  (∀ i, t (e i) = u i • e i) ∧ (∀ i, t (f i) = (s (u i))⁻¹ • f i) ∧ ∀ w ∈ W, t w = w
end Defs
def ForAll (P : ∀ (L : Type) [NontriviallyNormedField L] (V : Type) [AddCommGroup V] [Module L V],
    (L →+* L) → L → (V → V → L) → Prop) : Prop :=
  ∀ (L : Type) [NontriviallyNormedField L] [IsUltrametricDist L] [ProperSpace L] [CharZero L] (s : L →+* L), IsInv s →
    ∀ δ : L, IsDelta s δ → ∀ (V : Type) [AddCommGroup V] [Module L V] [FiniteDimensional L V] (h : V → V → L),
      IsHerm s h → P L V s δ h
def StDelta : Prop :=
  ∀ (L : Type) [NontriviallyNormedField L] [IsUltrametricDist L] [ProperSpace L] [CharZero L] (s : L →+* L), IsInv s →
    ∃ δ, IsDelta s δ
def StHensel : Prop :=
  ∀ (L : Type) [NontriviallyNormedField L] [IsUltrametricDist L] [CompleteSpace L] (s : L →+* L), IsInv s →
    ∀ c d : L, s c = c → s d = d → ‖c‖ < 1 → ‖d‖ ≤ 1 → ∃ u, s u = u ∧ ‖u‖ ≤ 1 ∧ d + u + c * u ^ 2 = 0
def StSandwich : Prop :=
  ∀ (L : Type) [NontriviallyNormedField L] [IsUltrametricDist L] [ProperSpace L] (V : Type) [AddCommGroup V] [Module L V]
    (Λ₀ Λ : AddSubgroup V) (c : L), IsLat L Λ₀ → c ≠ 0 → (∀ x ∈ Λ, c • x ∈ Λ₀) → (∀ x : V, ∃ a : L, a ≠ 0 ∧ a • x ∈ Λ) →
    (∀ a : L, ‖a‖ ≤ 1 → ∀ x ∈ Λ, a • x ∈ Λ) → IsLat L Λ
def StAniso : Prop := ForAll fun _ _ V _ _ _ _ h => (∀ x, h x x = 0 → x = 0) →
  ∀ Λ : AddSubgroup V, IsMax h Λ → ∀ x, x ∈ Λ ↔ ‖h x x‖ ≤ 1
def StExists : Prop := ForAll fun _ _ V _ _ _ _ h => ∃ Λ : AddSubgroup V, IsMax h Λ
def StPairing : Prop := ForAll fun L _ V _ _ _ δ h => ∀ Λ : AddSubgroup V, IsMax h Λ →
  (∀ x ∈ Λ, ∀ y ∈ Λ, ‖h x y‖ ≤ ‖δ‖) ∧ ∀ p : L, ‖p‖ < 1 → (∀ a : L, ‖a‖ < 1 → ‖a‖ ≤ ‖p‖) →
    ∀ x ∈ Λ, p⁻¹ • x ∉ Λ → ‖h x x‖ ≤ ‖p‖ ^ 2 → ∃ y ∈ Λ, h x y = δ
def StPlane : Prop := ForAll fun L _ V _ _ s δ h => (∃ x, x ≠ 0 ∧ h x x = 0) →
  ∀ Λ Λ' : AddSubgroup V, IsMax h Λ → IsMax h Λ' → ∃ (e f : V) (u : L), u ≠ 0 ∧ h e e = 0 ∧ h f f = 0 ∧ h e f = δ ∧
    e ∈ Λ ∧ f ∈ Λ ∧ u • e ∈ Λ' ∧ (s u)⁻¹ • f ∈ Λ'
def StSplit : Prop := ForAll fun L _ V _ _ s δ h => ∀ (e f : V) (U : Submodule L V), h e e = 0 → h f f = 0 → h e f = δ →
  (∀ x, x ∈ U ↔ h e x = 0 ∧ h f x = 0) →
    IsHerm s (fun x y : U => h x y) ∧ (∀ x, ∃ (a b : L), ∃ w ∈ U, x = a • e + b • f + w) ∧ U ≠ ⊤ ∧
    ∀ Λ : AddSubgroup V, IsMax h Λ → e ∈ Λ → f ∈ Λ →
      IsMax (fun x y : U => h x y) (Λ.comap U.subtype.toAddMonoidHom) ∧
      ∀ (a b : L), ∀ w ∈ U, (a • e + b • f + w ∈ Λ ↔ ‖a‖ ≤ 1 ∧ ‖b‖ ≤ 1 ∧ w ∈ Λ)
def StFrame : Prop := ForAll fun L _ V _ _ _ δ h => ∀ Λ Λ' : AddSubgroup V, IsMax h Λ → IsMax h Λ' →
  ∃ (l : ℕ) (e f : Fin l → V) (W : Submodule L V) (u : Fin l → L), (∀ i, u i ≠ 0) ∧ IsFrame h δ e f W ∧
    IsAdapted h e f W (fun _ => 1) Λ ∧ IsAdapted h e f W u Λ'
def StWitt : Prop := ForAll fun L _ V _ _ _ δ h => ∀ (l l' : ℕ) (e f : Fin l → V) (W : Submodule L V)
  (e' f' : Fin l' → V) (W' : Submodule L V), IsFrame h δ e f W → IsFrame h δ e' f' W' →
    ∃ (q : Fin l ≃ Fin l') (g : V ≃ₗ[L] V), IsIso h g ∧ (∀ i, g (e i) = e' (q i)) ∧ (∀ i, g (f i) = f' (q i)) ∧
      ∀ w, w ∈ W ↔ g w ∈ W'
def StTor : Prop := ForAll fun L _ V _ _ s δ h => ∀ (l : ℕ) (e f : Fin l → V) (W : Submodule L V), IsFrame h δ e f W →
  ∀ u : Fin l → L, (∀ i, u i ≠ 0) → ∃ t : V ≃ₗ[L] V, IsIso h t ∧ IsTor s e f W u t ∧
    ∀ t', IsTor s e f W u t' → t' = t
def StDecomp : Prop := ForAll fun L _ V _ _ s δ h => ∀ (l : ℕ) (e f : Fin l → V) (W : Submodule L V) (Λ : AddSubgroup V),
  IsFrame h δ e f W → IsMax h Λ → IsAdapted h e f W (fun _ => 1) Λ → ∀ p : L, p ≠ 0 → ‖p‖ < 1 →
    (∀ a : L, ‖a‖ < 1 → ‖a‖ ≤ ‖p‖) → ∀ g : V ≃ₗ[L] V, IsIso h g →
    ∃ (k t k' : V ≃ₗ[L] V) (r : Fin l → ℕ), Antitone r ∧ IsIso h k ∧ IsIso h k' ∧ (∀ x, k x ∈ Λ ↔ x ∈ Λ) ∧
      (∀ x, k' x ∈ Λ ↔ x ∈ Λ) ∧ IsTor s e f W (fun i => p ^ r i) t ∧ g = k * t * k'
def StIwahori : Prop := ForAll fun L _ V _ _ s δ h => ∀ (l : ℕ) (e f : Fin l → V) (W : Submodule L V) (Λ : AddSubgroup V),
  IsFrame h δ e f W → IsLat L Λ → IsAdapted h e f W (fun _ => 1) Λ → ∀ π : L, ‖π‖ < 1 → ∀ k : V ≃ₗ[L] V, IsIso h k →
    IsCong Λ π k → ∃ a b : V ≃ₗ[L] V, IsIso h a ∧ IsIso h b ∧ k = a * b ∧
      ∀ (u : Fin l → L) (t : V ≃ₗ[L] V), (∀ i, u i ≠ 0) → (Monotone fun i => ‖u i‖) → (∀ i, ‖u i‖ ≤ 1) →
        IsTor s e f W u t → IsCong Λ π (t * a * t⁻¹) ∧ IsCong Λ π (t⁻¹ * b * t)
end CompanionTheory.Rg.FlB
end


