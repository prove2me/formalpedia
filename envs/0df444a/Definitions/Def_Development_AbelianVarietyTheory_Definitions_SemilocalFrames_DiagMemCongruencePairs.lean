-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_DiagMemCongruencePairs
-- name    : Development_AbelianVarietyTheory_Definitions_SemilocalFrames_DiagMemCongruencePairs
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:07:09.597083+00:00
-- url     : https://prove2.me/theorems/8ff1b450-a24e-4b53-9cb2-2e6bd32f3823
-- title:
--   Diag Mem Congruence Pairs
-- statement:
--   Definitions and structural lemmas for Diag Mem Congruence Pairs, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/SemilocalFrames/DiagMemCongruencePairs.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FrameLats
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsDifferentPair
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Matrix GlobalTheory.SgAlg
open scoped nonZeroDivisors
namespace GlobalTheory.SgGlob
variable {E : Type} [Field E] [NumberField E]
abbrev Lz (E : Type) [Field E] (m : ℕ) : Type := Submodule (𝓞 E) (Fin m → E) × (Fin m → E)
def zOf {n r : ℕ} (P : Matrix (Fin n) (Fin (r + 1)) E) : Fin n → E := fun i => P i (Fin.last r)
def spanX {n r : ℕ} (P : Matrix (Fin n) (Fin (r + 1)) E) : Submodule E (Fin n → E) :=
  LinearMap.range (eOf P).mulVecLin
def perpX (σ : E →+* E) {n r : ℕ} (J : Matrix (Fin n) (Fin n) E) (P : Matrix (Fin n) (Fin (r + 1)) E) :
    Submodule E (Fin n → E) := LinearMap.ker (cT σ (eOf P) * J).mulVecLin
def latIn {n : ℕ} (Λ : Submodule (𝓞 E) (Fin n → E)) (S : Submodule E (Fin n → E)) :
    Submodule (𝓞 E) (Fin n → E) := Λ ⊓ S.restrictScalars (𝓞 E)
def mulLat {n : ℕ} (g : ℕ) (Λ : Submodule (𝓞 E) (Fin n → E)) : Submodule (𝓞 E) (Fin n → E) :=
  Λ.map ((g : 𝓞 E) • LinearMap.id)
def IsRed (σ : E →+* E) {n m r : ℕ} (J : Matrix (Fin n) (Fin n) E) (Jb : Matrix (Fin m) (Fin m) E)
    (Λ : Submodule (𝓞 E) (Fin n → E)) (P : Matrix (Fin n) (Fin (r + 1)) E) (x : Lz E m)
    (al : Matrix (Fin m) (Fin n) E) : Prop :=
  (∀ v ∈ perpX σ J P, al *ᵥ v = 0 ↔ v ∈ spanX P) ∧
  (∀ y, ∃ v ∈ perpX σ J P, al *ᵥ v = y) ∧
  (∀ v ∈ perpX σ J P, ∀ w ∈ perpX σ J P, form σ Jb (al *ᵥ v) (al *ᵥ w) = form σ J v w) ∧
  (latIn Λ (perpX σ J P)).map (al.mulVecLin.restrictScalars (𝓞 E)) = x.1 ∧
  al *ᵥ zOf P = x.2
def ModIso (σ : E →+* E) {m : ℕ} (Jb : Matrix (Fin m) (Fin m) E) (g : ℕ)
    (L' L : Submodule (𝓞 E) (Fin m → E)) (Γ : Submodule (𝓞 E) ((Fin m → E) × (Fin m → E))) : Prop :=
  Γ ≤ L'.prod L ∧ (mulLat g L').prod (mulLat g L) ≤ Γ ∧
  (∀ y' ∈ L', ∃ y, (y', y) ∈ Γ) ∧ (∀ y ∈ L, ∃ y', (y', y) ∈ Γ) ∧
  (∀ y, ((0 : Fin m → E), y) ∈ Γ → y ∈ mulLat g L) ∧
  (∀ y', (y', (0 : Fin m → E)) ∈ Γ → y' ∈ mulLat g L') ∧
  ∀ p ∈ Γ, ∀ q ∈ Γ, ∃ t : 𝓞 E, form σ Jb p.1 q.1 - form σ Jb p.2 q.2 = (g : E) * algebraMap (𝓞 E) E t
def iotaOf (σ : E →+* E) {n m r : ℕ} (J : Matrix (Fin n) (Fin n) E) (g : ℕ)
    (Λ : Submodule (𝓞 E) (Fin n → E)) (P P' : Matrix (Fin n) (Fin (r + 1)) E)
    (al al' : Matrix (Fin m) (Fin n) E) : Submodule (𝓞 E) ((Fin m → E) × (Fin m → E)) :=
  ((latIn Λ (perpX σ J P')).prod (latIn Λ (perpX σ J P)) ⊓
      (mulLat g Λ ⊔ latIn Λ (spanX P)).comap (LinearMap.snd (𝓞 E) _ _ - LinearMap.fst (𝓞 E) _ _)).map
    ((al'.mulVecLin.restrictScalars (𝓞 E)).prodMap (al.mulVecLin.restrictScalars (𝓞 E)))
def IsRow (σ : E →+* E) {m : ℕ} (Jb : Matrix (Fin m) (Fin m) E) (g : ℕ) (x x' : Lz E m)
    (Γ : Submodule (𝓞 E) ((Fin m → E) × (Fin m → E))) : Prop :=
  ModIso σ Jb g x'.1 x.1 Γ ∧ (x'.2, x.2) ∈ Γ
def LzClass (σ : E →+* E) {m : ℕ} (Jb : Matrix (Fin m) (Fin m) E) (T : E) : Type :=
  Quot fun x y : LzSet σ Jb T => ∃ γ, IsoLz σ Jb γ x.1 y.1
def lzRep {σ : E →+* E} {m : ℕ} {Jb : Matrix (Fin m) (Fin m) E} {T : E} (c : LzClass σ Jb T) : Lz E m :=
  (Quot.out c).1
def Rows (σ : E →+* E) {m : ℕ} (Jb : Matrix (Fin m) (Fin m) E) (T T' : E) (g : ℕ) :
    Set (LzClass σ Jb T × LzClass σ Jb T' × Submodule (𝓞 E) ((Fin m → E) × (Fin m → E))) :=
  {ρ | IsRow σ Jb g (lzRep ρ.1) (lzRep ρ.2.1) ρ.2.2}
def autLz (σ : E →+* E) {m : ℕ} (Jb : Matrix (Fin m) (Fin m) E) (x : Lz E m) : ℕ∞ :=
  ENat.card {γ : Matrix (Fin m) (Fin m) E // IsoLz σ Jb γ x x}
def wt (σ : E →+* E) {m : ℕ} (Jb : Matrix (Fin m) (Fin m) E) (x x' : Lz E m) : ENNReal :=
  (ENat.toENNReal (autLz σ Jb x) * ENat.toENNReal (autLz σ Jb x'))⁻¹
abbrev Rig (E : Type) [Field E] [NumberField E] (n m r : ℕ) : Type :=
  Tri E n r × Matrix (Fin m) (Fin n) E × Matrix (Fin m) (Fin n) E
def RigConf (σ : E →+* E) {n m r : ℕ} (J : Matrix (Fin n) (Fin n) E) (Jb : Matrix (Fin m) (Fin m) E)
    (T T' : E) (g : ℕ) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (x x' : Lz E m)
    (Γ : Submodule (𝓞 E) ((Fin m → E) × (Fin m → E))) : Set (Rig E n m r) :=
  {c | c.1 ∈ GenConf σ J T T' g Z ∧ IsRed σ J Jb c.1.1 c.1.2.1 x c.2.1 ∧
    IsRed σ J Jb c.1.1 c.1.2.2 x' c.2.2 ∧ iotaOf σ J g c.1.1 c.1.2.1 c.1.2.2 c.2.1 c.2.2 = Γ}
def IsoRig (σ : E →+* E) {n m r : ℕ} (J : Matrix (Fin n) (Fin n) E) (γ : Matrix (Fin n) (Fin n) E)
    (c d : Rig E n m r) : Prop :=
  IsoTri σ J γ c.1 d.1 ∧ (∀ v ∈ perpX σ J c.1.2.1, d.2.1 *ᵥ (γ *ᵥ v) = c.2.1 *ᵥ v) ∧
    ∀ v ∈ perpX σ J c.1.2.2, d.2.2 *ᵥ (γ *ᵥ v) = c.2.2 *ᵥ v
def rigCount (σ : E →+* E) {n m r : ℕ} (J : Matrix (Fin n) (Fin n) E) (Jb : Matrix (Fin m) (Fin m) E)
    (T T' : E) (g : ℕ) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (x x' : Lz E m)
    (Γ : Submodule (𝓞 E) ((Fin m → E) × (Fin m → E))) : ℕ∞ :=
  ENat.card (Quot fun c d : RigConf σ J Jb T T' g Z x x' Γ => ∃ γ, IsoRig σ J γ c.1 d.1)
def rigSum (σ : E →+* E) {n m r : ℕ} (J : Matrix (Fin n) (Fin n) E) (Jb : Matrix (Fin m) (Fin m) E)
    (T T' : E) (g : ℕ) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) : ENNReal :=
  ∑' ρ : Rows σ Jb T T' g, wt σ Jb (lzRep ρ.1.1) (lzRep ρ.1.2.1) *
    ENat.toENNReal (rigCount σ J Jb T T' g Z (lzRep ρ.1.1) (lzRep ρ.1.2.1) ρ.1.2.2)
def UO (E : Type) [Field E] [NumberField E] (r : ℕ) : Set (Matrix (Fin (r + 1)) (Fin (r + 1)) E) :=
  {u | IsUp u ∧ ∀ a b : Fin (r + 1), a < b → u a b ∈ dInv E ((b : ℕ) - a)}
def congruencePairs (E : Type) [Field E] [NumberField E] (r g : ℕ) :
    Set (Matrix (Fin (r + 1)) (Fin (r + 1)) E × Matrix (Fin (r + 1)) (Fin (r + 1)) E) :=
  {p | p.1 ∈ UO E r ∧ p.2 ∈ UO E r ∧
    ∀ a b : Fin (r + 1), a < b → ∃ t ∈ dInv E ((b : ℕ) - a), p.1 a b - p.2 a b = (g : E) * t}
section Basic
variable {σ : E →+* E} {n m r : ℕ} {J : Matrix (Fin n) (Fin n) E} {Jb : Matrix (Fin m) (Fin m) E}
omit [NumberField E] in

theorem mem_perpX (P : Matrix (Fin n) (Fin (r + 1)) E) (v : Fin n → E) :
    v ∈ perpX σ J P ↔ (cT σ (eOf P) * J) *ᵥ v = 0 := Iff.rfl
omit [NumberField E] in

theorem mem_perpX_iff_form (P : Matrix (Fin n) (Fin (r + 1)) E) (v : Fin n → E) :
    v ∈ perpX σ J P ↔ ∀ a : Fin r, form σ J v (fun i => P i a.castSucc) = 0 := by
  rw [mem_perpX, ← Matrix.mulVec_mulVec, funext_iff]
  rfl
end Basic
section Iota
variable {σ : E →+* E} {n m r : ℕ} {J : Matrix (Fin n) (Fin n) E} {Jb : Matrix (Fin m) (Fin m) E}
end Iota
section Iso
variable {σ : E →+* E} {n m r : ℕ} {J : Matrix (Fin n) (Fin n) E} {Jb : Matrix (Fin m) (Fin m) E}
end Iso
section Unip
variable {n r : ℕ}
end Unip
section Examples
variable {σ : E →+* E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}
example (σ : E →+* E) (Λ : Submodule (𝓞 E) (Fin 3 → E)) :
    ∃ L, IsRed (r := 1) σ !![0, 1, 0; 1, 0, 0; 0, 0, -1] !![-1] Λ !![1, 0; 0, 0; 0, 1] (L, ![1])
      !![0, 0, 1] := by
  have hp (v : Fin 3 → E) : v ∈ perpX (r := 1) σ !![0, 1, 0; 1, 0, 0; 0, 0, -1] !![1, 0; 0, 0; 0, 1] ↔
      v 1 = 0 := by
    simp [mem_perpX_iff_form, form, dotProduct, Matrix.mulVec, Fin.sum_univ_three]
  refine ⟨_, fun v hv => ?_, fun y => ⟨![0, 0, y 0], (hp _).2 rfl, ?_⟩, fun v hv w hw => ?_, rfl, ?_⟩
  · rw [hp] at hv
    constructor
    · intro h
      have h2 : v 2 = 0 := by simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_three] using congrFun h 0
      refine ⟨![v 0], ?_⟩
      ext i
      fin_cases i <;> simp [eOf, Matrix.mulVec, dotProduct, hv, h2]
    · rintro ⟨c, rfl⟩
      ext i
      fin_cases i
      simp [eOf, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  · ext i
    fin_cases i
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  · rw [hp] at hv hw
    simp [form, Matrix.mulVec, dotProduct, Fin.sum_univ_three, hv, hw]
  · ext i
    fin_cases i
    simp [zOf, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
example (t : E) : (!![1, t; 0, 1] : Matrix (Fin (1 + 1)) (Fin (1 + 1)) E) ∈ UO E 1 ↔ t ∈ dInv E 1 := by
  refine ⟨fun h => h.2 0 1 (by decide), fun h => ⟨fun i j => ?_, fun a b hab => ?_⟩⟩
  · fin_cases i <;> fin_cases j <;> simp
  · fin_cases a <;> fin_cases b <;> first | exact h | exact absurd hab (by decide)
end Examples
end GlobalTheory.SgGlob


