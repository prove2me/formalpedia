-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_RoundDown
-- name    : Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_RoundDown
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T01:52:16.022828+00:00
-- url     : https://prove2.me/theorems/130fa80c-ae4d-4b98-ad35-d545f7fc1bd6
-- title:
--   Round Down
-- statement:
--   Definitions and structural lemmas for Round Down, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/RoundDown.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MapCSmulMulVec
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PowerSeries
namespace GlobalTheory.NB
namespace Fr
variable {l : ℕ} {O : Type} [CommRing O] (R : Fr l O)
def pt (k : ℕ) (τ : Fin R.e) : O⟦X⟧ := (R.φ ^ k) (X - C (R.ϖ τ))
def OrdGe (π : O⟦X⟧) (i : ℤ) (x : R.EE) : Prop :=
  ∃ (f g : O⟦X⟧) (a y : ℕ), (l : O⟦X⟧) ^ y ∈ Ideal.span {f, π} ∧ 0 ≤ (a : ℤ) + i ∧
    R.ι (f * π ^ a) * x = R.ι (π ^ ((a : ℤ) + i).toNat * g)
def ConstMod (π : O⟦X⟧) (i : ℤ) (x : R.EE) : Prop :=
  ∃ (y : ℕ) (c : O), R.OrdGe π i ((l : R.EE) ^ y * x - algebraMap O R.EE c)
def cst {r : ℕ} (a : Fin r → O) : Fin r → R.EE := fun k => algebraMap O R.EE (a k)
def γv {r : ℕ} : (Fin r → R.EE) →ₗ[O] (Fin r → R.EE) := R.γE.toLinearMap.compLeft (Fin r)
variable [IsDomain O]
def toD (_R : Fr l O) {r : ℕ} (a : Fin r → O) : Fin r → FractionRing O :=
  fun k => algebraMap O (FractionRing O) (a k)
def InLev {r : ℕ} (π : O⟦X⟧) (Fl : ℤ → Submodule (FractionRing O) (Fin r → FractionRing O))
    (g : Fin r → R.EE) : Prop :=
  ∃ (y N : ℕ) (u : Fin N → ℤ) (a : Fin N → Fin r → O) (x : Fin N → R.EE),
    (∀ t, R.toD (a t) ∈ Fl (u t) ∧ R.OrdGe π (-(u t)) (x t)) ∧
      (l ^ y : ℕ) • g = ∑ t, x t • R.cst (a t)
def InLevC {r : ℕ} (π : O⟦X⟧) (Fl : ℤ → Submodule (FractionRing O) (Fin r → FractionRing O))
    (g : Fin r → R.EE) : Prop :=
  ∃ (y : ℕ) (a : Fin r → O), R.InLev π Fl ((l ^ y : ℕ) • g - R.cst a)
end Fr
def roundUp {K V : Type} [Field K] [AddCommGroup V] [Module K V] (b : ℕ) (Cs : Submodule K V)
    (u : ℤ) : Submodule K V := if u ≤ 0 then ⊤ else if u ≤ b then Cs else ⊥
def roundDown {K V : Type} [Field K] [AddCommGroup V] [Module K V] (b : ℕ) (Fs : Submodule K V)
    (u : ℤ) : Submodule K V := if u ≤ -(b : ℤ) then ⊤ else if u ≤ 0 then Fs else ⊥
def winU (b S η : ℕ) : Set ℤ := Set.Icc (b : ℤ) (b + S) ∪ Set.Icc (-(η : ℤ)) η
def winD (b S η : ℕ) : Set ℤ := Set.Icc (-((b : ℤ) + S)) (-(b : ℤ)) ∪ Set.Icc (-(η : ℤ)) η
def win (up : Bool) (b S η : ℕ) : Set ℤ := if up then winU b S η else winD b S η
def IsCuts {n : ℕ} (cut : ZMod n → Prop) (len : ZMod n → ℕ) : Prop :=
  (∃ c, cut c) ∧ ∀ c, cut c → 1 ≤ len c ∧ len c ≤ n ∧ cut (c - (len c : ZMod n)) ∧
    ∀ k, 0 < k → k < len c → ¬ cut (c - (k : ZMod n))
namespace Fr
variable {l : ℕ} {O : Type} [CommRing O] (R : Fr l O)
def Star (j : ℕ) (f : O⟦X⟧) (g : ℕ) : Prop :=
  ∀ y, 1 ≤ y → InId ((l : O) ^ eF l y) f ((l : O⟦X⟧) ^ g * (R.φ ^ j) X ^ y)
def IsMon (j : ℕ) (f : O⟦X⟧) : Prop := ∃ (m : ℕ) (a : ℕ → ℕ), f = X ^ m * R.pp j a
end Fr
namespace Sys
variable {l : ℕ} {O : Type} [CommRing O] {R : Fr l O} {n r : ℕ} (S : Sys R n r)
def IsFrame (i : ZMod n) (ρ k : ℕ) (H : Matrix (Fin r) (Fin r) O⟦X⟧) : Prop :=
  (∀ a b, X ∣ (H - (l : O⟦X⟧) ^ k • (1 : Matrix (Fin r) (Fin r) O⟦X⟧)) a b) ∧
    ∀ a b, X ^ ρ ∣ (S.G i * H.map R.γ - H) a b
def Coord (c' : ZMod n) (m : ℕ) (f : O⟦X⟧) (x g : Fin r → R.EE) : Prop :=
  ∃ (ρ k y : ℕ) (H : Matrix (Fin r) (Fin r) O⟦X⟧), S.IsFrame c' ρ k H ∧
    InMul f (R.N0 r) (((R.φ ^ m) X) ^ ρ • g) ∧
    InMul f (S.P c' m) ((l ^ y : ℕ) • ((l ^ k : ℕ) • x - ∑ j, g j • S.φit c' m (fun a => R.ι (H a j))))
variable [IsDomain O]
def FilArc (c' : ZMod n) (m s : ℕ) (τ : Fin R.e) (u : ℤ) :
    Submodule (FractionRing O) (Fin r → FractionRing O) :=
  (S.Fil (c' + ((m - s : ℕ) : ZMod n)) τ u).comap (S.φ0it c' (m - s)).mulVecLin
def InNN (c' : ZMod n) (m : ℕ) (g : Fin r → R.EE) : Prop :=
  ∀ s < m, ∀ τ, R.InLev (R.pt s τ) (S.FilArc c' m s τ) g
def Wid (i : ZMod n) (a b : ℕ) : Prop := ∀ τ, S.JumpsIn i τ (Set.Icc (-(a : ℤ)) b)
def Lat (c : ZMod n) (j : ℕ) : Submodule O (Fin r → FractionRing O) :=
  (D0 O r).map ((S.φ0it c j).mulVecLin.restrictScalars O)
end Sys
def ExtK {l : ℕ} {O : Type} [CommRing O] {R : Fr l O} {n r : ℕ} (S : Sys R n r)
    (K : ZMod n → O⟦X⟧ → Prop) : Prop :=
  ∀ (g : ℕ) (pr : Fin g → DD R n r × DD R n r), (∀ k, pr k ∈ S.Zf) →
    ∃ (Y : Sys R n (r + g)) (F : Hom S Y) (F' : Hom Y (Sys.one R n g)), F.IsSES F' ∧
      (∀ k, F.IsClassOf F' (Pi.single k 1) (pr k)) ∧ (∀ i f, K i f → F'.Kills i f) ∧
      ∀ i, ∃ a : ℕ, F'.Kills i ((l : O⟦X⟧) ^ a)
namespace Hom
variable {l : ℕ} {O : Type} [CommRing O] {R : Fr l O} {n r r' : ℕ} {S : Sys R n r} {S' : Sys R n r'}
  (F : Hom S S')
def F0 (i : ZMod n) : Matrix (Fin r') (Fin r) O := (F.F i).map constantCoeff
def Good : Prop := F.Onto ∧ ∀ i, ∃ a : ℕ, F.Kills i ((l : O⟦X⟧) ^ a)
def LiftsAt (c' : ZMod n) (m : ℕ) (Λ : O⟦X⟧) (e : ℕ) (g : Fin r' → R.EE) : Prop :=
  ∃ (w₁ : Fin r → R.EE) (v : Fin r' → R.EE), w₁ ∈ S.I (c' + (m : ZMod n)) ∧ Sys.Poles w₁ ∧
    Λ • v ∈ S'.P c' m ∧ S'.Coord c' m (X * Λ) v ((l ^ e : ℕ) • g) ∧
    Sys.InMul X (R.N0 r') (F.fl (c' + (m : ZMod n)) w₁ - v)
end Hom
end GlobalTheory.NB


