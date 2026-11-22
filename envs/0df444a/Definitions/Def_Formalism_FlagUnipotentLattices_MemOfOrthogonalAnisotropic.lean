-- Prove2me | Definitions.Def_Formalism_FlagUnipotentLattices_MemOfOrthogonalAnisotropic
-- name    : Formalism_FlagUnipotentLattices_MemOfOrthogonalAnisotropic
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T17:27:57.059595+00:00
-- url     : https://prove2.me/theorems/bf8b7820-102e-45f4-86ef-e5e842e8cf87
-- title:
--   Mem Of Orthogonal Anisotropic
-- statement:
--   Definitions and structural lemmas for Mem Of Orthogonal Anisotropic, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MemOfOrthogonalAnisotropic.lean

import Mathlib
import Definitions.Def_Formalism_HyperbolicPlaceProducts_Statement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Matrix
namespace Formalism.HermitianLatticeCounting.S6
structure HermSpace (K : Type) [Field K] [StarRing K] (V : Type) [AddCommGroup V] [Module K V] where
  B : V →ₗ[K] V →ₗ⋆[K] K
  herm : ∀ x y : V, star (B x y) = B y x
  nondeg : ∀ x : V, (∀ y : V, B x y = 0) → x = 0
section Flags
variable {K : Type} [Field K] [StarRing K] {V : Type} [AddCommGroup V] [Module K V]
structure FlagD (H : HermSpace K V) (r : ℕ) where
  e : Fin (r + 1) → V
  T : K
  indep : LinearIndependent K (fun a : Fin r => e a.castSucc)
  iso : ∀ a b : Fin r, H.B (e a.castSucc) (e b.castSucc) = 0
  zperp : ∀ a : Fin r, H.B (e a.castSucc) (e (Fin.last r)) = 0
  zz : H.B (e (Fin.last r)) (e (Fin.last r)) = -T
  hT : T ≠ 0
namespace FlagD
variable {H : HermSpace K V} {r : ℕ} (F : FlagD H r)
def z : V := F.e (Fin.last r)
def Xa (a : ℕ) : Submodule K V :=
  Submodule.span K ((fun b : Fin r => F.e b.castSucc) '' {b | b.val < a})
def X : Submodule K V := F.Xa r
def Aniso : Prop :=
  ∀ w : V, (∀ a : Fin (r + 1), H.B (F.e a) w = 0) → H.B w w = 0 → w ∈ F.X
def HasLevel (x : V) (a : Fin r) (al : K) : Prop :=
  al ≠ 0 ∧ x - al • F.e a.castSucc ∈ F.Xa a.val
def LieN (Y : V →ₗ[K] V) : Prop :=
  (∀ x y : V, H.B (Y x) y + H.B x (Y y) = 0) ∧
  (∀ a : Fin r, Y (F.e a.castSucc) ∈ F.Xa a.val) ∧
  (∀ y : V, (∀ a : Fin r, H.B (F.e a.castSucc) y = 0) → Y y ∈ F.X)
def DPsi (Y : V →ₗ[K] V) (s : K) : Prop :=
  ∃ c : Fin r → K, ∑ a, c a = s ∧
    ∀ a : Fin r, Y (F.e a.succ) - c a • F.e a.castSucc ∈ F.Xa a.val
def InN (g : V →ₗ[K] V) : Prop :=
  (∀ x y : V, H.B (g x) (g y) = H.B x y) ∧ Function.Bijective g ∧
  (∀ a : Fin r, g (F.e a.castSucc) - F.e a.castSucc ∈ F.Xa a.val) ∧
  (∀ y : V, (∀ a : Fin r, H.B (F.e a.castSucc) y = 0) → g y - y ∈ F.X)
def PosDefAt (σ : K →+* ℂ) : Prop :=
  ∀ w : V, (∀ a : Fin (r + 1), H.B (F.e a) w = 0) → w ∉ F.X → 0 < (σ (H.B w w)).re
def SigOneAt (σ : K →+* ℂ) : Prop :=
  ∃ z₀ : V, (∀ a : Fin r, H.B (F.e a.castSucc) z₀ = 0) ∧ (σ (H.B z₀ z₀)).re < 0 ∧
    ∀ w : V, (∀ a : Fin r, H.B (F.e a.castSucc) w = 0) → H.B w z₀ = 0 → w ∉ F.X →
      0 < (σ (H.B w w)).re
end FlagD
variable {H : HermSpace K V} {r : ℕ}
def II (F F' : FlagD H r) : Submodule K V := F.X ⊓ F'.X
def Relevant (F F' : FlagD H r) : Prop :=
  ∀ Y : V →ₗ[K] V, F.LieN Y → F'.LieN Y → ∀ s s' : K, F.DPsi Y s → F'.DPsi Y s' →
    s + star s = s' + star s'
def Zhat (F F' : FlagD H r) : Matrix (Fin (r + 1)) (Fin (r + 1)) K :=
  Matrix.of fun a b => H.B (F.e a) (F'.e b)
def Dl (F F' : FlagD H r) (l : ℕ) (hl : l ≤ r + 1) : K :=
  ((Zhat F F').submatrix (Fin.castLE hl) (Fin.castLE hl)).det
def Gval (F F' : FlagD H r) : K :=
  Dl F F' (r + 1) le_rfl * star (Dl F F' (r + 1) le_rfl) -
    F.T * F'.T * (Dl F F' r (Nat.le_succ r) * star (Dl F F' r (Nat.le_succ r)))
def Gram (F F' : FlagD H r) : Matrix (Fin (r + 1) ⊕ Fin (r + 1)) (Fin (r + 1) ⊕ Fin (r + 1)) K :=
  Matrix.of fun p q => H.B (Sum.elim F.e F'.e p) (Sum.elim F.e F'.e q)
def xv (H : HermSpace K V) (x v : V) : V →ₗ[K] V :=
  (H.B.flip v).smulRight x - (H.B.flip x).smulRight v
def V0 (F F' : FlagD H r) : Submodule K V :=
  F.X ⊔ F'.X ⊔ Submodule.span K {F.z, F'.z}
def SigPerp (F F' : FlagD H r) (σ : K →+* ℂ) : Prop :=
  ∃ z₀ : V, (∀ v ∈ F.X ⊔ F'.X, H.B v z₀ = 0) ∧ (σ (H.B z₀ z₀)).re < 0 ∧
    ∀ w : V, (∀ v ∈ F.X ⊔ F'.X, H.B v w = 0) → H.B w z₀ = 0 → w ≠ 0 → 0 < (σ (H.B w w)).re
def NFShape (F F' : FlagD H r) (j : ℕ) (c : K) : Prop :=
  c ≠ 0 ∧
  Module.finrank K (II F F') = r - j ∧
  (∀ x ∈ II F F', x ≠ 0 → ∃ (a : Fin r) (al al' : K),
    F.HasLevel x a al ∧ F'.HasLevel x a al' ∧ j ≤ a.val ∧ al = c * al') ∧
  (∀ a : Fin r, j ≤ a.val → ∃ x ∈ II F F', ∃ al al' : K, F.HasLevel x a al ∧ F'.HasLevel x a al') ∧
  II F F' ⊓ F.Xa j = ⊥ ∧ II F F' ⊓ F'.Xa j = ⊥ ∧
  F.X = F.Xa j ⊔ II F F' ∧ F'.X = F'.Xa j ⊔ II F F' ∧
  F'.z - c • F.z ∈ F.X ⊔ F'.X
def NFFull (F F' : FlagD H r) (j : ℕ) (hj : j ≤ r) (c : K) : Prop :=
  NFShape F F' j c ∧
  c * star c * F.T = F'.T ∧
  Dl F F' j (hj.trans (Nat.le_succ r)) ≠ 0 ∧
  (∀ v ∈ V0 F F', (∀ w ∈ V0 F F', H.B v w = 0) ↔ v ∈ II F F') ∧
  Module.finrank K (V0 F F') = r + j + 1 ∧
  (∀ x ∈ F.X, (∀ w ∈ V0 F F', H.B w x = 0) ↔ x ∈ II F F') ∧
  (∀ x ∈ F'.X, (∀ w ∈ V0 F F', H.B w x = 0) ↔ x ∈ II F F') ∧
  (∀ w : V, (∀ a : Fin (r + 1), H.B (F.e a) w = 0) → ∃ x ∈ F.X, ∀ v ∈ V0 F F', H.B v (w - x) = 0) ∧
  (∀ w : V, (∀ a : Fin (r + 1), H.B (F'.e a) w = 0) → ∃ x ∈ F'.X, ∀ v ∈ V0 F F', H.B v (w - x) = 0)
def eich (H : HermSpace K V) (x v : V) (c : K) : V →ₗ[K] V :=
  LinearMap.id + xv H x v + c • (H.B.flip x).smulRight x
def IsLift (F F' : FlagD H r) (Wt : Submodule K V) : Prop :=
  (∀ w ∈ Wt, ∀ y ∈ V0 F F', H.B y w = 0) ∧ Wt ⊓ II F F' = ⊥ ∧
  ∀ w : V, (∀ y ∈ V0 F F', H.B y w = 0) → w ∈ Wt ⊔ II F F'
end Flags
def LemmaG : Prop :=
  ∀ (K V : Type) [Field K] [StarRing K] [AddCommGroup V] [Module K V] (H : HermSpace K V) (r : ℕ)
    (F F' : FlagD H r), (Gram F F').det = (-1) ^ (r + 1) * Gval F F'
def WedgeMapNilpotent : Prop :=
  ∀ (K V : Type) [Field K] [StarRing K] [AddCommGroup V] [Module K V] (H : HermSpace K V) (x v : V),
    H.B x x = 0 → H.B x v = 0 →
      (∀ y y' : V, H.B (xv H x v y) y' + H.B y (xv H x v y') = 0) ∧
      (∀ y : V, xv H x v (xv H x v (xv H x v y)) = 0)
def Y1 : Prop :=
  ∀ (K V : Type) [Field K] [StarRing K] [AddCommGroup V] [Module K V] (H : HermSpace K V) (r : ℕ)
    (F : FlagD H r) (x v : V) (a : Fin r) (al : K),
    F.HasLevel x a al → (∀ b : Fin r, b ≤ a → H.B (F.e b.castSucc) v = 0) →
      (∀ y ∈ F.Xa (a.val + 1), xv H x v y = 0) ∧
      (∀ y : V, (∀ b : Fin r, H.B (F.e b.castSucc) y = 0) → xv H x v y ∈ K ∙ x) ∧
      F.LieN (xv H x v) ∧ F.DPsi (xv H x v) (al * H.B (F.e a.succ) v)
def LastVectorNotMemSup : Prop :=
  ∀ (K V : Type) [Field K] [StarRing K] [AddCommGroup V] [Module K V] (H : HermSpace K V) (r : ℕ)
    (F F' : FlagD H r), F.z ∉ F.X ⊔ F'.X
def EqZeroOfIsotropicAdd : Prop :=
  ∀ (K V : Type) [Field K] [StarRing K] [AddCommGroup V] [Module K V] (H : HermSpace K V) (r : ℕ)
    (F : FlagD H r) (x : V) (β : K), x ∈ F.X → H.B (x + β • F.z) (x + β • F.z) = 0 → β = 0
def MemOfOrthogonalAnisotropic : Prop :=
  ∀ (K V : Type) [Field K] [StarRing K] [AddCommGroup V] [Module K V] (H : HermSpace K V) (r : ℕ)
    (F F' : FlagD H r), F.Aniso → ∀ y ∈ F'.X, (∀ a : Fin (r + 1), H.B (F.e a) y = 0) → y ∈ F.X
def PerpPerp : Prop :=
  ∀ (K V : Type) [Field K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (H : HermSpace K V) (S : Submodule K V) (w : V),
    (∀ v : V, (∀ s ∈ S, H.B s v = 0) → H.B w v = 0) → w ∈ S
def NFStep : Prop :=
  ∀ (K V : Type) [Field K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (H : HermSpace K V) (r : ℕ) (F F' : FlagD H r) (x : V) (a a' : Fin r) (al al' : K),
    (∃ μ : K, μ + star μ ≠ 0) → Relevant F F' → x ∈ II F F' → F.HasLevel x a al → F'.HasLevel x a' al' →
      al • F.e a.succ - al' • F'.e a'.succ ∈ F.Xa (a.val + 1) ⊔ F'.Xa (a'.val + 1)
def NFCaseA : Prop :=
  ∀ (K V : Type) [Field K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (H : HermSpace K V) (r : ℕ) (F F' : FlagD H r),
    (∃ μ : K, μ + star μ ≠ 0) → Relevant F F' → II F F' ≠ ⊥ →
      ∃ (j : ℕ) (c : K), j < r ∧ NFShape F F' j c
def NFCaseB : Prop :=
  ∀ (K V : Type) [Field K] [StarRing K] [AddCommGroup V] [Module K V] (H : HermSpace K V) (r : ℕ)
    (F F' : FlagD H r), Dl F F' r (Nat.le_succ r) ≠ 0 →
      ∃ x ∈ F.X, ∃ x' ∈ F'.X,
        (∀ w ∈ F.X ⊔ F'.X, H.B w (F.z - x) = 0) ∧ (∀ w ∈ F.X ⊔ F'.X, H.B w (F'.z - x') = 0) ∧
        H.B (F.z - x) (F.z - x) = -F.T ∧ H.B (F'.z - x') (F'.z - x') = -F'.T ∧
        Dl F F' (r + 1) le_rfl = Dl F F' r (Nat.le_succ r) * H.B (F.z - x) (F'.z - x') ∧
        Gval F F' = Dl F F' r (Nat.le_succ r) * star (Dl F F' r (Nat.le_succ r)) *
          (H.B (F.z - x) (F'.z - x') * star (H.B (F.z - x) (F'.z - x')) - F.T * F'.T)
def NFCaseC : Prop :=
  ∀ (K V : Type) [Field K] [StarRing K] [AddCommGroup V] [Module K V] (H : HermSpace K V) (r : ℕ)
    (F F' : FlagD H r), F.Aniso → F'.Aniso → II F F' = ⊥ → Dl F F' r (Nat.le_succ r) = 0 →
      Gval F F' = 0 → False
def NFDj : Prop :=
  ∀ (K V : Type) [Field K] [StarRing K] [AddCommGroup V] [Module K V] (H : HermSpace K V) (r : ℕ)
    (F F' : FlagD H r) (j : ℕ) (hj : j ≤ r) (c : K), F'.Aniso →
      II F F' ⊓ F.Xa j = ⊥ → F'.X = F'.Xa j ⊔ II F F' → F'.z - c • F.z ∈ F.X ⊔ F'.X →
      Dl F F' j (hj.trans (Nat.le_succ r)) ≠ 0
def NFAbsC : Prop :=
  ∀ (K V : Type) [Field K] [StarRing K] [AddCommGroup V] [Module K V] (H : HermSpace K V) (r : ℕ)
    (F F' : FlagD H r) (j : ℕ) (hj : j ≤ r) (c : K),
      F.X = F.Xa j ⊔ II F F' → F'.X = F'.Xa j ⊔ II F F' → F'.z - c • F.z ∈ F.X ⊔ F'.X →
      Dl F F' j (hj.trans (Nat.le_succ r)) ≠ 0 → c * star c * F.T = F'.T
def JointSpanRadical : Prop :=
  ∀ (K V : Type) [Field K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (H : HermSpace K V) (r : ℕ) (F F' : FlagD H r) (j : ℕ) (hj : j ≤ r) (c : K), F'.Aniso →
      II F F' ⊓ F.Xa j = ⊥ → II F F' ⊓ F'.Xa j = ⊥ →
      F.X = F.Xa j ⊔ II F F' → F'.X = F'.Xa j ⊔ II F F' → F'.z - c • F.z ∈ F.X ⊔ F'.X →
      Dl F F' j (hj.trans (Nat.le_succ r)) ≠ 0 →
        (∀ v ∈ V0 F F', (∀ w ∈ V0 F F', H.B v w = 0) ↔ v ∈ II F F') ∧
        Module.finrank K (V0 F F') = r + j + 1 ∧
        (∀ x ∈ F.X, (∀ w ∈ V0 F F', H.B w x = 0) ↔ x ∈ II F F')
def JointSpanComplement : Prop :=
  ∀ (K V : Type) [Field K] [StarRing K] [AddCommGroup V] [Module K V] (H : HermSpace K V) (r : ℕ)
    (F F' : FlagD H r) (j : ℕ) (hj : j ≤ r) (c : K),
      F'.X = F'.Xa j ⊔ II F F' → F'.z - c • F.z ∈ F.X ⊔ F'.X →
      Dl F F' j (hj.trans (Nat.le_succ r)) ≠ 0 →
        ∀ w : V, (∀ a : Fin (r + 1), H.B (F.e a) w = 0) →
          ∃ x ∈ F.X, ∀ v ∈ V0 F F', H.B v (w - x) = 0
def NFCUnique : Prop :=
  ∀ (K V : Type) [Field K] [StarRing K] [AddCommGroup V] [Module K V] (H : HermSpace K V) (r : ℕ)
    (F F' : FlagD H r) (c₁ c₂ : K),
      F'.z - c₁ • F.z ∈ F.X ⊔ F'.X → F'.z - c₂ • F.z ∈ F.X ⊔ F'.X → c₁ = c₂
def NFJZero : Prop :=
  ∀ (K V : Type) [Field K] [StarRing K] [AddCommGroup V] [Module K V] (H : HermSpace K V) (r : ℕ)
    (F F' : FlagD H r) (c : K), NFShape F F' 0 c →
      (∀ a : ℕ, F'.Xa a = F.Xa a) ∧
      (∀ a : Fin r, F'.e a.castSucc - c • F.e a.castSucc ∈ F.Xa a.val) ∧
      F'.z - c • F.z ∈ F.X
def NFStepAsm : Prop := WedgeMapNilpotent → Y1 → PerpPerp → NFStep
def NFCaseAAsm : Prop := NFStep → LastVectorNotMemSup → NFCaseA
def SigOne (U : Type) [AddCommGroup U] [Module ℂ U] (h : U →ₗ[ℂ] U →ₗ⋆[ℂ] ℂ) : Prop :=
  ∃ z₀ : U, (h z₀ z₀).re < 0 ∧ ∀ w : U, h w z₀ = 0 → w ≠ 0 → 0 < (h w w).re
def PosDefPerpNeg : Prop :=
  ∀ (U : Type) [AddCommGroup U] [Module ℂ U] (h : U →ₗ[ℂ] U →ₗ⋆[ℂ] ℂ),
    (∀ x y : U, star (h x y) = h y x) → SigOne U h →
      ∀ z : U, (h z z).re < 0 → ∀ w : U, h w z = 0 → w ≠ 0 → 0 < (h w w).re
def ReverseCS : Prop :=
  ∀ (U : Type) [AddCommGroup U] [Module ℂ U] (h : U →ₗ[ℂ] U →ₗ⋆[ℂ] ℂ),
    (∀ x y : U, star (h x y) = h y x) → SigOne U h →
      ∀ z z' : U, (h z z).re < 0 → (h z' z').re < 0 →
        (h z z).re * (h z' z').re ≤ Complex.normSq (h z z') ∧
        ((h z z).re * (h z' z').re = Complex.normSq (h z z') → ∃ c : ℂ, z' = c • z)
def SigOneK (K U : Type) [Field K] [StarRing K] [AddCommGroup U] [Module K U] (σ : K →+* ℂ)
    (h : U →ₗ[K] U →ₗ⋆[K] K) : Prop :=
  ∃ z₀ : U, (σ (h z₀ z₀)).re < 0 ∧ ∀ w : U, h w z₀ = 0 → w ≠ 0 → 0 < (σ (h w w)).re
def PosDefPerpNegK : Prop :=
  ∀ (K U : Type) [Field K] [StarRing K] [AddCommGroup U] [Module K U] (σ : K →+* ℂ)
    (h : U →ₗ[K] U →ₗ⋆[K] K), (∀ x : K, σ (star x) = star (σ x)) →
    (∀ x y : U, star (h x y) = h y x) → SigOneK K U σ h →
      ∀ z : U, (σ (h z z)).re < 0 → ∀ w : U, h w z = 0 → w ≠ 0 → 0 < (σ (h w w)).re
def ReverseCSK : Prop :=
  ∀ (K U : Type) [Field K] [StarRing K] [AddCommGroup U] [Module K U] (σ : K →+* ℂ)
    (h : U →ₗ[K] U →ₗ⋆[K] K), (∀ x : K, σ (star x) = star (σ x)) →
    (∀ x y : U, star (h x y) = h y x) → SigOneK K U σ h →
      ∀ z z' : U, (σ (h z z)).re < 0 → (σ (h z' z')).re < 0 →
        (σ (h z z)).re * (σ (h z' z')).re ≤ Complex.normSq (σ (h z z')) ∧
        (h z z * h z' z' = h z z' * star (h z z') → ∃ c : K, z' = c • z)
def WDefinite : Prop :=
  ∀ (K V : Type) [Field K] [StarRing K] [AddCommGroup V] [Module K V] (σ : K →+* ℂ)
    (H : HermSpace K V) (r : ℕ) (F : FlagD H r), (∀ x : K, σ (star x) = star (σ x)) →
    F.SigOneAt σ → 0 < (σ F.T).re → F.PosDefAt σ
def AnisoOfPosDef : Prop :=
  ∀ (K V : Type) [Field K] [StarRing K] [AddCommGroup V] [Module K V] (σ : K →+* ℂ)
    (H : HermSpace K V) (r : ℕ) (F : FlagD H r), F.PosDefAt σ → F.Aniso
def NFCaseBSig : Prop :=
  ∀ (K V : Type) [Field K] [StarRing K] [AddCommGroup V] [Module K V] (σ : K →+* ℂ)
    (H : HermSpace K V) (r : ℕ) (F F' : FlagD H r), 0 < (σ F.T).re → F.PosDefAt σ →
    Dl F F' r (Nat.le_succ r) ≠ 0 → SigPerp F F' σ
def NFCaseBConcl : Prop :=
  ∀ (K V : Type) [Field K] [StarRing K] [AddCommGroup V] [Module K V] (σ : K →+* ℂ)
    (H : HermSpace K V) (r : ℕ) (F F' : FlagD H r), (∀ x : K, σ (star x) = star (σ x)) →
    0 < (σ F.T).re → 0 < (σ F'.T).re → SigPerp F F' σ →
    Dl F F' r (Nat.le_succ r) ≠ 0 → Gval F F' = 0 →
      ∃ c : K, F'.z - c • F.z ∈ F.X ⊔ F'.X
def NFCaseBConclAsm : Prop := NFCaseB → ReverseCSK → NFCaseBConcl
def NormalForm : Prop :=
  ∀ (K V : Type) [Field K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (σ : K →+* ℂ) (H : HermSpace K V) (r : ℕ) (F F' : FlagD H r),
    (∀ x : K, σ (star x) = star (σ x)) → 0 < (σ F.T).re → 0 < (σ F'.T).re →
    F.PosDefAt σ → F'.PosDefAt σ → Relevant F F' → Gval F F' = 0 →
      ∃ (j : ℕ) (hj : j ≤ r) (c : K), NFFull F F' j hj c
def NormalFormAsm : Prop :=
  AnisoOfPosDef → NFCaseA → NFCaseBSig → NFCaseBConcl → NFCaseC → NFDj → NFAbsC → JointSpanRadical → JointSpanComplement →
    NormalForm
def AmpExpansion : Prop :=
  ∀ (K V : Type) [Field K] [StarRing K] [AddCommGroup V] [Module K V] (H : HermSpace K V) (r : ℕ)
    (F F' : FlagD H r) (j : ℕ) (hj : j ≤ r) (wt₁ wt₂ i i' : V) (al al' : Fin j → K),
    (∀ v ∈ F.X ⊔ F'.X, H.B v wt₁ = 0) → (∀ v ∈ F.X ⊔ F'.X, H.B v wt₂ = 0) →
    i ∈ II F F' → i' ∈ II F F' →
      H.B (wt₁ + ∑ a, al a • F.e (Fin.castLE (hj.trans (Nat.le_succ r)) a) + i)
          (wt₂ + ∑ b, al' b • F'.e (Fin.castLE (hj.trans (Nat.le_succ r)) b) + i') =
        H.B wt₁ wt₂ + ∑ a, ∑ b, al a * star (al' b) *
          H.B (F.e (Fin.castLE (hj.trans (Nat.le_succ r)) a)) (F'.e (Fin.castLE (hj.trans (Nat.le_succ r)) b))
def ExtPowerBound : Prop :=
  ∀ (j m : ℕ) (A A' : Matrix (Fin j) (Fin m) ℂ) (Z : Matrix (Fin j) (Fin j) ℂ),
    (∀ w₁ w₂ : Fin m → ℂ, ∑ i, ‖w₁ i‖ ^ 2 ≤ 1 → ∑ i, ‖w₂ i‖ ^ 2 ≤ 1 →
      ‖∑ a, ∑ b, (A *ᵥ w₁) a * Z a b * star ((A' *ᵥ w₂) b)‖ ≤ 2) →
    Real.sqrt ‖(A * Aᴴ).det‖ * Real.sqrt ‖(A' * A'ᴴ).det‖ * ‖Z.det‖ ≤ 2 ^ j
def GramGS : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℂ E] (m : ℕ) (u : Fin m → E),
    (Matrix.gram ℂ u).det = ∏ a, ((‖InnerProductSpace.gramSchmidt ℂ u a‖ ^ 2 : ℝ) : ℂ)
def HadamardMaj : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℂ E] (B : E →ₗ[ℂ] E →ₗ⋆[ℂ] ℂ),
    (∀ x y, ‖B x y‖ ≤ ‖x‖ * ‖y‖) → ∀ (m : ℕ) (u w : Fin m → E),
      ‖(Matrix.of fun a b => B (u a) (w b)).det‖ ≤ ∏ a, ‖InnerProductSpace.gramSchmidt ℂ u a‖ * ‖InnerProductSpace.gramSchmidt ℂ w a‖
def HadamardMajAsm : Prop := Formalism.SLP.SesqDet → GramGS → HadamardMaj
def InvEntryBound : Prop :=
  ∀ (j : ℕ) (A : Matrix (Fin j) (Fin j) ℂ) (β : ℝ), 0 ≤ β → (∀ a b, ‖A a b‖ ≤ β) → A.det ≠ 0 →
    ∀ a b, ‖A⁻¹ a b‖ ≤ (j.factorial : ℝ) * β ^ (j - 1) / ‖A.det‖
def AmGm : Prop :=
  ∀ p q wt : ℝ, 0 < wt → |p| * |q| ≤ (wt * p ^ 2 + q ^ 2 / wt) / 2
def PieceBound : Prop :=
  ∀ (r l : ℕ) (D S S' la la' H₁ : ℝ), 1 ≤ l → l ≤ r → 0 ≤ D → 1 ≤ S → 1 ≤ S' →
    D ≤ (S * S') ^ l → S ≤ 2 * la * H₁ → S' ≤ 2 * la' * H₁ → 1 ≤ la → 1 ≤ la' → 1 / 2 ≤ H₁ →
      (max 1 (D / (2 * H₁) ^ (2 * r))) ^ (1 / (r : ℝ)) ≤ la * la'
def ProdMaxInv : Prop :=
  ∀ (ι : Type) [Fintype ι] (x : ι → ℝ), (∀ v, 0 < x v) → 1 ≤ ∏ v, x v →
    ∏ v, max 1 (1 / x v) ≤ ∏ v, max 1 (x v)
def SgBound : Prop :=
  ∀ (r : ℕ) (D H₁ sg : ℝ), 1 / 2 ≤ H₁ → 1 ≤ sg → D / (2 * H₁) ^ (2 * r) ≤ sg →
    max 1 D ≤ (2 * H₁) ^ (2 * r) * sg
def ProdMaxSg : Prop :=
  ∀ (ι : Type) [Fintype ι] (r f : ℕ) (D sg : ι → ℝ) (H₁ Hh : ℝ), Fintype.card ι = f → 1 / 2 ≤ H₁ →
    (2 * H₁) ^ (2 * r * f) ≤ Hh → (∀ v, 1 ≤ sg v) → (∀ v, D v / (2 * H₁) ^ (2 * r) ≤ sg v) →
      ∏ v, max 1 (D v) ≤ Hh * ∏ v, sg v
def NormSgBound : Prop :=
  ∀ (ι : Type) [Fintype ι] (r f : ℕ) (D sg : ι → ℝ) (H₁ Hh : ℝ), Fintype.card ι = f → 1 / 2 ≤ H₁ →
    (2 * H₁) ^ (4 * r * f) ≤ Hh → (∀ v, 0 ≤ D v) → (∀ v, 1 ≤ sg v) →
    (∀ v, D v / (2 * H₁) ^ (2 * r) ≤ sg v) →
      ∏ v, D v ^ 2 ≤ Hh * ∏ v, sg v ^ 2
def PowHeightLe : Prop :=
  ∀ (C r f : ℕ) (b : ℝ), 2 ≤ b →
    (2 * b ^ (C * (2 * r + 2))) ^ (4 * r * f) ≤ b ^ (2 * (C + 1) * (2 * r + 2) ^ 2 * f)
def DeProdBound : Prop :=
  ∀ (ι κ : Type) [Fintype ι] [Fintype κ] (r f : ℕ) (x : κ → ι → ℝ) (De sg : ι → ℝ) (H₁ Hh : ℝ),
    Fintype.card ι = f → Fintype.card κ ≤ r → 1 / 2 ≤ H₁ → (2 * H₁) ^ (2 * r * f) ≤ Hh →
    (∀ l v, 0 < x l v) → (∀ l, 1 ≤ ∏ v, x l v) → (∀ v, 1 ≤ sg v) →
    (∀ l v, x l v / (2 * H₁) ^ (2 * r) ≤ sg v) →
    (∀ v, 0 ≤ De v) → (∀ v, ∃ l, De v ≤ max 1 (1 / x l v)) →
      ∏ v, De v ≤ (Hh * ∏ v, sg v) ^ r
def IndexIneq : Prop :=
  ∀ g' i' Bc Dbar : ℝ, 0 ≤ g' → 0 ≤ i' → 0 < Bc → g' * i' ≤ Dbar / Bc → i' ≤ Bc → g' * i' ^ 2 ≤ Dbar
def CfBound : Prop :=
  ∀ f x k : ℕ, 1 ≤ f → 1 ≤ x →
    ((2 * f : ℕ) : ℝ) ^ (Nat.primeFactorsList x).length * (x : ℝ) ^ k ≤
      (x : ℝ) ^ ((k : ℝ) + (1 + Real.logb 2 (2 * f)))
def SublatticeCount : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (M : Type) [AddCommGroup M]
    [Module (NumberField.RingOfIntegers E) M] [Module.Finite (NumberField.RingOfIntegers E) M]
    [Module.Projective (NumberField.RingOfIntegers E) M] (f x : ℕ),
    Module.finrank ℚ E = 2 * f → 1 ≤ x →
      {N : Submodule (NumberField.RingOfIntegers E) M | N.toAddSubgroup.index = x}.Finite ∧
      (({N : Submodule (NumberField.RingOfIntegers E) M | N.toAddSubgroup.index = x}.ncard : ℕ) : ℝ) ≤
        (x : ℝ) ^ ((Module.finrank (NumberField.RingOfIntegers E) M : ℝ) + (1 + Real.logb 2 (2 * f)))
def SublatticeCountAsm : Prop := Formalism.SLP.SubmoduleIndexCountO → CfBound → SublatticeCount
def LeSqrtOfDivSqGeOne : Prop :=
  ∀ b₁ Del Dbar : ℝ, 0 < b₁ → Dbar = Del / b₁ ^ 2 → 1 ≤ Dbar → b₁ ≤ Real.sqrt Del
def HomCount : Prop :=
  ∀ (R M Q : Type) [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup Q] [Module R Q] [Finite Q]
    (e : ℕ) (s : Fin e → M), Submodule.span R (Set.range s) = ⊤ →
      Finite (M →ₗ[R] Q) ∧ Nat.card (M →ₗ[R] Q) ≤ Nat.card Q ^ e
def EichlerIsom : Prop :=
  ∀ (K V : Type) [Field K] [StarRing K] [AddCommGroup V] [Module K V] (H : HermSpace K V) (x v : V)
    (c : K), H.B x x = 0 → H.B x v = 0 → c + star c = -H.B v v →
      (∀ y y' : V, H.B (eich H x v c y) (eich H x v c y') = H.B y y') ∧
      (∀ y : V, eich H x (-v) (star c) (eich H x v c y) = y) ∧
      (∀ y : V, eich H x v c (eich H x (-v) (star c) y) = y)
def EichlerInR : Prop :=
  ∀ (K V : Type) [Field K] [StarRing K] [AddCommGroup V] [Module K V] (H : HermSpace K V) (r : ℕ)
    (F F' : FlagD H r) (x v : V) (c : K),
    x ∈ II F F' → (∀ y ∈ V0 F F', H.B y v = 0) → c + star c = -H.B v v →
      (∀ y ∈ V0 F F', eich H x v c y = y) ∧ F.InN (eich H x v c) ∧ F'.InN (eich H x v c) ∧
      (∀ w : V, (∀ y ∈ V0 F F', H.B y w = 0) → eich H x v c w = w + H.B w v • x)
def LiftTransitive : Prop :=
  ∀ (K V : Type) [Field K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (H : HermSpace K V) (r : ℕ) (F F' : FlagD H r) (W₁ W₂ : Submodule K V),
    (∃ μ : K, μ + star μ ≠ 0) → F.Aniso → F'.Aniso → IsLift F F' W₁ → IsLift F F' W₂ →
      ∃ g : V →ₗ[K] V, F.InN g ∧ F'.InN g ∧ (∀ y ∈ V0 F F', g y = y) ∧ W₁.map g = W₂
def LiftTransitiveAsm : Prop := EichlerIsom → EichlerInR → LiftTransitive
def MarginBound : Prop :=
  ∀ (C r : ℕ) (Db NT Hh S : ℝ), 1 ≤ r → 1 ≤ Hh → 1 ≤ S → 0 ≤ Db → 0 ≤ NT →
    Db ≤ (Hh * S ^ 2) ^ r → NT ≤ Hh →
      (Db * NT) ^ (C * r ^ 3) ≤ Hh ^ (2 * C * r ^ 4) * S ^ (2 * C * r ^ 4)
def EtaOne : Prop :=
  ∀ (k : ℕ) (g' g'' i' i'' b' b'' D' D'' : ℝ), 0 ≤ g' → 0 ≤ i' → 0 ≤ i'' → 0 ≤ b' → 0 ≤ b'' →
    g' = g'' → g' * i' ^ 2 * b' ^ 2 ≤ D' → g'' * i'' ^ 2 * b'' ^ 2 ≤ D'' →
      g' ^ k * (i' * b' * i'' * b'') ^ k ≤ Real.sqrt (D' * D'') ^ k
def bEta {K U : Type} [Field K] [StarRing K] [AddCommGroup U] [Module K U]
    (h : U →ₗ[K] U →ₗ⋆[K] K) (η : U →ₗ[K] U) (x' x'' : U) : K := h x' (x'' - η x'')
def BDescends : Prop :=
  ∀ (K U : Type) [Field K] [StarRing K] [AddCommGroup U] [Module K U] (h : U →ₗ[K] U →ₗ⋆[K] K)
    (η : U →ₗ[K] U), (∀ x y : U, h (η x) (η y) = h x y) →
      ∀ x' x'' t' t'' : U, η t' = t' → η t'' = t'' → bEta h η (x' + t') (x'' + t'') = bEta h η x' x''
def BNondeg : Prop :=
  ∀ (K U : Type) [Field K] [StarRing K] [AddCommGroup U] [Module K U] [FiniteDimensional K U]
    (h : U →ₗ[K] U →ₗ⋆[K] K) (η : U →ₗ[K] U), (∀ x y : U, star (h x y) = h y x) →
    (∀ w : U, h w w = 0 → w = 0) → (∀ x y : U, h (η x) (η y) = h x y) →
      (∀ x'' : U, (∀ t : U, η t = t → h x'' t = 0) →
        (∀ x' : U, (∀ t : U, η t = t → h x' t = 0) → bEta h η x' x'' = 0) → x'' = 0) ∧
      (∀ x' : U, (∀ t : U, η t = t → h x' t = 0) →
        (∀ x'' : U, (∀ t : U, η t = t → h x'' t = 0) → bEta h η x' x'' = 0) → x' = 0)
def DetBBound : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℂ E] (η : E →ₗᵢ[ℂ] E) (s : ℕ)
    (u w : Fin s → E),
      ‖(Matrix.of fun a b => inner ℂ (w b - η (w b)) (u a)).det‖ ≤
        2 ^ s * Real.sqrt ‖(Matrix.gram ℂ u).det‖ * Real.sqrt ‖(Matrix.gram ℂ w).det‖
def DetBBoundAsm : Prop := Formalism.SLP.SesqDet → DetBBound
def DetBBoundK : Prop :=
  ∀ (K U : Type) [Field K] [StarRing K] [AddCommGroup U] [Module K U] (σ : K →+* ℂ)
    (h : U →ₗ[K] U →ₗ⋆[K] K) (η : U →ₗ[K] U), (∀ x : K, σ (star x) = star (σ x)) →
    (∀ x y : U, star (h x y) = h y x) → (∀ w : U, w ≠ 0 → 0 < (σ (h w w)).re) →
    (∀ x y : U, h (η x) (η y) = h x y) → ∀ (s : ℕ) (u w : Fin s → U),
      ‖σ (Matrix.of fun a b => bEta h η (u a) (w b)).det‖ ≤
        2 ^ s * Real.sqrt ‖σ (Matrix.of fun a b => h (u a) (u b)).det‖ *
          Real.sqrt ‖σ (Matrix.of fun a b => h (w a) (w b)).det‖
def DelMBound : Prop :=
  ∀ (s f : ℕ) (g NT g' g'' dM P' P'' Nb : ℝ), 0 < g → 0 ≤ NT → 0 ≤ dM → 0 < P' → 0 < P'' →
    0 ≤ g' → 0 ≤ g'' → g ^ (2 * s * f) ≤ Nb → Nb ≤ 4 ^ (s * f) * (P' * P'') →
    dM * P' = g' * NT → dM * P'' = g'' * NT →
      dM ≤ (2 / g) ^ (s * f) * NT * Real.sqrt (g' * g'')
def SCArith : Prop :=
  ∀ (k s : ℕ) (de NT Xi C lf : ℝ), 1 ≤ s → s < k → 1 ≤ de → 1 ≤ NT → 0 ≤ Xi → 0 ≤ C → 0 ≤ lf →
    Xi * de ^ (k - s) * (de * NT) ^ s * NT ^ ((1 : ℤ) - k) = Xi * (de / NT) ^ k * NT ^ (s + 1) ∧
    Xi * de ^ (k - s) * (de * NT) ^ s * NT ^ ((1 : ℤ) - k) ≤ Xi * (de / NT) ^ k * (de * NT) ^ (s + 1) ∧
    Xi * de ^ (k - s) * (de * NT) ^ s * NT ^ ((1 : ℤ) - k) * (de * NT) ^ (C * s + C * lf) ≤
      Xi * (de / NT) ^ k * (de * NT) ^ ((C + 2) * s + (C + 2) * lf)
def EtaNeOne : Prop :=
  ∀ (k s f : ℕ) (g NT de dM g' g'' i' i'' b' b'' D' D'' : ℝ), 0 < g → 0 < NT → 0 < de → 0 ≤ dM →
    0 ≤ g' → 0 ≤ g'' → 0 ≤ i' → 0 ≤ i'' → 0 ≤ b' → 0 ≤ b'' →
    dM ≤ (2 / g) ^ (s * f) * NT * Real.sqrt (g' * g'') →
    g' * i' ^ 2 * b' ^ 2 ≤ D' → g'' * i'' ^ 2 * b'' ^ 2 ≤ D'' →
      (de / NT) ^ k * (dM / de) ^ k * (i' * b' * i'' * b'') ^ k ≤
        (2 / g) ^ (s * k * f) * Real.sqrt (D' * D'') ^ k
def SEqK : Prop :=
  ∀ (k f : ℕ) (g NT g' g'' i' i'' b' b'' D' D'' : ℝ), 0 < g → 0 ≤ NT →
    0 ≤ g' → 0 ≤ g'' → 0 ≤ i' → 0 ≤ i'' → 0 ≤ b' → 0 ≤ b'' →
    1 ≤ (2 / g) ^ (k * f) * NT * Real.sqrt (g' * g'') →
    g' * i' ^ 2 * b' ^ 2 ≤ D' → g'' * i'' ^ 2 * b'' ^ 2 ≤ D'' →
      1 ≤ (2 / g) ^ (k * k * f) * NT ^ k * Real.sqrt (g' * g'') ^ k ∧
      (i' * b' * i'' * b'') ^ k ≤ (2 / g) ^ (k * k * f) * NT ^ k * Real.sqrt (D' * D'') ^ k
def minkowskiExp (N p : ℕ) : ℕ := ∑ i ∈ Finset.range (N + 1), N / (p ^ i * (p - 1))
def minkowskiM (N : ℕ) : ℕ := ∏ p ∈ (Finset.range (N + 2)).filter Nat.Prime, p ^ minkowskiExp N p
def MinkowskiBound : Prop :=
  ∀ (N : ℕ) (G : Subgroup (Matrix.GeneralLinearGroup (Fin N) ℤ)), Finite G →
    Nat.card G ∣ minkowskiM N
def MinkowskiDvdFactorial : Prop := ∀ N : ℕ, minkowskiM N ∣ (2 * N).factorial
def AutBound : Prop :=
  ∀ (s f : ℕ) (G : Subgroup (Matrix.GeneralLinearGroup (Fin (2 * s * f)) ℤ)), Finite G →
    (Nat.card G : ℝ) ≤ ((4 * s * f : ℕ) : ℝ) ^ (4 * s * f)
def AutBoundAsm : Prop := MinkowskiBound → MinkowskiDvdFactorial → AutBound
def ExpIdentity : Prop :=
  ∀ (k j : ℕ) (D : ℝ), 0 < D →
    D ^ ((k : ℝ) / 2) * D ^ (-(((k : ℝ) - 1 - j) / 2)) = D ^ (((j : ℝ) + 1) / 2)
def FinalSum : Prop :=
  ∀ C : ℝ, 1 ≤ C → ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ (k r f : ℕ) (b d : ℝ), 2 ≤ b → 1 ≤ f → 0 ≤ d →
    C₀ * ((2 * r + 2 : ℕ) : ℝ) ^ 6 * Real.log b ≤ (k : ℝ) * Real.log k →
      2 * d * (∑ j ∈ Finset.Icc 1 r,
          Real.exp (C * ((2 * r + 2 : ℕ) : ℝ) ^ 6 * f * Real.log b) * (C / k) ^ (j * (k - 1 - j) * f)) ^ 2 ≤
        d * Real.exp (-((k : ℝ) * f * Real.log k))
end Formalism.HermitianLatticeCounting.S6


