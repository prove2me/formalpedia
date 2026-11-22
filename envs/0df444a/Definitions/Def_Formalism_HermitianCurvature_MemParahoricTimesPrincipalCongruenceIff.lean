-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
-- name    : Formalism_HermitianCurvature_MemParahoricTimesPrincipalCongruenceIff
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:14:53.24782+00:00
-- url     : https://prove2.me/theorems/df733f6d-09aa-4a2b-aea2-f2f953bb2ba8
-- title:
--   Mem Parahoric Times Principal Congruence Iff
-- statement:
--   Definitions and structural lemmas for Mem Parahoric Times Principal Congruence Iff, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/MemParahoricTimesPrincipalCongruenceIff.lean

import Definitions.Def_Formalism_DoubleCosetMeasures_Statement
import Definitions.Def_Formalism_HermitianCurvature_StatementK
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.FourierDecayAlt.S3
open Matrix Finset MeasureTheory
open Formalism.DoubleCosetMeasures (IsUpUni IsLowUni upUniG)
open scoped ENNReal
abbrev Mid (k : ℕ) : Type := Fin k ⊕ Unit
abbrev Idx (r k : ℕ) : Type := Fin r ⊕ Mid k ⊕ Fin r
section Blocks
variable {A : Type} {r k : ℕ}
def b11 (x : Matrix (Idx r k) (Idx r k) A) : Matrix (Fin r) (Fin r) A :=
  Matrix.of fun a b => x (Sum.inl a) (Sum.inl b)
def b12 (x : Matrix (Idx r k) (Idx r k) A) : Matrix (Fin r) (Mid k) A :=
  Matrix.of fun a b => x (Sum.inl a) (Sum.inr (Sum.inl b))
def b13 (x : Matrix (Idx r k) (Idx r k) A) : Matrix (Fin r) (Fin r) A :=
  Matrix.of fun a b => x (Sum.inl a) (Sum.inr (Sum.inr b))
def b21 (x : Matrix (Idx r k) (Idx r k) A) : Matrix (Mid k) (Fin r) A :=
  Matrix.of fun a b => x (Sum.inr (Sum.inl a)) (Sum.inl b)
def b22 (x : Matrix (Idx r k) (Idx r k) A) : Matrix (Mid k) (Mid k) A :=
  Matrix.of fun a b => x (Sum.inr (Sum.inl a)) (Sum.inr (Sum.inl b))
def b23 (x : Matrix (Idx r k) (Idx r k) A) : Matrix (Mid k) (Fin r) A :=
  Matrix.of fun a b => x (Sum.inr (Sum.inl a)) (Sum.inr (Sum.inr b))
def b31 (x : Matrix (Idx r k) (Idx r k) A) : Matrix (Fin r) (Fin r) A :=
  Matrix.of fun a b => x (Sum.inr (Sum.inr a)) (Sum.inl b)
def b32 (x : Matrix (Idx r k) (Idx r k) A) : Matrix (Fin r) (Mid k) A :=
  Matrix.of fun a b => x (Sum.inr (Sum.inr a)) (Sum.inr (Sum.inl b))
def b33 (x : Matrix (Idx r k) (Idx r k) A) : Matrix (Fin r) (Fin r) A :=
  Matrix.of fun a b => x (Sum.inr (Sum.inr a)) (Sum.inr (Sum.inr b))
variable [CommRing A]
def IsN (x : Matrix (Idx r k) (Idx r k) A) : Prop :=
  IsUpUni (b11 x) ∧ IsUpUni (b33 x) ∧ b22 x = 1 ∧ b21 x = 0 ∧ b31 x = 0 ∧ b32 x = 0
def midEmb (h : Matrix (Fin k) (Fin k) A) : Matrix (Mid k) (Mid k) A := Matrix.fromBlocks h 0 0 1
def hEmb (r : ℕ) (h : Matrix (Fin k) (Fin k) A) : Matrix (Idx r k) (Idx r k) A :=
  Matrix.fromBlocks 1 0 0 (Matrix.fromBlocks (midEmb h) 0 0 1)
def IsH (x : Matrix (Idx r k) (Idx r k) A) : Prop := ∃ h, IsUnit h.det ∧ x = hEmb r h
def IsUk (x : Matrix (Idx r k) (Idx r k) A) : Prop := ∃ u, IsUpUni u ∧ x = hEmb r u
def IsS (x : Matrix (Idx r k) (Idx r k) A) : Prop := ∃ n h, IsN n ∧ IsH h ∧ x = n * h
def IsNU (x : Matrix (Idx r k) (Idx r k) A) : Prop := ∃ n u, IsN n ∧ IsUk u ∧ x = n * u
def IsInertiaInfiniteCyclotomic (x : Matrix (Idx r k) (Idx r k) A) : Prop :=
  IsS x ∧ b11 x = 1 ∧ b33 x = 1 ∧ (∀ a, b12 x a (Sum.inr ()) = 0) ∧ ∀ b, b23 x (Sum.inr ()) b = 0
def IsSubgroupSet (P : Matrix (Idx r k) (Idx r k) A → Prop) : Prop :=
  ∃ B : Subgroup (GL (Idx r k) A), ∀ x, P x ↔ ∃ g ∈ B, (g : Matrix (Idx r k) (Idx r k) A) = x
end Blocks
def GroupsAreGroups : Prop :=
  ∀ (A : Type) [CommRing A] (r k : ℕ),
    IsSubgroupSet (IsN (A := A) (r := r) (k := k)) ∧ IsSubgroupSet (IsH (A := A) (r := r) (k := k)) ∧
    IsSubgroupSet (IsUk (A := A) (r := r) (k := k)) ∧ IsSubgroupSet (IsS (A := A) (r := r) (k := k)) ∧
    IsSubgroupSet (IsNU (A := A) (r := r) (k := k)) ∧ IsSubgroupSet (IsInertiaInfiniteCyclotomic (A := A) (r := r) (k := k))
def SExplicit : Prop :=
  ∀ (A : Type) [CommRing A] (r k : ℕ) (x : Matrix (Idx r k) (Idx r k) A),
    IsS x ↔ IsUpUni (b11 x) ∧ IsUpUni (b33 x) ∧ b21 x = 0 ∧ b31 x = 0 ∧ b32 x = 0 ∧
      ∃ h, IsUnit h.det ∧ b22 x = midEmb h
def NUExplicit : Prop :=
  ∀ (A : Type) [CommRing A] (r k : ℕ) (x : Matrix (Idx r k) (Idx r k) A),
    IsNU x ↔ IsUpUni (b11 x) ∧ IsUpUni (b33 x) ∧ b21 x = 0 ∧ b31 x = 0 ∧ b32 x = 0 ∧
      ∃ u, IsUpUni u ∧ b22 x = midEmb u
def CardN : Prop :=
  ∀ (K : Type) [Field K] [Fintype K] (r k : ℕ),
    Nat.card {x : Matrix (Idx r k) (Idx r k) K // IsN x} =
      Fintype.card K ^ (r * (r - 1) + 2 * r * (k + 1) + r ^ 2)
def CardS : Prop :=
  ∀ (K : Type) [Field K] [Fintype K] (r k : ℕ),
    Nat.card {x : Matrix (Idx r k) (Idx r k) K // IsS x} =
      Nat.card (GL (Fin k) K) * Nat.card {x : Matrix (Idx r k) (Idx r k) K // IsN x}
def CardNU : Prop :=
  ∀ (K : Type) [Field K] [Fintype K] (r k : ℕ),
    Nat.card {x : Matrix (Idx r k) (Idx r k) K // IsNU x} =
      Nat.card {x : Matrix (Idx r k) (Idx r k) K // IsN x} * Nat.card (upUniG K k)
def CardUk : Prop :=
  ∀ (K : Type) [Field K] [Fintype K] (k : ℕ),
    Nat.card (upUniG K k) = Fintype.card K ^ (k * (k - 1) / 2)
def GammaProduct : Prop :=
  ∀ (K : Type) [Field K] [Fintype K] (k : ℕ),
    Nat.card (GL (Fin k) K) = Nat.card (upUniG K k) * ∏ i ∈ Icc 1 k, (Fintype.card K ^ i - 1)
def StabiliserIndexFinite : Prop :=
  ∀ (K : Type) [Field K] [Fintype K] (r k : ℕ),
    Nat.card {x : Matrix (Idx r k) (Idx r k) K // IsS x} =
      Nat.card {x : Matrix (Idx r k) (Idx r k) K // IsInertiaInfiniteCyclotomic x} * Fintype.card K ^ (r * (r + 1))
noncomputable def red (o : Type) [CommRing o] [IsLocalRing o] (ι : Type) [Fintype ι] [DecidableEq ι] :
    GL ι o →* GL ι (IsLocalRing.ResidueField o) :=
  Matrix.GeneralLinearGroup.map (IsLocalRing.residue o)
structure Levels (o : Type) [CommRing o] [IsLocalRing o] (r k : ℕ) where

  Kpp : Subgroup (GL (Idx r k) o)

  Knat : Subgroup (GL (Idx r k) o)

  JH : Subgroup (GL (Fin k) o)
  mem_Kpp : ∀ x, x ∈ Kpp ↔
    IsNU (red o (Idx r k) x : Matrix (Idx r k) (Idx r k) (IsLocalRing.ResidueField o))
  mem_Knat : ∀ x, x ∈ Knat ↔
    IsS (red o (Idx r k) x : Matrix (Idx r k) (Idx r k) (IsLocalRing.ResidueField o))
  mem_JH : ∀ h, h ∈ JH ↔
    IsUpUni (red o (Fin k) h : Matrix (Fin k) (Fin k) (IsLocalRing.ResidueField o))
def LevelsExist : Prop :=
  ∀ (o : Type) [CommRing o] [IsLocalRing o] (r k : ℕ), Nonempty (Levels o r k)
def ReductionOnto : Prop :=
  ∀ (o : Type) [CommRing o] [IsLocalRing o] (ι : Type) [Fintype ι] [DecidableEq ι],
    Function.Surjective (red o ι)
def IndexKpp : Prop :=
  ∀ (o : Type) [CommRing o] [IsLocalRing o] [Finite (IsLocalRing.ResidueField o)] (r k : ℕ)
    (L : Levels o r k),
    L.Kpp.index * (Nat.card {x : Matrix (Idx r k) (Idx r k) (IsLocalRing.ResidueField o) // IsN x} *
        Nat.card (upUniG (IsLocalRing.ResidueField o) k)) =
      Nat.card (GL (Idx r k) (IsLocalRing.ResidueField o))
def IndexJH : Prop :=
  ∀ (o : Type) [CommRing o] [IsLocalRing o] [Finite (IsLocalRing.ResidueField o)] (r k : ℕ)
    (L : Levels o r k),
    L.JH.index * Nat.card (upUniG (IsLocalRing.ResidueField o) k) =
      Nat.card (GL (Fin k) (IsLocalRing.ResidueField o))
def IndexKnat : Prop :=
  ∀ (o : Type) [CommRing o] [IsLocalRing o] [Finite (IsLocalRing.ResidueField o)] (r k : ℕ)
    (L : Levels o r k),
    L.Knat.index * Nat.card {x : Matrix (Idx r k) (Idx r k) (IsLocalRing.ResidueField o) // IsS x} =
      Nat.card (GL (Idx r k) (IsLocalRing.ResidueField o)) ∧
    L.Kpp ≤ L.Knat ∧
    L.Kpp.relIndex L.Knat * Nat.card (upUniG (IsLocalRing.ResidueField o) k) =
      Nat.card (GL (Fin k) (IsLocalRing.ResidueField o))
def KnatProduct : Prop :=
  ∀ (o : Type) [CommRing o] [IsLocalRing o] (r k : ℕ) (L : Levels o r k) (x : GL (Idx r k) o),
    x ∈ L.Knat ↔ ∃ s κ : GL (Idx r k) o, IsS (s : Matrix (Idx r k) (Idx r k) o) ∧
      κ ∈ (red o (Idx r k)).ker ∧ x = s * κ
def KppProduct : Prop :=
  ∀ (o : Type) [CommRing o] [IsLocalRing o] (r k : ℕ) (L : Levels o r k) (x : GL (Idx r k) o),
    x ∈ L.Kpp ↔ ∃ (n κ : GL (Idx r k) o) (h : GL (Fin k) o),
      IsN (n : Matrix (Idx r k) (Idx r k) o) ∧ h ∈ L.JH ∧ κ ∈ (red o (Idx r k)).ker ∧
      (x : Matrix (Idx r k) (Idx r k) o) = n * hEmb r (h : Matrix (Fin k) (Fin k) o) * κ
def TypedArithmetic : Prop :=
  ∀ (o : Type) [CommRing o] [IsLocalRing o] [Finite (IsLocalRing.ResidueField o)] (r k : ℕ)
    (L : Levels o r k) (volK volKpp volKnat volKH volJH volNo : ℝ),
    0 < volKpp → 0 < volKnat → 0 < volJH → 0 < volNo →
    volK = L.Kpp.index * volKpp → volK = L.Knat.index * volKnat → volKH = L.JH.index * volJH →
    ∀ (cG cS cGLk cUk γ : ℝ),
      cG = Nat.card (GL (Idx r k) (IsLocalRing.ResidueField o)) →
      cS = Nat.card {x : Matrix (Idx r k) (Idx r k) (IsLocalRing.ResidueField o) // IsS x} →
      cGLk = Nat.card (GL (Fin k) (IsLocalRing.ResidueField o)) →
      cUk = Nat.card (upUniG (IsLocalRing.ResidueField o) k) → γ = cGLk / cUk →
      γ * cS / cG = γ ^ 2 / L.Kpp.index ∧
      volKnat / volK = cS / cG ∧
      (volKnat / (volNo * volKH) ^ 2) / (volK / (volNo * volKH) ^ 2) = cS / cG ∧
      (volKpp / volJH ^ 2) / (volK / volKH ^ 2) = γ ^ 2 / L.Kpp.index ∧
      γ * (volKnat / (volNo * volKH) ^ 2) = (volKpp / volJH ^ 2) / volNo ^ 2
def Integral (o : Type) [CommRing o] {k0 : Type} [Field k0] [Algebra o k0] {ι κ : Type}
    (x : Matrix ι κ k0) : Prop := ∃ y : Matrix ι κ o, y.map (algebraMap o k0) = x
def InGLo (o : Type) [CommRing o] {k0 : Type} [Field k0] [Algebra o k0] {ι : Type} [Fintype ι]
    [DecidableEq ι] (x : Matrix ι ι k0) : Prop :=
  ∃ y : Matrix ι ι o, IsUnit y.det ∧ y.map (algebraMap o k0) = x
def KppO {o : Type} [CommRing o] [IsLocalRing o] {r k : ℕ} (j : Matrix (Idx r k) (Idx r k) o) : Prop :=
  IsUnit j.det ∧ IsNU (j.map (IsLocalRing.residue o))
def IntegralProduct : Prop :=
  ∀ (o : Type) [CommRing o] [IsDomain o] [IsLocalRing o] (k0 : Type) [Field k0] [Algebra o k0]
    [IsFractionRing o k0] (r k : ℕ) (n : Matrix (Idx r k) (Idx r k) k0) (h : Matrix (Fin k) (Fin k) k0),
    IsN n → IsUnit h.det →
    (InGLo o (n * hEmb r h) ↔ InGLo o n ∧ InGLo o h) ∧
    (InGLo o (hEmb r h * n) ↔ InGLo o n ∧ InGLo o h) ∧
    ((∃ y : Matrix (Idx r k) (Idx r k) o, KppO y ∧ y.map (algebraMap o k0) = n * hEmb r h) ↔
      InGLo o n ∧ ∃ y : Matrix (Fin k) (Fin k) o, IsUnit y.det ∧
        IsUpUni (y.map (IsLocalRing.residue o)) ∧ y.map (algebraMap o k0) = h) ∧
    ((∃ y : Matrix (Idx r k) (Idx r k) o, KppO y ∧ y.map (algebraMap o k0) = hEmb r h * n) ↔
      InGLo o n ∧ ∃ y : Matrix (Fin k) (Fin k) o, IsUnit y.det ∧
        IsUpUni (y.map (IsLocalRing.residue o)) ∧ y.map (algebraMap o k0) = h)
noncomputable def densP (η : ℤ) (q : ℕ) (lo hi : ℤ) : ℝ :=
  ∏ i ∈ Finset.Icc lo hi, (1 - (η : ℝ) ^ i * (q : ℝ) ^ (-i))
def SplitFrameCount : Prop :=
  ∀ (K : Type) [Field K] [Fintype K] (n a : ℕ) (R : Matrix (Fin a) (Fin a) K),
    Nat.card {p : Matrix (Fin n) (Fin a) K × Matrix (Fin n) (Fin a) K //
        p.1.rank = a ∧ p.2.rank = a ∧ p.2ᵀ * p.1 = Rᵀ} =
      (∏ j ∈ range a, (Fintype.card K ^ n - Fintype.card K ^ j)) *
        Fintype.card K ^ ((n - a) * R.rank) *
        ∏ j ∈ range (a - R.rank), (Fintype.card K ^ (n - a) - Fintype.card K ^ j)
def SplitFrameDensity : Prop :=
  ∀ (K : Type) [Field K] [Fintype K] (n a : ℕ) (R : Matrix (Fin a) (Fin a) K),
    (Nat.card {p : Matrix (Fin n) (Fin a) K × Matrix (Fin n) (Fin a) K //
        p.1.rank = a ∧ p.2.rank = a ∧ p.2ᵀ * p.1 = Rᵀ} : ℝ) =
      (Fintype.card K : ℝ) ^ ((2 * n * a : ℤ) - a ^ 2) *
        densP 1 (Fintype.card K) ((n : ℤ) - a - ((a : ℤ) - R.rank) + 1) n
def SplitFrameTransitive : Prop :=
  ∀ (K : Type) [Field K] [Fintype K] (n a : ℕ) (X₁ X₂ Y₁ Y₂ : Matrix (Fin n) (Fin a) K),
    X₁.rank = a → X₂.rank = a → Y₁.rank = a → Y₂.rank = a → X₂ᵀ * X₁ = Y₂ᵀ * Y₁ →
    ∃ g : Matrix (Fin n) (Fin n) K, IsUnit g.det ∧ g * X₁ = Y₁ ∧ gᵀ * Y₂ = X₂
def fconj {K : Type} [Field K] (q : ℕ) {m n : Type} (X : Matrix m n K) : Matrix n m K :=
  (X.map (· ^ q))ᵀ
def UnitaryOrder : Prop :=
  ∀ (K : Type) [Field K] [Fintype K] (q b : ℕ) (J : Matrix (Fin b) (Fin b) K),
    Fintype.card K = q ^ 2 → fconj q J = J → IsUnit J.det →
    (Nat.card {g : Matrix (Fin b) (Fin b) K // fconj q g * J * g = J} : ℝ) =
      (q : ℝ) ^ (b ^ 2) * densP (-1) q 1 b
def WittHerm : Prop :=
  ∀ (K : Type) [Field K] [Fintype K] (q n a : ℕ) (J : Matrix (Fin n) (Fin n) K)
    (X Y : Matrix (Fin n) (Fin a) K),
    Fintype.card K = q ^ 2 → fconj q J = J → IsUnit J.det → X.rank = a → Y.rank = a →
    fconj q X * J * X = fconj q Y * J * Y →
    ∃ g : Matrix (Fin n) (Fin n) K, fconj q g * J * g = J ∧ g * X = Y
def HermFrameCount : Prop :=
  UnitaryOrder → WittHerm →
  ∀ (K : Type) [Field K] [Fintype K] (q n a : ℕ) (J : Matrix (Fin n) (Fin n) K)
    (T : Matrix (Fin a) (Fin a) K),
    Fintype.card K = q ^ 2 → fconj q J = J → IsUnit J.det → fconj q T = T →
    (Nat.card {X : Matrix (Fin n) (Fin a) K // X.rank = a ∧ fconj q X * J * X = T} : ℝ) =
      (q : ℝ) ^ ((2 * n * a : ℤ) - a ^ 2) *
        densP (-1) q ((n : ℤ) - a - ((a : ℤ) - T.rank) + 1) n
def DensCases : Prop :=
  ∀ (η : ℤ) (q k r c : ℕ),
    densP η q (((k + 2 * r + 1 : ℕ) : ℤ) - ((2 * r + 2 : ℕ) : ℤ) - c + 1) ((k + 2 * r + 1 : ℕ) : ℤ) =
      densP η q ((k : ℤ) - c) ((k + 2 * r + 1 : ℕ) : ℤ) ∧
    densP η q (((k + 2 * r + 1 : ℕ) : ℤ) - ((r + 1 : ℕ) : ℤ) - r + 1) ((k + 2 * r + 1 : ℕ) : ℤ) =
      densP η q ((k : ℤ) + 1) ((k + 2 * r + 1 : ℕ) : ℤ) ∧
    densP η q (((k + 2 * r + 1 : ℕ) : ℤ) - ((r + 1 : ℕ) : ℤ) - ((r + 1 : ℕ) : ℤ) + 1)
        ((k + 2 * r + 1 : ℕ) : ℤ) =
      densP η q (k : ℤ) ((k + 2 * r + 1 : ℕ) : ℤ)
def DensOrdinaryBound : Prop :=
  ∀ (η : ℤ) (q k r c l l' : ℕ), (η = 1 ∨ η = -1) → 2 ≤ q → 3 ≤ k → c ≤ 2 * r + 2 →
    (l = k ∨ l = k + 1) → (l' = k ∨ l' = k + 1) →
    densP η q ((k : ℤ) - c) ((k + 2 * r + 1 : ℕ) : ℤ) /
        (densP η q l ((k + 2 * r + 1 : ℕ) : ℤ) * densP η q l' ((k + 2 * r + 1 : ℕ) : ℤ)) ≤
      Real.exp (4 * (q : ℝ) ^ (-((k : ℤ) - 2 * r - 2)))
def DensTyped : Prop :=
  ∀ (g k r c : ℕ), 2 ≤ g →
    ((g : ℝ) ^ (-(2 * ((r : ℤ) + 1) * ((k : ℤ) - 1))) *
          densP 1 g ((k : ℤ) - c) ((k + 2 * r + 1 : ℕ) : ℤ)) *
        (g : ℝ) ^ (-(3 * ((r : ℤ) + 1) ^ 2)) /
        (densP 1 g ((k : ℤ) + 1) ((k + 2 * r + 1 : ℕ) : ℤ) *
          (g : ℝ) ^ (-(2 * ((k : ℤ) + 2 * r + 1) * ((r : ℤ) + 1) - ((r : ℤ) + 1) ^ 2))) =
      densP 1 g ((k : ℤ) - c) k ∧
    0 ≤ densP 1 g ((k : ℤ) - c) k ∧ densP 1 g ((k : ℤ) - c) k ≤ 1
def TypedUnitCheck : Prop :=
  ∀ (g : ℝ) (r : ℕ), 0 < g →
    1 / g ^ (-(3 * ((r : ℤ) + 1) ^ 2)) =
      g ^ (2 * (r : ℤ) * (r + 1)) / (g ^ (-((r : ℤ) * (r + 1))) * (g ^ (-3 : ℤ)) ^ (r + 1))
def PrimeTail : Prop :=
  ∀ (s N : ℕ), 2 ≤ s → ∑ l ∈ Icc 2 N, ((l : ℝ) ^ s)⁻¹ ≤ 3 * ((2 : ℝ) ^ s)⁻¹
def lead {A : Type} [CommRing A] {r : ℕ} (M : Matrix (Fin r) (Fin r) A) (l : ℕ) (hl : l ≤ r) : A :=
  (M.submatrix (Fin.castLE hl) (Fin.castLE hl)).det
def cm {A : Type} [CommRing A] {r : ℕ} (X : Matrix (Fin r) (Fin r) A) (l : ℕ) (hl : l ≤ r) : A :=
  (X.submatrix (fun i : Fin l => (Fin.castLE hl i).rev) (Fin.castLE hl)).det
def LDUExists : Prop :=
  ∀ (A : Type) [CommRing A] (r : ℕ) (M : Matrix (Fin r) (Fin r) A),
    (∀ (l : ℕ) (hl : l < r), IsUnit (lead M l hl.le)) →
    ∃ (L U : Matrix (Fin r) (Fin r) A) (d : Fin r → A), IsLowUni L ∧ IsUpUni U ∧
      M = L * Matrix.diagonal d * U ∧
      ∀ (l : ℕ) (hl : l < r), lead M (l + 1) hl = d ⟨l, hl⟩ * lead M l hl.le
def LDUUnique : Prop :=
  ∀ (A : Type) [CommRing A] (r : ℕ) (L U L' U' : Matrix (Fin r) (Fin r) A) (d d' : Fin r → A),
    IsLowUni L → IsUpUni U → IsLowUni L' → IsUpUni U' →
    (∀ (l : ℕ) (hl : l < r), IsUnit (lead (L * Matrix.diagonal d * U) l hl.le)) →
    lead (L * Matrix.diagonal d * U) r le_rfl ∈ nonZeroDivisors A →
    L * Matrix.diagonal d * U = L' * Matrix.diagonal d' * U' → L = L' ∧ d = d' ∧ U = U'
def LeadInvariant : Prop :=
  ∀ (A : Type) [CommRing A] (r : ℕ) (L M U : Matrix (Fin r) (Fin r) A), IsLowUni L → IsUpUni U →
    ∀ (l : ℕ) (hl : l ≤ r), lead (L * M * U) l hl = lead M l hl
def CornerInvariant : Prop :=
  ∀ (A : Type) [CommRing A] (r : ℕ) (v₂ X v₁ : Matrix (Fin r) (Fin r) A), IsUpUni v₂ → IsUpUni v₁ →
    ∀ (l : ℕ) (hl : l ≤ r), cm (v₂ * X * v₁) l hl = cm X l hl
def InOm {o : Type} [CommRing o] [IsLocalRing o] {r k : ℕ} (ϖ : o)
    (j : Matrix (Idx r k) (Idx r k) o) : Prop :=
  KppO j ∧ ∃ X : Matrix (Fin r) (Fin r) o, b31 j = ϖ • X ∧ ∀ (l : ℕ) (hl : l ≤ r), IsUnit (cm X l hl)
def InverseCorner : Prop :=
  ∀ (o : Type) [CommRing o] [IsDomain o] [IsDiscreteValuationRing o] (ϖ : o), Irreducible ϖ →
    ∀ (r k : ℕ) (j : Matrix (Idx r k) (Idx r k) o) (X : Matrix (Fin r) (Fin r) o),
      KppO j → b31 j = ϖ • X →
      ∃ Y : Matrix (Fin r) (Fin r) o, b31 j⁻¹ = ϖ • Y ∧
        ((b33 j) * Y * (b11 j)).map (IsLocalRing.residue o) = -(X.map (IsLocalRing.residue o)) ∧
        ∀ (l : ℕ) (hl : l ≤ r),
          IsLocalRing.residue o (cm Y l hl) = (-1) ^ l * IsLocalRing.residue o (cm X l hl)
def Forcing : Prop :=
  ∀ (o : Type) [CommRing o] [IsDomain o] [IsDiscreteValuationRing o] (k0 : Type) [Field k0]
    [Algebra o k0] [IsFractionRing o k0] (ϖ : o), Irreducible ϖ →
    ∀ (r k : ℕ) (j j' : Matrix (Idx r k) (Idx r k) o) (n n' : Matrix (Idx r k) (Idx r k) k0),
      InOm ϖ j → KppO j' → IsN n → IsN n' →
      n * j'.map (algebraMap o k0) = j.map (algebraMap o k0) * n' →
      Integral o n ∧ Integral o n' ∧ InOm ϖ j'
def CentreBlocks : Prop :=
  ∀ (F : Type) [Field F] (r : ℕ) (ϖ : F) (j₁₁ j₁₃ j₃₃ X S S' : Matrix (Fin r) (Fin r) F),
    ϖ ≠ 0 → IsUnit X.det →
    j₁₃ - S * j₃₃ + (j₁₁ - S * (ϖ • X)) * S' =
      j₁₃ + ϖ⁻¹ • ((j₁₁ - ϖ • (S * X)) * X⁻¹ * (j₃₃ + ϖ • (X * S')) - j₁₁ * X⁻¹ * j₃₃)
def CentreForcing : Prop :=
  ∀ (o : Type) [CommRing o] [IsDomain o] [IsDiscreteValuationRing o] (k0 : Type) [Field k0]
    [Algebra o k0] [IsFractionRing o k0] (ϖ : o), Irreducible ϖ →
    ∀ (r : ℕ) (ξ₁ ξ₂ j₁₃ X y₁ y₂ y₃ : Matrix (Fin r) (Fin r) o) (S S' : Matrix (Fin r) (Fin r) k0),
      IsUpUni (ξ₁.map (IsLocalRing.residue o)) → IsUpUni (ξ₂.map (IsLocalRing.residue o)) →
      (∀ (l : ℕ) (hl : l ≤ r), IsUnit (cm X l hl)) →
      IsUpUni (y₁.map (IsLocalRing.residue o)) → IsUpUni (y₂.map (IsLocalRing.residue o)) →
      y₁.map (algebraMap o k0) = ξ₁.map (algebraMap o k0) - S * (ϖ • X).map (algebraMap o k0) →
      y₂.map (algebraMap o k0) = ξ₂.map (algebraMap o k0) + (ϖ • X).map (algebraMap o k0) * S' →
      y₃.map (algebraMap o k0) = j₁₃.map (algebraMap o k0) - S * ξ₂.map (algebraMap o k0) +
        (ξ₁.map (algebraMap o k0) - S * (ϖ • X).map (algebraMap o k0)) * S' →
      Integral o S ∧ Integral o S'
def StabiliserTrivial : Prop :=
  ∀ (F : Type) [Field F] (r k : ℕ) (g n n' : Matrix (Idx r k) (Idx r k) F), IsUnit g.det →
    (∀ (l : ℕ) (hl : l ≤ r), cm (b31 g) l hl ≠ 0) → (∀ (l : ℕ) (hl : l ≤ r), cm (b31 g⁻¹) l hl ≠ 0) →
    IsN n → IsN n' → g * n' = n * g → n = 1 ∧ n' = 1
def CornerMinorsCount : Prop :=
  ∀ (K : Type) [Field K] [Fintype K] (r : ℕ),
    Nat.card {X : Matrix (Fin r) (Fin r) K // ∀ (l : ℕ) (hl : l ≤ r), cm X l hl ≠ 0} =
      Fintype.card K ^ (r ^ 2 - r) * (Fintype.card K - 1) ^ r
def UnitStratumCoset : Prop :=
  ∀ (o : Type) [CommRing o] [IsDomain o] [IsDiscreteValuationRing o] (ϖ : o), Irreducible ϖ →
    ∀ (r k : ℕ) (j₀ M : Matrix (Idx r k) (Idx r k) o) (X₀ : Matrix (Fin r) (Fin r) o),
      KppO j₀ → b31 j₀ = ϖ • X₀ →
      ∃ X : Matrix (Fin r) (Fin r) o, b31 (j₀ * (1 + ϖ • M)) = ϖ • X ∧
        X.map (IsLocalRing.residue o) = (X₀ + b33 j₀ * b31 M).map (IsLocalRing.residue o)
def UnitStratumShare : Prop :=
  ∀ (K : Type) [Field K] [Fintype K] (r k : ℕ) (X₀ u : Matrix (Fin r) (Fin r) K), IsUnit u.det →
    (Nat.card {M : Matrix (Idx r k) (Idx r k) K //
        ∀ (l : ℕ) (hl : l ≤ r), cm (X₀ + u * b31 M) l hl ≠ 0} : ℝ) =
      (1 - 1 / (Fintype.card K : ℝ)) ^ r * Nat.card (Matrix (Idx r k) (Idx r k) K)
def UnitStratumMass : Prop :=
  ∀ (volNo volJH volKpp volOm cUk c J : ℝ), 0 < volNo → 0 < volJH → 0 < volKpp → 0 < cUk →
    c = volNo * volJH / volKpp → J = c⁻¹ * volNo ^ 2 / volKpp →
    J = volNo / volJH ∧
    J ^ 2 * volOm / volNo ^ 2 = volKpp / volJH ^ 2 * (volOm / volKpp) ∧
    cUk * (volNo / volJH) ^ 2 * (volKpp / cUk) / volNo ^ 2 = volKpp / volJH ^ 2
noncomputable def ROrd (o : Type) [CommRing o] [IsLocalRing o] : Subring (o × o) :=
  RingHom.eqLocus ((IsLocalRing.residue o).comp (RingHom.fst o o))
    ((IsLocalRing.residue o).comp (RingHom.snd o o))
def ROrderUnits : Prop :=
  ∀ (o : Type) [CommRing o] [IsLocalRing o],
    (∀ x : ROrd o, IsUnit x ↔ IsLocalRing.residue o (x : o × o).1 ≠ 0) ∧
    Function.Surjective fun x : ROrd o => IsLocalRing.residue o (x : o × o).1
def ROrderSelfDual : Prop :=
  ∀ (o : Type) [CommRing o] [IsDomain o] [IsDiscreteValuationRing o] (k0 : Type) [Field k0]
    [Algebra o k0] [IsFractionRing o k0] (ϖ : o), Irreducible ϖ → ∀ a₁ a₂ : k0,
    (∀ b : ROrd o, ∃ y : o, algebraMap o k0 y =
        (a₁ * algebraMap o k0 (b : o × o).1 - a₂ * algebraMap o k0 (b : o × o).2) /
          algebraMap o k0 ϖ) ↔
      ∃ x : ROrd o, algebraMap o k0 (x : o × o).1 = a₁ ∧ algebraMap o k0 (x : o × o).2 = a₂
noncomputable def chainWeight {X : Type} (nrm : X → ℝ≥0∞) (i : ℕ) (c : Fin i → X) : ℝ≥0∞ :=
  ∏ l ∈ Finset.range i, ∏ j : Fin i, if (j : ℕ) < l then nrm (c j) ^ 2 else 1
def ChainStep {X : Type} [MeasurableSpace X] (μ : Measure X) (nrm : X → ℝ≥0∞)
    (Kk : (i : ℕ) → (Fin i → X) → ℝ≥0∞) : Prop :=
  ∀ (i : ℕ) (h : Fin i → X), (∀ l, nrm (h l) ≠ 0 ∧ nrm (h l) ≠ ⊤) →
    ∫⁻ c, Kk (i + 1) (Fin.snoc h c : Fin (i + 1) → X) ∂μ = ((∏ l, nrm (h l)) ^ 2)⁻¹ * Kk i h
def ChainIdentity : Prop :=
  ∀ (X : Type) [MeasurableSpace X] (μ : Measure X) [SigmaFinite μ] (nrm : X → ℝ≥0∞)
    (Kk : (i : ℕ) → (Fin i → X) → ℝ≥0∞),
    Measurable nrm → (∀ i, Measurable (Kk i)) → (∀ᵐ x ∂μ, nrm x ≠ 0 ∧ nrm x ≠ ⊤) →
    (∀ c, Kk 0 c = 1) → ChainStep μ nrm Kk →
    ∀ i, ∫⁻ c, Kk i c * chainWeight nrm i c ∂(Measure.pi fun _ : Fin i => μ) = 1
def UnitHeadsMass : Prop :=
  ∀ (X : Type) [MeasurableSpace X] (μ : Measure X) [SigmaFinite μ] (nrm : X → ℝ≥0∞)
    (Kk : (i : ℕ) → (Fin i → X) → ℝ≥0∞) (Rs Ru : Set X) (r : ℕ),
    MeasurableSet Rs → MeasurableSet Ru → (∀ x ∈ Ru, nrm x = 1) →
    (∀ᵐ x ∂μ, nrm x ≠ 0) →
    (∀ c : Fin (r + 1) → X, (∀ l : Fin (r + 1), (l : ℕ) < r → c l ∈ Ru) → nrm (c (Fin.last r)) ≠ 0 →
      Kk (r + 1) c = Rs.indicator 1 (c (Fin.last r))) →
    ∫⁻ c in {c : Fin (r + 1) → X | ∀ l : Fin (r + 1), (l : ℕ) < r → c l ∈ Ru},
        Kk (r + 1) c * chainWeight nrm (r + 1) c ∂(Measure.pi fun _ : Fin (r + 1) => μ) =
      μ Ru ^ r * μ Rs
structure MassData (P : Type) where

  g : P → ℝ

  glk : P → ℝ

  uk : P → ℝ

  nn : P → ℝ

  gg : P → ℝ

  μKp : P → ℝ

  μKnatp : P → ℝ

  μKppp : P → ℝ

  μSp : P → ℝ

  μSp' : P → ℝ

  μSppp : P → ℝ

  μSppp' : P → ℝ

  Mp : P → ℝ

  localVolumeAtPlace : P → ℝ

  μKo : ℝ

  μSo : ℝ

  μSo' : ℝ

  Mo : ℝ

  localVolumeArchimedean : ℝ

  μH : ℝ

  μH' : ℝ

  μHpp : ℝ

  μHpp' : ℝ

  μN : ℝ

  μN' : ℝ

  volZZ : ℝ

  volPP : ℝ

  al : ℝ

  volG : ℝ

  volHa : ℝ

  volHa' : ℝ

  volNa : ℝ

  volNa' : ℝ

  volB : ℝ

  volH : ℝ

  volH' : ℝ

  volN : ℝ

  volN' : ℝ

  Coo : ℝ

  deg : ℝ

  dimπ : ℝ

  dimπ' : ℝ

  ρ0 : ℝ

  ρ0' : ℝ

  d : ℝ

  d' : ℝ

  n0c : ℝ

  supdens : ℝ

  e1 : ℝ

  δ : ℝ

  Kgs2 : ℝ

  KV : ℝ

  Sig : ℝ

  KtopV : ℝ

  IntN : ℝ

  IntC : ℝ

  IntOO : ℝ
namespace MassData
variable {P : Type} [Fintype P] (B : MassData P)
noncomputable def ga (p : P) : ℝ := B.glk p / B.uk p
noncomputable def Gam1 : ℝ := ∏ p, B.ga p
noncomputable def tt : ℝ := ∏ p, (1 + 3 / B.g p)
noncomputable def μK : ℝ := B.μKo * ∏ p, B.μKp p
noncomputable def μKnat : ℝ := B.μKo * ∏ p, B.μKnatp p
noncomputable def μKpp : ℝ := B.μKo * ∏ p, B.μKppp p
noncomputable def μS : ℝ := B.μSo * ∏ p, B.μSp p
noncomputable def μS' : ℝ := B.μSo' * ∏ p, B.μSp' p
noncomputable def μSpp : ℝ := B.μSo * ∏ p, B.μSppp p
noncomputable def μSpp' : ℝ := B.μSo' * ∏ p, B.μSppp' p
noncomputable def MM : ℝ := B.Mo * ∏ p, B.Mp p
noncomputable def unitLevelVolume : ℝ := B.localVolumeArchimedean * ∏ p, B.localVolumeAtPlace p
noncomputable def c0 : ℝ := B.volN * B.volH / B.dimπ
noncomputable def c0' : ℝ := B.volN' * B.volH' / B.dimπ'
noncomputable def V0 : ℝ := B.volG / B.μK
noncomputable def Dstar : ℝ := B.deg * (B.volG / B.μKpp)
noncomputable def AA : ℝ := B.volB * B.Coo * (B.MM / B.volZZ) / B.μK
noncomputable def GS : ℝ := B.tt * (B.d / B.dimπ) * B.KV
noncomputable def Smod : ℝ := B.c0 * B.c0' * B.KtopV
noncomputable def nn0 : ℝ := B.volB * (B.MM / (B.al * B.unitLevelVolume)) / B.μK
def Pos : Prop :=
  (∀ p, 0 < B.g p ∧ 0 < B.glk p ∧ 0 < B.uk p ∧ 0 < B.nn p ∧ 0 < B.gg p ∧ 0 < B.μKp p ∧
    0 < B.μKnatp p ∧ 0 < B.μKppp p ∧ 0 < B.μSp p ∧ 0 < B.μSp' p ∧ 0 < B.μSppp p ∧ 0 < B.μSppp' p ∧
    0 < B.Mp p ∧ 0 < B.localVolumeAtPlace p) ∧
  0 < B.μKo ∧ 0 < B.μSo ∧ 0 < B.μSo' ∧ 0 < B.Mo ∧ 0 < B.localVolumeArchimedean ∧ 0 < B.μH ∧ 0 < B.μH' ∧
  0 < B.μHpp ∧ 0 < B.μHpp' ∧ 0 < B.μN ∧ 0 < B.μN' ∧ 0 < B.volZZ ∧ 0 < B.volPP ∧ 0 < B.al ∧ 0 < B.volG ∧
  0 < B.volHa ∧ 0 < B.volHa' ∧ 0 < B.volNa ∧ 0 < B.volNa' ∧ 0 < B.volB ∧ 0 < B.volH ∧
  0 < B.volH' ∧ 0 < B.volN ∧ 0 < B.volN' ∧ 0 < B.Coo ∧ 0 < B.deg ∧ 0 < B.dimπ ∧ 0 < B.dimπ' ∧
  0 < B.ρ0 ∧ 0 < B.ρ0' ∧ 0 < B.d ∧ 0 < B.d' ∧ 0 < B.n0c ∧ 0 ≤ B.supdens ∧ 0 ≤ B.δ
def InTwoA : Prop := B.Kgs2 ≤ B.tt * B.Gam1 * B.Sig
def InForm : Prop := B.Sig = B.ρ0 * B.KV
def InKernel : Prop := B.KV ≤ B.supdens * B.n0c * B.KtopV ∧ 0 ≤ B.KtopV
def InMass : Prop := B.n0c * B.ρ0 = B.AA
def InDens : Prop := B.supdens ≤ B.e1
def InTheoremA : Prop := B.Smod ≤ (1 + B.δ) * B.IntN
def InJacMod : Prop := B.IntN = B.volZZ / (B.unitLevelVolume * B.volPP) * (B.volPP * B.IntC)
def InNu : Prop := B.IntOO = B.Coo * B.IntC
def InInfinity : Prop := B.IntOO ≤ 1 / B.deg
def InVolumes : Prop := B.volB * B.volG = B.volHa * B.volHa' ∧ B.volNa = 1 ∧ B.volNa' = 1
def InLevelS : Prop :=
  B.μS = B.μN * B.μH ∧ B.μSpp = B.μN * B.μHpp ∧ B.μS' = B.μN' * B.μH' ∧ B.μSpp' = B.μN' * B.μHpp'
def InMasses : Prop :=
  B.ρ0 = B.volHa / (B.volH * B.μH) ∧ B.volNa = B.volN * B.μN ∧
  B.ρ0' = B.volHa' / (B.volH' * B.μH') ∧ B.volNa' = B.volN' * B.μN'
def InColumns : Prop :=
  B.d = B.dimπ * (B.volHa / (B.volH * B.μHpp)) ∧ B.μH / B.μHpp = B.Gam1 ∧
  B.d' = B.dimπ' * (B.volHa' / (B.volH' * B.μHpp')) ∧ B.μH' / B.μHpp' = B.Gam1
def InOrdinary : Prop := B.Mo / B.localVolumeArchimedean = B.μKo ^ 2 / (B.μSo * B.μSo')
def InTyped : Prop :=
  ∀ p, B.Mp p / B.localVolumeAtPlace p = B.μKp p * B.μKnatp p / (B.μSp p * B.μSp' p) ∧
    B.μSp p = B.ga p * B.μSppp p ∧ B.μSp' p = B.ga p * B.μSppp' p
def InIndices : Prop :=
  ∀ p, B.μKp p = B.gg p / (B.nn p * B.uk p) * B.μKppp p ∧
    B.μKnatp p / B.μKp p = B.glk p * B.nn p / B.gg p
end MassData
def Columns : Prop :=
  ∀ (P : Type) [Fintype P] (B : MassData P), B.Pos → B.InVolumes → B.InLevelS → B.InMasses →
    B.InColumns →
    B.ρ0 * B.volN * B.volH = B.volHa / B.μS ∧ B.d = B.Gam1 * B.ρ0 * B.dimπ ∧
    1 / B.c0 = B.d * B.μSpp / B.volHa ∧
    B.ρ0' * B.volN' * B.volH' = B.volHa' / B.μS' ∧ B.d' = B.Gam1 * B.ρ0' * B.dimπ' ∧
    1 / B.c0' = B.d' * B.μSpp' / B.volHa'
def KnatGamma : Prop :=
  ∀ (P : Type) [Fintype P] (B : MassData P), B.Pos → B.InIndices →
    ∀ p, B.μKnatp p = B.ga p * B.μKppp p
def LocalProduct : Prop :=
  ∀ (P : Type) [Fintype P] (B : MassData P), B.Pos → B.InOrdinary → B.InTyped → B.InIndices →
    B.MM / B.unitLevelVolume / B.μK = B.μKpp / (B.Gam1 * B.μSpp * B.μSpp') ∧
    B.MM / B.unitLevelVolume / B.μK = B.μKnat / (B.μS * B.μS')
def JacobianConstant : Prop :=
  ∀ (P : Type) [Fintype P] (B : MassData P), B.Pos → B.InJacMod → B.InNu →
    B.IntN = B.volZZ / B.unitLevelVolume * B.Coo⁻¹ * B.IntOO
def SigBound : Prop :=
  ∀ (P : Type) [Fintype P] (B : MassData P), B.Pos → B.InForm → B.InKernel → B.InMass → B.InDens →
    B.InTheoremA → B.InJacMod → B.InNu → B.InInfinity →
    B.Sig ≤ (1 + B.δ) * B.e1 * (B.c0 * B.c0')⁻¹ * B.volB * (B.MM / B.unitLevelVolume) / (B.μK * B.deg)
def MainTheorem : Prop :=
  ∀ (P : Type) [Fintype P] (B : MassData P), B.Pos → B.InTwoA → B.InForm → B.InKernel → B.InMass →
    B.InDens → B.InTheoremA → B.InJacMod → B.InNu → B.InInfinity → B.InVolumes → B.InLevelS →
    B.InMasses → B.InColumns → B.InOrdinary → B.InTyped → B.InIndices →
    B.GS = B.tt * B.Gam1 * B.Sig ∧
    B.GS ≤ (1 + B.δ) * B.e1 * B.tt * (B.d * B.d' / B.Dstar) ∧
    B.Kgs2 ≤ (1 + B.δ) * B.e1 * B.tt * (B.d * B.d' / B.Dstar)
def DstarProductFormula : Prop :=
  ∀ (P : Type) [Fintype P] (B : MassData P), B.Pos → B.InIndices →
    B.Dstar = (∏ p, B.gg p / (B.nn p * B.uk p)) * B.V0 * B.deg
def NN0Formula : Prop :=
  ∀ (P : Type) [Fintype P] (B : MassData P), B.Pos → B.InVolumes → B.InLevelS → B.InMasses →
    B.InOrdinary → B.InTyped → B.InIndices →
    B.nn0 = B.al⁻¹ * (B.ρ0 * B.ρ0' * B.volN * B.volN' * B.volH * B.volH' * B.V0⁻¹ *
      ∏ p, B.glk p * B.nn p / B.gg p)
def VolumeMassSum : Prop :=
  ∀ (P : Type) [Fintype P] (B : MassData P), B.Pos → B.InVolumes → B.InLevelS → B.InMasses →
    B.InColumns → B.InIndices →
    (∏ p, B.ga p * (B.glk p * B.nn p) / B.gg p) * (B.ρ0 * B.dimπ) * (B.ρ0' * B.dimπ') /
      (B.V0 * B.deg) = B.d * B.d' / B.Dstar
def SIsFrameStabiliser : Prop :=
  ∀ (A : Type) [CommRing A] (r k : ℕ) (x : Matrix (Idx r k) (Idx r k) A), IsUnit x.det →
    (IsS x ↔
      (IsUpUni (b11 x) ∧ b21 x = 0 ∧ b31 x = 0 ∧
        (∀ a, b22 x a (Sum.inr ()) = if a = Sum.inr () then 1 else 0) ∧ (∀ a, b32 x a (Sum.inr ()) = 0)) ∧
      (IsUpUni (b33 x) ∧ b32 x = 0 ∧
        (∀ b, b22 x (Sum.inr ()) b = if b = Sum.inr () then 1 else 0) ∧ (∀ b, b21 x (Sum.inr ()) b = 0)))
def FrameStabiliserPointwise : Prop :=
  ∀ (A : Type) [CommRing A] (r k : ℕ) (x : Matrix (Idx r k) (Idx r k) A), IsUnit x.det →
    (IsInertiaInfiniteCyclotomic x ↔
      (∀ i (b : Fin r), x i (Sum.inl b) = (1 : Matrix (Idx r k) (Idx r k) A) i (Sum.inl b)) ∧
      (∀ i, x i (Sum.inr (Sum.inl (Sum.inr ()))) =
        (1 : Matrix (Idx r k) (Idx r k) A) i (Sum.inr (Sum.inl (Sum.inr ())))) ∧
      (∀ (a : Fin r) i, x (Sum.inr (Sum.inr a)) i = (1 : Matrix (Idx r k) (Idx r k) A) (Sum.inr (Sum.inr a)) i) ∧
      (∀ i, x (Sum.inr (Sum.inl (Sum.inr ()))) i =
        (1 : Matrix (Idx r k) (Idx r k) A) (Sum.inr (Sum.inl (Sum.inr ()))) i))
structure FrameLevel (o : Type) [CommRing o] [IsLocalRing o] (r k : ℕ) where

  K1 : Subgroup (GL (Idx r k) o)
  mem_parahoricTimesPrincipalCongruence_iff : ∀ x, x ∈ K1 ↔
    IsInertiaInfiniteCyclotomic (red o (Idx r k) x : Matrix (Idx r k) (Idx r k) (IsLocalRing.ResidueField o))
def FrameLevelExists : Prop :=
  ∀ (o : Type) [CommRing o] [IsLocalRing o] (r k : ℕ), Nonempty (FrameLevel o r k)
def CongruenceLevelIndex : Prop :=
  ∀ (o : Type) [CommRing o] [IsLocalRing o] [Finite (IsLocalRing.ResidueField o)] (r k : ℕ)
    (L : Levels o r k) (M : FrameLevel o r k),
    M.K1 ≤ L.Knat ∧
    M.K1.relIndex L.Knat = Nat.card (IsLocalRing.ResidueField o) ^ (r * (r + 1))
def FrameIndex : Prop :=
  ∀ (K : Type) [Field K] [Fintype K] (r k : ℕ),
    (Nat.card (GL (Idx r k) K) : ℝ) =
      Nat.card {x : Matrix (Idx r k) (Idx r k) K // IsS x} *
        ((Fintype.card K : ℝ) ^ (((r : ℤ) + 1) * (2 * k + 2 * r + 1)) *
          densP 1 (Fintype.card K) ((k : ℤ) + 1) ((k + 2 * r + 1 : ℕ) : ℤ))
def KppCorner : Prop :=
  ∀ (o : Type) [CommRing o] [IsDomain o] [IsDiscreteValuationRing o] (ϖ : o), Irreducible ϖ →
    ∀ (r k : ℕ) (j : Matrix (Idx r k) (Idx r k) o), KppO j → ∃ X : Matrix (Fin r) (Fin r) o, b31 j = ϖ • X
def OmStable : Prop :=
  ∀ (o : Type) [CommRing o] [IsDomain o] [IsDiscreteValuationRing o] (ϖ : o), Irreducible ϖ →
    ∀ (r k : ℕ) (j n n' : Matrix (Idx r k) (Idx r k) o) (h : Matrix (Fin k) (Fin k) o),
      InOm ϖ j → IsN n → IsN n' → IsUnit h.det → IsUpUni (h.map (IsLocalRing.residue o)) →
      InOm ϖ (n * j * n') ∧ InOm ϖ (hEmb r h * j) ∧ InOm ϖ (j * hEmb r h) ∧ InOm ϖ j⁻¹
def ROrderIndex : Prop :=
  ∀ (o : Type) [CommRing o] [IsLocalRing o] [Finite (IsLocalRing.ResidueField o)],
    Nat.card (ROrd o ⧸ RingHom.ker ((IsLocalRing.residue o).comp
      ((RingHom.fst o o).comp (ROrd o).subtype))) = Nat.card (IsLocalRing.ResidueField o)
def UnitStratumTotal : Prop :=
  ∀ (volNo volJH volKpp volOm q : ℝ) (r : ℕ), 0 < volNo → 0 < volJH → 0 < volKpp →
    volOm = (1 - 1 / q) ^ r * volKpp →
    (volNo / volJH) ^ 2 * volOm / volNo ^ 2 = volKpp / volJH ^ 2 * (1 - 1 / q) ^ r
def DensityFromMassFormula : Prop :=
  ∀ (P : Type) [Fintype P] (B : MassData P), B.Pos →
    B.nn0 = B.AA / B.al * (B.volZZ / B.unitLevelVolume) * B.Coo⁻¹
def MainSharp : Prop :=
  ∃ (P : Type) (_ : Fintype P) (B : MassData P), B.Pos ∧ B.InTwoA ∧ B.InForm ∧ B.InKernel ∧ B.InMass ∧
    B.InDens ∧ B.InTheoremA ∧ B.InJacMod ∧ B.InNu ∧ B.InInfinity ∧ B.InVolumes ∧ B.InLevelS ∧
    B.InMasses ∧ B.InColumns ∧ B.InOrdinary ∧ B.InTyped ∧ B.InIndices ∧ 0 < B.GS ∧
    B.GS = (1 + B.δ) * B.e1 * B.tt * (B.d * B.d' / B.Dstar)
end Formalism.FourierDecayAlt.S3


