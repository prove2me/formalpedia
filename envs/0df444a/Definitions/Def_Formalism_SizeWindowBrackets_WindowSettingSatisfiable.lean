-- Prove2me | Definitions.Def_Formalism_SizeWindowBrackets_WindowSettingSatisfiable
-- name    : Formalism_SizeWindowBrackets_WindowSettingSatisfiable
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:53:09.417796+00:00
-- url     : https://prove2.me/theorems/8c51c299-3397-44fb-b5a3-f4027b26a1cf
-- title:
--   Window Setting Satisfiable
-- statement:
--   Definitions and structural lemmas for Window Setting Satisfiable, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SizeWindowBrackets/WindowSettingSatisfiable.lean

import Definitions.Def_Formalism_SizeWindowBrackets_SecondKindBucket
import Definitions.Def_Formalism_SizeWindowBrackets_ErrorFormsWeakWindowsFalse
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.LFunctionChainParameters.PrimeWindowSizeBounds
open Finset Classical
open Formalism.LFunctionChainParameters.DeficitSplitLemmas Formalism.LFunctionChainParameters.LErr
noncomputable section
structure Par where

  x : ℝ

  ε : ℝ

  e₂ : ℕ

  nA : ℝ := 2 ^ e₂

  k : ℝ

  N : ℝ

  t : ℝ

  p₀ : ℕ

  La : ℝ

  rG : ℝ

  Sc : ℝ

  η : ℝ

  ρ : ℝ

  th : ℝ

  K₀ : ℝ

  d : ℕ

  C : ℝ

  β : ℝ

  Cord : ℝ

  Y : ℝ

  s₀ : ℝ

  bo : ℝ
namespace Par
variable (P : Par)
def n : ℝ := P.nA
def f : ℝ := 2 * P.n
def b : ℝ := bTx P.x P.ε
def a : ℝ := aTx P.x P.ε
def Xp : ℝ := XpTx P.x P.ε
def bp : ℝ := bpTx P.x P.ε
def wpp : ℝ := wppTx P.x P.ε P.n
def Xpp : ℝ := XppTx P.x P.ε P.n
def lx : ℝ := Real.log P.x
def δ₁ : ℝ := P.x ^ (-(P.ε / 8))
def θ : ℝ := P.x ^ (-P.ε)
def Sk : ℝ := P.Sc + P.k + P.η
def Q₁ : ℝ := P.C * P.rG * P.bp * P.lx
def Q₂ : ℝ := P.C * (P.bp / P.x + P.η + P.Sc + (P.wpp + P.t) * P.lx / P.δ₁) + P.bo
def Jo : ℕ := ⌊P.x ^ (P.ε / 4)⌋₊
def Ib : ℕ := ⌊P.x ^ (P.ε / 3)⌋₊
end Par
def Windows (P : Par) (e K : ℝ) : Prop :=
  0 < P.ε ∧ P.ε ≤ 1 ∧ 0 ≤ e ∧ 1 ≤ K ∧
  (P.x ^ 2 ≤ (2 : ℝ) ^ P.e₂ ∧ (2 : ℝ) ^ P.e₂ ≤ P.n) ∧ P.n ≤ P.x ^ e ∧
  P.x ^ 2 ≤ P.k ∧ P.k ≤ P.x ^ e ∧
  0 ≤ P.N ∧ P.N ≤ P.x ^ e ∧ 0 ≤ P.t ∧ P.t ≤ P.x ^ e ∧
  P.x ^ 4 + 1 ≤ (P.p₀ : ℝ) ∧ (P.p₀ : ℝ) ≤ P.x ^ e ∧
  0 ≤ P.La ∧ P.La ≤ P.x ^ (2 * P.ε) ∧
  0 ≤ P.rG ∧ P.rG ≤ P.x ^ e ∧
  0 ≤ P.Sc ∧ P.Sc ≤ Real.exp (P.x ^ (P.ε / 4)) ∧ 0 ≤ P.η ∧ P.η ≤ Real.exp (P.x ^ (P.ε / 4)) ∧
  0 ≤ P.ρ ∧ P.ρ ≤ (P.x ^ 2)⁻¹ ∧
  0 ≤ P.th ∧ P.th ≤ P.x⁻¹ ∧
  P.x ^ 2 ≤ P.K₀ ∧ P.x ^ 2 ≤ (P.d : ℝ) ∧
  0 ≤ P.C ∧ P.C ≤ K ∧ 0 ≤ P.β ∧ P.β ≤ K * (P.x ^ 2)⁻¹ ∧ 0 ≤ P.Cord ∧ P.Cord ≤ K ∧
  1 ≤ P.Y ∧ P.Y ≤ 2 * P.Xp ∧
  0 ≤ P.s₀ ∧ P.s₀ ≤ (P.x ^ 2)⁻¹ ∧
  0 ≤ P.bo ∧ P.bo ≤ Real.exp (P.x ^ P.ε / 2)
def LargeX (x ε e K : ℝ) : Prop :=
  1 ≤ x ∧ 100 * K * x ^ (4 * ε) ≤ x ∧
  100 * K * x ^ (4 * e + 4) ≤ Real.exp (x ^ (ε / 3)) ∧
  100 * K * x ^ (4 * e + 4) * Real.exp (x ^ (ε / 3) + x ^ (ε / 4)) ≤ Real.exp (x ^ ε / 2)
def LargeXEv : Prop :=
  ∀ ε e K : ℝ, 0 < ε → ε < 1 / 4 → ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → LargeX x ε e K
def WindowsSat : Prop :=
  ∀ ε e K c : ℝ, 0 < ε → ε ≤ 1 / 52 → 40 ≤ e → 1 ≤ K → 0 ≤ c → c ≤ K → ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
    ∃ P : Par, P.x = x ∧ P.ε = ε ∧ x ^ (2 + 8 * ε) < P.n ∧ P.n ≤ 2 * x ^ (2 + 8 * ε) ∧
      P.k = x ^ (9 / 2 + 10 * ε) ∧ P.p₀ = ⌈P.k ^ 2 * x ^ 26⌉₊ ∧ P.th = 1 / (P.k * x ^ 13) ∧
      P.K₀ = P.k ^ 2 * x ^ 78 ∧ P.ρ = (x ^ 2)⁻¹ ∧ P.La = x ^ ε ∧
      P.Sc = Real.exp (x ^ (ε / 4)) ∧ P.η = Real.exp (x ^ (ε / 4)) ∧ P.N = x ^ e ∧ P.t = x ^ e ∧
      P.C = K ∧ P.Cord = c ∧ P.rG = K ∧ P.β = K * (x ^ 2)⁻¹ ∧ P.Y = P.Xp * (1 + P.ρ) ∧
      P.s₀ = (x ^ 9)⁻¹ ∧ P.bo = Real.exp (x ^ ε / 2) ∧
      Windows P e K ∧ LargeX x ε e K
def unitU (P : Par) (m T : ℝ) : ℝ := T * m * P.b
def tFloors (P : Par) (m : ℝ) : ℝ :=
  m * (2 * P.C * P.f * P.Xpp * (P.N ^ 2 * Real.log P.a + 2 * Real.log P.a ^ 2))
def tCp (P : Par) (m T : ℝ) : ℝ := 2 * P.C * P.Sk * Real.log (2 * P.a) * (m * T) * P.Xpp
def tPrLow (P : Par) (m T : ℝ) : ℝ := m * T * (2 * Real.log 4 * (P.p₀ * P.Q₁))
def tPrHigh (P : Par) (m T : ℝ) : ℝ := m * T * (2 * Real.log 4 * (P.Xp * P.Q₂))
def tOr (P : Par) (m T : ℝ) : ℝ :=
  m * T * (2 * P.C * P.lx * P.a * ((P.La / P.k + 1 / P.K₀) * (Real.log P.Xp + Real.log 4) +
    2 * (Real.log ((P.p₀ : ℝ) - 1) + 1) / ((P.p₀ : ℝ) - 1)))
def tBad (P : Par) (m T : ℝ) : ℝ := 32 * P.β * m * P.a * T * (Real.log P.Xp + Real.log 4)
def tOrders (P : Par) (m T : ℝ) : ℝ :=
  4 * m * T * P.a * (P.Cord * P.Jo * Real.log (2 ^ P.e₂ * max P.Y P.Xpp) ^ 2 / (2 : ℝ) ^ P.e₂)
def tBand (P : Par) (m T : ℝ) : ℝ :=
  4 * m * T * P.a * (P.Ib * ((4 * P.ρ + 1 / (P.p₀ : ℝ)) * Real.log (2 * P.Xp)))
def tHigh (P : Par) (m T : ℝ) : ℝ :=
  m * T * (2 * Real.log (2 * P.Xpp) * (P.a * P.th ^ 2 + P.wpp * P.th))
def tD (P : Par) (m T : ℝ) : ℝ := m * T * (2 * P.a * Real.log P.d / P.d)
def tSecondIo (P : Par) (m T : ℝ) : ℝ :=
  (P.s₀ / P.θ + P.s₀) * (4 * (m * T * P.a) * (Real.log P.Y + Real.log 4))
def sg (P : Par) (K : ℝ) : ℝ := 100 * K * P.x ^ (4 * P.ε) / P.x
def SgLeOne : Prop :=
  ∀ (P : Par) (e K : ℝ), Windows P e K → LargeX P.x P.ε e K → 0 ≤ sg P K ∧ sg P K ≤ 1
def SgSmall : Prop :=
  ∀ ε K δ : ℝ, 0 < ε → ε < 1 / 4 → 0 < δ → ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → 100 * K * x ^ (4 * ε) / x ≤ δ
def SizeFloors : Prop :=
  ∀ (P : Par) (e K m T : ℝ), Windows P e K → LargeX P.x P.ε e K → 0 ≤ m → 1 ≤ T →
    tFloors P m ≤ sg P K * unitU P m T
def SizeCp : Prop :=
  ∀ (P : Par) (e K m T : ℝ), Windows P e K → LargeX P.x P.ε e K → 0 ≤ m → 1 ≤ T →
    tCp P m T ≤ sg P K * unitU P m T
def SizePrLow : Prop :=
  ∀ (P : Par) (e K m T : ℝ), Windows P e K → LargeX P.x P.ε e K → 0 ≤ m → 1 ≤ T →
    tPrLow P m T ≤ sg P K * unitU P m T
def SizePrHigh : Prop :=
  ∀ (P : Par) (e K m T : ℝ), Windows P e K → LargeX P.x P.ε e K → 0 ≤ m → 1 ≤ T →
    tPrHigh P m T ≤ (2 * Real.log 4 * P.C + 3 * sg P K) * unitU P m T
def SizePrHighLower : Prop :=
  ∀ (P : Par) (e K m T : ℝ), Windows P e K → LargeX P.x P.ε e K → 0 ≤ m → 1 ≤ T →
    2 * Real.log 4 * P.C * unitU P m T ≤ tPrHigh P m T
def SizeOr : Prop :=
  ∀ (P : Par) (e K m T : ℝ), Windows P e K → LargeX P.x P.ε e K → 0 ≤ m → 1 ≤ T →
    tOr P m T ≤ sg P K * unitU P m T
def SizeBad : Prop :=
  ∀ (P : Par) (e K m T : ℝ), Windows P e K → LargeX P.x P.ε e K → 0 ≤ m → 1 ≤ T →
    tBad P m T ≤ sg P K * unitU P m T
def SizeOrders : Prop :=
  ∀ (P : Par) (e K m T : ℝ), Windows P e K → LargeX P.x P.ε e K → 0 ≤ m → 1 ≤ T →
    tOrders P m T ≤ sg P K * unitU P m T
def SizeBand : Prop :=
  ∀ (P : Par) (e K m T : ℝ), Windows P e K → LargeX P.x P.ε e K → 0 ≤ m → 1 ≤ T →
    tBand P m T ≤ sg P K * unitU P m T
def SizeHigh : Prop :=
  ∀ (P : Par) (e K m T : ℝ), Windows P e K → LargeX P.x P.ε e K → 0 ≤ m → 1 ≤ T →
    tHigh P m T ≤ sg P K * unitU P m T
def SizeD : Prop :=
  ∀ (P : Par) (e K m T : ℝ), Windows P e K → LargeX P.x P.ε e K → 0 ≤ m → 1 ≤ T →
    tD P m T ≤ sg P K * unitU P m T
def SizeSecondIo : Prop :=
  ∀ (P : Par) (e K m T : ℝ), Windows P e K → LargeX P.x P.ε e K → 0 ≤ m → 1 ≤ T →
    tSecondIo P m T ≤ sg P K * unitU P m T
def tDet (P : Par) (m T : ℝ) : ℝ :=
  tFloors P m + tCp P m T + tPrLow P m T + tPrHigh P m T + tOr P m T + tBad P m T + tOrders P m T
    + tBand P m T + tHigh P m T + tD P m T
def WindowSizeBoundSharp : Prop :=
  ∀ (P : Par) (e K m T : ℝ), Windows P e K → LargeX P.x P.ε e K → 0 ≤ m → 1 ≤ T →
    tDet P m T + tSecondIo P m T ≤ (2 * Real.log 4 * P.C + 13 * sg P K) * unitU P m T
def WindowSizeBound : Prop :=
  ∀ (P : Par) (e K m T : ℝ), Windows P e K → LargeX P.x P.ε e K → 0 ≤ m → 1 ≤ T →
    tDet P m T + tSecondIo P m T ≤ (3 * P.C + 13) * unitU P m T
def SideConditionsOfWindows : Prop :=
  ∀ (P : Par) (e K : ℝ), Windows P e K → LargeX P.x P.ε e K →
    0 < P.wpp ∧ 0 ≤ P.th ∧ P.th ≤ 1 / 2 ∧ 2 ≤ P.Xpp ∧ P.Xpp * P.wpp = P.a ∧ 1 ≤ P.a ∧ 1 ≤ P.Xp ∧
    3 ≤ P.p₀ ∧ 4 ≤ P.d ∧ 0 ≤ P.C ∧ 0 ≤ P.f ∧ 0 ≤ P.Sk ∧ 0 ≤ P.Q₁ ∧ 0 ≤ P.Q₂ ∧ 0 ≤ P.lx ∧ 0 ≤ P.La ∧
    0 < P.k ∧ 0 < P.K₀ ∧ P.Xpp = P.x * P.n * P.Xp
structure LD (ι κ τ : Type) where

  W : Finset ι

  below : ι → ℕ

  l : ι → ℝ

  cl : ℕ → PClass

  TTp : ℕ → Finset τ

  Iex : κ → τ → ℕ → Finset ℕ

  at_ : τ → ℝ

  wz : κ → τ → ℕ → ℕ → ℝ

  Id : κ → τ → Finset ℕ

  wd : κ → τ → ℕ → ℝ

  gainW : κ → ι → ℝ

  tauW : ι → ℝ

  gain : κ → ℕ → ℝ

  tau : ℕ → ℝ

  lo : ℕ → ℝ

  fl : ℕ → ℝ

  L₁ : ℕ → ℝ
variable {ι κ τ : Type}
def LD.vonMangoldtClassSum (D : LD ι κ τ) (j : κ) (t : τ) (p : ℕ) : ℝ := askAt (D.Iex j t p) (D.at_ t) p (D.wz j t p)
def LD.ASK (D : LD ι κ τ) (d : ℕ) (Ps : Finset ℕ) (J : Finset κ) (TT : Finset τ) : ℝ :=
  DeficitSplitLemmas.ASK Ps J TT (fun j t p => askAt (D.Iex j t p) (D.at_ t) p (D.wz j t p))
    (fun j t => Real.log d * askAt (D.Id j t) (D.at_ t) d (D.wd j t))
def LD.Ga (D : LD ι κ τ) (J : Finset κ) : ℝ := GaW D.W J D.l D.gainW D.tauW
def ParametersHyp (P : Par) (Ps : Finset ℕ) (J : Finset κ) (TT : Finset τ) (D : LD ι κ τ) : Prop :=
  UnitRule D.W D.below D.l Ps J D.gainW D.tauW D.gain D.tau ∧
  (∀ t ∈ TT, 0 ≤ D.at_ t ∧ D.at_ t ≤ P.a * (1 + P.th)) ∧
  (∀ j ∈ J, ∀ t ∈ TT, ∀ p ∈ Ps, ∀ i ∈ D.Iex j t p, Odd i ∧ P.wpp ≤ D.wz j t p i) ∧
  (∀ j ∈ J, ∀ t ∈ TT, ∀ i ∈ D.Id j t, 1 ≤ i ∧ 0 ≤ D.wd j t i) ∧
  (∀ p ∈ Ps, D.cl p = PClass.served → (p : ℝ) ≤ P.Xpp) ∧
  (∀ p ∈ Ps, D.cl p = PClass.high → P.Xpp < p) ∧
  (∀ p ∈ Ps, D.cl p = PClass.served →
    SizeData₂ J TT D.TTp (fun j t p => askAt (D.Iex j t p) (D.at_ t) p (D.wz j t p))
      D.gain D.tau D.lo D.fl p) ∧
  (∀ p ∈ Ps, D.cl p ≠ PClass.served → (∀ j ∈ J, D.gain j p = 0) ∧ D.tau p = 0) ∧
  (∀ p ∈ Ps, D.cl p = PClass.served → D.fl p ≤ flF P.C P.f P.N P.a p) ∧
  (∀ p ∈ Ps, D.cl p = PClass.served →
    D.lo p ≤ loF P.C P.Sk P.a P.Xp P.Q₁ P.Q₂ P.lx P.La P.k D.L₁ P.p₀ p) ∧
  (∀ p ∈ Ps, p < P.p₀ → P.K₀ ≤ (p : ℝ) ^ (D.L₁ p - 1))
def FirstHyp (P : Par) (Ps : Finset ℕ) (cl : ℕ → PClass) : Prop :=
  ∀ p ∈ Ps, cl p = PClass.first →
    (((p : ℝ) ≤ max P.Y P.Xpp ∧ ∃ hl : Nat.Coprime p (4 * 2 ^ P.e₂),
        (orderOf (Formalism.RankGapBounds.LocalQuadraticParts.hOf P.e₂ p hl) : ℝ) < P.x ^ (P.ε / 4)) ∨
      (P.p₀ ≤ p ∧ ∃ i : ℕ, 1 ≤ i ∧ P.Xp * (1 - P.ρ) ≤ (p : ℝ) ^ i ∧ (p : ℝ) ^ i ≤ P.Xp * (1 + P.ρ)))
def LossChoiceU : Prop :=
  ∀ (Ω U : Type) [Fintype Ω] (π : Ω → ℝ) (Loss : U → Ω → ℝ) (s : Finset ℕ) (Sig : ℕ → Ω → ℝ)
    (io : U → ℕ → Ω → ℝ) (D : U → ℝ) (Y θ s₀ mTa : ℝ),
    (∀ o, 0 ≤ π o) → ∑ o, π o = 1 → 0 < θ → 0 ≤ s₀ → 0 ≤ mTa → 1 ≤ Y →
    (∀ p ∈ s, p.Prime ∧ (p : ℝ) ≤ Y) → (∀ p ∈ s, ∀ o, 0 ≤ Sig p o) →
    (∀ p ∈ s, ∑ o, π o * Sig p o ≤ s₀) →
    (∀ υ o, Loss υ o ≤ D υ + ∑ p ∈ s, (if θ < Sig p o then 4 * mTa * Real.log p / p else 0)) →
    (∀ υ, ∀ p ∈ s, ∀ o, io υ p o ≤ 2 * Sig p o * (2 * mTa / p)) →
    ∃ o, 0 < π o ∧
      (∀ υ, Loss υ o ≤ D υ + (s₀ / θ + s₀) * (4 * mTa * (Real.log Y + Real.log 4))) ∧
      ∀ υ, ∑ p ∈ s, Real.log p * io υ p o ≤ (s₀ / θ + s₀) * (4 * mTa * (Real.log Y + Real.log 4))
def SecondLe : Prop :=
  ∀ (Ps s : Finset ℕ) (cl : ℕ → PClass) (Sg : ℕ → ℝ) (θ m T a : ℝ), 0 ≤ m → 0 ≤ T → 0 ≤ a →
    (∀ p ∈ Ps, cl p = PClass.second → p ∈ s ∧ θ < Sg p) →
    4 * m * T * a * (∑ p ∈ Ps.filter (fun p => cl p = PClass.second), Real.log p / p) ≤
      ∑ p ∈ s, (if θ < Sg p then 4 * (m * T * a) * Real.log p / p else 0)
def FirstKind : Prop :=
  ∃ C : ℝ, ∀ (e J : ℕ) (Y X' ρ p₀ : ℝ) (s : Finset ℕ), 1 ≤ e → 1 ≤ J → 1 ≤ Y →
    0 ≤ ρ → ρ ≤ 1 / 2 → 8 ≤ p₀ → 2 ≤ X' →
    (∀ p ∈ s, p.Prime ∧ p ≠ 2 ∧
      (((p : ℝ) ≤ Y ∧ ∃ hl : Nat.Coprime p (4 * 2 ^ e), orderOf (Formalism.RankGapBounds.LocalQuadraticParts.hOf e p hl) ≤ J) ∨
        (p₀ ≤ p ∧ ∃ i : ℕ, 1 ≤ i ∧ X' * (1 - ρ) ≤ (p : ℝ) ^ i ∧ (p : ℝ) ^ i ≤ X' * (1 + ρ)))) →
    ∑ p ∈ s, Real.log p / p ≤
      C * J * Real.log (2 ^ e * Y) ^ 2 / (2 : ℝ) ^ e +
        (⌊Real.log X'⌋₊ : ℝ) * ((4 * ρ + 1 / p₀) * Real.log (2 * X'))
def TopsOutcome : Prop :=
  ∀ (α : Type) [Fintype α] [DecidableEq α] (sB : Finset ℕ) (δ β m a : ℝ)
    (BAD : ℕ → α → Finset α → Prop),
    0 < δ → δ ≤ 1 → 16 ≤ δ * Fintype.card α → 0 ≤ β → 0 ≤ m → 0 ≤ a →
    (∀ p ∈ sB, ∀ t, ∑ T ∈ (Finset.univ : Finset (Finset α)).filter (fun T => t ∈ T ∧ BAD p t T),
        Formalism.RankGapBounds.LocalQuadraticParts.wt δ T ≤ β * δ) →
    ∃ T : Finset α, δ * Fintype.card α / 2 ≤ T.card ∧ (T.card : ℝ) ≤ 2 * δ * Fintype.card α ∧
      ∑ p ∈ sB, 4 * m * a * (Real.log p / p) * ((T.filter fun t => BAD p t T).card : ℝ) ≤
        32 * β * m * a * T.card * ∑ p ∈ sB, Real.log p / p
def WindowSettingHypotheses (P : Par) {U Ω : Type} [Fintype Ω] (π : Ω → ℝ) (Ps s sB : Finset ℕ) (J : Finset κ)
    (TT : Finset τ) (BAD : ℕ → τ → Prop) (Sig : ℕ → Ω → ℝ) (io : U → ℕ → Ω → ℝ)
    (D : U → Ω → LD ι κ τ) : Prop :=
  TT.Nonempty ∧ (∀ p ∈ Ps, p.Prime ∧ p ≠ 2) ∧
  (∀ o, 0 ≤ π o) ∧ ∑ o, π o = 1 ∧
  (∀ p ∈ s, p.Prime ∧ (p : ℝ) ≤ P.Y) ∧ (∀ p ∈ s, ∀ o, 0 ≤ Sig p o) ∧
  (∀ p ∈ s, ∑ o, π o * Sig p o ≤ P.s₀) ∧
  (∀ υ, ∀ p ∈ s, ∀ o, io υ p o ≤ 2 * Sig p o * (2 * ((J.card : ℝ) * TT.card * P.a) / p)) ∧
  (∀ p ∈ sB, p.Prime ∧ (p : ℝ) ≤ P.Xp) ∧
  (∑ p ∈ sB, 4 * (J.card : ℝ) * P.a * (Real.log p / p) * ((TT.filter fun t => BAD p t).card : ℝ) ≤
    32 * P.β * (J.card : ℝ) * P.a * TT.card * ∑ p ∈ sB, Real.log p / p) ∧
  (∀ υ o, ParametersHyp P Ps J TT (D υ o) ∧ FirstHyp P Ps (D υ o).cl ∧
    (∀ p ∈ Ps, (D υ o).cl p = PClass.second → p ∈ s ∧ P.θ < Sig p o) ∧
    (∀ p ∈ Ps, (D υ o).cl p = PClass.served → ∀ t ∈ TT \ (D υ o).TTp p, p ∈ sB ∧ BAD p t))
def LossesWithinWindowUnit (P : Par) {U Ω : Type} (Ps s : Finset ℕ) (J : Finset κ) (TT : Finset τ)
    (io : U → ℕ → Ω → ℝ) (D : U → Ω → LD ι κ τ) (o : Ω) : Prop :=
  (∀ υ, (D υ o).ASK P.d Ps J TT - (D υ o).Ga J ≤ (3 * P.C + 13) * unitU P J.card TT.card) ∧
  ∀ υ, ∑ p ∈ s, Real.log p * io υ p o ≤ unitU P J.card TT.card
def WindowLossesBound : Prop :=
  ∃ Cord : ℝ, 0 ≤ Cord ∧ ∀ (P : Par) (e K : ℝ), P.Cord = Cord → Windows P e K → LargeX P.x P.ε e K →
    ∀ (ι κ τ U Ω : Type) [Fintype Ω] (π : Ω → ℝ) (Ps s sB : Finset ℕ) (J : Finset κ) (TT : Finset τ)
      (BAD : ℕ → τ → Prop) (Sig : ℕ → Ω → ℝ) (io : U → ℕ → Ω → ℝ) (D : U → Ω → LD ι κ τ),
      WindowSettingHypotheses P π Ps s sB J TT BAD Sig io D →
      ∃ o, 0 < π o ∧ LossesWithinWindowUnit P Ps s J TT io D o
def WindowLossesEventual : Prop :=
  ∃ Cord : ℝ, 0 ≤ Cord ∧ ∀ ε e K : ℝ, 0 < ε → ε < 1 / 4 → ∃ x₀ : ℝ,
    ∀ (P : Par), P.ε = ε → P.Cord = Cord → x₀ ≤ P.x → Windows P e K →
    ∀ (ι κ τ U Ω : Type) [Fintype Ω] (π : Ω → ℝ) (Ps s sB : Finset ℕ) (J : Finset κ) (TT : Finset τ)
      (BAD : ℕ → τ → Prop) (Sig : ℕ → Ω → ℝ) (io : U → ℕ → Ω → ℝ) (D : U → Ω → LD ι κ τ),
      WindowSettingHypotheses P π Ps s sB J TT BAD Sig io D →
      ∃ o, 0 < π o ∧ LossesWithinWindowUnit P Ps s J TT io D o
open Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds in

def LeadingTermLossesOfWindow : Prop :=
  ∀ (P : Par) (ι κ τ U U0 Ω : Type) (Ps s : Finset ℕ) (J : Finset κ) (TT : Finset τ)
    (io : U → ℕ → Ω → ℝ) (D : U → Ω → LD ι κ τ) (o : Ω) (sel : U0 → U)
    {W : U0 → Type} {Top : Type} [Fintype Top] {m f : ℕ} (Dd : Data U0 W Top m f) (Cc : Consts),
    LossesWithinWindowUnit P Ps s J TT io D o → 1 ≤ P.x → 0 ≤ P.ε → 0 ≤ P.C →
    Dd.x = P.x → Dd.ε = P.ε → Dd.b = P.b → Fintype.card Top = TT.card → m = J.card →
    (∀ u0, Dd.ASK u0 = (D (sel u0) o).ASK P.d Ps J TT) → (∀ u0, Dd.Ga u0 = (D (sel u0) o).Ga J) →
    (∀ u0, Dd.IO u0 = ∑ p ∈ s, Real.log p * io (sel u0) p o) →
    3 * P.C + 13 ≤ Cc.cLoss → 0 ≤ Cc.eLoss →
    LossBounds Dd Cc
open Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds in

def WindowLossesLeadingTermForm : Prop :=
  ∃ Cord : ℝ, 0 ≤ Cord ∧ ∀ ε e K : ℝ, 0 < ε → ε < 1 / 4 → ∃ x₀ : ℝ,
    ∀ (P : Par), P.ε = ε → P.Cord = Cord → x₀ ≤ P.x → Windows P e K →
    ∀ (ι κ τ U U0 Ω : Type) [Fintype Ω] (π : Ω → ℝ) (Ps s sB : Finset ℕ) (J : Finset κ)
      (TT : Finset τ) (BAD : ℕ → τ → Prop) (Sig : ℕ → Ω → ℝ) (io : U → ℕ → Ω → ℝ)
      (D : U → Ω → LD ι κ τ),
      WindowSettingHypotheses P π Ps s sB J TT BAD Sig io D →
      ∃ o, 0 < π o ∧
        ∀ (sel : U0 → U) {W : U0 → Type} {Top : Type} [Fintype Top] {m f : ℕ}
          (Dd : Data U0 W Top m f) (Cc : Consts),
          Dd.x = P.x → Dd.ε = P.ε → Dd.b = P.b → Fintype.card Top = TT.card → m = J.card →
          (∀ u0, Dd.ASK u0 = (D (sel u0) o).ASK P.d Ps J TT) → (∀ u0, Dd.Ga u0 = (D (sel u0) o).Ga J) →
          (∀ u0, Dd.IO u0 = ∑ p ∈ s, Real.log p * io (sel u0) p o) →
          3 * P.C + 13 ≤ Cc.cLoss → 0 ≤ Cc.eLoss →
          LossBounds Dd Cc
def WindowSettingSatisfiable : Prop :=
  ∀ (P : Par) (e K : ℝ), Windows P e K → LargeX P.x P.ε e K →
    ∃ (π : Unit → ℝ) (Ps s sB : Finset ℕ) (J : Finset Unit) (TT : Finset Unit) (BAD : ℕ → Unit → Prop)
      (Sig : ℕ → Unit → ℝ) (io : Unit → ℕ → Unit → ℝ) (D : Unit → Unit → LD Unit Unit Unit),
      WindowSettingHypotheses P π Ps s sB J TT BAD Sig io D ∧ J.card = 1 ∧ TT.card = 1 ∧ Ps.Nonempty ∧
      0 < (D () ()).ASK P.d Ps J TT
end
end Formalism.LFunctionChainParameters.PrimeWindowSizeBounds


