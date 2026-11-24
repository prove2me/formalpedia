-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_LetterProductDoubleDegreeCount
-- name    : Formalism_HermitianCurvature_LetterProductDoubleDegreeCount
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-24T14:26:48.734057+00:00
-- url     : https://prove2.me/theorems/66cd47a3-f758-4a4a-9b9d-8a74c8c51493
-- title:
--   Letter Product Double Degree Count
-- statement:
--   Definitions and structural lemmas for Letter Product Double Degree Count, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/LetterProductDoubleDegreeCount.lean

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementLE
import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_StatementI
import Definitions.Def_Formalism_HermitianCurvature_StatementQ
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.FourierDecayAlt.C7
open Finset Matrix
open scoped ComplexConjugate ComplexOrder InnerProductSpace
noncomputable section
def zhat {V : Type*} [AddCommGroup V] [Module ℂ V] (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) {r : ℕ}
    (f x' : Fin (r + 1) → V) : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ :=
  Matrix.of fun a b => B (x' b) (f a)
def minorR {r : ℕ} (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) : ℂ :=
  (Z.submatrix Fin.castSucc Fin.castSucc).det
def cofX' {V : Type*} [AddCommGroup V] [Module ℂ V] (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) {r : ℕ}
    (f x' : Fin (r + 1) → V) : V :=
  ∑ b, adjugate (zhat B f x') b (Fin.last r) • x' b
def cofX {V : Type*} [AddCommGroup V] [Module ℂ V] (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) {r : ℕ}
    (f x' : Fin (r + 1) → V) : V :=
  ∑ a, conj (adjugate (zhat B f x') (Fin.last r) a) • f a
def CofactorPair : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) (r : ℕ) (f x' : Fin (r + 1) → V),
    (∀ a, B (cofX' B f x') (f a) = if a = Fin.last r then (zhat B f x').det else 0) ∧
    (∀ b, B (x' b) (cofX B f x') = if b = Fin.last r then (zhat B f x').det else 0)
def CofactorCorner : Prop :=
  ∀ (r : ℕ) (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ), adjugate Z (Fin.last r) (Fin.last r) = minorR Z
def AdjLastCol : Prop :=
  ∀ (r : ℕ) (Z l u : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ),
    (∀ i j, i < j → l i j = 0) → (∀ i, l i i = 1) → (∀ i j, j < i → u i j = 0) → (∀ i, u i i = 1) →
    ∀ b, adjugate (l * Z * u) b (Fin.last r) = ∑ c, u⁻¹ b c * adjugate Z c (Fin.last r)
def GramCofactor : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) (r : ℕ) (f x' : Fin (r + 1) → V) (T' : ℝ),
    (∀ b b', B (x' b) (x' b') = if b = Fin.last r ∧ b' = Fin.last r then -(T' : ℂ) else 0) →
    B (cofX' B f x') (cofX' B f x') = -(T' : ℂ) * (Complex.normSq (minorR (zhat B f x')) : ℂ)
def IsHerm {V : Type*} [AddCommGroup V] [Module ℂ V] (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) : Prop :=
  ∀ u v, B v u = conj (B u v)
def OmNorm : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) (x ω z : V) (T T' : ℝ) (D Dr : ℂ),
    IsHerm B → 0 < T → B x x = 0 → B x ω = 0 → B x z = 0 → B ω z = 0 → B z z = -(T : ℂ) →
    B (x + ω + (-D / T) • z) (x + ω + (-D / T) • z) = -(T' : ℂ) * Complex.normSq Dr →
    (T : ℂ) * B ω ω = Complex.normSq D - T * T' * Complex.normSq Dr
def OmNormCofactor : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) (r : ℕ) (f x' : Fin (r + 1) → V)
    (x ω z : V) (T T' : ℝ),
    IsHerm B → 0 < T → (∀ b b', B (x' b) (x' b') = if b = Fin.last r ∧ b' = Fin.last r then -(T' : ℂ) else 0) →
    B x x = 0 → B x ω = 0 → B x z = 0 → B ω z = 0 → B z z = -(T : ℂ) →
    cofX' B f x' = x + ω + (-(zhat B f x').det / T) • z →
    (T : ℂ) * B ω ω = Complex.normSq (zhat B f x').det - T * T' * Complex.normSq (minorR (zhat B f x'))
def OmNormCofactorOfParts : Prop := GramCofactor → OmNorm → OmNormCofactor
def ScalarPairCommon : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) (V' : Type) [AddCommGroup V'] [Module ℂ V']
    (ω₁ ω₂ : V) (ω₁' ω₂' : V') (D₁ D₂ Dr₁ Dr₂ : ℂ) (T T' : ℝ),
    D₁ ≠ 0 → D₂ ≠ 0 → 0 < T → 0 < T' → ω₂ = (D₂ / D₁) • ω₁ → ω₂' = conj (D₂ / D₁) • ω₁' →
    (T : ℂ) * B ω₁ ω₁ = Complex.normSq D₁ - T * T' * Complex.normSq Dr₁ →
    (T : ℂ) * B ω₂ ω₂ = Complex.normSq D₂ - T * T' * Complex.normSq Dr₂ →
    D₂⁻¹ • ω₂ = D₁⁻¹ • ω₁ ∧ (conj D₂)⁻¹ • ω₂' = (conj D₁)⁻¹ • ω₁' ∧ (Dr₁ = 0 ↔ Dr₂ = 0)
def taS (a b : ℤ) (φ : ℝ) : ℂ := Complex.exp (-(Complex.I * φ * a) - Complex.I * φ * b)
def TaGroup : Prop :=
  ∀ (a b : ℤ) (φ ψ : ℝ), ‖taS a b φ‖ = 1 ∧ taS a b (φ + ψ) = taS a b φ * taS a b ψ ∧ taS a b 0 = 1
def TaArgMul : Prop :=
  ∀ (a b : ℤ) (Dr ζ : ℂ), Dr ≠ 0 → ζ ≠ 0 →
    taS a b (Complex.arg (Dr * ζ)) = taS a b (Complex.arg Dr) * taS a b (Complex.arg ζ)
def frameConj {E E' : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [NormedAddCommGroup E']
    [InnerProductSpace ℂ E'] (U : E ≃ₗᵢ[ℂ] E) (U' : E' ≃ₗᵢ[ℂ] E') (J : E' →L[ℂ] E) : E' →L[ℂ] E :=
  (U.symm.toContinuousLinearEquiv : E →L[ℂ] E) ∘L J ∘L (U'.toContinuousLinearEquiv : E' →L[ℂ] E')
def HSFrame : Prop :=
  ∀ (E E' : Type) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup E'] [InnerProductSpace ℂ E'] [FiniteDimensional ℂ E']
    (U : E ≃ₗᵢ[ℂ] E) (U' : E' ≃ₗᵢ[ℂ] E') (J₁ J₂ : E' →L[ℂ] E),
    LinearMap.trace ℂ E' ((ContinuousLinearMap.adjoint (frameConj U U' J₂) ∘L frameConj U U' J₁ : E' →L[ℂ] E') :
        E' →ₗ[ℂ] E') =
      LinearMap.trace ℂ E' ((ContinuousLinearMap.adjoint J₂ ∘L J₁ : E' →L[ℂ] E') : E' →ₗ[ℂ] E')
def SchurProductPSD : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (A C : Matrix ι ι ℂ), A.PosSemidef → C.PosSemidef → (A ⊙ C).PosSemidef
def FormMono : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (V : ι → H) (K K' : Matrix ι ι ℂ), (K' - K).PosSemidef →
    0 ≤ ∑ w, ∑ w', (K' - K) w w' * ⟪V w', V w⟫_ℂ
def FormMonoOfSchur : Prop := SchurProductPSD → FormMono
def ExtendZeroPSD : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (S : Set ι) [DecidablePred (· ∈ S)] (K : Matrix S S ℂ), K.PosSemidef →
    (Matrix.of fun w w' : ι => if h : w ∈ S ∧ w' ∈ S then K ⟨w, h.1⟩ ⟨w', h.2⟩ else 0).PosSemidef
def IsUnitaryRep {K E : Type*} [Group K] [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (π : K →* (E →L[ℂ] E)) : Prop :=
  ∀ k x y, ⟪π k x, π k y⟫_ℂ = ⟪x, y⟫_ℂ
def Intertw {K A C : Type*} [Group K] [NormedAddCommGroup A] [InnerProductSpace ℂ A] [NormedAddCommGroup C]
    [InnerProductSpace ℂ C] (σ : K →* (A →L[ℂ] A)) (τ : K →* (C →L[ℂ] C)) (J : A →L[ℂ] C) : Prop :=
  ∀ k, τ k ∘L J = J ∘L σ k
def SchurIsotypic : Prop :=
  ∀ (K : Type) [Group K] (E E' R : Type) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup E'] [InnerProductSpace ℂ E'] [FiniteDimensional ℂ E']
    [NormedAddCommGroup R] [InnerProductSpace ℂ R] [FiniteDimensional ℂ R]
    (π : K →* (E →L[ℂ] E)) (π' : K →* (E' →L[ℂ] E')) (ρ : K →* (R →L[ℂ] R)),
    IsUnitaryRep π → IsUnitaryRep π' → IsUnitaryRep ρ →
    (∀ φ : R →L[ℂ] E', Intertw ρ π' φ → φ = 0) →
    ∀ J : E' →L[ℂ] E, Intertw π' π J → ∀ φ : R →L[ℂ] E, Intertw ρ π φ → ∀ v x, ⟪φ x, J v⟫_ℂ = 0
def DetW : Prop := ∀ s : ℕ, (G.wMat s).det = (-1) ^ (s * (s - 1) / 2)
def DEqualRoots : Prop :=
  ∀ (s : ℕ) (D'' c t z : ℂ), 1 ≤ s → z ^ s = (-1) ^ (s + 1) * c * t ^ (s - 1) →
    D'' * (G.wMat (s - 1)).det * c * t ^ (s - 1) = D'' * (G.wMat s).det * z ^ s
def DEqualOfParts : Prop := G.DetMatch → DEqualRoots
def nOf (k r : ℕ) : ℕ := k + 2 * r + 1
def Nprime (N : ℕ) : ℕ := 3 * (N + 1)
def B0 (r : ℕ) : ℕ := 3 * (r + 1)
def mmP (r N n : ℕ) : ℕ := 5 + 3 * (r + 1) * (N + 2) * n
def Dstar (r N n : ℕ) : ℕ := 5 * (r + 1) * (N + 1) * n
def NprimeLe : Prop := ∀ N : ℕ, 1 ≤ N → Nprime N ≤ 6 * N
def ThresholdE : Prop :=
  ∀ (k r N : ℕ) (AP : ℝ), 1 ≤ k → r + 1 ≤ N →
    AP ≤ 126 * ((r : ℝ) + 1) ^ 3 * ((Nprime N : ℝ) * (nOf k r : ℝ) ^ 2 + (nOf k r : ℝ) ^ 3) →
    AP + (B0 r : ℝ) * (mmP r (Nprime N) (nOf k r) : ℝ) + 12 * ((r : ℝ) + 1) * (Nprime N : ℝ) * (nOf k r : ℝ) ≤
      915 * ((r : ℝ) + 1) ^ 3 * ((N : ℝ) * (nOf k r : ℝ) ^ 2 + (nOf k r : ℝ) ^ 3)
def DegreeCount : Prop :=
  ∀ (k r N M dl Dl : ℕ), 1 ≤ k → r + 1 ≤ N → M ≤ Nprime N → dl ≤ nOf k r →
    Dl ≤ 2 * (r + 1) + (r + 1) * (2 * r + 2) →
    2 * M * dl ≤ 2 * Nprime N * nOf k r ∧ 2 * M * Dl ≤ 6 * (r + 1) * Nprime N * nOf k r ∧
    Nprime N * nOf k r ≤ 2 * Nprime N * nOf k r ∧ 2 * Nprime N ≤ 6 * (r + 1) * Nprime N * nOf k r ∧
    2 * (r + 1) ^ 2 ≤ (r + 1) * nOf k r
def BudgetSum : Prop :=
  ∀ (r N' n d D : ℕ), d ≤ 2 * N' * n → D ≤ 6 * (r + 1) * N' * n → D + B0 r * d ≤ 12 * (r + 1) * N' * n
def LetterProductDegreeCount : Prop :=
  ∀ (k r N d D : ℕ), 1 ≤ k → d ≤ (N + 1) * nOf k r → D ≤ (N + 1) * (r + 1) * (nOf k r + 2) →
    D + 3 * (r + 1) * d ≤ 6 * (r + 1) * (N + 1) * nOf k r ∧
      6 * (r + 1) * (N + 1) * nOf k r ≤ Dstar r (Nprime N) (nOf k r)
def lamOf (n : ℕ) (a : ℕ → ℝ) (i : ℕ) : ℝ := a i + ((n : ℝ) + 1) / 2 - i
def EigenShift : Prop :=
  ∀ (k r : ℕ) (Y : ℂ) (a : ℕ → ℝ) (i : ℕ),
    Q.uC k r 0 Y - i + 1 + (a i : ℂ) = Y + (lamOf (nOf k r) a i : ℂ)
def LamInterlaces (k r : ℕ) (u : ℕ → ℝ) (lam : Fin (k + 2 * r + 1) → ℝ) : Prop :=
  StrictAnti lam ∧ ∀ i : Fin (k + 2 * r + 1),
    (i.val + 1 ≤ k → lam i < u (i.val + 1)) ∧ (i.val + 2 ≤ k → u (i.val + 2) < lam i)
def Between (u u' : ℕ → ℝ) (l : ℕ) (Y : ℝ) : Prop :=
  min (u l) (u' l) < -Y ∧ -Y < max (u l) (u' l)
def LamSide : Prop :=
  ∀ (k r : ℕ) (u u' : ℕ → ℝ) (lam : Fin (k + 2 * r + 1) → ℝ) (l : ℕ) (Y : ℝ), 1 ≤ l → l ≤ k →
    LamInterlaces k r u lam → LamInterlaces k r u' lam → Between u u' l Y →
    ∀ i : Fin (k + 2 * r + 1), (l ≤ i.val + 1 → lam i < min (u l) (u' l)) ∧
      (i.val + 1 < l → max (u l) (u' l) < lam i)
def RhoSide : Prop :=
  ∀ (k : ℕ) (u u' ρ : ℕ → ℝ) (l : ℕ) (Y : ℝ), 1 ≤ l → l ≤ k → I.Interlaces k u u' ρ → Between u u' l Y →
    ∀ i ∈ Icc 1 (k - 1), (l ≤ i → ρ i < -Y) ∧ (i < l → -Y < ρ i)
def SignCount : Prop :=
  ∀ (ι : Type) [Fintype ι] (f : ι → ℝ) (S : Finset ι), (∀ i, i ∈ S ↔ f i < 0) → (∀ i, f i ≠ 0) →
    0 < (-1 : ℝ) ^ S.card * ∏ i, f i
def PSign : Prop :=
  ∀ (k r : ℕ) (u u' ρ : ℕ → ℝ) (lam : Fin (k + 2 * r + 1) → ℝ) (l : ℕ) (Y : ℝ), 1 ≤ l → l ≤ k →
    LamInterlaces k r u lam → LamInterlaces k r u' lam → I.Interlaces k u u' ρ → Between u u' l Y →
    0 < (-1 : ℝ) ^ (k - l) * ∏ s, (Y + lam s) ∧ 0 < (-1 : ℝ) ^ (k - l) * I.xpoly k ρ Y ∧
      |∏ s, (Y + lam s)| = (-1 : ℝ) ^ (k - l) * ∏ s, (Y + lam s)
def PSignOfParts : Prop := LamSide → RhoSide → SignCount → PSign
def GGz (TT : ℝ) (ζ : ℂ) : ℝ := Complex.normSq ζ - TT
def Wz (TT : ℝ) (ζ : ℂ) : ℝ := Complex.normSq ζ / GGz TT ζ
def WInv : Prop :=
  ∀ (TT : ℝ) (ζ : ℂ), 0 < TT → 0 < GGz TT ζ →
    (((Wz TT ζ)⁻¹ : ℝ) : ℂ) = 1 - TT * (1 / conj ζ) * (1 / ζ) ∧ ‖1 / ζ‖ < (Real.sqrt TT)⁻¹
def WExact : Prop :=
  ∀ (TT : ℝ) (Dr ζ : ℂ), Dr ≠ 0 →
    Complex.normSq (Dr * ζ) / (Complex.normSq Dr * GGz TT ζ) = Wz TT ζ
def NFWeight : Prop :=
  ∀ (N : ℕ) (i i' : ℤ) (D : ℂ) (Gv c : ℝ), D ≠ 0 → 0 < Gv → 0 ≤ c → i + i' = -(N : ℤ) →
    Real.sqrt ((Complex.normSq D / Gv) ^ N * c) * ‖D ^ i * (conj D) ^ i'‖ = Gv ^ (-(N : ℝ) / 2) * Real.sqrt c
def dbar (f : ℂ → ℂ) (ζ : ℂ) : ℂ := (fderiv ℝ f ζ 1 + Complex.I * fderiv ℝ f ζ Complex.I) / 2
def DbarConjW : Prop :=
  ∀ (TT : ℝ) (N : ℕ) (f : ℂ → ℂ) (ζ : ℂ), 0 < TT → 0 < GGz TT ζ → DifferentiableAt ℝ f ζ →
    dbar (fun x => ((Wz TT x : ℝ) : ℂ) ^ N * f x) ζ =
      ((Wz TT ζ : ℝ) : ℂ) ^ N * (dbar f ζ - (N : ℂ) * TT / (conj ζ * (GGz TT ζ : ℂ)) * f ζ)
def LdLeibniz : Prop :=
  ∀ (f g : ℝ → ℝ) (p : ℕ) (x : ℝ), LE.SmoothLog f → LE.SmoothLog g →
    LE.ld p (fun y => f y * g y) x = ∑ q ∈ range (p + 1), (p.choose q : ℝ) * LE.ld q f x * LE.ld (p - q) g x
def principalHermitianLattice {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (s : ℂ) (w : List (Bool × ℝ))
    (F : B.Mat k r → (Wq →L[ℂ] Wp)) : ℂ :=
  B.beta D (w.foldr (fun a H => s • Q.CV k r (a.2 : ℂ) H) F) F
def RootsOutJoint : Prop :=
  ∀ (S : LE.Sys) (u u' : ℕ → ℝ) (l : ℕ), 1 ≤ l → l ≤ S.k →
    LamInterlaces S.k S.r u S.lam → LamInterlaces S.k S.r u' S.lam →
    (∀ Y ∈ Set.Icc S.α S.β, Between u u' l Y) → S.RootsOut
def RootsOutOfParts : Prop := LamSide → RootsOutJoint
def LemmaEInterlacing : Prop :=
  ∀ CR Cd CP : ℝ, 0 ≤ CR → 0 ≤ Cd → 0 ≤ CP →
    ∀ C₂ : ℝ, 64 * (1 + 2 * Real.exp 1 * √(LE.C7 CR Cd CP)) ≤ C₂ → ∀ C₆ : ℝ, 6 * C₂ ≤ C₆ →
    ∀ (S : LE.Sys) (u u' : ℕ → ℝ) (l : ℕ), 1 ≤ l → l ≤ S.k →
      LamInterlaces S.k S.r u S.lam → LamInterlaces S.k S.r u' S.lam →
      (∀ Y ∈ Set.Icc S.α S.β, Between u u' l Y) →
      S.r + 1 ≤ S.Ntot → S.L = C₂ * S.Ntot * ((S.r : ℝ) + 1) ^ 2 →
      C₆ * ((S.k : ℝ) * S.Ntot * ((S.r : ℝ) + 1) ^ 2 + (S.Ntot : ℝ) ^ 2 * ((S.r : ℝ) + 1) ^ 2) ≤ S.β - S.α →
      S.I1 → S.BaseDensityIntegrable → S.ThmP → S.StepImports (4 * S.Ntot) CR Cd CP → S.FamImports → S.EnergyLimit
def LemmaEInterlacingOfParts : Prop := LE.LemmaE → RootsOutJoint → LemmaEInterlacing
def DegreeCount2 : Prop :=
  ∀ (k r N M dl Dl : ℕ), 1 ≤ k → r + 1 ≤ N → M ≤ Nprime N → dl ≤ nOf k r →
    Dl ≤ (r + 1) * (2 * nOf k r + 2) →
    2 * M * dl ≤ 2 * Nprime N * nOf k r ∧ 2 * M * Dl ≤ 6 * (r + 1) * Nprime N * nOf k r ∧
    Nprime N * nOf k r ≤ 2 * Nprime N * nOf k r ∧ 2 * Nprime N ≤ 6 * (r + 1) * Nprime N * nOf k r
def LetterProductDoubleDegreeCount : Prop :=
  ∀ (k r N d D : ℕ), 1 ≤ k → d ≤ (N + 1) * nOf k r → D ≤ (N + 1) * (r + 1) * (2 * nOf k r + 2) →
    D + 3 * (r + 1) * d ≤ 6 * (r + 1) * (N + 1) * nOf k r ∧
      6 * (r + 1) * (N + 1) * nOf k r ≤ Dstar r (Nprime N) (nOf k r)
end
end Formalism.FourierDecayAlt.C7


