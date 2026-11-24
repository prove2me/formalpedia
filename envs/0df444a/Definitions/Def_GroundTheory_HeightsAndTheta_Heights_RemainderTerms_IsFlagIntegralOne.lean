-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_IsFlagIntegralOne
-- name    : GroundTheory_HeightsAndTheta_Heights_RemainderTerms_IsFlagIntegralOne
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:09:58.680166+00:00
-- url     : https://prove2.me/theorems/34cf0604-18bf-4231-857a-500b0cf5c51d
-- title:
--   Is Flag Integral One
-- statement:
--   Definitions and structural lemmas for Is Flag Integral One, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/RemainderTerms/IsFlagIntegralOne.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KernelsRest
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.RestTerms
open MvPolynomial Matrix Real Finset
noncomputable section
def IsPart {r : ℕ} (la : Fin r → ℕ) : Prop := ∀ a b : Fin r, a ≤ b → la b ≤ la a
instance {r : ℕ} (la : Fin r → ℕ) : Decidable (IsPart la) := by
  unfold IsPart; infer_instance
def partitionsLE (r n : ℕ) : Finset (Fin r → ℕ) :=
  ((Finset.univ : Finset (Fin r → Fin (n + 1))).image fun g a => (g a : ℕ)).filter
    fun la => IsPart la ∧ ∑ a, la a = n
def shapeCells {r : ℕ} (la : Fin r → ℕ) : Finset (ℕ × ℕ) :=
  Finset.univ.biUnion fun a : Fin r => (Finset.range (la a)).image fun b => ((a : ℕ), b)
def numSYT {r : ℕ} (la : Fin r → ℕ) : ℕ :=
  Nat.card {T : shapeCells la ≃ Fin (shapeCells la).card // Monotone T}
def hAt (m : ℕ) (e : ℤ) : MvPolynomial (Fin m) ℚ :=
  if 0 ≤ e then hsymm (Fin m) ℚ e.toNat else 0
def schurPoly (m : ℕ) {r : ℕ} (la : Fin r → ℕ) : MvPolynomial (Fin m) ℚ :=
  (Matrix.of fun a b : Fin r => hAt m ((la a : ℤ) - a + b)).det
def staircase (r : ℕ) : Fin r → ℕ := fun a => r - 1 - a
def frobChar {r : ℕ} (la : Fin r → ℕ) (q m : ℕ) : ℚ :=
  coeff (Finsupp.equivFunOnFinite.symm (la + staircase r))
    (psum (Fin r) ℚ q * psum (Fin r) ℚ 1 ^ m * alternant (staircase r))
def hookShape (k b : ℕ) : Fin (b + 1) → ℕ := fun a => if (a : ℕ) = 0 then k - b else 1
def IsHook {m : ℕ} (nu : Fin m → ℕ) : Prop := ∀ a : Fin m, 1 ≤ (a : ℕ) → nu a ≤ 1
def topVarQ (j k : ℕ) : Fin j → MvPolynomial (Fin (j + k)) ℚ := fun a => X (Fin.castAdd k a)
def botVarQ (j k : ℕ) : Fin k → MvPolynomial (Fin (j + k)) ℚ := fun b => X (Fin.natAdd j b)
def FrobeniusFormula.Statement : Prop :=
  ∀ (r : ℕ) (la : Fin r → ℕ), IsPart la →
    (numSYT la : ℚ) = frobDim la ∧
      (1 ≤ ∑ a, la a → (numSYT la : ℚ) = frobChar la 1 (∑ a, la a - 1))
def RectangleBound.Statement : Prop :=
  ∀ (r s : ℕ) (nu : Fin r → ℕ), IsPart nu →
    numSYT (fun a => s + nu a) ≤
      (r * s + ∑ a, nu a).choose (∑ a, nu a) * numSYT (fun _ : Fin r => s) * numSYT nu
def HookPowerSum.Statement : Prop :=
  ∀ (N k : ℕ), 1 ≤ k → k ≤ N → ∀ nu : Fin N → ℕ, IsPart nu → ∑ a, nu a = k →
    ∃ (c : ℚ) (R : MvPolynomial (Fin (k - 1)) ℚ),
      schurPoly N nu = c • psum (Fin N) ℚ k +
          aeval (fun i : Fin (k - 1) => psum (Fin N) ℚ ((i : ℕ) + 1)) R ∧
        (IsHook nu → c = 1 / k ∨ c = -1 / k) ∧ (¬ IsHook nu → c = 0)
def HookCount.Statement : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∑ b ∈ Finset.range k, numSYT (hookShape k b) = 2 ^ (k - 1)
def PowerSumExpansion.Statement : Prop :=
  ∀ (r q m : ℕ), 1 ≤ q →
    psum (Fin r) ℚ q * psum (Fin r) ℚ 1 ^ m =
        ∑ la ∈ partitionsLE r (q + m), frobChar la q m • schurPoly r la ∧
      ∀ la ∈ partitionsLE r (q + m), |frobChar la q m| ≤ numSYT la
def PushBottom.Statement : Prop :=
  ∀ j k : ℕ, ∃ κ : ℚ, (κ = k.factorial * j.factorial ∨ κ = -(k.factorial * j.factorial)) ∧
    ∀ la : Fin k → ℕ, IsPart la →
      antisym (aeval (botVarQ j k) (schurPoly k la) * vandermonde (botVarQ j k) *
          vandermonde (topVarQ j k)) =
        if ∀ b, j ≤ la b then
          κ • (schurPoly (j + k) (fun b => la b - j) *
            vandermonde (fun i : Fin (j + k) => (X i : MvPolynomial (Fin (j + k)) ℚ)))
        else 0
def PushTop.Statement : Prop :=
  ∀ j k : ℕ, ∃ κ : ℚ, (κ = j.factorial * k.factorial ∨ κ = -(j.factorial * k.factorial)) ∧
    ∀ la : Fin j → ℕ, IsPart la →
      antisym (aeval (fun a => -topVarQ j k a) (schurPoly j la) *
          vandermonde (fun a => -topVarQ j k a) * vandermonde (botVarQ j k)) =
        if ∀ a, k ≤ la a then
          κ • (aeval (fun i : Fin (j + k) => -(X i : MvPolynomial (Fin (j + k)) ℚ))
              (schurPoly (j + k) (fun a => la a - k)) *
            vandermonde (fun i : Fin (j + k) => (X i : MvPolynomial (Fin (j + k)) ℚ)))
        else 0
def ShiftIdentity.Statement : Prop :=
  ∀ j r : ℕ, 1 ≤ r → r ≤ j →
    (j : ℚ) * numSYT (fun a : Fin r => j + if (a : ℕ) = 0 then 1 else 0) =
      ∑ m ∈ Finset.Icc 2 (j + r), ∑ b ∈ Finset.range (min m r),
        (-1 : ℚ) ^ b * frobChar (fun a : Fin r =>
            j + if (a : ℕ) = 0 then m - b else if (a : ℕ) ≤ b then 1 else 0)
          (m - 1) (r * j + 1)
def TotalIdentity.Statement : Prop :=
  ∀ j r : ℕ, 1 ≤ r → r ≤ j →
    (j + r) * numSYT (fun a : Fin r => j + if (a : ℕ) = 0 then 1 else 0) =
      (r * j + 1) * r * numSYT (fun _ : Fin r => j)
abbrev Roots (f j k : ℕ) : Type := MvPolynomial (Fin f × Fin (j + k)) ℝ
variable (f j k : ℕ)
def dimFl : ℕ := f * ((j + k) * (j + k - 1) / 2)
def nDim : ℕ := f * j * k
def bigX : ℝ := 2 * ((j * k : ℕ) + (j + k : ℕ))
def psumAt (m : ℕ) (τ : Fin f) : Roots f j k := ∑ i, X (τ, i) ^ m
def lieClass (m : ℕ) (σ : Fin f × Bool) : Roots f j k :=
  if σ.2 then (-1) ^ m * ∑ b : Fin k, X (σ.1, Fin.natAdd j b) ^ m
  else ∑ a : Fin j, X (σ.1, Fin.castAdd k a) ^ m
def IsSmallBlock (bot : Bool) : Prop := (bot = true → k ≤ j) ∧ (bot = false → j ≤ k)
def smallPsum (bot : Bool) (m : ℕ) (τ : Fin f) : Roots f j k :=
  if bot then ∑ b : Fin k, X (τ, Fin.natAdd j b) ^ m
  else ∑ a : Fin j, (-X (τ, Fin.castAdd k a)) ^ m
def muClass (bot : Bool) : Roots f j k := ∑ τ, smallPsum f j k bot 1 τ
def fibClass (bot : Bool) : Roots f j k :=
  ∏ τ : Fin f, if bot then
      vandermonde (fun b : Fin k => (X (τ, Fin.natAdd j b) : Roots f j k)) *
        vandermonde (fun a : Fin j => (X (τ, Fin.castAdd k a) : Roots f j k))
    else
      vandermonde (fun a : Fin j => -(X (τ, Fin.castAdd k a) : Roots f j k)) *
        vandermonde (fun b : Fin k => (X (τ, Fin.natAdd j b) : Roots f j k))
def restPoly (bot : Bool) : Roots f j k := muClass f j k bot ^ (nDim f j k + 1) * fibClass f j k bot
def degPoly (bot : Bool) : Roots f j k := muClass f j k bot ^ nDim f j k * fibClass f j k bot
structure IsFlagIntegral (I : Roots f j k →ₗ[ℝ] ℝ) : Prop where
  kills : ∀ (m : ℕ) (τ : Fin f) (G : Roots f j k), 1 ≤ m → m ≤ dimFl f j k →
    G.IsHomogeneous (dimFl f j k - m) → I (psumAt f j k m τ * G) = 0
  ne_zero : ∃ G : Roots f j k, G.IsHomogeneous (dimFl f j k) ∧ I G ≠ 0
def IsPsumDecomp (F : Roots f j k) (Q : Fin f → ℕ → Roots f j k) : Prop :=
  (∀ τ m, 1 ≤ m → m ≤ j + k → (Q τ m).IsHomogeneous (dimFl f j k + 1 - m)) ∧
    F = ∑ τ : Fin f, ∑ m ∈ Finset.Icc 1 (j + k), psumAt f j k m τ * Q τ m
def blockAntisym : Roots f j k →ₗ[ℝ] Roots f j k :=
  ∑ w : Fin f → Equiv.Perm (Fin (j + k)),
    (((∏ τ, (Equiv.Perm.sign (w τ) : ℤ) : ℤ) : ℝ)) •
      (rename (Equiv.prodCongrRight w)).toLinearMap
def rhoMon : (Fin f × Fin (j + k)) →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun v => j + k - 1 - (v.2 : ℕ)
def ddConst : Roots f j k →ₗ[ℝ] ℝ := (lcoeff ℝ (rhoMon f j k)).comp (blockAntisym f j k)
def blockVdm : Roots f j k := ∏ τ : Fin f, vandermonde fun i : Fin (j + k) => (X (τ, i) : Roots f j k)
def onlyBlock (τ : Fin f) : Roots f j k →ₐ[ℝ] Roots f j k :=
  bind₁ fun v => if v.1 = τ then X v else 0
def primesOver (P : Set ℕ) (B₀ : ℝ) : Type := {p : ℕ // p ∈ P ∧ p.Prime ∧ B₀ < p}
def restTerm (I : Roots f j k →ₗ[ℝ] ℝ) (σ : ℕ → ℕ → Fin f → Fin f × Bool)
    (Q : Fin f → ℕ → Roots f j k) (p : ℕ) (τ : Fin f) (m n : ℕ) : ℝ :=
  ((p : ℝ) ^ ((n + 1) * m))⁻¹ * m * I (lieClass f j k (m - 1) (σ p (n + 1) τ) * Q τ m)
def restAt (I : Roots f j k →ₗ[ℝ] ℝ) (vol : ℝ) (σ : ℕ → ℕ → Fin f → Fin f × Bool)
    (Q : Fin f → ℕ → Roots f j k) (p : ℕ) : ℝ :=
  Real.log p * vol * ∑ τ : Fin f, ∑ m ∈ Finset.Icc 2 (j + k), ∑' n : ℕ, restTerm f j k I σ Q p τ m n
def shiftAt (I : Roots f j k →ₗ[ℝ] ℝ) (τ : Fin f) (F : Roots f j k) : ℝ :=
  I (∑ a : Fin j, pderiv (τ, Fin.castAdd k a) F)
def totalAt (I : Roots f j k →ₗ[ℝ] ℝ) (τ : Fin f) (F : Roots f j k) : ℝ :=
  I (∑ i : Fin (j + k), pderiv (τ, i) F)
def DividedDifference.Statement : Prop :=
  ∀ f j k : ℕ, 1 ≤ f → 1 ≤ j → 1 ≤ k →
    IsFlagIntegral f j k (ddConst f j k) ∧
      ddConst f j k (blockVdm f j k) = ((j + k).factorial : ℝ) ^ f
def FlagIntegralProportional.Statement : Prop :=
  ∀ f j k : ℕ, 1 ≤ f → 1 ≤ j → 1 ≤ k → ∀ I : Roots f j k →ₗ[ℝ] ℝ, IsFlagIntegral f j k I →
    ∃ c : ℝ, c ≠ 0 ∧ ∀ G : Roots f j k, G.IsHomogeneous (dimFl f j k) → I G = c * ddConst f j k G
def Extraction.Statement : Prop :=
  ∀ f j k : ℕ, ∀ (I : Roots f j k →ₗ[ℝ] ℝ) (c : ℝ),
    (∀ H : Roots f j k, H.IsHomogeneous (dimFl f j k) → I H = c * ddConst f j k H) →
    ∀ (F : Roots f j k) (Q : Fin f → ℕ → Roots f j k), IsPsumDecomp f j k F Q →
    ∀ (τ : Fin f) (m : ℕ), 1 ≤ m → m ≤ j + k → ∀ G : Roots f j k, G.IsHomogeneous (m - 1) →
      ∃ P : Roots f j k, blockAntisym f j k (G * F) = P * blockVdm f j k ∧
        ∃ (a : ℝ) (R : MvPolynomial (Fin (m - 1)) ℝ),
          onlyBlock f j k τ P = a • psumAt f j k m τ +
              aeval (fun i : Fin (m - 1) => psumAt f j k ((i : ℕ) + 1) τ) R ∧
            I (G * Q τ m) = c * a
def LieReduction.Statement : Prop :=
  ∀ f j k : ℕ, 1 ≤ f → 1 ≤ j → 1 ≤ k → ∀ bot : Bool,
    ∀ I : Roots f j k →ₗ[ℝ] ℝ, IsFlagIntegral f j k I →
    ∀ Q : Fin f → ℕ → Roots f j k,
      (∀ τ m, 1 ≤ m → m ≤ j + k → (Q τ m).IsHomogeneous (dimFl f j k + 1 - m)) →
    ∀ (σ : Fin f × Bool) (τ : Fin f) (m : ℕ), 2 ≤ m → m ≤ j + k →
      I (lieClass f j k (m - 1) σ * Q τ m) = I (smallPsum f j k bot (m - 1) σ.1 * Q τ m) ∨
        I (lieClass f j k (m - 1) σ * Q τ m) = -I (smallPsum f j k bot (m - 1) σ.1 * Q τ m)
def DegreeValue.Statement : Prop :=
  ∀ f j k : ℕ, 1 ≤ f → 1 ≤ j → 1 ≤ k → ∀ bot : Bool, IsSmallBlock j k bot →
    |ddConst f j k (degPoly f j k bot)| =
      ((j.factorial * k.factorial : ℕ) : ℝ) ^ f * ((nDim f j k).factorial : ℝ) /
          ((j * k).factorial : ℝ) ^ f *
        ((if bot then numSYT (fun _ : Fin k => j) else numSYT (fun _ : Fin j => k) : ℕ) : ℝ) ^ f
def TermBound.Statement : Prop :=
  ∀ f j k : ℕ, 1 ≤ f → 1 ≤ j → 1 ≤ k → ∀ bot : Bool, IsSmallBlock j k bot →
    ∀ I : Roots f j k →ₗ[ℝ] ℝ, IsFlagIntegral f j k I →
    ∀ Q : Fin f → ℕ → Roots f j k, IsPsumDecomp f j k (restPoly f j k bot) Q →
    ∀ (τ τ' : Fin f) (m : ℕ), 2 ≤ m → m ≤ j + k →
      |(m : ℝ) * I (smallPsum f j k bot (m - 1) τ' * Q τ m)| ≤
        ((nDim f j k : ℝ) + 1) * |I (degPoly f j k bot)| * bigX j k ^ (m - 1) / (m.factorial : ℝ)
def TwoCases.Statement : Prop :=
  ∀ f j k : ℕ, ∀ (I : Roots f j k →ₗ[ℝ] ℝ) (τ : Fin f),
    (shiftAt f j k I τ (restPoly f j k true) = 0 ∧
      totalAt f j k I τ (restPoly f j k true) =
        ((nDim f j k : ℝ) + 1) * k * I (degPoly f j k true)) ∧
    (shiftAt f j k I τ (restPoly f j k false) =
        -(((nDim f j k : ℝ) + 1) * j * I (degPoly f j k false)) ∧
      totalAt f j k I τ (restPoly f j k false) =
        -(((nDim f j k : ℝ) + 1) * j * I (degPoly f j k false)))
def GeometricTail.Statement : Prop :=
  ∀ (p : ℝ) (m : ℕ), 2 ≤ p → 1 ≤ m →
    Summable (fun n : ℕ => (p ^ ((n + 1) * m))⁻¹) ∧
      ∑' n : ℕ, (p ^ ((n + 1) * m))⁻¹ ≤ 2 * (p ^ m)⁻¹
def ExpSeriesBound.Statement : Prop :=
  ∀ X p : ℝ, 0 ≤ X → 0 < p → X ≤ 3 / 8 * p →
    Summable (fun m : ℕ => 2 * (p ^ (m + 2))⁻¹ * X ^ (m + 1) / ((m + 2).factorial : ℝ)) ∧
      ∑' m : ℕ, 2 * (p ^ (m + 2))⁻¹ * X ^ (m + 1) / ((m + 2).factorial : ℝ) ≤ 1.5 * X / p ^ 2
def PrimeTail.Statement : Prop :=
  ∀ B : ℝ, 0 < B →
    Summable (fun p : {p : ℕ // p.Prime ∧ B < p} => Real.log p.1 / (p.1 : ℝ) ^ 2) ∧
      ∑' p : {p : ℕ // p.Prime ∧ B < p}, Real.log p.1 / (p.1 : ℝ) ^ 2 ≤ 2 * Real.log 4 / B
def IntegerTail.Statement : Prop :=
  ∀ B : ℝ, 1 ≤ B →
    Summable (fun m : {m : ℕ // B < m} => Real.log m.1 / (m.1 : ℝ) ^ 2) ∧
      ∑' m : {m : ℕ // B < m}, Real.log m.1 / (m.1 : ℝ) ^ 2 ≤ 2 * (1 + Real.log B) / B
def RestAtBound.Statement : Prop :=
  ∀ f j k : ℕ, 1 ≤ f → 1 ≤ j → 1 ≤ k → ∀ bot : Bool, IsSmallBlock j k bot →
    ∀ I : Roots f j k →ₗ[ℝ] ℝ, IsFlagIntegral f j k I →
    ∀ vol : ℝ, 0 < vol → ∀ B₀ : ℝ, 4 * f * ((j + k : ℕ) : ℝ) ^ 2 ≤ B₀ →
    ∀ σ : ℕ → ℕ → Fin f → Fin f × Bool,
    ∀ Q : Fin f → ℕ → Roots f j k, IsPsumDecomp f j k (restPoly f j k bot) Q →
    ∀ p : ℕ, p.Prime → B₀ < p →
      (∀ (τ : Fin f) (m : ℕ), Summable (restTerm f j k I σ Q p τ m)) ∧
        |restAt f j k I vol σ Q p| ≤
          1.5 * f * bigX j k * (Real.log p / (p : ℝ) ^ 2) * ((nDim f j k : ℝ) + 1) * vol *
            |I (degPoly f j k bot)|
def RestBound.Statement : Prop :=
  ∀ f j k : ℕ, 1 ≤ f → 1 ≤ j → 1 ≤ k → ∀ bot : Bool, IsSmallBlock j k bot →
    ∀ I : Roots f j k →ₗ[ℝ] ℝ, IsFlagIntegral f j k I →
    ∀ vol : ℝ, 0 < vol → ∀ P : Set ℕ, (∀ p ∈ P, p.Prime) →
    ∀ B₀ : ℝ, 4 * f * ((j + k : ℕ) : ℝ) ^ 2 ≤ B₀ →
    ∀ σ : ℕ → ℕ → Fin f → Fin f × Bool,
    ∀ Q : Fin f → ℕ → Roots f j k, IsPsumDecomp f j k (restPoly f j k bot) Q →
      Summable (fun p : primesOver P B₀ => restAt f j k I vol σ Q p.1) ∧
        |∑' p : primesOver P B₀, restAt f j k I vol σ Q p.1| ≤
          1.6 * ((nDim f j k : ℝ) + 1) * vol * |I (degPoly f j k bot)|
def RestBoundIntegers.Statement : Prop :=
  ∀ f j k : ℕ, 1 ≤ f → 1 ≤ j → 1 ≤ k → ∀ bot : Bool, IsSmallBlock j k bot →
    ∀ I : Roots f j k →ₗ[ℝ] ℝ, IsFlagIntegral f j k I →
    ∀ vol : ℝ, 0 < vol → ∀ P : Set ℕ, (∀ p ∈ P, p.Prime) →
    ∀ B₀ : ℝ, 4 * f * ((j + k : ℕ) : ℝ) ^ 2 ≤ B₀ →
    ∀ σ : ℕ → ℕ → Fin f → Fin f × Bool,
    ∀ Q : Fin f → ℕ → Roots f j k, IsPsumDecomp f j k (restPoly f j k bot) Q →
      Summable (fun p : primesOver P B₀ => restAt f j k I vol σ Q p.1) ∧
        |∑' p : primesOver P B₀, restAt f j k I vol σ Q p.1| ≤
          2 * (1 + Real.log B₀) * ((nDim f j k : ℝ) + 1) * vol * |I (degPoly f j k bot)|
def PluckerHeight.Statement : Prop :=
  ∀ (a b : ℕ) (Z : Matrix (Fin a) (Fin b) ℂ), (∀ i l, ∃ m : ℕ, 0 < m ∧ Z i l ^ m = 1) →
    (∑ S : {S : Finset (Fin (a + b)) // S.card = a},
        ‖((Matrix.of fun i : Fin a => Fin.append (fun l : Fin a => if i = l then (1 : ℂ) else 0)
            (Z i)).submatrix id (S.1.orderEmbOfFin S.2)).det‖ ^ 2 =
      (1 + Z * Zᴴ).det.re) ∧
    (1 + Z * Zᴴ).det.im = 0 ∧ 0 < (1 + Z * Zᴴ).det.re ∧
    1 / 2 * Real.log (1 + Z * Zᴴ).det.re ≤ a / 2 * Real.log (1 + b)
def SmallBlockInequality.Statement : Prop :=
  ∀ kk m ff j' : ℕ, 2 ≤ m → m ^ 4 ≤ ff → ff ≤ kk → j' ≤ m →
    2 * m + 2 ≤ kk ∧ 3 * j' ≤ kk + m - 1 - 1
def WeakDegreeInsufficient.Statement : Prop :=
  ¬ ∀ kk m j' : ℕ, 2 ≤ m → m + 3 ≤ kk → j' ≤ m → 3 * j' ≤ kk + m - 1 - 1
def flagIntegralOne : Roots 1 1 1 →ₗ[ℝ] ℝ :=
  lcoeff ℝ (Finsupp.single ((0 : Fin 1), (0 : Fin (1 + 1))) 1) -
    lcoeff ℝ (Finsupp.single ((0 : Fin 1), (1 : Fin (1 + 1))) 1)
def decompOne : Fin 1 → ℕ → Roots 1 1 1 := fun _ m =>
  if m = 1 then C (1 / 2) * X ((0 : Fin 1), (1 : Fin (1 + 1))) +
      C (-1 / 2) * X ((0 : Fin 1), (0 : Fin (1 + 1)))
  else if m = 2 then C (1 / 2) else 0
example : (0 : ℝ) < 1 ∧ (∀ p ∈ {p : ℕ | p.Prime}, p.Prime) ∧
    4 * ((1 : ℕ) : ℝ) * ((1 + 1 : ℕ) : ℝ) ^ 2 ≤ 16 :=
  ⟨one_pos, fun _ h => h, by norm_num⟩
example : IsPart (![2, 1] : Fin 2 → ℕ) := by decide
example : ∀ i l, ∃ m : ℕ, 0 < m ∧ (Matrix.of fun (_ : Fin 1) (_ : Fin 2) => (1 : ℂ)) i l ^ m = 1 :=
  fun _ _ => ⟨1, one_pos, by simp⟩
example : 2 ≤ 2 ∧ 2 ^ 4 ≤ 16 ∧ 16 ≤ 16 ∧ 2 ≤ 2 := by decide
end
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.RestTerms


