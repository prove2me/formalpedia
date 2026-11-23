-- Prove2me | Definitions.Def_Formalism_FlagUnipotentLattices_HeightThresholdInequalities
-- name    : Formalism_FlagUnipotentLattices_HeightThresholdInequalities
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:28:58.405607+00:00
-- url     : https://prove2.me/theorems/b01b9802-9fca-4bc1-835b-e892a81e58b0
-- title:
--   Height Threshold Inequalities
-- statement:
--   Definitions and structural lemmas for Height Threshold Inequalities, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/HeightThresholdInequalities.lean

import Definitions.Def_Formalism_FlagUnipotentLattices_FlagUnipotentLattice
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset MeasureTheory NumberField Matrix
open scoped ComplexOrder
noncomputable section
namespace Formalism.HermitianLatticeCounting.S7
open Formalism.NuclearRankWeightBounds.D (lead hs q0)
def MinorTriangular2 : Prop :=
  ∀ (N : ℕ) (c z c' : Matrix (Fin N) (Fin N) ℂ) (i : ℕ), i ≤ N →
    (∀ r s : Fin N, r < s → c r s = 0) → (∀ r s : Fin N, s < r → c' r s = 0) →
    lead (c * z * c') i = (∏ a ∈ univ.filter (fun a : Fin N => a.val < i), c a a * c' a a) * lead z i
def IntegThresh : Prop :=
  ∀ (n q : ℕ) (h r s : ℝ), 1 ≤ q → 0 < r →
    (16 * (n : ℝ) * q / r + 8 * s * Real.sqrt (2 * (q : ℝ)) / r < h ↔
      s + (n : ℝ) * Real.sqrt (2 * (q : ℝ)) < r * h / 8 / Real.sqrt (2 * (q : ℝ)))
def HeightThresholdInequalities : Prop :=
  ∀ (n q : ℕ) (h s : ℝ), 1 ≤ n → 1 ≤ q → s ≤ 9 * (n : ℝ) * q →
    120 * (n : ℝ) * (q : ℝ) ^ ((3 : ℝ) / 2) ≤ h →
    16 * (n : ℝ) * q + 8 * s * Real.sqrt (2 * (q : ℝ)) < h ∧ 16 * (n : ℝ) * (q : ℝ) ^ ((3 : ℝ) / 2) < h
def TauLipOp : Prop :=
  ∀ (K V ι : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] [AddCommGroup V]
    [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι K V) (X g : InfinitePlace K → Matrix ι ι ℂ) (r : InfinitePlace K → ℝ),
    (∀ v, IsUnit (X v).det) → (∀ v, IsUnit (g v).det) →
    (∀ v, ((Real.exp (r v) ^ 2 : ℝ) • (1 : Matrix ι ι ℂ) - (g v).conjTranspose * g v).PosSemidef) →
    ∀ L : Submodule (𝓞 K) V, L.FG → L ≠ ⊥ →
      Formalism.HN.leastSize b X L * Real.exp (-(1 / (Formalism.HN.nPl K : ℝ)) * ∑ v, r v) ≤
        Formalism.HN.leastSize b (fun v => X v * g v) L
def KappaHalf : Prop :=
  ∀ C : ℝ, 1 ≤ C → ∃ n₀ : ℕ, ∀ (n p q J a f dN : ℕ) (v res ℓ : ℝ),
    n₀ ≤ n → p + q = n → q ^ 2 ≤ n → 1 ≤ a → a ≤ J → J ≤ q → 1 ≤ f → dN ≤ 2 * J * n →
    1 / 2 ≤ v → 0 < ℓ → Real.log ℓ ≤ n → 0 ≤ res → res ≤ (C * ℓ) ^ (2 * f) →
    v ^ (-((f : ℝ) * dN / 2)) * C ^ (J * n * f) * res ^ a
        * ((C / (p : ℝ)) ^ (J * (p - J)) * (J : ℝ) ^ ((J : ℝ) ^ 2 / 2)) ^ f ≤
      Real.exp (-(1 / 2 * J * n * f * Real.log n))
def NearTotalExp : Prop :=
  ∀ c : ℝ, 0 < c → ∀ C Cg : ℝ, 1 ≤ C → 1 ≤ Cg → ∃ n₀ : ℕ,
    ∀ (n q J a f : ℕ) (rd g b : ℝ), n₀ ≤ n → q ^ 2 ≤ n → 1 ≤ a → a ≤ J → J ≤ q → 1 ≤ f →
    Real.log f ≤ Real.sqrt n → 2 ≤ b → 1 ≤ g → g ≤ b ^ Cg → 1 ≤ rd →
    Real.log (Real.log rd) ≤ n → Real.log (Real.log b) ≤ c / 8 * n * f * Real.log n →
    (2 : ℝ) ^ q * (2 * Real.exp (-(c * J * n * f * Real.log n)))
        * (C * f * (q : ℝ) ^ 2 * Real.log (Ydat n f rd g b)) ^ a ≤
      Real.exp (-(c / 2 * n * f * Real.log n))
def ProbINonzeroExp : Prop :=
  ∀ c : ℝ, 0 < c → ∃ n₀ : ℕ, ∀ (n q J f : ℕ), n₀ ≤ n → q ^ 2 ≤ n → 1 ≤ J → 1 ≤ f →
    (2 : ℝ) ^ q * Real.exp (-(c * J * n * f * Real.log n)) ≤ Real.exp (-(c / 2 * n * f * Real.log n))
open Classical in

def FarSum3 : Prop :=
  ∀ (ι Γ : Type) [Fintype ι] [Nonempty ι] (S : Finset Γ) (d : Γ → ι → ℝ) (A B h ε : ℝ) (q : ℕ),
    1 ≤ q → 0 ≤ A → 0 ≤ B → 0 < ε → ε * Real.sqrt (2 * (q : ℝ)) ≤ 1 → Real.exp (B * ε) ≤ 2 →
    32 * B ≤ h * ε → 16 ≤ h * ε ^ 2 →
    (∀ γ ∈ S, ∀ v, 0 ≤ d γ v) → (∀ γ ∈ S, ∃ v, ε < d γ v) →
    (∀ r : ι → ℝ, (∀ v, 0 ≤ r v) →
      ((S.filter fun γ => ∀ v, d γ v ≤ r v).card : ℝ) ≤ A * Real.exp (B * ∑ v, r v)) →
    ∑ γ ∈ S, ∏ v, Real.exp (-(decExp h q (d γ v))) ≤
      A * (2 * Fintype.card ι) * 3 ^ Fintype.card ι * Real.exp (-(h * ε ^ 2 / 16))
def Ch (c C₁ Cg : ℝ) : ℝ := 16 / c ^ 2 * (4 * C₁ + 6) * (Cg + 4)
def ThreshFarExp : Prop :=
  ∀ (C₁ c Cg : ℝ) (n q f : ℕ) (rd g b h : ℝ), 0 ≤ C₁ → 0 < c → 0 ≤ Cg → 1 ≤ n → 1 ≤ f → q ^ 2 ≤ n →
    Real.log f ≤ Real.sqrt n → 2 ≤ b → 1 ≤ rd → 1 ≤ g → g ≤ b ^ Cg →
    Ch c C₁ Cg * (n : ℝ) ^ 19 * (f : ℝ) ^ 5 * Real.log (b * rd) ≤ h →
    (4 * C₁ * q + 6) * ((n : ℝ) ^ 2 * f) * Real.log (Ydat n f rd g b) ≤ h * epsN c n f ^ 2 / 16
def ThreshSideExp : Prop :=
  ∀ (C₁ c Cg : ℝ) (n q f : ℕ) (rd b h : ℝ), 1 ≤ C₁ → 0 < c → c ≤ 1 → 0 ≤ Cg → 1 ≤ n → 1 ≤ f → q ^ 2 ≤ n →
    2 ≤ b → 1 ≤ rd → Ch c C₁ Cg * (n : ℝ) ^ 19 * (f : ℝ) ^ 5 * Real.log (b * rd) ≤ h →
    32 * (2 * (n : ℝ) ^ 2) ≤ h * epsN c n f ∧ 16 ≤ h * epsN c n f ^ 2 ∧
      120 * (n : ℝ) * (q : ℝ) ^ ((3 : ℝ) / 2) ≤ h ∧ 40 * (n : ℝ) ^ 2 * Real.sqrt q ≤ h ∧
      (n : ℝ) ^ 19 ≤ h / 2
def EpsSide2 : Prop :=
  ∀ (n f : ℕ) (c : ℝ), 1 ≤ n → 1 ≤ f → 0 < c → c ≤ 1 / 90000 →
    Real.exp (2 * (n : ℝ) ^ 2 * epsN c n f) ≤ 2
def FarNegligibleExp : Prop :=
  ∀ (C₁ : ℝ) (n q f : ℕ) (Y T : ℝ), 0 ≤ C₁ → 1 ≤ n → 1 ≤ f → 3 * Real.sqrt n ≤ Y →
    (4 * C₁ * q + 6) * ((n : ℝ) ^ 2 * f) * Real.log Y ≤ T →
    (3 * Real.sqrt n / (Y ^ (-(C₁ * q))) ^ 2) ^ (2 * n ^ 2 * f) * (2 * f) * 3 ^ f * Real.exp (-T) ≤
      Real.exp (-((n : ℝ) ^ 2 * f))
def CoverArith7 : Prop :=
  ∀ (n f m₁ m₂ : ℕ) (rd ρ₀ g μ₁ μS : ℝ), 1 ≤ f → 4 * m₁ ≤ n ^ 2 * f → 2 * m₂ ≤ n ^ 2 * f → 0 < rd →
    0 < ρ₀ → 0 ≤ g →
    μ₁ ≤ (m₁ : ℝ) / (2 * (Real.sqrt (2 * (f : ℝ)) / (rd * ρ₀))) →
    μS ≤ (m₂ : ℝ) / (2 * (8 * Real.sqrt f / (rd * ρ₀))) →
    2 * g * μ₁ + g * (2 * μS) ≤ (n : ℝ) ^ 2 * Real.sqrt f * g * rd * ρ₀ / 4
def beP (n P : ℕ) (b : ℝ) : ℝ := Real.sqrt n * b ^ 2 + 3 / 2 * (n : ℝ) ^ ((3 : ℝ) / 2) + 3 * P
def StepBound7 : Prop :=
  ∀ (n P : ℕ) (b L rn rho2 : ℝ), 0 ≤ L → L ≤ Real.sqrt n * b ^ 2 →
    0 ≤ rn → rn ≤ 2 * Real.sqrt ((n : ℝ) ^ 3 / 12) → rho2 ≤ (n : ℝ) ^ 3 / 12 →
    2 * (L + rn + Real.sqrt 2 * P) ^ 2 - L ^ 2 + rho2 ≤ beP n P b ^ 2
def BasisCS2 : Prop :=
  ∀ (ι H : Type) [Fintype ι] [NormedAddCommGroup H] [NormedSpace ℝ H] (c : ι → ℝ) (v : ι → H),
    ‖∑ i, c i • v i‖ ≤ Real.sqrt (∑ i, c i ^ 2) * Real.sqrt (∑ i, ‖v i‖ ^ 2)
def SobolevSum3 : Prop :=
  ∀ (m : ℕ) (s β X : ℝ) (I : Finset (Fin m) → ℝ), 0 < s → 0 ≤ β → (s * β) ^ 2 ≤ 2 → 0 ≤ X →
    (∀ S, I S ≤ β ^ (2 * S.card) * X) →
    (2 / s) ^ m * ∑ S : Finset (Fin m), s ^ (2 * S.card) * I S ≤ (6 / s) ^ m * X
def BeBound : Prop :=
  ∀ (n q f : ℕ) (b : ℝ), 1 ≤ n → 1 ≤ q → 1 ≤ f → 1 ≤ b →
    beP n (P0 n q f + n ^ 2 * f) b ≤ 30 * q * (n : ℝ) ^ 2 * f * b ^ 2
def DeepChain7 : Prop :=
  ∀ (n q f : ℕ) (rd g b τ₁ τs ρ be Kxx Bs D volG volK : ℝ), 1 ≤ n → 1 ≤ q → q ^ 2 ≤ n → 1 ≤ f →
    1 ≤ rd → 1 ≤ g → 2 ≤ b → 15 ≤ Ydat n f rd g b → 0 < τ₁ → τ₁ < τs → 0 ≤ D → 0 < volK → 0 ≤ volG →
    0 ≤ ρ → 0 ≤ be →
    ρ ≤ (n : ℝ) ^ 2 * Real.sqrt f * g * rd * (2 * τ₁) ^ ((1 : ℝ) / q) / 4 →
    be ≤ 30 * q * (n : ℝ) ^ 2 * f * b ^ 2 →
    Kxx ≤ (2 * ρ * Real.sqrt f * be) ^ (2 * P0 n q f) * Bs →
    Bs ≤ (6 * be) ^ (n ^ 2 * f) * Real.exp f * (17 * Real.sqrt n / τ₁ ^ 2) ^ (2 * n ^ 2 * f) * D / volK →
    volK⁻¹ ≤ g ^ (2 * n ^ 2 * f) → volG ≤ Ydat n f rd g b ^ (n ^ 2 * f) →
    volG * Kxx ≤ D * Ydat n f rd g b ^ ((96 * q + 17) * n ^ 2 * f) * τs ^ (12 * n ^ 2 * f)
def DeepTermExponentialBound : Prop :=
  ∀ (n q f : ℕ) (Y : ℝ), 1 ≤ q → 2 ≤ Y →
    Y ^ ((96 * q + 17) * n ^ 2 * f) * (Y ^ (-((11 : ℝ) * q))) ^ (12 * n ^ 2 * f) ≤
      Real.exp (-((n : ℝ) ^ 2 * f))
def FinalSumExp : Prop :=
  ∀ c A : ℝ, 0 < c → 0 ≤ A → ∃ n₀ : ℕ,
    ∀ (n f : ℕ) (D Ds pr E₁ E₂ : ℝ), n₀ ≤ n → 1 ≤ f → 0 ≤ D → 0 ≤ Ds → pr ≤ 1 →
    1 - Real.exp (-(c * n * f * Real.log n)) ≤ pr →
    |E₁| ≤ A * Real.exp (-(c * n * f * Real.log n)) * Ds →
    |E₂| ≤ A * Real.exp (-((n : ℝ) ^ 2 * f)) * D →
    D = Ds * pr + E₁ + E₂ →
    |D - Ds| ≤ Real.exp (-(c / 2 * n * f * Real.log n)) * Ds
def VolArith : Prop :=
  ∀ (n f : ℕ) (rd X : ℝ), 1 ≤ f → 48 ≤ n ^ 2 → 1 ≤ rd → 2 ≤ X → rd ≤ X → 2 * (f : ℝ) * rd ≤ X ^ 2 →
    (8 * Real.pi ^ 3 * (7 / 5) * 4) ^ f * rd ^ (5 * f) * (1 + (f : ℝ) * Real.log rd) ^ (5 * f)
        * rd ^ ((f : ℝ) * ((n : ℝ) ^ 2 - 4) / 2) ≤ X ^ (n ^ 2 * f)
def SkewCover : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] (S : Submodule ℤ V) (σ : V ≃ₗᵢ[ℝ] V) (μ : ℝ),
    (∀ x, σ (σ x) = x) → (∀ z ∈ S, σ z ∈ S) → (∀ x : V, ∃ y ∈ S, ‖x - y‖ ≤ μ) →
    ∀ w : V, σ w = -w → ∃ y ∈ S, σ y = -y ∧ ‖w - y‖ ≤ 2 * μ
end Formalism.HermitianLatticeCounting.S7


