-- Prove2me | Definitions.Def_Formalism_FlagUnipotentLattices_BlockDistFromLows
-- name    : Formalism_FlagUnipotentLattices_BlockDistFromLows
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:34:40.555276+00:00
-- url     : https://prove2.me/theorems/e15804c1-d24e-49f2-8537-56fbd6ee3161
-- title:
--   Block Dist From Lows
-- statement:
--   Definitions and structural lemmas for Block Dist From Lows, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/BlockDistFromLows.lean

import Definitions.Def_Formalism_FlagUnipotentLattices_QDetNegTranspose
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset MeasureTheory Filter Topology TensorProduct
noncomputable section
namespace Formalism.HermitianLatticeCounting.S8
def SoftVanish : Prop :=
  ∀ (X O : Type) [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X] [SecondCountableTopology X]
    [TopologicalSpace O] [LocallyCompactSpace O] [MeasurableSpace O] [BorelSpace O] (μ : Measure O)
    [μ.IsOpenPosMeasure] (ι : O → X) (𝒜 : Set (X → ℂ)) (c : O → ℂ),
    Continuous ι → Function.Injective ι → Continuous c →
    (∀ β ∈ 𝒜, Continuous β ∧ HasCompactSupport β) →
    (∀ β ∈ 𝒜, ∀ β' ∈ 𝒜, (fun x => β x * β' x) ∈ 𝒜) →
    (∀ β ∈ 𝒜, (fun x => star (β x)) ∈ 𝒜) →
    (∀ x y : X, x ≠ y → ∃ β ∈ 𝒜, β x ≠ β y) →
    (∀ C : Set X, IsCompact C → ∃ β ∈ 𝒜, ∀ x ∈ C, β x = 1) →
    (∀ β ∈ 𝒜, Integrable (fun h => β (ι h) * c h) μ) →
    (∀ β ∈ 𝒜, ∫ h, β (ι h) * c h ∂μ = 0) →
    c = 0
def SoftNonzero : Prop :=
  ∀ (X O : Type) [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X] [SecondCountableTopology X]
    [TopologicalSpace O] [LocallyCompactSpace O] [MeasurableSpace O] [BorelSpace O] (μ : Measure O)
    [μ.IsOpenPosMeasure] (ι : O → X) (𝒜 : Set (X → ℂ)) (c : O → ℂ) (h₀ : O),
    Continuous ι → Function.Injective ι → Continuous c →
    (∀ β ∈ 𝒜, Continuous β ∧ HasCompactSupport β) →
    (∀ β ∈ 𝒜, ∀ β' ∈ 𝒜, (fun x => β x * β' x) ∈ 𝒜) →
    (∀ β ∈ 𝒜, (fun x => star (β x)) ∈ 𝒜) →
    (∀ x y : X, x ≠ y → ∃ β ∈ 𝒜, β x ≠ β y) →
    (∀ C : Set X, IsCompact C → ∃ β ∈ 𝒜, ∀ x ∈ C, β x = 1) →
    (∀ β ∈ 𝒜, Integrable (fun h => β (ι h) * c h) μ) →
    c h₀ ≠ 0 → ∃ β ∈ 𝒜, ∫ h, β (ι h) * c h ∂μ ≠ 0
def EIdempotent : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] (G : Type) [Group G]
    [MeasurableSpace G] (μ : Measure G) (ρ : G →* (E →L[ℂ] E)) (d : ℝ),
    (∀ g, ρ g ∈ unitary (E →L[ℂ] E)) → d ≠ 0 →
    (∀ a b c b' : E, ∫ g, (inner ℂ b (ρ g a) : ℂ) * star (inner ℂ b' (ρ g c) : ℂ) ∂μ =
      (d : ℂ)⁻¹ * (inner ℂ c a : ℂ) * star (inner ℂ b' b : ℂ)) →
    ∀ w : E, ‖w‖ = 1 →
      (∀ x : G, ∫ g, ((d : ℂ) * star (inner ℂ w (ρ g w) : ℂ)) * ((d : ℂ) * star (inner ℂ w (ρ (g⁻¹ * x) w) : ℂ)) ∂μ =
        (d : ℂ) * star (inner ℂ w (ρ x w) : ℂ)) ∧
      (∀ y : E, ∫ g, ((d : ℂ) * star (inner ℂ w (ρ g w) : ℂ)) * (inner ℂ y (ρ g w) : ℂ) ∂μ = (inner ℂ y w : ℂ)) ∧
      (∀ g x : G, ∫ y, ((d : ℂ) * star (inner ℂ w (ρ y w) : ℂ)) *
          ((d : ℂ) * star (inner ℂ w (ρ (g⁻¹ * y⁻¹ * x) w) : ℂ)) ∂μ =
        (inner ℂ w (ρ g w) : ℂ) * ((d : ℂ) * star (inner ℂ w (ρ x w) : ℂ)))
def PsiInvert : Prop :=
  ∀ (V U : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup U] [Module ℂ U] (n r k : ℕ) (c w : ℕ → Fin n)
    (E : Fin n → Fin n → Module.End ℂ V) (π : Fin k → Fin k → Module.End ℂ U) (d : ℕ → ℂ) (ℓ : V →ₗ[ℂ] U)
    (A : Module.End ℂ V) (ε : Fin n → ℂ),
    ChainLabel r k c w → ChainEquivariant r k c w E π d ℓ →
    (∀ i ≤ 2 * r, ε (c i) = (-1) ^ (r + i)) → (∀ s < k, ε (w s) = 1) →
    (∀ a b v, A (E a b v) = (ε a * ε b) • E a b (A v)) →
    ChainEquivariant r k c w E π (fun j => -d j) (ℓ ∘ₗ A)
def BlockDistFromLows : Prop :=
  ∀ (m t : ℕ) (b e : ℕ → ℝ),
    (∀ i < m, b i < e i) → (∀ i, i + 1 < m → e i < b (i + 1)) →
    (∀ i < m, ∀ j < m, ((t : ℝ) + 3) / 2 ≤ |b i - e j|) →
    ∀ i < m, ∀ j < m, i ≠ j → (t : ℝ) + 3 ≤ |e i - e j| ∧
      ∀ len ≤ t + 1, ∀ x ∈ blockP (-e i) len, (t : ℝ) / 2 + 3 ≤ |x + e j|
def Mrk (k m t : ℕ) : ℝ := ((k + m - 1 : ℕ) : ℝ) + (m : ℝ) * t
def GArith : Prop :=
  ∀ k m t : ℕ, 1 ≤ k → Even m → 2 ≤ m → (k + m - 1) + 5 ≤ t →
    (m : ℝ) * ((m : ℝ) + 6) ≤ Mrk k m t ∧
    (∀ n q₀ : ℝ, 0 ≤ n → n ≤ Mrk k m t → 0 ≤ q₀ → q₀ ≤ (m : ℝ) / 2 →
      120 * n * (q₀ * Real.sqrt q₀) < Mrk k m t ^ 3 ∧ 16 * n * (q₀ * Real.sqrt q₀) ≤ 2 * Mrk k m t ^ 3) ∧
    (Even k → Odd t → 20 * Real.sqrt ((m : ℝ) / 2) ≤ Mrk k m t ∧
      ∀ n q₀ : ℝ, 0 ≤ n → n ≤ Mrk k m t → 0 ≤ q₀ → q₀ ≤ (m : ℝ) / 2 →
        40 * n ^ 2 * Real.sqrt q₀ ≤ 2 * Mrk k m t ^ 3)
def DSArgs : Prop :=
  ∀ a t' i : ℕ, 1 ≤ t' → i < a → (t' : ℝ) + 1 ≤ (a : ℝ) + t' - i ∧ (2 : ℝ) ≤ (a : ℝ) + t' - i
def paramPi (t j : ℕ) (u : List ℝ) (e : ℕ → ℝ) : List ℝ :=
  u ++ (List.range j).flatMap (fun i => blockP (-e i) (t + 1))
def ParamPiCoset : Prop :=
  ∀ (k t j : ℕ) (u : List ℝ) (e : ℕ → ℝ), Odd t →
    (∀ x ∈ u, ∃ z : ℤ, x = (z : ℝ) + ((k : ℝ) - 1) / 2) → (∀ i < j, ∃ z : ℤ, e i = (z : ℝ) + (k : ℝ) / 2) →
    ∀ x ∈ paramPi t j u e, ∃ z : ℤ, x - ((dimX k t j : ℝ) - 1) / 2 = (z : ℝ)
def CompactPairRange : Prop :=
  ∀ (k m t j : ℕ) (u : List ℝ) (b e : ℕ → ℝ), Odd t → j < m → (∀ x ∈ u, -b 0 < x) →
    (∀ i < m, b i < e i) → (∀ i, i + 1 < m → e i < b (i + 1)) →
    (∀ i < m, ∀ i' < m, ((t : ℝ) + 3) / 2 ≤ |b i' - e i|) →
    (∀ x ∈ u, ∃ z : ℤ, x = (z : ℝ) + ((k : ℝ) - 1) / 2) → (∀ i < m, ∃ z : ℤ, e i = (z : ℝ) + (k : ℝ) / 2) →
    ∀ x ∈ paramPi t j u e, -e j + ((t : ℝ) + 2) / 2 ≤ x ∧ ∃ z : ℤ, x - (-e j + ((t : ℝ) + 2) / 2) = (z : ℝ)
def CentreInt : Prop :=
  ∀ (k : ℕ) (e : ℝ), Even k → (∃ z : ℤ, e = (z : ℝ) + (k : ℝ) / 2) → ∃ z : ℤ, e = (z : ℝ)
def kCh (k : ℕ) (t : ℕ → ℕ) : ℕ → ℕ
  | 0 => k
  | j + 1 => kCh k t j + t j + 1
def BaseRank : Prop :=
  ∀ (k m : ℕ) (t : ℕ → ℕ), 1 ≤ k → 1 ≤ m → (∀ j, 1 ≤ t j) →
    (∀ j ≤ m, (k + m - 1 + ∑ i ∈ Finset.range j, t i) + (j + 1) = kCh k t j + m) ∧
    (∀ j ≤ m, k + m - 1 + ∑ i ∈ Finset.range j, t i ≤ kCh k t m - 1)
def BaseExplicit : Prop :=
  ∀ (k m : ℕ) (t : ℕ → ℕ), Even k → 2 ≤ k → Even m → 2 ≤ m → (∀ j, t j = kCh k t j + 1) →
    (∀ j, kCh k t j + 2 = 2 ^ j * (k + 2)) ∧
    (∀ j, Even (kCh k t j) ∧ Odd (t j) ∧ 2 * kCh k t j < kCh k t (j + 1) ∧ t j < t (j + 1)) ∧
    kCh k t m + 2 = 2 ^ m * (k + 2) ∧ 13 ≤ kCh k t m - 1 ∧
    120 * ((m : ℝ) / 2 * Real.sqrt ((m : ℝ) / 2)) < ((kCh k t m : ℝ) - 1) ^ 2 ∧
    (∀ j, ((t j : ℝ) + 2) / 2 - ((kCh k t j : ℝ) - 1) / 2 = 2)
def sgnDV (k m : ℕ) (t : ℕ → ℕ) (j : ℕ) : List Bool :=
  List.replicate (k - 1 + (j + 1) + ∑ i ∈ Finset.range j, t i) true ++
    (List.range (m - j - 1)).map (fun i => decide (i % 2 = 1))
def paramDV (t : ℕ → ℕ) (j m : ℕ) (v : List ℝ) (b e : ℕ → ℝ) : List ℝ :=
  v ++ (List.range m).flatMap (fun i => -b i :: if i < j then blockP (-e i) (t i) else [])
def VConst : Prop :=
  ∀ (k m t j : ℕ) (v : List ℝ) (b e : ℕ → ℝ),
    sgnDV k m (fun _ => t) j = sgnD k m t j ∧ paramDV (fun _ => t) j m v b e = paramD t j m v b e
def ParamDChainV : Prop :=
  ∀ (k m j : ℕ) (t : ℕ → ℕ) (u v : List ℝ) (b e : ℕ → ℝ),
    1 ≤ k → j < m → Interlaces u v → u.length = k → (∀ x ∈ u, -b 0 < x) →
    (∀ i < m, b i < e i) → (∀ i, i + 1 < m → e i < b (i + 1)) →
    (∀ i < m, ∀ i' < m, ((t i : ℝ) + 1) / 2 ≤ |b i' - e i|) →
    (paramDV t j m v b e).IsChain (· > ·) ∧ (paramDV t j m v b e).length = (sgnDV k m t j).length ∧
      (sgnDV k m t j).length = k + m - 1 + ∑ i ∈ Finset.range j, t i
def GapDV : Prop :=
  ∀ (k m j : ℕ) (t : ℕ → ℕ) (h : ℝ) (u v : List ℝ) (b e : ℕ → ℝ),
    1 ≤ k → j < m → Interlaces u v → u.length = k → (∀ x ∈ u, -b 0 < x) →
    (∀ i < m, b i < e i) → (∀ i, i + 1 < m → e i < b (i + 1)) →
    (∀ i < m, ∀ i' < m, ((t i : ℝ) + 1) / 2 ≤ |b i' - e i|) →
    (∀ i, i + 1 < m → h ≤ b (i + 1) - b i) →
    Formalism.QuantumDeterminants.GapAtLeast (n := (paramDV t j m v b e).length)
      (fun a => (sgnDV k m t j).getD (a : ℕ) true) (fun a => (paramDV t j m v b e).get a) h
def BaseExists : Prop :=
  ∀ (b : ℕ → ℝ) (H : ℝ), ∃ b0 : ℕ → ℝ, b0 0 = b 0 ∧ (∀ i, ∃ z : ℕ, b0 i = b i + (z : ℝ)) ∧
    ∀ i, H ≤ b0 (i + 1) - b0 i
def ExplicitC : Prop :=
  ∀ (n : ℕ) (q h : ℝ), 2 ≤ n → 0 ≤ q → q ≤ (n : ℝ) / 2 →
    16 * (((n ^ 2 / 2 + 1 : ℕ) : ℝ)) * Real.sqrt q ≤ 8 * ((n : ℝ) ^ 2 + 2) * Real.sqrt q ∧
    43 * ((n : ℝ) ^ 2 * Real.sqrt n) ≤ 43 * (n : ℝ) ^ 3 ∧
    (43 * ((n : ℝ) ^ 2 * Real.sqrt n) ≤ h →
      120 * n * (q * Real.sqrt q) ≤ h ∧ 8 * ((n : ℝ) ^ 2 + 2) * Real.sqrt q + 16 * ((n : ℝ) - 1) * q < h ∧
        16 * (n : ℝ) ^ 2 * Real.sqrt q ≤ h)
def DecayArith : Prop :=
  ∀ (q : ℕ) (n : ℝ) (t : Fin q → ℝ), (∀ i, 0 ≤ t i) →
    ((∑ i : Fin q, ∑ j ∈ univ.filter (fun j : Fin q => i < j), (2 * ((t i - t j) + (t i + t j)))) +
        (∑ i : Fin q, ((2 * (n - 2 * q) + 2) * t i)) = ∑ i : Fin q, (2 * (n - 2 * (i : ℕ) - 1) * t i)) ∧
    (∑ i : Fin q, 2 * (n - 2 * (i : ℕ) - 1) * t i ≤ 2 * (n - 1) * ∑ i, t i) ∧
    (∑ i : Fin q, 2 * (n - 2 * ((i : ℕ) : ℝ) - 1) = 2 * q * (n - q)) ∧
    (∀ i, t i ≤ Real.sqrt (2 * ∑ i, t i ^ 2) / Real.sqrt 2) ∧
    (∑ i, t i ≤ Real.sqrt ((q : ℝ) / 2) * Real.sqrt (2 * ∑ i, t i ^ 2)) ∧
    (1 ≤ q → ∀ h M : ℝ, (0 < h / (8 * Real.sqrt (2 * q)) - M / Real.sqrt 2 - (n - 1) * Real.sqrt (2 * q) ↔
      8 * M * Real.sqrt q + 16 * (n - 1) * q < h))
def HypArith : Prop :=
  ∀ (k r : ℕ) (n q B₀ h : ℝ), 1 ≤ k → n = (k : ℝ) + 2 * r + 1 → q = (r : ℝ) + 1 →
    B₀ = ((r : ℝ) * (r - 1) + 2 * r * (k + 1) + (r : ℝ) ^ 2) + (r : ℝ) ^ 2 + 1 →
    (r : ℝ) * (r - 1) + 2 * r * (k + 1) + (r : ℝ) ^ 2 = r * (n + k) ∧ B₀ = r * (2 * n - r - 1) + 1 ∧
    2 * B₀ + 2 * q * (n - q) + 1 = 6 * r * n - 4 * (r : ℝ) ^ 2 - 6 * r + 2 * n + 1 ∧
    2 * B₀ + 2 * q * (n - q) + 1 ≤ 2 * n ^ 2 - 3 * n + 3 ∧ 2 * n ^ 2 - 3 * n + 3 ≤ 2 * n ^ 2 ∧
    (16 * n ^ 2 * Real.sqrt q ≤ h → 2 * B₀ + 2 * q * (n - q) + 1 ≤ h / (8 * Real.sqrt q))
def ResidueValue : Prop :=
  ∀ (E : Type) [AddCommGroup E] [Module ℂ E] (n k : ℕ) (lam : Fin n → ℂ) (u : Fin k → ℂ) (a : Fin n → E)
    (K : E) (s₀ s₁ : ℂ),
    Function.Injective lam →
    (∀ x : ℂ, (∀ s, x + s₀ - lam s ≠ 0) →
      ∑ i, (x - (lam i - s₀))⁻¹ • a i = ((∏ j, (x + s₁ - u j)) / ∏ s, (x + s₀ - lam s)) • K) →
    ∀ i, a i = ((∏ j, (lam i + (s₁ - s₀) - u j)) / ∏ s ∈ univ.erase i, (lam i - lam s)) • K
end Formalism.HermitianLatticeCounting.S8


