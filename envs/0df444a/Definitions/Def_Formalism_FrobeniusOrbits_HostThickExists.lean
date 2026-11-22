-- Prove2me | Definitions.Def_Formalism_FrobeniusOrbits_HostThickExists
-- name    : Formalism_FrobeniusOrbits_HostThickExists
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T19:33:34.247978+00:00
-- url     : https://prove2.me/theorems/b3f6c6b6-756c-4cf6-8bbb-35e960616018
-- title:
--   Host Thick Exists
-- statement:
--   Definitions and structural lemmas for Host Thick Exists, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/HostThickExists.lean

import Definitions.Def_Formalism_FrobeniusOrbits_HostOrbitsPlaces
import Definitions.Def_Formalism_FrobeniusOrbits_HostDiffSupport
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField Ideal
open scoped Pointwise
noncomputable section
namespace Formalism.FrobeniusOrbits
open Formalism.TwoAdicCyclotomicDecomposition
def NoRel (T : Finset ℕ) (L : ℕ) : Prop :=
  ∀ s₁ ∈ T, ∀ s₂ ∈ T, ∀ s₃ ∈ T, s₁ ≠ s₂ → s₁ ≠ s₃ → s₂ ≠ s₃ →
    ∀ i j : ℤ, 0 < |i| → |i| ≤ L → 0 < |j| → |j| ≤ L → i ≠ j →
      j * ((s₂ : ℤ) - s₁) ≠ i * ((s₃ : ℤ) - s₁)
def InTranslate {n : ℕ} (T : Finset ℕ) (u₀ x : ZMod n) : Prop := ∃ s ∈ T, x = (s : ZMod n) + u₀
open Classical in

def HostThickOrbit : Prop :=
  ∀ (n L : ℕ), 0 < n → 2 ≤ L → ∀ T : Finset ℕ, (∀ s ∈ T, 4 * L * s < n) → NoRel T L →
  ∀ u₀ t h : ZMod n,
    (4 * L < addOrderOf h → ∀ i₀ : ℤ,
      ((Finset.Ico i₀ (i₀ + L)).filter (fun i : ℤ => InTranslate T u₀ (t + i • h))).card ≤ 2) ∧
    (addOrderOf h ≤ 4 * L →
      {x : ZMod n | (∃ i : ℤ, x = t + i • h) ∧ InTranslate T u₀ x}.ncard ≤ 1)
def HostThickExists : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ n L : ℕ, 2 ≤ L → ∃ T : Finset ℕ, (∀ s ∈ T, 4 * L * s < n) ∧ NoRel T L ∧
    (n : ℝ) * Real.exp (-C * Real.sqrt (Real.log n * Real.log L)) / L ≤ T.card
def bern {α : Type*} [Fintype α] (δ : ℝ) (T : Finset α) : ℝ :=
  δ ^ T.card * (1 - δ) ^ (Fintype.card α - T.card)
open Classical in

def HostTops : Prop :=
  ∀ (α ι : Type) [Fintype α] [Fintype ι] (δ β : ℝ) (ω : ι → ℝ) (BAD : ι → α → Finset α → Prop),
    0 < δ → δ ≤ 1 → 0 ≤ β → (∀ p, 0 ≤ ω p) → 16 ≤ δ * Fintype.card α →
    (∀ p t, (∑ T : Finset α, if t ∈ T ∧ BAD p t T then bern δ T else 0) ≤ β * δ) →
    ∃ T : Finset α, δ * Fintype.card α / 2 ≤ T.card ∧ (T.card : ℝ) ≤ 2 * δ * Fintype.card α ∧
      (∑ p, ω p * ((T.filter (fun t => BAD p t T)).card : ℝ)) ≤
        4 * β * δ * Fintype.card α * ∑ p, ω p
def HostProG : Prop :=
  ∀ (g : ℕ), g.Prime →
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [TotallyDisconnectedSpace G],
    (∀ N : Subgroup G, IsOpen (N : Set G) → N.Normal → ∃ m : ℕ, N.index = g ^ m) →
    ∀ x : G, IsOfFinOrder x → ∃ m : ℕ, orderOf x = g ^ m
def HostStab : Prop :=
  ∀ (e q d : ℕ), HypOdd q d →
  ∀ (L : Type) [Field L] [NumberField L] (ζ a b : L), IsLayer (e + 2) q d ζ a b →
  ∀ (k g : ℕ), g.Prime → 2 ^ (e + 2) * k < g - 1 →
  ∀ Γ : Subgroup (Matrix.GeneralLinearGroup (Fin k) (hostE ζ a b)),
    (∀ γ ∈ Γ, ∃ m : ℕ, orderOf γ = g ^ m) → Γ = ⊥
def HostOrdinary : Prop :=
  ∀ (e q d : ℕ), HostHyp q d →
  ∀ (L : Type) [Field L] [NumberField L] (ζ a b : L), IsLayer (e + 2) q d ζ a b →
  ∀ (p : ℕ) [Fact p.Prime] (P : Ideal (𝓞 (hostE ζ a b))) [P.IsPrime]
    [P.LiesOver (span {(p : ℤ)})],
    (∀ σ τ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b, τ ∈ MulAction.stabilizer _ P →
      (galE e ζ a b (σ * τ) ∈ Psi e ↔ galE e ζ a b σ ∈ Psi e)) ↔
    (primesOver (span {(p : ℤ)}) (𝓞 (Kd b))).ncard = 2
def HostUnimodular : Prop :=
  ∀ (e q d : ℕ), HostHyp q d →
  ∀ (L : Type) [Field L] [NumberField L] (ζ a b : L), IsLayer (e + 2) q d ζ a b →
  ∀ σ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b, galE e ζ a b σ = cc e →
  ∀ 𝔟 : Ideal (𝓞 (hostE ζ a b)),
    differentIdeal (𝓞 (KinE ζ a b)) (𝓞 (hostE ζ a b)) = 𝔟 * (σ • 𝔟) →
    ∀ x : hostE ζ a b,
      x ∈ ((𝔟 : FractionalIdeal (nonZeroDivisors (𝓞 (hostE ζ a b))) (hostE ζ a b))⁻¹) ↔
        ∀ y ∈ ((𝔟 : FractionalIdeal (nonZeroDivisors (𝓞 (hostE ζ a b))) (hostE ζ a b))⁻¹),
          Algebra.trace (KinE ζ a b) (hostE ζ a b) (x * σ y) ∈
            (algebraMap (𝓞 (KinE ζ a b)) (KinE ζ a b)).range
def HostConductor : Prop :=
  ∀ (e q d : ℕ), HostHyp q d →
  ∀ (L : Type) [Field L] [NumberField L] (ζ a b : L), IsLayer (e + 2) q d ζ a b →
  ∀ m : ℕ, 0 < m →
    (Nonempty (hostE ζ a b →ₐ[ℚ] CyclotomicField m ℚ) ↔
      (if e = 0 then q * d else 2 ^ (e + 2) * q * d) ∣ m)
def etaF {L : Type*} [Field L] [NumberField L] (ζ a b : L) (𝔭 : Ideal (𝓞 (hostF ζ a b))) : ℤ :=
  if (primesOver 𝔭 (𝓞 (hostE ζ a b))).ncard = 2 then 1 else -1
def HostEta : Prop :=
  ∀ (e q d : ℕ), HostHyp q d →
  ∀ (L : Type) [Field L] [NumberField L] (ζ a b : L), IsLayer (e + 2) q d ζ a b →
    (∀ 𝔭 : Ideal (𝓞 (hostF ζ a b)), 𝔭.IsPrime → 𝔭 ≠ ⊥ →
      (primesOver 𝔭 (𝓞 (hostE ζ a b))).ncard = 2 ∨
        ((primesOver 𝔭 (𝓞 (hostE ζ a b))).ncard = 1 ∧ 𝔭.inertiaDegIn (𝓞 (hostE ζ a b)) = 2)) ∧
    (∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → p ≠ q → p ≠ d →
      ∀ (P : Ideal (𝓞 (hostE ζ a b))) [P.IsPrime] [P.LiesOver (span {(p : ℤ)})]
        (σ : hostE ζ a b ≃ₐ[ℚ] hostE ζ a b), IsArithFrobAt ℤ σ P →
        (etaF ζ a b (P.comap (algebraMap (𝓞 (hostF ζ a b)) (𝓞 (hostE ζ a b)))) = -1 ↔
          galE e ζ a b σ = cc e)) ∧
    (∀ (p : ℕ) [Fact p.Prime], (p = 2 ∨ p = q ∨ (p = d ∧ 2 ≤ e)) →
      ∀ (P : Ideal (𝓞 (hostE ζ a b))) [P.IsPrime] [P.LiesOver (span {(p : ℤ)})],
        etaF ζ a b (P.comap (algebraMap (𝓞 (hostF ζ a b)) (𝓞 (hostE ζ a b)))) = 1)
end Formalism.FrobeniusOrbits


