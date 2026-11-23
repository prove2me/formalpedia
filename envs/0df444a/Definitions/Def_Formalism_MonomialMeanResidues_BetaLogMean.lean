-- Prove2me | Definitions.Def_Formalism_MonomialMeanResidues_BetaLogMean
-- name    : Formalism_MonomialMeanResidues_BetaLogMean
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:38:59.952049+00:00
-- url     : https://prove2.me/theorems/e0adbe45-33dc-48d8-9b53-d9431259e09c
-- title:
--   Beta Log Mean
-- statement:
--   Definitions and structural lemmas for Beta Log Mean, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MonomialMeanResidues/BetaLogMean.lean

import Mathlib
import Definitions.Def_Formalism_MonomialMeanResidues_FilteredDegree
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField Finset
noncomputable section
namespace Formalism.HermiteSiegelSlopes
open Formalism.HN
def ShareCount : Prop :=
  ∀ (D m δ d : ℕ) (dimGr : ℕ → ℕ), 1 ≤ D → d = ∑ a ∈ range (m + 1), dimGr a →
    (∀ a ≤ m, dimGr a ≤ (a + D - 1).choose (D - 1) * δ) → d ≤ (m + D).choose D * δ
def ShareZ : Prop :=
  ∀ (D T : ℕ) (x δ d : ℝ), 1 ≤ D → D + 1 ≤ T → 0 ≤ x → 0 < δ → 0 < d →
    ((T - 1).choose D : ℝ) * δ ≤ d →
    d ≤ (∏ i ∈ range D, (x + ((i : ℝ) + 1)) / ((i : ℝ) + 1)) * δ →
    1 - ((T - 1).choose D : ℝ) * δ / d ≤ D * (x - T + D + 1) / (x + 1) ∧
    ∀ ρ : ℝ, 0 ≤ ρ → ρ < 1 → x = ((T : ℝ) + D + 3) / (1 - ρ) →
      D * (x - T + D + 1) / (x + 1) ≤ D * (2 * D + 4) / T + D * ρ
def MinkowskiCount : Prop :=
  ∀ (K V ι : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
    [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι] [DecidableEq ι]
    (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ), (∀ v, IsUnit (X v).det) →
    ∀ (M : Submodule (𝓞 K) V) (R : InfinitePlace K → ℝ), M.FG → M ≠ ⊥ → (∀ v, 0 < R v) →
      {x : V | x ∈ M ∧ ∀ v, Formalism.HermitianLatticesTheory.normAt b X v x ≤ R v}.Finite ∧
      (Module.finrank ℚ K : ℝ) * (degT b X M + (rkK M : ℝ) * meanPl (fun v => Real.log (R v))
          - (rkK M : ℝ) / 2 * Real.log (2 * (rkK M : ℝ))
          - (rkK M : ℝ) / (2 * (Module.finrank ℚ K : ℝ)) * logDisc K) ≤
        Real.log ({x : V | x ∈ M ∧ ∀ v, Formalism.HermitianLatticesTheory.normAt b X v x ≤ R v}.ncard : ℝ)
def SlopeLimit : Prop :=
  ∀ (D : ℕ) (N δ δ' h t sl c : ℝ) (lν r η : ℕ → ℝ) (l : Filter ℕ), l.NeBot → l ≤ Filter.atTop →
    0 < N →
    Filter.Tendsto (fun τ => r τ * (D.factorial : ℝ) / (τ : ℝ) ^ D) l (nhds δ') →
    Filter.Tendsto η l (nhds 0) →
    Filter.Tendsto (fun τ => lν τ * (D.factorial : ℝ) / (N * (τ : ℝ) ^ (D + 1))) l
      (nhds (δ * (h + t))) →
    (∀ᶠ τ in l, N * τ * r τ * (sl - c + t - η τ) ≤ lν τ) → (∀ᶠ τ in l, 0 ≤ lν τ) →
    δ' * (sl - c + t) ≤ δ * (h + t) ∧ 0 ≤ δ * (h + t)
def SlopeCor : Prop :=
  ∀ h sl c δ δ' lΛ : ℝ, 0 < δ → 0 ≤ δ' →
    (∀ t, lΛ ≤ t → δ' / δ * max 0 (sl - c + t) ≤ h + t) →
    -lΛ ≤ h ∧
    (∀ t0, lΛ ≤ t0 + c → δ' / δ * max 0 (sl + t0) ≤ h + c + t0) ∧
    (0 ≤ c → sl ≤ 0 → δ' ≤ δ → ∀ cs, lΛ ≤ cs → sl - c - cs * (1 - δ' / δ) ≤ h) ∧
    (∀ ρ cs, 0 ≤ c → lΛ ≤ cs → ρ < 1 → δ ≤ δ' / (1 - ρ) →
      0 ≤ h + cs ∧ (1 - ρ) * max 0 (sl + cs) ≤ h + cs + c)
def BetaLogMean : Prop :=
  ∀ N : ℕ, 2 ≤ N →
    ∫ x in (0 : ℝ)..1, Real.log x * (((N : ℝ) - 1) * (1 - x) ^ (N - 2)) = -(harmonic (N - 1) : ℝ)
def ZerosPerVariable : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] [DecidableEq R] (q e : ℕ) (Cs : Finset R)
    (G : MvPolynomial (Fin q) R), G ≠ 0 → (∀ i, G.degreeOf i ≤ e) →
    ((Fintype.piFinset fun _ : Fin q => Cs).filter fun c => MvPolynomial.eval c G = 0).card
      ≤ q * e * Cs.card ^ (q - 1)
end Formalism.HermiteSiegelSlopes


