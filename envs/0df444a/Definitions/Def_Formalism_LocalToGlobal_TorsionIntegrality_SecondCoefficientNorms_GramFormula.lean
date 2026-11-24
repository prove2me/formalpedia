-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_GramFormula
-- name    : Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_GramFormula
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-24T21:10:44.6678+00:00
-- url     : https://prove2.me/theorems/fec8edd0-7207-44f6-b832-44a27170925e
-- title:
--   Gram Formula
-- statement:
--   Definitions and structural lemmas for Gram Formula, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/SecondCoefficientNorms/GramFormula.lean

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_IsotropicVanish
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
namespace Formalism.L2.Th1.C
def GramFormula : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (R : Subring K) (l linv ph : PowerSeries K),
    Frame R l linv ph →
    ∀ (O : Type) [CommRing O] [StarRing O] (τ : O →+* K),
    (∀ α, EndInt R l linv (τ α)) →
    (∀ z : O, star z = z → IsBinomScalar R (τ z)) →
    F1 R l linv ph →
    (∀ α : O, PhNormAt R l linv ph (τ α) (τ (star α))) →
    (∀ α : O, AdjAt R l linv ph (τ α) (τ (star α))) →
    ∀ (n : Type) [Fintype n] (k : ℕ) (A : n → Fin k → O)
      (σ : Type) (u : Fin k → MvPowerSeries σ K), (∀ j, IsPt R (u j)) →
      Cong R (∑ i, PowerSeries.subst (flin l linv (fun j => τ (A i j)) u) ph)
        ((∑ j, τ (∑ i, star (A i j) * A i j) • PowerSeries.subst (u j) ph) +
          ∑ j, ∑ j' ∈ Finset.univ.filter (fun j' => j < j'),
            be0 l linv ph (fmul l linv (τ (∑ i, star (A i j') * A i j)) (u j)) (u j'))
def TraceDiag : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (R : Subring K) (l linv ph : PowerSeries K),
    Frame R l linv ph →
    ∀ (O : Type) [CommRing O] [StarRing O] (τ : O →+* K),
    (∀ α, EndInt R l linv (τ α)) →
    (∀ z : O, star z = z → IsBinomScalar R (τ z)) →
    (∀ z : O, star z = z → ZLinAt R l linv ph (τ z)) →
    F1 R l linv ph → (2 : K)⁻¹ ∈ R →
    PhNormAt R l linv ph 2 2 →
    ∀ γ : O, AdjAt R l linv ph (τ (star γ)) (τ γ) →
    ∀ (σ : Type) (u : MvPowerSeries σ K), IsPt R u →
      Cong R (be0 l linv ph u (fmul l linv (τ γ) u)) (τ (star γ + γ) • PowerSeries.subst u ph)
def DiagTwoPh : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (R : Subring K) (l linv ph : PowerSeries K),
    Frame R l linv ph → PhNormAt R l linv ph 2 2 →
    ∀ (σ : Type) (u : MvPowerSeries σ K), IsPt R u →
      Cong R (be0 l linv ph u u) ((2 : K) • PowerSeries.subst u ph)
def PhRational : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (K0 : Subfield K) (e l ph : PowerSeries K) (s2 : K),
    PowerSeries.constantCoeff l = 0 → PowerSeries.coeff 1 l = 1 → IsPh e s2 l ph →
    (∀ n, PowerSeries.coeff n e ∈ K0) → (∀ n, PowerSeries.coeff n l ∈ K0) → s2 ∈ K0 →
    ∀ n, PowerSeries.coeff n ph ∈ K0
def PhUnique : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (e l ph ph' : PowerSeries K) (s2 : K),
    IsPh e s2 l ph → IsPh e s2 l ph' → ph = ph'
end Formalism.L2.Th1.C


