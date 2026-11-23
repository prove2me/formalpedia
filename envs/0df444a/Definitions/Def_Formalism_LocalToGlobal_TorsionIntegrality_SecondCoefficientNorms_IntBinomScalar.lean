-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_IntBinomScalar
-- name    : Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_IntBinomScalar
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:58:29.963403+00:00
-- url     : https://prove2.me/theorems/0d58951f-cd4e-48b0-99b2-4a6a667e4011
-- title:
--   Int Binom Scalar
-- statement:
--   Definitions and structural lemmas for Int Binom Scalar, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/SecondCoefficientNorms/IntBinomScalar.lean

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_HasSecondLogDeriv
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
def MvExpLaws : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (σ : Type),
    mvExp (0 : MvPowerSeries σ K) = 1 ∧
    (∀ f : MvPowerSeries σ K, MvPowerSeries.constantCoeff f = 0 →
      MvPowerSeries.constantCoeff (mvExp f) = 1) ∧
    (∀ f g : MvPowerSeries σ K, MvPowerSeries.constantCoeff f = 0 →
      MvPowerSeries.constantCoeff g = 0 → mvExp (f + g) = mvExp f * mvExp g) ∧
    (∀ f g : MvPowerSeries σ K, MvPowerSeries.constantCoeff f = 0 →
      MvPowerSeries.constantCoeff g = 0 → mvExp f = mvExp g → f = g)
def MvExpSubst : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (σ : Type) (f : PowerSeries K) (a : MvPowerSeries σ K),
    PowerSeries.constantCoeff f = 0 → MvPowerSeries.constantCoeff a = 0 →
      PowerSeries.subst a (mvExp f : PowerSeries K) = mvExp (PowerSeries.subst a f)
def LGSubgroup : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (R : Subring K) (σ : Type),
    LG R (0 : MvPowerSeries σ K) ∧
    (∀ f g : MvPowerSeries σ K, LG R f → LG R g → LG R (f + g)) ∧
    (∀ f : MvPowerSeries σ K, LG R f → LG R (-f))
def LGBinom : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (R : Subring K) (σ : Type) (z : K), IsBinomScalar R z →
    ∀ f : MvPowerSeries σ K, LG R f → LG R (z • f)
def LGHalf : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (R : Subring K) (σ : Type), (2 : K)⁻¹ ∈ R →
    ∀ f : MvPowerSeries σ K, LG R (f + f) → LG R f
def IntBinomScalar : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (R : Subring K) (n : ℤ), IsBinomScalar R (n : K)
def LGSubst : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (R : Subring K) (f : PowerSeries K), LG R f →
    ∀ (σ : Type) (a : MvPowerSeries σ K), IsPt R a → LG R (PowerSeries.subst a f)
def LGSubstMv : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (R : Subring K) (σ : Type) [Finite σ]
    (f : MvPowerSeries σ K), LG R f →
    ∀ (τ : Type) (a : σ → MvPowerSeries τ K), (∀ s, IsPt R (a s)) → LG R (MvPowerSeries.subst a f)
def IntSubst : Prop :=
  ∀ (K : Type) [Field K] (R : Subring K) (f : PowerSeries K), IntPS R f →
    ∀ (σ : Type) (a : MvPowerSeries σ K), IsPt R a → IntMv R (PowerSeries.subst a f)
def LGDeriv : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (R : Subring K) (σ : Type) (f : MvPowerSeries σ K),
    LG R f → ∀ i : σ, IntMv R (MvPowerSeries.pderiv K i f)
end Formalism.L2.Th1.C


