-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_VeluIntegral
-- name    : Formalism_LocalToGlobal_TorsionIntegrality_SecondCoefficientNorms_VeluIntegral
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:58:59.150551+00:00
-- url     : https://prove2.me/theorems/cfc8a065-3f2d-4ca5-8e67-5f19227b8b03
-- title:
--   Velu Integral
-- statement:
--   Definitions and structural lemmas for Velu Integral, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/SecondCoefficientNorms/VeluIntegral.lean

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
def veluXs {K : Type} [Field K] {ι : Type} [Fintype ι] (A : PowerSeries K) (xs : ι → PowerSeries K)
    (xP : ι → K) (r : K) : PowerSeries K :=
  A + PowerSeries.X ^ 2 * (∑ P, (xs P - PowerSeries.C (xP P)) - PowerSeries.C r)
def veluYs {K : Type} [Field K] {ι : Type} [Fintype ι] (A : PowerSeries K)
    (xs ys : ι → PowerSeries K) (xP yP : ι → K) (r s t : K) : PowerSeries K :=
  A - PowerSeries.X ^ 3 * ∑ P, (ys P - PowerSeries.C (yP P))
    + PowerSeries.C s * PowerSeries.X * veluXs A xs xP r + PowerSeries.C t * PowerSeries.X ^ 3
def VeluIntegral : Prop :=
  ∀ (K : Type) [Field K] (R : Subring K) (A v : PowerSeries K) (ι : Type) [Fintype ι]
    (xs ys : ι → PowerSeries K) (xP yP : ι → K) (al r s t : K),
    IsOneUnit R A → (∀ P, IntPS R (xs P)) → (∀ P, IntPS R (ys P)) →
    (∀ P, xP P ∈ R) → (∀ P, yP P ∈ R) → r ∈ R → s ∈ R → t ∈ R →
    PowerSeries.constantCoeff v = 0 → v ≠ 0 →
    PowerSeries.C (al ^ 2) * PowerSeries.subst v A * PowerSeries.X ^ 2 = v ^ 2 * veluXs A xs xP r →
    PowerSeries.C (al ^ 3) * PowerSeries.subst v A * PowerSeries.X ^ 3 =
      v ^ 3 * veluYs A xs ys xP yP r s t →
    ∃ g : PowerSeries K, IsOneUnit R g ∧ v = PowerSeries.C al * PowerSeries.X * g ∧
      g * veluYs A xs ys xP yP r s t = veluXs A xs xP r
def VeluXFromZ : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (e l linv A : PowerSeries K) (c0 : K) (ι : Type) [Fintype ι]
    (neg : ι → ι) (xP : ι → K) (w xs : ι → PowerSeries K) (al : K),
    IsLogPair l linv → XIsWp e l A c0 → IsEndoZ e neg (fun P => xP P + c0) w al →
    (∀ P, PowerSeries.subst l (w P) = xs P + PowerSeries.C c0) →
    PowerSeries.C (al ^ 2) * PowerSeries.subst (mulBy l linv al) A * PowerSeries.X ^ 2 =
      (mulBy l linv al) ^ 2 * veluXs A xs xP ((al ^ 2 - 1) * c0)
def IsogenyU : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (e : PowerSeries K) (s2 : K) (l linv ph A : PowerSeries K)
    (c0 : K) (ι : Type) [Fintype ι] (xP : ι → K) (al : K),
    IsLogPair l linv → IsPh e s2 l ph → XIsWp e l A c0 →
    IsogenyFormula e s2 (fun P => xP P + c0) al →
    (mulBy l linv al) ^ 2 * mvExp (-((2 : K) • PowerSeries.subst (mulBy l linv al) ph))
        * PowerSeries.X ^ (2 * Fintype.card ι) =
      PowerSeries.C (al ^ 2) * PowerSeries.X ^ (2 * (Fintype.card ι + 1))
        * mvExp (-((2 * ((Fintype.card ι : K) + 1)) • ph))
        * ∏ P, (A - PowerSeries.C (xP P) * PowerSeries.X ^ 2)
def PhNormUnit : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (R : Subring K) (e : PowerSeries K) (s2 : K)
    (l linv ph A : PowerSeries K) (c0 : K) (ι : Type) [Fintype ι] (xP : ι → K) (al : K),
    IsLogPair l linv → IsPh e s2 l ph → XIsWp e l A c0 →
    IsogenyFormula e s2 (fun P => xP P + c0) al →
    IsOneUnit R A → (∀ P, xP P ∈ R) → al ∈ R → al⁻¹ ∈ R → al ≠ 0 → (2 : K)⁻¹ ∈ R →
    IntPS R (mulBy l linv al) →
    Cong R (PowerSeries.subst (mulBy l linv al) ph) (((Fintype.card ι : K) + 1) • ph)
end Formalism.L2.Th1.C


