-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_FinOrdRedOne
-- name    : Formalism_PeriodIntegrals_FinOrdRedOne
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:09:34.936041+00:00
-- url     : https://prove2.me/theorems/18adb0f7-c7d9-45ab-bd11-0be886985190
-- title:
--   Fin Ord Red One
-- statement:
--   Definitions and structural lemmas for Fin Ord Red One, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/FinOrdRedOne.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.FinOrdRedOne
open NumberField IsDedekindDomain Ideal
abbrev OP (E : Type) [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) : Type :=
  P.adicCompletionIntegers E
def red {E : Type} [Field E] [NumberField E] {P : HeightOneSpectrum (𝓞 E)} {N : ℕ}
    (M : Matrix (Fin N) (Fin N) (OP E P)) :
    Matrix (Fin N) (Fin N) (IsLocalRing.ResidueField (OP E P)) :=
  M.map (IsLocalRing.residue (OP E P))
def Unram (E : Type) [Field E] [NumberField E] (p : ℕ) : Prop :=
  ∀ (Q : Ideal (𝓞 E)) [Q.IsPrime] [Q.LiesOver (span {(p : ℤ)})], Q.ramificationIdx ℤ = 1
end PI.FinOrdRedOne
namespace PI
open NumberField IsDedekindDomain Ideal PI.FinOrdRedOne
def FinOrdRedOne : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (p : ℕ), p.Prime → 3 ≤ p → Unram E p →
  ∀ (P : HeightOneSpectrum (𝓞 E)), (p : 𝓞 E) ∈ P.asIdeal →
  ∀ (N : ℕ) (β : GL (Fin N) (OP E P)), IsOfFinOrder β →
    red (β : Matrix (Fin N) (Fin N) (OP E P)) = 1 → β = 1
end PI


