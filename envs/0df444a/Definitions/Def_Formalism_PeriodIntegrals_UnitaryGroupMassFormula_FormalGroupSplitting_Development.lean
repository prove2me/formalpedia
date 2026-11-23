-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupSplitting_Development
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FormalGroupSplitting_Development
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T02:33:26.705333+00:00
-- url     : https://prove2.me/theorems/47efe9f8-f88e-491d-8008-23c4a80d4c3b
-- title:
--   Development
-- statement:
--   Definitions and structural lemmas for Development, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/FormalGroupSplitting/Development.lean

import Definitions.Def_Formalism_PeriodIntegrals_FglPhSplit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.FglPhSplit.Wk
open PI.FglPhSplit MvPowerSeries
def S1 : Prop :=
  ∀ (K : Type) [Field K] (l ex : PowerSeries K), PowerSeries.constantCoeff ex = 0 →
    PowerSeries.subst ex l = PowerSeries.X →
    PowerSeries.constantCoeff l = 0 ∧ PowerSeries.subst l ex = PowerSeries.X
def S2 : Prop :=
  ∀ (K : Type) [Field K] (g : Dat K), PowerSeries.constantCoeff g.ex = 0 →
    PowerSeries.subst g.ex g.l = PowerSeries.X → PowerSeries.constantCoeff g.ph = 0 →
    ∀ (κ ι ι' : Type) [Fintype κ] [Fintype ι] [Fintype ι'] (a : ι → κ → K × K)
      (a' : ι' → κ → K × K), (∀ f f', hP (a f) (a' f') = 0) → g.sdR a a' = 0
def S3 : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (W : Subring K) (σ : Type) (f g f' g' : MvPowerSeries σ K),
    SimeqW W f g → SimeqW W f' g' → SimeqW W (f + f') (g + g')
def S4 : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (W : Subring K) (g : Dat K),
    PowerSeries.constantCoeff g.ex = 0 → PowerSeries.subst g.ex g.l = PowerSeries.X →
    ∀ (κ ι ι' : Type) [Fintype κ] [Fintype ι] [Fintype ι'] (b b' : ι → κ → K × K),
      SimeqW W (g.PhOn (Sum.elim b b')) (g.beSum ι) →
      SimeqW W (g.PhV (Sum.elim b b') (fun e => (X (Sum.inl e) : MvPowerSeries ((ι ⊕ ι) ⊕ ι') K)))
        (∑ e : ι, g.be (X (Sum.inl (Sum.inl e))) (X (Sum.inl (Sum.inr e))))
end PI.FglPhSplit.Wk
end


