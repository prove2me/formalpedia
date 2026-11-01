-- Prove2me | Definitions.Def_RelaxRoundPoA_vcgMech
-- name    : RelaxRoundPoA_vcgMech
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T07:50:45.537981+00:00
-- url     : https://prove2.me/theorems/a82ccb2c-c084-45d5-b428-21e31ce4545e
-- title:
--   The VCG mechanism $M^{\mathrm{VCG}}=(f,p^{\mathrm{VCG}})$
-- statement:
--   Given a mechanism $M=(f,p)$ and a feasible set $F$, the **VCG mechanism** $M^{\mathrm{VCG}}=(f,p^{\mathrm{VCG}})$ keeps the outcome rule $f$ of $M$ and charges the VCG payments $p^{\mathrm{VCG}}$.
--
--   The proof of Lemma 1 compares the pay-your-bid mechanism with this truthful mechanism on the same outcome rule.
-- source:
--   Dütting, Kesselheim, Tardos, Algorithms as Mechanisms: The Price of Anarchy of Relax-and-Round, arXiv:1511.09208v1, §3, proof of Lemma 1, p.8

import Mathlib
import Definitions.Def_RelaxRoundPoA_Mechanism
import Definitions.Def_RelaxRoundPoA_vcgPay

open MeasureTheory NNReal

namespace RelaxRoundPoA

/-- **The VCG mechanism `M^VCG = (f, p^VCG)`.**
Dütting, Kesselheim, Tardos, arXiv:1511.09208v1, §3, p.8 (proof of Lemma 1): `M^VCG` keeps the
outcome rule `f` of `M` and charges VCG payments.

`vcgMech M Feas` has the outcome law of `M` and expected payments `vcgPay M Feas`. -/
noncomputable def vcgMech {N : Type*} [Fintype N] [DecidableEq N] {Ω' : Type*}
    [MeasurableSpace Ω'] (M : Mechanism N Ω') (Feas : Set Ω') : Mechanism N Ω' where
  outcome := M.outcome
  outcome_isProb := M.outcome_isProb
  expPay := vcgPay M Feas

end RelaxRoundPoA


