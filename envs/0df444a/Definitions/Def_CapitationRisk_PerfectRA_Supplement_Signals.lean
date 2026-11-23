-- Prove2me | Definitions.Def_CapitationRisk_PerfectRA_Supplement_Signals
-- name    : CapitationRisk_PerfectRA_Supplement_Signals
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T09:32:33.202684+00:00
-- url     : https://prove2.me/theorems/a5c748b2-4556-43ed-b402-36bbfd4bb5fd
-- title:
--   Appendix A — noisy signals, Bayes payments (23)–(25), and the source rate family
-- statement:
--   Let I be the finite set of true patient types and also the signal set. A channel has conditional probabilities ρ_ji = P[x_j|i] that are nonnegative, sum to one over j for each i, and satisfy 0 < ρ_ii < 1. Let λ_i(w*) be target enrollment and let r*_i be the exact accounting-cost rate (7) from the published model. Define
--   $$p(k\mid x_j)=\frac{\rho_{jk}\lambda_k(w^*)}{\sum_l\rho_{jl}\lambda_l(w^*)},\qquad \widehat r_j=\sum_kp(k\mid x_j)r^*_k,\qquad r_i=\sum_j\rho_{ji}\widehat r_j.$$
--   The source rate family consists of r* and all such signal-generated vectors. It does not identify noisy signals with a changed payment vector. This layer supplies the rates for Theorem 2.
--
--   **Formalization Note** The positive target enrollments in Standing and the positive diagonal make each Bayes denominator positive. Outside that context Lean division is total; the definitions alone claim no probability theorem. The shadowed inner type index in printed (25) is renamed k.
-- source:
--   She, Ayer & Montanera, Can big data cure risk selection in healthcare capitation program? A game theoretical analysis, author manuscript (SSRN 3556992; MSOM 2022), pp. 33–34, Appendix A, (23)–(25)

import Definitions.Def_CapitationRisk_PerfectRA_Model

namespace CapitationRisk.PerfectRA.Supplement

variable {S I : Type*} [Fintype S] [Fintype I]

/-- Appendix A: a noisy channel from true patient types to signals, with Z = I.
The first index is the signal, the second is the true type. -/
structure SignalChannel (I : Type*) [Fintype I] where
  rho : I → I → ℝ
  nonneg : ∀ j i, 0 ≤ rho j i
  total : ∀ i, ∑ j, rho j i = 1
  diagonal : ∀ i, 0 < rho i i ∧ rho i i < 1

/-- Bayes posterior in (23); target enrollment supplies the prior weights. -/
noncomputable def posterior (M : Model S I) (Q : SignalChannel I) (j k : I) : ℝ :=
  Q.rho j k * M.lam k M.wstar / ∑ l, Q.rho j l * M.lam l M.wstar

/-- Payment conditional on signal j, equation (23). -/
noncomputable def signalPayment (M : Model S I) (Q : SignalChannel I) (j : I) : ℝ :=
  ∑ k, posterior M Q j k * M.rate k

/-- Expected payment for true type i, equations (24)–(25). -/
noncomputable def signalRate (M : Model S I) (Q : SignalChannel I) (i : I) : ℝ :=
  ∑ j, Q.rho j i * signalPayment M Q j

/-- The source's rate family: exact accounting-cost rates (7), or Bayesian rates (25).
No assertion that every noisy channel changes the rate vector is built in. -/
def SourceRates (M : Model S I) (r : I → ℝ) : Prop :=
  r = M.rate ∨ ∃ Q : SignalChannel I, r = signalRate M Q

end CapitationRisk.PerfectRA.Supplement


