-- Prove2me | Definitions.Def_GaussDiffSVP_leafTrial
-- name    : GaussDiffSVP_leafTrial
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:58:52.03937+00:00
-- url     : https://prove2.me/theorems/183d0247-ec72-497d-b44f-d51a6b3e4108
-- title:
--   Corrected leaf trial law $q_{R,p}$
-- statement:
--   One corrected trial at $(p,R,S)$ for $\Gamma = B\mathbb Z^n$ returns each vector $x$ with probability
--   $$q_{R,p}(x) = \frac{\rho_R(x)}{2V_R}\,\mathbf 1[x\in(p+\Gamma)\cap S],$$
--   and the failure symbol $\dagger$ with the remaining probability. The law is not normalized: its coefficient is known without computing the total Gaussian mass on the coset.
--
--   **Formalization Note** Its total vector mass is at most one under Lemma 3.3's hypothesis $R \ge G\sqrt{\log(8n)/\pi}$, which every statement using it assumes; otherwise the definition returns the constant failure law, a totality device only.
-- source:
--   Gao–Han–Hu, Gaussian Difference Dynamics: Breaking the 2^{n/2} Barrier for the Shortest Vector Problem and Discrete Gaussian Sampling, arXiv:2611.04336 (held version, sha256 233bf8bb…0692), Lemma 3.3, (15), p.21

import Mathlib
import Definitions.Def_GaussDiffSVP_volFactor
import Definitions.Def_SuperlatSVP_lat

open scoped ENNReal

namespace GaussDiffSVP

/-- One corrected trial at `(p, R, S)` (Lemma 3.3, (15), Gao–Han–Hu, *Gaussian Difference Dynamics*, arXiv:2611.04336 (held version, sha256 233bf8bb…0692), p.21): it returns the vector `x`
(as `some x`) with probability `q_{R,p}(x) = ρ_R(x) / (2V_R) · 1[x ∈ (p + Γ) ∩ S]`, and the failure
symbol `†` (as `none`) with the remaining probability. Here `Γ = Bℤⁿ`, `V_R = Rⁿ/det Γ`.

**Formalization Note.** The law is sub-stochastic on vectors and is **not** normalized; its total
vector mass is at most one under the hypotheses of Lemma 3.3 (`R ≥ G√(log(8n)/π)`), which every
statement that uses it assumes. A `PMF` needs total mass one, so when the vector mass exceeds one
(never under those hypotheses) the definition returns the constant failure law; that branch is a
totality device only. -/
noncomputable def leafTrial {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) (R : ℝ)
    (S : Set (SuperlatSVP.E n)) (p : SuperlatSVP.E n) : PMF (Option (SuperlatSVP.E n)) := by
  classical
  let f : SuperlatSVP.E n → ℝ≥0∞ := fun x =>
    if x - p ∈ SuperlatSVP.lat B ∧ x ∈ S then
      ENNReal.ofReal (RegevLWE.GaussConv.rho R x / (2 * volFactor B R)) else 0
  exact if h : ∑' x, f x ≤ 1 then
    ⟨fun o => o.elim (1 - ∑' x, f x) f, by
      rw [ENNReal.summable.hasSum_iff, ENNReal.tsum_eq_add_tsum_ite none]
      have key : (∑' o : Option (SuperlatSVP.E n),
          if o = none then 0 else o.elim (1 - ∑' x, f x) f) = ∑' x, f x := by
        rw [← (Option.some_injective _).tsum_eq]
        · rfl
        · intro o ho
          cases o with
          | none => simp at ho
          | some x => exact ⟨x, rfl⟩
      refine Eq.trans ?_ (tsub_add_cancel_of_le h)
      congr 1
      convert key⟩
  else PMF.pure none

end GaussDiffSVP


