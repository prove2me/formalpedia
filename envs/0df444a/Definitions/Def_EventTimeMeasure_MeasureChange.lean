-- Prove2me | Definitions.Def_EventTimeMeasure_MeasureChange
-- name    : EventTimeMeasure_MeasureChange
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T20:24:37.929379+00:00
-- url     : https://prove2.me/theorems/632ecccb-9ece-424a-93f6-169195387947
-- title:
--   Multiplier $u$, tilted clocks $Q^i$, density $Z_\infty$, simulation measure $\mathbb Q=Z_\infty P$, and the Appendix A processes
-- statement:
--   The change of measure of §3 (p.9) and the auxiliary objects of Appendix A (pp.27–28) of Giesecke and Shkolnik, on the event timing model `EventTimeMeasure.Model`.
--
--   1. **Multiplier.** $u=(u^1,\dots,u^n)$ with each $u^i\ge0$, $\mathbb H_i$-predictable and locally bounded.
--   2. **Tilted clocks** (7). $Q^i_t=\int_0^t u^i_s h^i_s\,ds$ for $t\in[0,\infty]$; $q^i=u^ip^i$.
--   3. **Density** (9) and fn 17. $Z_\infty=L_\infty^{-1}$, that is
--   $$Z_\infty=\exp\Bigl(\sum_{i=1}^n (H^i-Q^i)_{\tau_i}\Bigr)\prod_{i=1}^n u^i_{\tau_i}.$$
--   4. **Simulation measure.** $\mathbb Q=Z_\infty P$.
--   5. **Partial multiplier** (p.27). $u$ on the first $\ell$ events and $1$ on the others; with it, $Z^\ell_\infty$ and $\mathbb Q_\ell=Z^\ell_\infty P$.
--   6. **Single-event density process** (p.27). For one event (the paper's $\ell+1$), $0\le t\le\infty$,
--   $$Z_t=\exp\Bigl(\int_0^t(1-u_s)p_s\,ds+N_t\log u_\tau\Bigr)=e^{(H-Q)_{t\wedge\tau}}\cdot\begin{cases}u_\tau,&\tau\le t,\\ 1,&\tau>t,\end{cases}$$
--   and its left limit $Z_{s-}$ (same formula with $\tau<s$).
--   7. **Localization times** (40). $\theta_k=\inf\{t\ge0:\int_0^t(1+u_s)h_s\,ds\ge k\}$, $k\in\mathbb N$, in $[0,\infty]$.
--
--   These objects state Theorem 3.1 and the steps of its proof.
--
--   **Formalization Note** Local boundedness is Mathlib's `Locally` along a localizing sequence of $\mathbb F$-stopping times (the page does not name the filtration; localization in $\mathbb H_i$ implies it). No logarithm is taken: $\exp(\log u_\tau)$ is the factor $u_\tau$, so $u_\tau=0$ gives $Z=0$, matching the paper's convention $1/0=\infty$ for $L_\infty$. $(H^i-Q^i)_{\tau_i}$ is a difference of real numbers. On the $P$-null event that some $\tau_i=\infty$, $Z_\infty$ is set to $1$, and in the single-event process $u_\tau$ is read as $u_0$.
-- source:
--   Giesecke–Shkolnik, Reducing Bias in Event Time Simulations via Measure Changes, authors' manuscript of January 16, 2018 (Math. Oper. Res., doi:10.1287/moor.2021.1156), §3, p.9, eqs. (7), (9), fn 17; Appendix A, p.27, display defining Z and eq. (40)

import Mathlib
import Definitions.Def_EventTimeMeasure_Model

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal

namespace EventTimeMeasure

namespace Model

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {n : ℕ}

/-- **Admissible multiplier** (Giesecke–Shkolnik, *Reducing Bias in Event Time Simulations via
Measure Changes*, manuscript of January 16, 2018, §3, p.9): a process `u = (u^1, …, u^n)` with
every `u^i` nonnegative, `ℍ_i`-predictable and locally bounded.

**Formalization Note** Nonnegativity is the codomain `ℝ≥0`. Predictability is Mathlib's
`IsStronglyPredictable` for the clock filtration `ℍ_i`. Local boundedness is Mathlib's `Locally`
with respect to the information filtration `𝔽` and `P`: there is a localizing sequence `(T_k)` of
`𝔽`-stopping times, increasing to `∞` almost surely, such that each stopped process
`u^i_{t ∧ T_k} 1{T_k > 0}` is bounded by a constant. The page does not name the filtration of the
localization; `𝔽` contains every `ℍ_i`, so localization in `ℍ_i` implies localization in `𝔽`. -/
structure IsMultiplier (M : Model P n) (u : Fin n → ℝ≥0 → Ω → ℝ≥0) : Prop where
  predictable : ∀ i, IsStronglyPredictable (M.𝓗 i) (u i)
  locallyBounded : ∀ i, Locally (fun X : ℝ≥0 → Ω → ℝ≥0 ↦ ∃ C : ℝ≥0, ∀ t ω, X t ω ≤ C)
    M.𝓕 (u i) P

/-- **Tilted clock** `Q^i_t = ∫_0^t u^i_s h^i_s ds`, `t ∈ [0, ∞]` (Giesecke–Shkolnik, manuscript
of January 16, 2018, eq. (7), p.9). -/
noncomputable def Qc (M : Model P n) (u : Fin n → ℝ≥0 → Ω → ℝ≥0) (i : Fin n) :
    WithTop ℝ≥0 → Ω → ℝ≥0∞ :=
  clock (fun s ω ↦ u i s ω * M.h i s ω)

/-- **The density `Z_∞`** (Giesecke–Shkolnik, manuscript of January 16, 2018, eq. (9) and fn 17,
p.9): `Z_∞ = L_∞^{-1}`, the expression in (9) with the exponent negated,
`Z_∞ = exp(∑_i (H^i − Q^i)_{τ_i}) ∏_i u^i_{τ_i}`.

**Formalization Note** The product form encodes the paper's `exp(… + ∑_i log u^i_{τ_i})` under its
convention `1/0 = ∞`: a factor `u^i_{τ_i} = 0` makes `Z_∞ = 0`; no logarithm is taken. The
formula is used on the event that every `τ_i` is finite; on the complementary event (which is
`P`-null, since `H^i_∞ = ∞` and `ξ_i < ∞`) the value is set to `1`. `(H^i − Q^i)_{τ_i}` is
computed as a difference of real numbers; both clocks are finite at a finite `τ_i` almost
surely. -/
noncomputable def density (M : Model P n) (u : Fin n → ℝ≥0 → Ω → ℝ≥0) (ω : Ω) : ℝ := by
  classical
  exact if hτ : ∀ i, M.τ i ω ≠ ⊤ then
    Real.exp (∑ i, ((M.H i (M.τ i ω) ω).toReal - (M.Qc u i (M.τ i ω) ω).toReal)) *
      ∏ i, ((u i ((M.τ i ω).untop (hτ i)) ω : ℝ≥0) : ℝ)
  else 1

/-- **The simulation measure `ℚ = Z_∞ P`** (Giesecke–Shkolnik, manuscript of January 16, 2018,
§3, p.9, Theorem 3.1): the measure with density `Z_∞` with respect to `P`. -/
noncomputable def simMeasure (M : Model P n) (u : Fin n → ℝ≥0 → Ω → ℝ≥0) : Measure Ω :=
  P.withDensity fun ω ↦ ENNReal.ofReal (M.density u ω)

/-- **Partial multiplier** (Giesecke–Shkolnik, manuscript of January 16, 2018, Appendix A,
p.27: "`L^ℓ_∞` … be in (9) but with `u^i = 1` for all `i > ℓ`"): `u` on the first `m` events
(indices `0, …, m − 1` of `Fin n`, the paper's `1, …, m`) and `1` on the others. With `m = ℓ`
the measure `simMeasure (uBefore u ℓ)` is the paper's `ℚ_ℓ = Z^ℓ_∞ P`. -/
def uBefore (u : Fin n → ℝ≥0 → Ω → ℝ≥0) (m : ℕ) : Fin n → ℝ≥0 → Ω → ℝ≥0 :=
  fun i ↦ if (i : ℕ) < m then u i else fun _ _ ↦ 1

/-- **Single-event density process** (Giesecke–Shkolnik, manuscript of January 16, 2018,
Appendix A, p.27): for event `j`, `0 ≤ t ≤ ∞`,
`Z_t = exp(∫_0^t (1 − u_s) p_s ds + N_t log(u_τ))`, written
`Z_t = exp((H − Q)_{t ∧ τ}) · (u_τ if τ ≤ t, else 1)`.

**Formalization Note** `∫_0^t (1 − u_s) p_s ds = (H − Q)_{t ∧ τ}` because `p_s = h_s 1{s < τ}`;
the exponential of `N_t log u_τ` is written as the factor `u_τ` on `{τ ≤ t}` (convention
`log 0 = −∞`, `e^{−∞} = 0`), so no logarithm is taken. The time `t` lives in `[0, ∞]`; `Z_∞` is
`zProc M u j ⊤`. On the `P`-null event `{τ = ∞}`, `u_τ` is read as `u_0`. -/
noncomputable def zProc (M : Model P n) (u : Fin n → ℝ≥0 → Ω → ℝ≥0) (j : Fin n)
    (t : WithTop ℝ≥0) (ω : Ω) : ℝ :=
  Real.exp ((M.H j (min t (M.τ j ω)) ω).toReal - (M.Qc u j (min t (M.τ j ω)) ω).toReal) *
    (if M.τ j ω ≤ t then ((u j ((M.τ j ω).untopD 0) ω : ℝ≥0) : ℝ) else 1)

/-- **Left limit `Z_{s−}`** of the single-event density process `zProc` at a finite time `s`
(Giesecke–Shkolnik, manuscript of January 16, 2018, Appendix A, eq. (41), p.28):
`Z_{s−} = exp((H − Q)_{s ∧ τ}) · (u_τ if τ < s, else 1)`.

**Formalization Note** Because `t ↦ (H − Q)_{t ∧ τ}` is continuous wherever the clocks are
finite, this is the left limit of `t ↦ Z_t` at `s > 0`; it is written in closed form. -/
noncomputable def zProcLeft (M : Model P n) (u : Fin n → ℝ≥0 → Ω → ℝ≥0) (j : Fin n)
    (s : ℝ≥0) (ω : Ω) : ℝ :=
  Real.exp ((M.H j (min (s : WithTop ℝ≥0) (M.τ j ω)) ω).toReal -
      (M.Qc u j (min (s : WithTop ℝ≥0) (M.τ j ω)) ω).toReal) *
    (if M.τ j ω < (s : WithTop ℝ≥0) then ((u j ((M.τ j ω).untopD 0) ω : ℝ≥0) : ℝ) else 1)

/-- **Localization times** (Giesecke–Shkolnik, manuscript of January 16, 2018, Appendix A,
eq. (40), p.27): for event `j` and `k ∈ ℕ`,
`θ_k = inf{t ≥ 0 : ∫_0^t (1 + u_s) h_s ds ≥ k}`.

**Formalization Note** The infimum is taken in `[0, ∞]`, so `θ_k = ∞` when the integral never
reaches `k`. -/
noncomputable def theta (M : Model P n) (u : Fin n → ℝ≥0 → Ω → ℝ≥0) (j : Fin n) (k : ℕ)
    (ω : Ω) : WithTop ℝ≥0 :=
  sInf {t : WithTop ℝ≥0 | ∃ s : ℝ≥0, t = s ∧
    (k : ℝ≥0∞) ≤ clock (fun r ω' ↦ (1 + u j r ω') * M.h j r ω') s ω}

end Model

end EventTimeMeasure


