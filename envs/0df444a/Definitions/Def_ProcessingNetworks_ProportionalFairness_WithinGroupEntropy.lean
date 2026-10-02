-- Prove2me | Definitions.Def_ProcessingNetworks_ProportionalFairness_WithinGroupEntropy
-- name    : ProcessingNetworks_ProportionalFairness_WithinGroupEntropy
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T19:29:42.656582+00:00
-- url     : https://prove2.me/theorems/75720652-fd62-45d0-8dde-b2bacba57eca
-- title:
--   Dini derivatives, the entropy Lyapunov function φ, and the within-group entropy term f (Eqs. 10.38-10.39, 10.50)
-- statement:
--   The **entropy Lyapunov function**, Eqs. (10.38)-(10.39), restated identically from mission IX:
--   $\varphi(t) := \sum_i Z_i(t) \log(\dot D_i(t)/\alpha_i)$, term $0$ when $Z_i(t) = 0$. `D⁺`/`D⁻`
--   are the upper-right/upper-left Dini derivatives (Eqs. A.9-A.10). New to this chunk: the
--   **within-group entropy term**, Eq. (10.50), $$f(t) := \sum_{\ell\in\mathcal L}
--   \sum_{i\in\mathcal I(\ell)} Z_i(t)\log\!\left(\frac{Z_i(t)}{Y_\ell(t)}\right),$$ term $0$ when
--   $Z_i(t)=0$ (conventions 10.46).
--
--   **Formalization note.** Renamed `withinGroupEntropy` to avoid colliding with the PF objective
--   `f` (Eq. 10.2) — the book itself reuses the letter `f` for two distinct quantities in this
--   chapter. `withinGroupEntropy` uses `Real.log`, not an extended log: $Z_i(t) \le Y_{\mathrm{grp}\,
--   i}(t)$ always, so the ratio is a genuine element of $[0,1]$ whenever $Z_i(t) > 0$, and no
--   $-\infty$ value ever arises here (unlike the PF objective `f`). The Dini derivatives take values
--   in the extended reals (a real-valued `limsup` would replace $\pm\infty$ by a junk real and make
--   the bounds of Lemmas 10.8 and 10.13 vacuous where they matter), and $\dot D_i(t)$ in $\varphi$
--   is the right derivative, matching mission IX.
-- source:
--   Dai & Harrison, Processing Networks: Fluid Models and Stability, pre-publication draft 2020-4-2, p. 196-197, 199, Section 10.5, Eqs. (10.38)-(10.39),(10.46),(10.50); Appendix A.4, Eqs. (A.9)-(A.10)

import Mathlib
import Definitions.Def_ProcessingNetworks_ProportionalFairness_RestatedCore

namespace ProcessingNetworks.ProportionalFairness

/-- The upper-right Dini derivative `D⁺f(t)`, Appendix A.4, Eq. (A.9), restated identically from
mission IX (which itself restates mission V's `LyapunovCriteria.diniUpperRight`); `EReal`-valued,
so that `±∞` values are represented as such rather than by a junk real. -/
noncomputable def diniUpperRight (f : ℝ → ℝ) (t : ℝ) : EReal :=
  Filter.limsup (fun h : ℝ => (((f (t + h) - f t) / h : ℝ) : EReal))
    (nhdsWithin (0 : ℝ) (Set.Ioi 0))

/-- The upper-left Dini derivative `D⁻f(t)`, Appendix A.4, Eq. (A.10) — new to this chunk (mission
IX only needed `D⁺`): `D⁻f(t) := limsup_{h ↓ 0} (f(t) - f(t-h))/h`. -/
noncomputable def diniUpperLeft (f : ℝ → ℝ) (t : ℝ) : EReal :=
  Filter.limsup (fun h : ℝ => (((f t - f (t - h)) / h : ℝ) : EReal))
    (nhdsWithin (0 : ℝ) (Set.Ioi 0))

/-- The entropy Lyapunov function `φ` (Eqs. 10.38-10.39), restated identically from mission IX
(`Ḋᵢ(t)` the right derivative, which for a PF fluid model solution exists and is positive
whenever `Zᵢ(t) > 0`). -/
noncomputable def phi {I : ℕ} (Dh Zh : ℝ → Fin I → ℝ) (alpha : Fin I → ℝ) (t : ℝ) : ℝ :=
  ∑ i, if Zh t i = 0 then 0 else
    Zh t i * Real.log (derivWithin (fun s => Dh s i) (Set.Ici t) t / alpha i)

/-- The within-group entropy term `f` (Eq. 10.50, renamed `withinGroupEntropy` to avoid colliding
with the PF objective `f` of Eq. 10.2 — the book itself reuses the letter `f` for two different
quantities within this chapter): `f(t) := ∑_ℓ ∑_{i∈I(ℓ)} Z_i(t) log(Z_i(t)/Y_ℓ(t))`, with the term
for class `i` defined to be `0` when `Z_i(t) = 0` (conventions 10.46: `0/0=0`, `0log(0)=0`). Since
`Z_i(t) ≤ Y_{grp i}(t)` always, the ratio is a genuine real number in `[0,1]` whenever `Z_i(t) >
0`, so `Real.log` (not an extended log) suffices here — unlike the PF objective `f`, this term
never needs `-∞`. -/
noncomputable def withinGroupEntropy {I L : ℕ} (grp : Fin I → Fin L) (Zh : ℝ → Fin I → ℝ)
    (t : ℝ) : ℝ :=
  ∑ i, if Zh t i = 0 then 0 else Zh t i * Real.log (Zh t i / groupAggregate grp (Zh t) (grp i))

end ProcessingNetworks.ProportionalFairness


