-- Prove2me | Definitions.Def_ProcessingNetworks_ProportionalFairness_EntropyLyapunov
-- name    : ProcessingNetworks_ProportionalFairness_EntropyLyapunov
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T19:16:47.758367+00:00
-- url     : https://prove2.me/theorems/2fcd1570-2add-4d3e-9d8e-8588cc898c40
-- title:
--   The Dini derivative and the entropy Lyapunov function φ (Eqs. 10.38-10.39)
-- statement:
--   The **entropy Lyapunov function**, Eqs. (10.38)-(10.39): $\varphi(t) := \sum_i Z_i(t)
--   \log(\dot D_i(t)/\alpha_i)$, with the term for class $i$ defined to be $0$ when $Z_i(t) = 0$
--   (the book's own convention, since $\dot D_i(t)$ need not otherwise be defined or positive
--   there). $D^+\varphi$ is the upper-right Dini derivative (Eq. A.9).
--
--   **Formalization note.** `diniUpperRight` duplicates mission V's `LyapunovCriteria.diniUpperRight`
--   definition; this chunk's own dependency list does not include mission V, so per this series'
--   restate-rather-than-import convention it is restated here rather than cross-imported. It takes
--   values in the extended reals, so that $\pm\infty$ values (which the Dini derivative of a merely
--   continuous function can take) are represented as such rather than by a junk real, which would
--   make Lemma 10.8's bound vacuous exactly where it matters. In `phi`, $\dot D_i(t)$ is the right
--   derivative (`derivWithin … (Ici t)`), the one-sided derivative appropriate for a process defined
--   on $t \ge 0$; for a PF fluid model solution, (10.34) makes it exist and be positive whenever
--   $Z_i(t) > 0$, so `phi` is (10.38) at every $t \ge 0$.
-- source:
--   Dai & Harrison, Processing Networks: Fluid Models and Stability, pre-publication draft 2020-4-2, p. 196-197, Section 10.5, Eqs. (10.38)-(10.39); Appendix A.4, Eq. (A.9) (restated)

import Mathlib

namespace ProcessingNetworks.ProportionalFairness

/-- The upper-right Dini derivative `D⁺f(t)`, Appendix A.4, Eq. (A.9) — restated locally as in
mission V's `LyapunovCriteria` sub-namespace (this chunk's own `BRIEF.md` does not list mission V
as a dependency, so per this series' restate-not-import convention the definition is duplicated
here rather than cross-imported; see `MODERATION_NOTES.md`). It takes values in the extended reals
`EReal`, so that `+∞`/`-∞` (which the Dini derivative of a merely continuous function can take)
are represented as such rather than by a junk real value. -/
noncomputable def diniUpperRight (f : ℝ → ℝ) (t : ℝ) : EReal :=
  Filter.limsup (fun h : ℝ => (((f (t + h) - f t) / h : ℝ) : EReal))
    (nhdsWithin (0 : ℝ) (Set.Ioi 0))

/-- The entropy Lyapunov function `φ` (Eqs. 10.38-10.39): `φ(t) := ∑_i Z_i(t) log(Ḋ_i(t)/α_i)`,
with the convention that the term for class `i` is `0` when `Z_i(t) = 0` (the only case in which
`Ḋ_i(t)` need not exist or be positive). `Ḋ_i(t)` is the right derivative `derivWithin … (Ici t)`,
which at `t = 0` is the one-sided derivative of a process defined on `t ≥ 0` and at `t > 0` agrees
with the ordinary derivative wherever it exists; for a fluid model solution satisfying (10.34),
`Ḋ_i(t)` exists and is positive whenever `Z_i(t) > 0`, so `φ` is the book's (10.38) at every
`t ≥ 0`. -/
noncomputable def phi {I : ℕ} (Dh Zh : ℝ → Fin I → ℝ) (alpha : Fin I → ℝ) (t : ℝ) : ℝ :=
  ∑ i, if Zh t i = 0 then 0 else
    Zh t i * Real.log (derivWithin (fun s => Dh s i) (Set.Ici t) t / alpha i)

end ProcessingNetworks.ProportionalFairness


