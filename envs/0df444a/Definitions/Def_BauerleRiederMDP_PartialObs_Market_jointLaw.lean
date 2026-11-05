-- Prove2me | Definitions.Def_BauerleRiederMDP_PartialObs_Market_jointLaw
-- name    : BauerleRiederMDP_PartialObs_Market_jointLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T07:01:22.100365+00:00
-- url     : https://prove2.me/theorems/7c815460-8290-4ea8-bc36-e2d6d3764034
-- title:
--   Joint law of the returns $(R_1,\dots,R_n)$ and the hidden state $Y_n$
-- statement:
--   Let $Y_0\sim\rho$. By (6.1), given $Y_n=y$ the next pair $(R_{n+1},Y_{n+1})$ has law $Q^R(\cdot\mid y)\otimes Q^Y(\cdot\mid y)$, independently of the past. The joint law $P_n^\rho$ of $\big((R_1,\dots,R_n),Y_n\big)$ is defined recursively: $P_0^\rho$ is the law of $((),Y_0)$, and $P^\rho_{n+1}$ is obtained from $P^\rho_n$ by drawing $(R_{n+1},Y_{n+1})\sim Q^R(\cdot\mid Y_n)\otimes Q^Y(\cdot\mid Y_n)$ and appending $R_{n+1}$ to the return path.
--
--   This is the law of the partially observable process of Section 5.1 restricted to the coordinates that matter in Chapter 6: the wealth is a function of the returns and the strategy.
--
--   **Formalization Note** Return paths are 0-indexed vectors in $(\mathbb R^d)^n$; the recursion uses `Measure.bind`.
-- source:
--   Bäuerle & Rieder (2011), eq. (6.1), p.175 (PDF 188); probability measure IP^π_x, p.150 (PDF 163)

import Mathlib
import Definitions.Def_BauerleRiederMDP_PartialObs_Market

open MeasureTheory ProbabilityTheory
open scoped ENNReal Matrix

namespace BauerleRiederMDP.PartialObs

/-- **The joint law of the observed returns `(R_1, …, R_n)` and the hidden state `Y_n`.**
Bäuerle & Rieder (2011), Chapter 6 introduction, eq. (6.1), p.175 (PDF 188): `(R_n, Y_n)` is a
Markov process with
`P(R_{n+1} ∈ B, Y_{n+1} ∈ C | Y_n = y, R_n) = Q^R(B|y) Q^Y(C|y)`,
and `Y_0` has the law `ρ` (the prior `Q_0` in the book, p.177).

`M.jointLaw ρ 0` is the law of `((), Y_0)` and `M.jointLaw ρ (n+1)` is obtained from
`M.jointLaw ρ n` by drawing `(R_{n+1}, Y_{n+1}) ~ Q^R(·|Y_n) ⊗ Q^Y(·|Y_n)` and appending
`R_{n+1}` to the return path. This is the law of the Partially Observable Markov Decision Process
of p.150 (PDF 163) restricted to the coordinates that matter for Chapter 6 (the wealth is a
function of the returns and the strategy).

**Formalization Note.** The return path is `Fin n → ℝ^d`, 0-indexed (`r k = R_{k+1}`). -/
noncomputable def Market.jointLaw {EY : Type*} [MeasurableSpace EY] {d : ℕ} (M : Market EY d)
    (ρ : ProbabilityMeasure EY) : (n : ℕ) → Measure ((Fin n → Fin d → ℝ) × EY)
  | 0 => (ρ : Measure EY).map (fun y => ((fun k : Fin 0 => k.elim0), y))
  | n + 1 => (Market.jointLaw M ρ n).bind (fun p =>
      ((M.QR p.2).prod (M.QY p.2)).map (fun q => (Fin.snoc p.1 q.1, q.2)))

end BauerleRiederMDP.PartialObs


