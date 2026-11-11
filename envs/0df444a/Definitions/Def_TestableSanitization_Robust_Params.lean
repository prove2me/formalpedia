-- Prove2me | Definitions.Def_TestableSanitization_Robust_Params
-- name    : TestableSanitization_Robust_Params
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T18:52:42.877203+00:00
-- url     : https://prove2.me/theorems/7933a236-3046-4a16-a8c1-aa6cc29bb233
-- title:
--   The parameters (1) and (4) and the isolation test of Algorithm 3: $s$, $b$, $m$, $K$, $\tilde\phi_i$ and $\hat I$
-- statement:
--   **Parameters (1).** For a testing radius $L>r>0$ in dimension $d$, the correction radius and the isolation threshold are
--   $$s=\sqrt{L^2-r^2+\tfrac{16r^2}{d}}-\tfrac{4r}{\sqrt d},\qquad b=\tfrac1{32}\Big(\tfrac sL\Big)^d$$
--   (`sParam d L r`, `bParam d L r`).
--
--   **Parameters (4).** For an acceptance threshold $a$ and a failure probability $\zeta$, the number of sampled points and of perturbations per point are
--   $$m=\Big\lceil\tfrac{50}{a}\log\tfrac8\zeta\Big\rceil,\qquad K=\Big\lceil\tfrac{12}{b}\log\tfrac{8m}{\zeta}\Big\rceil$$
--   (`mParam a ζ`, `KParam b m ζ`).
--
--   **The isolation test (Algorithm 3).** Draw $x_1,\dots,x_m$ i.i.d. from $D$ and, independently, $Z_{ij}$ ($i\le m$, $j\le K$) i.i.d. from $U$; `isoLaw D m K` is the joint law. At each sampled point the estimate of $\phi_{f,L}(x_i)$ is
--   $$\tilde\phi_i=\frac1K\sum_{j=1}^K\mathbb 1\{f(x_i+LZ_{ij})\neq f(x_i)\}$$
--   (`phiTilde`), and the empirical isolation statistic is $\hat I=\frac1m\sum_{i=1}^m\mathbb 1\{\tilde\phi_i>b/2\}$ (`isoStat f L b m K`). The test passes when $\hat I\le a$ and rejects when $\hat I>a$.
--
--   These are the quantities the proof of Theorem 1 analyses; the goal itself is existential over algorithms and does not mention them.
--
--   **Formalization Note.** The ceilings are natural-number ceilings `⌈·⌉₊`; `Real.log` and `Real.sqrt` are the usual functions on the positive reals (they are only applied to positive arguments under the hypotheses of the statements that use them). The draws are indexed by `Fin m` and `Fin m → Fin K`.
-- source:
--   Cai, Mamali, Sotiraki, Yu, Zampetakis, Testable Sanitization via Boundary Geometry, STOC 2027 submission (manuscript sha256 bcf6434f…), p. 22 (PDF 24), Eq. (1) and the statistic Iso-hat; p. 23 (PDF 25), Algorithm 3; p. 24 (PDF 26), Eq. (4)

import Mathlib
import Definitions.Def_TestableSanitization_Robust_Boundary

/-!
# The parameters (1) and (4) and the isolation test of Algorithm 3

Cai, Mamali, Sotiraki, Yu, Zampetakis, *Testable Sanitization via Boundary Geometry*, STOC 2027
submission (manuscript sha256 bcf6434f…), §4.1: Eq. (1) p. 22, Algorithm 3 p. 23, Eq. (4) p. 24.

Conventions.
* `sParam d L r = √(L² − r² + 16r²/d) − 4r/√d` and `bParam d L r = (1/32)(s/L)^d` are the
  correction radius and the isolation threshold of (1).
* `mParam a ζ = ⌈(50/a) log(8/ζ)⌉` and `KParam b m ζ = ⌈(12/b) log(8m/ζ)⌉` are the sample and
  perturbation counts of (4) (natural-number ceilings).
* The isolation test draws `x_1, …, x_m` i.i.d. from `D` and, independently, `Z_{ij}`
  (`i ≤ m`, `j ≤ K`) i.i.d. from `U`; `isoLaw D m K` is the joint law of `(x, Z)`.
* `phiTilde f L x Z = (1/K) Σ_j 1{f(x + L Z_j) ≠ f(x)}` is the estimate `ϕ̃_i` at one sampled
  point, and `isoStat f L b m K ω = (1/m) Σ_i 1{ϕ̃_i > b/2}` is the statistic `Î`; the test passes
  when `Î ≤ a`.
-/

open MeasureTheory

namespace TestableSanitization.Robust

/-- The correction radius `s = √(L² − r² + 16r²/d) − 4r/√d` of (1), p. 22. -/
noncomputable def sParam (d : ℕ) (L r : ℝ) : ℝ :=
  Real.sqrt (L ^ 2 - r ^ 2 + 16 * r ^ 2 / d) - 4 * r / Real.sqrt d

/-- The isolation threshold `b = (1/32)(s/L)^d` of (1), p. 22. -/
noncomputable def bParam (d : ℕ) (L r : ℝ) : ℝ :=
  (1 / 32) * (sParam d L r / L) ^ d

/-- The number of sampled points `m = ⌈(50/a) log(8/ζ)⌉` of (4), p. 24. -/
noncomputable def mParam (a ζ : ℝ) : ℕ :=
  ⌈(50 / a) * Real.log (8 / ζ)⌉₊

/-- The number of perturbations per point `K = ⌈(12/b) log(8m/ζ)⌉` of (4), p. 24. -/
noncomputable def KParam (b : ℝ) (m : ℕ) (ζ : ℝ) : ℕ :=
  ⌈(12 / b) * Real.log (8 * m / ζ)⌉₊

/-- The joint law of the isolation test's draws: `x_1, …, x_m` i.i.d. from `D` and, independently,
`Z_{ij}` i.i.d. from `U` (Algorithm 3, p. 23). -/
noncomputable def isoLaw {d : ℕ} (D : Measure (Pt d)) (m K : ℕ) :
    Measure ((Fin m → Pt d) × (Fin m → Fin K → Pt d)) :=
  (Measure.pi fun _ : Fin m => D).prod (Measure.pi fun _ : Fin m => Measure.pi fun _ : Fin K => U d)

open Classical in
/-- `ϕ̃ = (1/K) Σ_{j} 1{f(x + L Z_j) ≠ f(x)}`, the estimate of `ϕ_{f,L}(x)` (Algorithm 3). -/
noncomputable def phiTilde {d K : ℕ} (f : Pt d → ℝ) (L : ℝ) (x : Pt d) (Z : Fin K → Pt d) : ℝ :=
  ((Finset.univ.filter fun j : Fin K => f (x + L • Z j) ≠ f x).card : ℝ) / K

open Classical in
/-- The empirical isolation statistic `Î = (1/m) Σ_i 1{ϕ̃_i > b/2}` (Algorithm 3, p. 23). -/
noncomputable def isoStat {d : ℕ} (f : Pt d → ℝ) (L b : ℝ) (m K : ℕ)
    (ω : (Fin m → Pt d) × (Fin m → Fin K → Pt d)) : ℝ :=
  ((Finset.univ.filter fun i : Fin m => b / 2 < phiTilde f L (ω.1 i) (ω.2 i)).card : ℝ) / m

end TestableSanitization.Robust


