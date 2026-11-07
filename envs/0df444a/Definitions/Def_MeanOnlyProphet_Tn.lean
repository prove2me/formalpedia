-- Prove2me | Definitions.Def_MeanOnlyProphet_Tn
-- name    : MeanOnlyProphet_Tn
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T03:23:03.55668+00:00
-- url     : https://prove2.me/theorems/941984d4-cff1-4704-8ba9-5000200513f6
-- title:
--   Finite-$n$ quantities $P$, $\overline P$, $A_P$, $T_n$, $D_n$ and $\mathcal E$
-- statement:
--   Fix $n\ge1$ and a nonnegative rate $q$ on $[0,1]$, possibly $+\infty$-valued. Define
--   1. $P(t)=\exp\!\left(-\frac1n\sum_{j=1}^{\lfloor nt\rfloor}q\!\left(t-\frac jn\right)\right)$ for $t\in[0,1+\frac1n]$;
--   2. $\overline P(t)=n\int_t^{t+1/n}P(s)\,ds$ and $A_P(t)=\int_t^1P(s)\,ds$ for $t\in[0,1]$;
--   3. $T_n(t)=1-\overline P(t)+n\left(1-e^{-q(t)/n}\right)A_P(t)$ for $0\le t\le 1-\frac1n$, and $T_n(t)=1-e^{-q(t)/n}\,\overline P(1-\frac1n)$ for $1-\frac1n<t\le1$;
--   4. $D_n(t)=T_\infty(t)-T_n(t)$ and $\mathcal E=A_P(0)-A(0)$.
--
--   For the input rate $q=r$, $P(\sigma_i)$ is the conditional probability that the randomly shifted rule sees the $i$-th arrival, and $T_n(t)$ is the probability that its reward exceeds $\theta(t)$ (Lemma A.3). The comparison of $T_n$ with $T_\infty$ carries the guarantee from $n\to\infty$ to every $n$.
--
--   **Formalization Note** Sums are taken in $[0,\infty]$ with $e^{-\infty}=0$; $\lfloor nt\rfloor$ is `Nat.floor`. For $t\in[0,1+1/n]$ every argument $t-j/n$ lies in $[0,1]$.
-- source:
--   Feng, Jin, Wu, Xiang, Mean-only Prophet Inequalities, arXiv:2610.24711 (held version, sha256 c68bfec4…74e93a), App. A.2, pp.28–30 (PDF pp.29–31), Lemma A.3

import Mathlib
import Definitions.Def_MeanOnlyProphet_Tinf

namespace MeanOnlyProphet

/-- **`P(t) = exp(−(1/n) Σ_{j=1}^{⌊nt⌋} q(t − j/n))`.** Feng, Jin, Wu, Xiang, *Mean-only Prophet
Inequalities*, arXiv:2610.24711 (held version, sha256 c68bfec4…), App. A.2, p.28 (PDF p.29): "For t ∈
[0, 1 + 1/n], define P(t) = exp(−(1/n) · Σ_{j=1}^{⌊nt⌋} r(t − j/n))", with `r` replaced by a general
rate `q` (p.30: "We define the quantities with finite n by replacing r with q").

**Formalization Note.** The sum is taken in `ℝ≥0∞` and `e^{−∞} = 0` (`eNeg`); `⌊nt⌋` is `Nat.floor`.
For `t ∈ [0, 1 + 1/n]` every argument `t − j/n` lies in `[0, 1]`. -/
noncomputable def Pfun (n : ℕ) (q : ℝ → ENNReal) (t : ℝ) : ℝ :=
  eNeg ((n : ENNReal)⁻¹ * ∑ j ∈ Finset.Icc 1 ⌊(n : ℝ) * t⌋₊, q (t - (j : ℝ) / n))

/-- **`P̄(t) = n · ∫_t^{t+1/n} P(s) ds`.** Feng, Jin, Wu, Xiang, arXiv:2610.24711 (held version), App.
A.2, p.29 (PDF p.30). (The overbar distinguishes it from `P`.) -/
noncomputable def Pbar (n : ℕ) (q : ℝ → ENNReal) (t : ℝ) : ℝ :=
  n * ∫ s in t..t + 1 / (n : ℝ), Pfun n q s

/-- **`A_P(t) = ∫_t^1 P(s) ds`.** Feng, Jin, Wu, Xiang, arXiv:2610.24711 (held version), App. A.2,
p.29 (PDF p.30). -/
noncomputable def AP (n : ℕ) (q : ℝ → ENNReal) (t : ℝ) : ℝ :=
  ∫ s in t..1, Pfun n q s

/-- **`T_n(t)`, the finite-`n` tail probability of Lemma A.3.** Feng, Jin, Wu, Xiang, *Mean-only Prophet
Inequalities*, arXiv:2610.24711 (held version, sha256 c68bfec4…), Lemma A.3, p.29 (PDF p.30):
`T_n(t) = 1 − P̄(t) + n · (1 − e^{−q(t)/n}) · A_P(t)` for `0 ≤ t ≤ 1 − 1/n`, and
`T_n(t) = 1 − e^{−q(t)/n} · P̄(1 − 1/n)` for `1 − 1/n < t ≤ 1`.

**Formalization Note.** `e^{−q(t)/n}` is `eNeg (q t / n)` (so it is `0` when `q t = +∞`); `1 − 1/n` is
computed in `ℝ`. Only `t ∈ [0, 1]` is meaningful. -/
noncomputable def Tn (n : ℕ) (q : ℝ → ENNReal) (t : ℝ) : ℝ :=
  if t ≤ 1 - 1 / (n : ℝ) then
    1 - Pbar n q t + n * (1 - eNeg (q t / n)) * AP n q t
  else
    1 - eNeg (q t / n) * Pbar n q (1 - 1 / (n : ℝ))

/-- **`D_n(t) = T∞(t) − T_n(t)`.** Feng, Jin, Wu, Xiang, arXiv:2610.24711 (held version), App. A.2,
p.30 (PDF p.31). -/
noncomputable def Dn (n : ℕ) (q : ℝ → ENNReal) (t : ℝ) : ℝ :=
  Tinf q t - Tn n q t

/-- **`ℰ = A_P(0) − A(0)`.** Feng, Jin, Wu, Xiang, *Mean-only Prophet Inequalities*, arXiv:2610.24711
(held version, sha256 c68bfec4…), App. A.2, p.30 (PDF p.31): "Let ℰ = A_P(0) − A(0) and Dn(t) = T∞(t) −
Tn(t)." -/
noncomputable def Ecal (n : ℕ) (q : ℝ → ENNReal) : ℝ :=
  AP n q 0 - areaA q 0

end MeanOnlyProphet


