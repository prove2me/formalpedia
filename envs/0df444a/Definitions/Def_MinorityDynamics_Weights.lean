-- Prove2me | Definitions.Def_MinorityDynamics_Weights
-- name    : MinorityDynamics_Weights
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:16:26.932292+00:00
-- url     : https://prove2.me/theorems/bf6a051a-217d-446b-ab96-ad29b71c3195
-- title:
--   Weights α, π, w, the matrix Q, the contributions 𝓛 and 𝓡, δ_s and the logarithmic distance Δ
-- statement:
--   With the notation of the module `Chain`, the module defines the weight construction of §4 (Definition 4.4) and the quantities used in its estimates:
--
--   1. $A(t)=1-\dfrac{9\ln t}{5\ln k}-\dfrac{t}{8L}$ for $1\le t\le L+\ln k+2$ (4.5), and $\alpha(x)=A(\ln(1/x))$ (4.4).
--   2. The reference weights $\pi(x)=\alpha(x)/(32nx)$ for $x\in\mathcal S\cap(K/n,b)$ and $\pi(x)=1/n$ for $x\in\mathcal S\cap(c,1/2)$.
--   3. The final weights $w(x)=\pi(x)\big/\big(1+\sqrt{k/(nx)}\big)$, $x\in\mathcal S$ (4.7).
--   4. The matrix $Q(x,y)=P_{ny}(f(x))+P_{n-ny}(f(x))$, $x,y\in\mathcal S$ (4.1), of the auxiliary chain killed on entering $\mathcal H$.
--   5. $(\pi Q)(y)=\sum_{x\in\mathcal S}\pi(x)Q(x,y)$ and $(wQ)(y)=\sum_{x\in\mathcal S}w(x)Q(x,y)$.
--   6. The normalized contributions $\mathcal L(y)=\frac1{\pi(y)}\sum_{x\in\mathcal S\cap(0,a)}\pi(x)Q(x,y)$ and $\mathcal R(y)=\frac1{\pi(y)}\sum_{x\in\mathcal S\cap([a,b)\cup(c,1/2))}\pi(x)Q(x,y)$.
--   7. $\delta_s=\sqrt{L\ln L/s}$ (4.8) and the logarithmic error $\Delta(x,y)=|\ln x-\ln y|$ (§6.1).
--
--   These are the objects of Lemmas 4.2, 4.5 and 4.6: the weight vector $w$ is a sub-eigenvector of $Q$, which gives the hitting-time bound of Lemma 3.1.
--
--   **Formalization Note** $A$, $\alpha$ are written as formulas on all reals and only evaluated inside their domain by the statements. $\pi$ is written as $\alpha(x)/(32nx)$ when $K/n<x<b$, $1/n$ when $c<x<1/2$, and $0$ elsewhere; it is only evaluated at surviving states. All functions of states take the count $s=nx$.
-- source:
--   Giakkoupis, Los, Sauerwald, Ziccardi, Minority Dynamics with Small Samples, manuscript (STOC 2027 submission), §4.1, p.14, (4.1); §4.2, p.15, (4.4)–(4.5); Definition 4.4, p.18, (4.7); §4.4, pp.18–19, (4.8); §6.1, p.32

import Mathlib
import Definitions.Def_MinorityDynamics_Chain

set_option autoImplicit false

namespace MinorityDynamics

open Classical

/-- The function `A(t) = 1 − 9 ln t/(5 ln k) − t/(8L)`, `1 ≤ t ≤ L + ln k + 2` (Giakkoupis, Los,
Sauerwald, Ziccardi, *Minority Dynamics with Small Samples*, manuscript (STOC 2027 submission),
(4.5), p.15 = PDF p.17, and Definition 4.4, p.18 = PDF p.20).

**Formalization Note** The formula is written for every real `t`; every statement of the mission
evaluates it only at `t = ln(1/x)` for surviving states `x ∈ (K/n, b)` and at `t = ln(k/x)`, which
lie in the stated domain for large `n`. -/
noncomputable def AFun (n k : ℕ) (t : ℝ) : ℝ :=
  1 - 9 * Real.log t / (5 * Real.log k) - t / (8 * logN n)

/-- The **weight coefficients** `α(x) = A(ln(1/x))` (manuscript, (4.4), p.15, Definition 4.4,
p.18). -/
noncomputable def alphaW (n k : ℕ) (x : ℝ) : ℝ := AFun n k (Real.log (1 / x))

/-- The **reference weights** (manuscript, Definition 4.4, p.18 = PDF p.20):
`π(x) = α(x)/(32nx)` for `x ∈ S ∩ (K/n, b)` and `π(x) = 1/n` for `x ∈ S ∩ (c, 1/2)`.

**Formalization Note** `piRef n k x` is the formula for a fraction `x`: `α(x)/(32nx)` when
`K/n < x < b`, `1/n` when `c < x < 1/2`, and `0` elsewhere. It is only evaluated at surviving
states `x = s/n`, `s ∈ S`, which lie in exactly one of the two intervals. -/
noncomputable def piRef (n k : ℕ) (x : ℝ) : ℝ :=
  if KK n k / n < x ∧ x < bPt n k then alphaW n k x / (32 * n * x)
  else if cPt n k < x ∧ x < 1 / 2 then 1 / (n : ℝ)
  else 0

/-- The **final weights** (4.7) (manuscript, Definition 4.4, p.18 = PDF p.20):
`w(x) = π(x) / (1 + √(k/(nx)))`, `x ∈ S`. -/
noncomputable def wFinal (n k : ℕ) (x : ℝ) : ℝ :=
  piRef n k x / (1 + Real.sqrt ((k : ℝ) / (n * x)))

/-- The matrix `Q` of the stopped auxiliary chain (4.1) (manuscript, §4.1, p.14 = PDF p.16):
`Q(x, y) = P_{ny}(f(x)) + P_{n−ny}(f(x))` for `x, y ∈ S`, as a function of the counts
`s = nx`, `s' = ny`.

**Formalization Note** Defined for all counts; every statement uses it with `s, s' ∈ S`. -/
noncomputable def Qmat (n k : ℕ) (s s' : Fin (n + 1)) : ℝ :=
  binomPMF n (fMap n k (((s : ℕ) : ℝ) / n)) s' + binomPMF n (fMap n k (((s : ℕ) : ℝ) / n)) (n - s')

/-- The surviving states `S` as a finite set of counts. -/
noncomputable def SFin (n k : ℕ) : Finset (Fin (n + 1)) :=
  Finset.univ.filter (fun s => s ∈ Sset n k)

/-- `(πQ)(y) = ∑_{x ∈ S} π(x) Q(x, y)` (manuscript, §4.4, p.18 = PDF p.20), at the count `s' = ny`. -/
noncomputable def piQ (n k : ℕ) (s' : Fin (n + 1)) : ℝ :=
  ∑ s ∈ SFin n k, piRef n k (((s : ℕ) : ℝ) / n) * Qmat n k s s'

/-- `(wQ)(y) = ∑_{x ∈ S} w(x) Q(x, y)` (manuscript, Lemma 4.6, p.19 = PDF p.21), at the count
`s' = ny`. -/
noncomputable def wQ (n k : ℕ) (s' : Fin (n + 1)) : ℝ :=
  ∑ s ∈ SFin n k, wFinal n k (((s : ℕ) : ℝ) / n) * Qmat n k s s'

/-- The normalized **lower-branch contribution** (manuscript, §4.4, p.18 = PDF p.20):
`𝓛(y) = (1/π(y)) ∑_{x ∈ S ∩ (0, a)} π(x) Q(x, y)`, at the count `s' = ny`. -/
noncomputable def Lcontrib (n k : ℕ) (s' : Fin (n + 1)) : ℝ :=
  (1 / piRef n k (((s' : ℕ) : ℝ) / n)) *
    ∑ s ∈ (SFin n k).filter (fun s : Fin (n + 1) => 0 < ((s : ℕ) : ℝ) / n ∧ ((s : ℕ) : ℝ) / n < aPt k),
      piRef n k (((s : ℕ) : ℝ) / n) * Qmat n k s s'

/-- The normalized **middle- and upper-branch contribution** (manuscript, §4.4, p.18):
`𝓡(y) = (1/π(y)) ∑_{x ∈ S ∩ ([a, b) ∪ (c, 1/2))} π(x) Q(x, y)`, at the count `s' = ny`. -/
noncomputable def Rcontrib (n k : ℕ) (s' : Fin (n + 1)) : ℝ :=
  (1 / piRef n k (((s' : ℕ) : ℝ) / n)) *
    ∑ s ∈ (SFin n k).filter (fun s : Fin (n + 1) =>
        (aPt k ≤ ((s : ℕ) : ℝ) / n ∧ ((s : ℕ) : ℝ) / n < bPt n k) ∨
          (cPt n k < ((s : ℕ) : ℝ) / n ∧ ((s : ℕ) : ℝ) / n < 1 / 2)),
      piRef n k (((s : ℕ) : ℝ) / n) * Qmat n k s s'

/-- `δ_s = √(L ln L / s)` (4.8) (manuscript, p.19 = PDF p.21). -/
noncomputable def deltaS (n : ℕ) (s : ℝ) : ℝ := Real.sqrt (logN n * Real.log (logN n) / s)

/-- The **logarithmic error** `Δ(x, y) = |ln(x/y)| = |ln x − ln y|` for `x, y > 0` (manuscript,
§6.1, p.32 = PDF p.34). -/
noncomputable def logDist (x y : ℝ) : ℝ := |Real.log x - Real.log y|

end MinorityDynamics


