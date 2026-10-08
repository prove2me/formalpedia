-- Prove2me | Definitions.Def_SamuelCahnProphet_IID_Setting
-- name    : SamuelCahnProphet_IID_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T15:16:50.352911+00:00
-- url     : https://prove2.me/theorems/5b00f870-bb79-4e41-b203-c73095965ab9
-- title:
--   §1–§2, pp. 1213–1215 — i.i.d. samples, X*ₙ, threshold rules t(c), s(c), E⁺, the class T*ₙ, the three-point law, a* and Q(b, c)
-- statement:
--   This file sets up the objects of §2 (*Identically distributed $X_i$*) of Samuel-Cahn (1984).
--
--   **Samples.** Let $n \ge 1$ and let $\mu$ be a probability law on $\mathbb R$. A sample is a vector $x = (x_1, \dots, x_n) \in \mathbb R^n$, and the i.i.d. model is the product measure $\mu^{\otimes n}$ on $\mathbb R^n$: under it the coordinates $X_1, \dots, X_n$ are independent with common law $\mu$. The maximum is $X_n^* = \max(X_1, \dots, X_n)$.
--
--   **Threshold rules** (p. 1213). For a constant $c$,
--
--   - $t(c)$ is the smallest $i < n$ with $X_i \ge c$, and $t(c) = n$ otherwise;
--   - $s(c)$ is the smallest $i < n$ with $X_i > c$, and $s(c) = n$ otherwise.
--
--   Both rules always stop, at the latest at time $n$. The stopped values are $X_{t(c)}$ and $X_{s(c)}$.
--
--   **Expectations.** All expectations are taken in $[0, \infty]$, of the nonnegative part:
--   $$
--   EX_n^*, \qquad EX_{t(c)}, \qquad EX_{s(c)}, \qquad E^+X_{t(c)} = E[X_{t(c)} I(X_{t(c)} \ge c)], \qquad E^+X_{s(c)} = E[X_{s(c)} I(X_{s(c)} > c)].
--   $$
--
--   **The class $T_n^*$** (§2, p. 1214) is the set of all threshold rules $s(c)$ and $t(c)$ with $c \ge 0$, so
--   $$
--   \sup_{t \in T_n^*} EX_t = \sup_{c \ge 0} \max\{EX_{t(c)}, EX_{s(c)}\}, \qquad \sup_{t \in T_n^*} E^+X_t = \sup_{c \ge 0} \max\{E^+X_{t(c)}, E^+X_{s(c)}\}.
--   $$
--
--   **The extremal family** (proof of Theorem 2, p. 1215). For reals $n > 0$, $a$, $b$, $c$, the law $\nu_{n,a,b,c}$ puts mass $1 - (b+c)/n$ at $0$, mass $c/n$ at $a$ and mass $b/n$ at $1$. It is a probability measure when $b, c \ge 0$ and $b + c \le n$. With it come the two constants
--   $$
--   a^*(b,c) = \frac{c(1 - e^{-b}) - b e^{-b}(1 - e^{-c})}{c(1 - e^{-b-c})}, \qquad
--   Q(b, c) = 1 + \frac{e^{-b} - e^{-b-c}}{1 - e^{-b-c}} - \frac{b(e^{-b} - e^{-b-c})^2}{c(1 - e^{-b-c})(1 - e^{-b})}.
--   $$
--   This $a^*$ is the one of the proof of Theorem 2; it is unrelated to the $a^*$ of the NOTE in §1, which the paper denotes by the same symbol.
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note.** Indices are 0-based: the paper's $X_i$ is the coordinate `x ⟨i − 1, _⟩` of `x : Fin n → ℝ`, and the paper's index $n$ is `⊤ : Fin n` (with `[NeZero n]`). `tIdx x c` is the least index $i$ with $c \le x_i$ or $i = \top$, which is exactly "smallest $i < n$ with $X_i \ge c$, $n$ otherwise"; `sIdx` is the same with $<$. Expectations are `lintegral`s of `ENNReal.ofReal`, so no integrability hypothesis is needed and the value $+\infty$ is allowed. The weights of `threePoint` are `ENNReal.ofReal` of the printed probabilities; outside $b + c \le n$ the clipped weights do not form a probability measure, and every statement using the law either assumes $b + c < n$ or concerns a limit $n \to \infty$, where the condition holds eventually.
-- source:
--   Samuel-Cahn, Comparison of threshold stop rules and maximum for independent nonnegative random variables, Ann. Probab. 12 (1984), pp. 1213–1215: §1 p. 1213 (t(c), s(c), E⁺), §2 pp. 1214–1215 (T*ₙ), proof of Theorem 2 p. 1215 (three-point law, a*, Q(b, c))

import Mathlib

namespace SamuelCahnProphet.IID

open MeasureTheory

/-- `X*ₙ = max(x₁, …, xₙ)` of a sample `x : Fin n → ℝ` (p. 1213). -/
noncomputable def maxV {n : ℕ} [NeZero n] (x : Fin n → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty x

/-- The threshold rule `t(c)` on a sample (p. 1213): the smallest (0-based) index `i` before the
last with `c ≤ x i`, and the last index `⊤` (the paper's `n`) otherwise. -/
noncomputable def tIdx {n : ℕ} [NeZero n] (x : Fin n → ℝ) (c : ℝ) : Fin n :=
  (Finset.univ.filter (fun i : Fin n => c ≤ x i ∨ i = ⊤)).min' ⟨⊤, by simp⟩

/-- The threshold rule `s(c)` on a sample (p. 1213): the smallest (0-based) index `i` before the
last with `c < x i`, and the last index `⊤` (the paper's `n`) otherwise. -/
noncomputable def sIdx {n : ℕ} [NeZero n] (x : Fin n → ℝ) (c : ℝ) : Fin n :=
  (Finset.univ.filter (fun i : Fin n => c < x i ∨ i = ⊤)).min' ⟨⊤, by simp⟩

/-- The i.i.d. model: the law of `(X₁, …, Xₙ)` with `Xᵢ` i.i.d. of law `μ`, on the coordinate space. -/
noncomputable def iidLaw (μ : Measure ℝ) (n : ℕ) : Measure (Fin n → ℝ) :=
  Measure.pi (fun _ : Fin n => μ)

/-- `E X*ₙ`, in `[0, ∞]`. -/
noncomputable def Emax (μ : Measure ℝ) (n : ℕ) [NeZero n] : ENNReal :=
  ∫⁻ x, ENNReal.ofReal (maxV x) ∂(iidLaw μ n)

/-- `E X_{t(c)}`, in `[0, ∞]`. -/
noncomputable def EstopT (μ : Measure ℝ) (n : ℕ) [NeZero n] (c : ℝ) : ENNReal :=
  ∫⁻ x, ENNReal.ofReal (x (tIdx x c)) ∂(iidLaw μ n)

/-- `E X_{s(c)}`, in `[0, ∞]`. -/
noncomputable def EstopS (μ : Measure ℝ) (n : ℕ) [NeZero n] (c : ℝ) : ENNReal :=
  ∫⁻ x, ENNReal.ofReal (x (sIdx x c)) ∂(iidLaw μ n)

/-- `E⁺X_{t(c)} = E[X_{t(c)} I(X_{t(c)} ≥ c)]` (p. 1213). -/
noncomputable def EplusT (μ : Measure ℝ) (n : ℕ) [NeZero n] (c : ℝ) : ENNReal :=
  ∫⁻ x, (if c ≤ x (tIdx x c) then ENNReal.ofReal (x (tIdx x c)) else 0) ∂(iidLaw μ n)

/-- `E⁺X_{s(c)} = E[X_{s(c)} I(X_{s(c)} > c)]` (p. 1213). -/
noncomputable def EplusS (μ : Measure ℝ) (n : ℕ) [NeZero n] (c : ℝ) : ENNReal :=
  ∫⁻ x, (if c < x (sIdx x c) then ENNReal.ofReal (x (sIdx x c)) else 0) ∂(iidLaw μ n)

/-- `sup_{t ∈ T*ₙ} E X_t`, where `T*ₙ = {t(c), s(c) : c ≥ 0}` (§2, p. 1214). -/
noncomputable def supE (μ : Measure ℝ) (n : ℕ) [NeZero n] : ENNReal :=
  ⨆ (c : ℝ) (_ : 0 ≤ c), max (EstopT μ n c) (EstopS μ n c)

/-- `sup_{t ∈ T*ₙ} E⁺X_t` (§2, p. 1214–1215). -/
noncomputable def supEplus (μ : Measure ℝ) (n : ℕ) [NeZero n] : ENNReal :=
  ⨆ (c : ℝ) (_ : 0 ≤ c), max (EplusT μ n c) (EplusS μ n c)

/-- The law of `Xᵢ⁽ⁿ⁾` in the proof of Theorem 2 (p. 1215): the values `0`, `a`, `1` with
probabilities `1 − (b + c)/n`, `c/n`, `b/n`. It is a probability measure when `0 ≤ b`, `0 ≤ c`,
`b + c ≤ n`, `0 < n`. -/
noncomputable def threePoint (n a b c : ℝ) : Measure ℝ :=
  ENNReal.ofReal (1 - (b + c) / n) • Measure.dirac 0 + ENNReal.ofReal (c / n) • Measure.dirac a
    + ENNReal.ofReal (b / n) • Measure.dirac 1

/-- The proof's `a* = [c(1 − e^{−b}) − b e^{−b}(1 − e^{−c})] / [c(1 − e^{−b−c})]` (p. 1215). Not the
`a*` of the NOTE in §1. -/
noncomputable def aStarIID (b c : ℝ) : ℝ :=
  (c * (1 - Real.exp (-b)) - b * Real.exp (-b) * (1 - Real.exp (-c))) /
    (c * (1 - Real.exp (-b - c)))

/-- `Q(b, c) = 1 + (e^{−b} − e^{−b−c})/(1 − e^{−b−c}) − b(e^{−b} − e^{−b−c})² / [c(1 − e^{−b−c})(1 − e^{−b})]`
(p. 1215). -/
noncomputable def Q (b c : ℝ) : ℝ :=
  1 + (Real.exp (-b) - Real.exp (-b - c)) / (1 - Real.exp (-b - c))
    - b * (Real.exp (-b) - Real.exp (-b - c)) ^ 2 /
      (c * (1 - Real.exp (-b - c)) * (1 - Real.exp (-b)))

end SamuelCahnProphet.IID


