-- Prove2me | Definitions.Def_MulticlassOmni_Lipschitz_OmniRegret
-- name    : MulticlassOmni_Lipschitz_OmniRegret
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T22:09:44.658684+00:00
-- url     : https://prove2.me/theorems/79f3a0f7-f220-4b2d-8a24-2e93c569c7a6
-- title:
--   §2.1 — randomized batch learners, output law $P_D$, population regret, pseudo-omni-regret $\mathrm{OR}_D$ and tail omni-regret $\mathrm{OR}^{(\varepsilon)}_D$
-- statement:
--   Fix a finite domain $X\subseteq\mathbb R^k$ (a `Finset`, used as the type $\uparrow X$).
--
--   - A **predictor** (or benchmark) is a map $p:X\to\Delta_k$ into the closed simplex (`Predictor X`); the predictor space carries the Borel structure of a finite product of simplices, so randomization may be continuous.
--   - A **distribution** $D\in\Delta(X\times[k])$ is a nonnegative function on the finite set $X\times[k]$ summing to $1$ (`IsDist`).
--   - A **randomized learner with sample size $n$** (`Learner X n`) assigns to every data set $S\in(X\times[k])^n$ an arbitrary probability measure on predictors (the law of its output given $S$; its private randomness is independent of $D$ given $S$).
--   - Its **output law** under $D$ is $P_D=\sum_{S}\big(\prod_{j=1}^nD(S_j)\big)\,A(S)$ (`outputLaw`): the $n$ examples are i.i.d. from $D$.
--   - **Population regret** $R_D(p,\ell,f)=\sum_{(x,y)}D(x,y)\,[\ell(p(x),y)-\ell(f(x),y)]$ (`popRegret`); for proper losses the best response is the identity (p. 10).
--   - **Pseudo-omni-regret** $\mathrm{OR}_D(P;L,F)=\sup_{\ell\in L}\max_{f\in F}\mathbb E_{p\sim P}[R_D(p,\ell,f)]$ (`pseudoOmniRegret`, a supremum in `EReal`).
--   - **Tail omni-regret** $\mathrm{OR}^{(\varepsilon)}_D(P;L,F)=\sup_{\ell\in L}\max_{f\in F}\Pr_{p\sim P}[R_D(p,\ell,f)>\varepsilon]$ (`tailOmniRegret`, a supremum in $[0,\infty]$).
-- source:
--   Hu, Luo, Schneider, Yang (2026), Sample Complexity of Multiclass Omniprediction, supplied PDF (SHA-256 aaa73474…584f0, citation basis published; STOC 2027 submission), §2.1, pp. 9–10; learner model of Theorem 4.1, pp. 15–16

import Mathlib
import Definitions.Def_MulticlassOmni_Lipschitz_ProperLosses

noncomputable section

open MeasureTheory

namespace MulticlassOmni.Lipschitz

/-! # Randomized batch learners, population regret and pseudo-omni-regret (§2.1)

Hu, Luo, Schneider, Yang (2026), *Sample Complexity of Multiclass Omniprediction*, supplied PDF,
§2.1, pp. 9–10, and the learner model of Theorem 4.1, pp. 15–16.

The domain is a finite set `X ⊆ ℝ^k` (in Theorem 4.1 a subset of `Δ_k`), used as the type `↥X`.
Predictors are maps `p : X → Δ_k` into the closed simplex (the subtype `↥(stdSimplex ℝ (Fin k))`
with its Borel structure), so their randomization may be continuous as well as atomic. For a
proper loss the best response is the identity (p. 10), so regret is computed at `p(x)` itself. -/

/-- A report in the closed simplex `Δ_k`. -/
abbrev Simplex (k : ℕ) := ↥(stdSimplex ℝ (Fin k))

/-- A predictor (or benchmark) `p : X → Δ_k`. -/
abbrev Predictor {k : ℕ} (X : Finset (Fin k → ℝ)) := ↥X → Simplex k

/-- A data set of `n` labeled examples `((x_1, y_1), …, (x_n, y_n)) ∈ (X × [k])^n`. -/
abbrev Sample {k : ℕ} (X : Finset (Fin k → ℝ)) (n : ℕ) := Fin n → ↥X × Fin k

/-- `D ∈ Δ(X × [k])`: a probability mass function on the finite set `X × [k]`. -/
def IsDist {k : ℕ} {X : Finset (Fin k → ℝ)} (D : ↥X × Fin k → ℝ) : Prop :=
  (∀ z, 0 ≤ D z) ∧ ∑ z, D z = 1

/-- A randomized learner with sample size `n`: to every data set `S` it assigns the law of its
output predictor, an arbitrary probability measure on the predictor space (this is the
learner's private randomness, independent of the data-generating distribution given `S`). -/
abbrev Learner {k : ℕ} (X : Finset (Fin k → ℝ)) (n : ℕ) :=
  Sample X n → ProbabilityMeasure (Predictor X)

/-- `P_D`, the law of the learner's output predictor when its `n` examples are drawn i.i.d. from
`D`: `P_D = ∑_S (∏_{j} D(S_j)) · A(S)`, the learner's kernel integrated against `D^n`. -/
def outputLaw {k : ℕ} {X : Finset (Fin k → ℝ)} {n : ℕ} (A : Learner X n)
    (D : ↥X × Fin k → ℝ) : Measure (Predictor X) :=
  ∑ S : Sample X n, ENNReal.ofReal (∏ j, D (S j)) • ((A S : ProbabilityMeasure _) : Measure _)

/-- Population regret `R_D(p, ℓ, f) = E_{(x,y)∼D}[ℓ(p(x), y) - ℓ(f(x), y)]`. -/
def popRegret {k : ℕ} {X : Finset (Fin k → ℝ)} (D : ↥X × Fin k → ℝ) (ℓ : Loss k)
    (p f : Predictor X) : ℝ :=
  ∑ z : ↥X × Fin k, D z * (ℓ (p z.1 : Fin k → ℝ) z.2 - ℓ (f z.1 : Fin k → ℝ) z.2)

/-- Pseudo-omni-regret `OR_D(P; L, F) = sup_{ℓ∈L} max_{f∈F} E_{p∼P}[R_D(p, ℓ, f)]` (p. 10),
computed in `EReal` so that the supremum is a genuine supremum. -/
def pseudoOmniRegret {k : ℕ} {X : Finset (Fin k → ℝ)} (D : ↥X × Fin k → ℝ)
    (P : Measure (Predictor X)) (L : Set (Loss k)) (F : Set (Predictor X)) : EReal :=
  ⨆ ℓ ∈ L, ⨆ f ∈ F, ((∫ p, popRegret D ℓ p f ∂P : ℝ) : EReal)

/-- Tail omni-regret `OR^{(ε)}_D(P; L, F) = sup_{ℓ∈L} max_{f∈F} Pr_{p∼P}[R_D(p, ℓ, f) > ε]`
(p. 10), computed in `ℝ≥0∞`. -/
def tailOmniRegret {k : ℕ} {X : Finset (Fin k → ℝ)} (D : ↥X × Fin k → ℝ)
    (P : Measure (Predictor X)) (L : Set (Loss k)) (F : Set (Predictor X)) (ε : ℝ) :
    ENNReal :=
  ⨆ ℓ ∈ L, ⨆ f ∈ F, P {p | ε < popRegret D ℓ p f}

end MulticlassOmni.Lipschitz


