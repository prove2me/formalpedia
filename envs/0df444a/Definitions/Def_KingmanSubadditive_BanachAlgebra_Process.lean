-- Prove2me | Definitions.Def_KingmanSubadditive_BanachAlgebra_Process
-- name    : KingmanSubadditive_BanachAlgebra_Process
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:15:04.714987+00:00
-- url     : https://prove2.me/theorems/4485e53d-ffa6-4b7c-9444-7461c3635878
-- title:
--   §1.1–1.2: two-parameter processes, conditions S₁, S₂, S₃, S₃′, the truncation x^(N) and the extended expectation
-- statement:
--   This module fixes the vocabulary of §1.1 and §1.2 of Kingman's *Subadditive ergodic theory* for families of random variables $x_{st}$ indexed by pairs of nonnegative integers $s<t$, defined on a probability space $(\Omega,\mathcal F,P)$.
--
--   1. **Index pairs and paths.** The index set is $\{(s,t)\in\mathbb N^2 : s<t\}$. The **path** of the family at $\omega$ is $(x_{st}(\omega))_{s<t}$ and the **shifted path** is $(x_{s+1,t+1}(\omega))_{s<t}$. The value type is $\mathbb R$ for the processes of §1.1 and $[-\infty,\infty]$ for the log-norm process of §2.3.
--   2. **Measurability.** Every $x_{st}$, $s<t$, is a random variable.
--   3. **Condition S₁**, (1.1.1): whenever $s<t<u$,
--   $$x_{su}\le x_{st}+x_{tu}.$$
--   4. **Condition S₂**: the joint distributions of $(x_{s+1,t+1})$ are the same as those of $(x_{st})$, i.e. the shifted path and the path have the same law on the product $\sigma$-algebra.
--   5. **Condition S₃**, (1.1.2)–(1.1.3): for every $t\ge1$ the expectation $g_t=E(x_{0t})$ exists and is finite, and $g_t\ge -At$ for some constant $A$ and all $t\ge 1$.
--   6. **Condition S₃′** (p. 885): $E(x_{01}^+)<\infty$, where $x^+=\max(x,0)$.
--   7. A **subadditive process** is a measurable real family satisfying S₁, S₂ and S₃.
--   8. The **truncation** of the proof of Theorem 2: for a positive integer $N$,
--   $$x^{(N)}_{st}=\max\big(x_{st},\,-N(t-s)\big).$$
--   9. The **extended expectation** of an $[-\infty,\infty]$-valued random variable $f$ is
--   $$E(f)=\int f^+\,dP-\int f^-\,dP\in[-\infty,\infty],$$
--   which is well defined whenever $\int f^+\,dP<\infty$ and may equal $-\infty$.
--
--   These are the objects in which Theorem 2 (the extension of Kingman's ergodic theorem from S₃ to S₃′) and the reduction of Theorem 6 to it are stated.
--
--   **Formalization Note** The family is a function `x : ℕ → ℕ → Ω → β`; only pairs $s<t$ enter any condition. S₁ is required almost surely, separately for each triple $s<t<u$, which is weaker than requiring it at every $\omega$. S₃′ and positive-part integrals are lower Lebesgue integrals. The extended expectation is computed in `EReal`; it is never a Bochner integral, which would return $0$ for a non-integrable function.
-- source:
--   Kingman, Subadditive ergodic theory, Ann. Probab. 1(6):883–899 (1973), DOI 10.1214/aop/1176996798, pp. 883–886, §1.1 (S₁, S₂, S₃, (1.1.1)–(1.1.3)), §1.2 (S₃′, proof of Theorem 2)

import Mathlib
import Definitions.Def_KingmanSubadditive_Ergodic_Process

namespace KingmanSubadditive.BanachAlgebra

open MeasureTheory

/-- The whole sample path `(x_st)_{s<t}` of a two-parameter family at the sample point `ω`. The
value type `β` is `ℝ` for the processes of §1.1 and `EReal` for the log-norm process of §2.3. -/
def path {Ω β : Type*} (x : ℕ → ℕ → Ω → β) (ω : Ω) : KingmanSubadditive.Ergodic.Interval → β :=
  fun p => x p.1.1 p.1.2 ω

/-- The shifted sample path `(x_{s+1,t+1})_{s<t}` (§1.1, p. 884, condition S₂; the shift
`x'_st = x_{s+1,t+1}` of (1.2.3), p. 885). -/
def shiftedPath {Ω β : Type*} (x : ℕ → ℕ → Ω → β) (ω : Ω) : KingmanSubadditive.Ergodic.Interval → β :=
  fun p => x (p.1.1 + 1) (p.1.2 + 1) ω

/-- Measurability: every `x_st`, `s < t`, is a random variable. -/
def IsMeasurableFamily {Ω β : Type*} [MeasurableSpace Ω] [MeasurableSpace β]
    (x : ℕ → ℕ → Ω → β) : Prop :=
  ∀ s t : ℕ, s < t → Measurable (x s t)

/-- Condition **S₁**, (1.1.1), p. 883: whenever `s < t < u`, `x_su ≤ x_st + x_tu`.

**Formalization Note.** The inequality between random variables is required almost surely,
separately for each triple `s < t < u` (countably many null sets). This is weaker than a pointwise
requirement, so theorems assuming it are at least as strong as with the pointwise reading. -/
def S1 {Ω β : Type*} [MeasurableSpace Ω] [Add β] [LE β] (P : Measure Ω)
    (x : ℕ → ℕ → Ω → β) : Prop :=
  ∀ s t u : ℕ, s < t → t < u → ∀ᵐ ω ∂P, x s u ω ≤ x s t ω + x t u ω

/-- Condition **S₂**, p. 884: "The joint distributions of the process `(x_{s+1,t+1})` are the same
as those of `(x_st)`." Encoded as equality of the laws of the whole shifted and unshifted sample
paths on the product σ-algebra of `Interval → β` (all finite-dimensional distributions). This is
strictly stronger than the one-dimensional condition S₂′. -/
def S2 {Ω β : Type*} [MeasurableSpace Ω] [MeasurableSpace β] (P : Measure Ω)
    (x : ℕ → ℕ → Ω → β) : Prop :=
  Measure.map (shiftedPath x) P = Measure.map (path x) P

/-- Condition **S₃′**, p. 885, for a real process: `E(x₀₁⁺) < ∞`, written as the lower Lebesgue
integral of the positive part `x₀₁⁺ = max(x₀₁, 0)`. -/
def S3' {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (x : ℕ → ℕ → Ω → ℝ) : Prop :=
  ∫⁻ ω, ENNReal.ofReal (x 0 1 ω) ∂P < ⊤

/-- A **subadditive process** (§1.1, p. 884): a family of real random variables `x_st`, `s < t`,
satisfying S₁, S₂ and S₃. -/
def IsSubadditiveProcess {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (x : ℕ → ℕ → Ω → ℝ) : Prop :=
  IsMeasurableFamily x ∧ S1 P x ∧ S2 P x ∧ KingmanSubadditive.Ergodic.S3 P x

/-- The truncated process of the proof of Theorem 2 (p. 886):
`x_st^(N) = max(x_st, −N(t − s))`. -/
def truncate {Ω : Type*} (x : ℕ → ℕ → Ω → ℝ) (N : ℕ) : ℕ → ℕ → Ω → ℝ :=
  fun s t ω => max (x s t ω) (-(N : ℝ) * ((t : ℝ) - (s : ℝ)))

/-- The extended-real expectation `E(f) = ∫ f⁺ dP − ∫ f⁻ dP ∈ [−∞, +∞]` of an `EReal`-valued
random variable, the difference of the lower Lebesgue integrals of the positive part `f⁺` and the
negative part `f⁻ = (−f)⁺`, computed in `EReal`.

**Formalization Note.** This is the expectation the paper uses whenever a mean may be `−∞`
((1.2.9), (1.2.10), (2.3.5)). It is meaningful when `∫ f⁺ < ∞`; every theorem that uses it either
assumes or concludes that. (If both parts were `+∞`, `EReal` subtraction would return `⊥`; that
case never arises in the statements of this mission.) It is never a Bochner integral, which would
return `0` for a non-integrable function. -/
noncomputable def eMean {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (f : Ω → EReal) : EReal :=
  ((∫⁻ ω, (f ω).toENNReal ∂P : ENNReal) : EReal) - ((∫⁻ ω, (-f ω).toENNReal ∂P : ENNReal) : EReal)

end KingmanSubadditive.BanachAlgebra


