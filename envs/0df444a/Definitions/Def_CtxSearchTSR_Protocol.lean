-- Prove2me | Definitions.Def_CtxSearchTSR_Protocol
-- name    : CtxSearchTSR_Protocol
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:33:47.077087+00:00
-- url     : https://prove2.me/theorems/0f25b3f9-acf6-4f44-861d-acf3447887c2
-- title:
--   The contextual-search protocol: loss $|x^\top z-P|$, feedback $\operatorname{sign}(x^\top z-P)$ with $\operatorname{sign}(0)=1$, adaptive context strategies
-- statement:
--   In **contextual search** a learner looks for an unknown target $z\in\mathbb R^d$. At each round the learner receives a context $x\in\mathbb R^d$ with $\|x\|_2\le 1$, posts a price $P\in\mathbb R$, suffers the loss
--
--   $$\ell=|x^\top z-P|,$$
--
--   and observes only the one-bit feedback $Y=\operatorname{sign}(x^\top z-P)$, with the convention $\operatorname{sign}(0)=1$. It observes neither $x^\top z$ nor the loss.
--
--   This module fixes:
--
--   1. $\operatorname{sign}$ with $\operatorname{sign}(0)=1$, and the map from a learner coin $b\in\{\text{true},\text{false}\}$ to the sign $\pm1$;
--   2. the Euclidean norm $\|v\|_2=\sqrt{v^\top v}$;
--   3. the loss $\ell$ and the feedback $Y$ of a posted price;
--   4. **adaptive context strategies**: the context of round $t$ is a function of the learner's previous random signs. Contexts may adapt to the observed history but are chosen before the learner's fresh randomization; for a fixed target and a deterministic strategy the whole history (contexts, prices, feedback, past signs) is a function of the past signs, so this covers every such strategy.
--
--   These are the objects in which Theorem 2.4 is stated.
--
--   **Formalization Note** Vectors are `Fin d → ℝ` with the dot product; the Euclidean norm is written out as $\sqrt{v^\top v}$, never Mathlib's default sup norm on `Fin d → ℝ`. Rounds are indexed from $0$.
-- source:
--   Cosson, Fusco, Gupta, Leonardi, Paes Leme, Russo, Contextual Search and Bilateral Trade with a Trace-Square-Root Potential, STOC 2027 submission manuscript (sha256 70eeb0d19227c9eee557cdff5598f97062f442373fcde3a3eb76a6cb65a2ad6c), §1.4 Notation and §2, p.7

import Mathlib

open Matrix

namespace CtxSearchTSR

/-!
# The contextual-search protocol

Cosson, Fusco, Gupta, Leonardi, Paes Leme, Russo, *Contextual Search and Bilateral Trade with a
Trace-Square-Root Potential*, STOC 2027 submission (manuscript sha256 70eeb0d1…),
§1.4 "Notation" and §2, p.7.

"In contextual search, the learner is looking for an unknown target z ∈ ℝ^d. At round t, the
learner receives a context x_t with ‖x_t‖₂ ≤ 1, posts P_t ∈ ℝ, suffers loss ℓ_t = |x_tᵀz − P_t|, and
receives feedback Y_t = sign(x_tᵀz − P_t)" (p.7). "We set sign(0) = 1" (p.7). "Contexts may adapt
to this history but are chosen before the learner's fresh randomization" (p.7).

**Formalization Note.** Vectors of ℝ^d are `Fin d → ℝ`, with the dot product `⬝ᵥ`. The Euclidean
norm ‖v‖₂ is `eucNorm v = √(v ⬝ᵥ v)`; Mathlib's default norm on `Fin d → ℝ` (the sup norm) is
never used. The learner's random signs are `Bool`, mapped to ±1 by `signOf` (`true ↦ 1`).
-/

/-- The sign function with the paper's convention sign(0) = 1 (§1.4, p.7). -/
noncomputable def sgn0 (v : ℝ) : ℝ := if 0 ≤ v then 1 else -1

/-- A learner sign `b : Bool` as the real number ±1 (`true ↦ 1`, `false ↦ -1`). -/
def signOf (b : Bool) : ℝ := if b then 1 else -1

/-- The Euclidean norm ‖v‖₂ = √(vᵀv) on ℝ^d (§1.4, p.7). -/
noncomputable def eucNorm {d : ℕ} (v : Fin d → ℝ) : ℝ := Real.sqrt (v ⬝ᵥ v)

/-- The loss ℓ = |xᵀz − P| of posting the price `P` at context `x` for the target `z` (§2, p.7). -/
noncomputable def searchLoss {d : ℕ} (z x : Fin d → ℝ) (P : ℝ) : ℝ := |x ⬝ᵥ z - P|

/-- The one-bit feedback Y = sign(xᵀz − P), with sign(0) = 1 (§2, p.7). -/
noncomputable def feedback {d : ℕ} (z x : Fin d → ℝ) (P : ℝ) : ℝ := sgn0 (x ⬝ᵥ z - P)

/-- An adaptive (non-anticipating) context strategy: the context of round `t` (0-based; the paper's
round t + 1) is a function of the learner's previous `t` random signs.

**Formalization Note.** For a fixed target `z` and a deterministic strategy, the whole observed
history before round `t` (contexts, posted prices, feedback and the learner's randomization, §1.4
p.7) is a function of the learner's first `t` signs, so this type covers every strategy that adapts
to the history. The strategy never sees the current sign, as the paper requires. The strategy may
also depend on `z` (it is chosen after `z` is fixed). -/
abbrev ContextStrategy (d : ℕ) : Type := (t : ℕ) → (Fin t → Bool) → (Fin d → ℝ)

end CtxSearchTSR


