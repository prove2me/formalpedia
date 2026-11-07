-- Prove2me | Definitions.Def_CtxSearchTSR_ExpectedTotalLoss
-- name    : CtxSearchTSR_ExpectedTotalLoss
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:35:03.575125+00:00
-- url     : https://prove2.me/theorems/b94d1157-6dca-4e1b-ad74-c787617b8e1b
-- title:
--   The expected total loss $\sum_{t=1}^T\mathbb E[\ell_t]$ of Algorithm 2 over the learner's random signs
-- statement:
--   Fix a target $z\in\mathbb R^d$, an adaptive context strategy $X$ and a horizon $T$. The only randomness in the interaction is the learner's signs $\varepsilon_1,\dots,\varepsilon_T$, independent and uniform on $\{-1,1\}$. The **expected total loss** is
--
--   $$\sum_{t=1}^T\mathbb E[\ell_t]=\frac1{2^T}\sum_{\varepsilon\in\{-1,1\}^T}\ \sum_{t=1}^T\bigl|x_t^\top z-P_t\bigr|,$$
--
--   where $x_t$, $P_t$ are the context and the price of round $t$ in the run of Algorithm 2 with signs $\varepsilon$.
--
--   **Formalization Note** The expectation is the average over the $2^T$ sign vectors (`Fin T → Bool`). A sign vector is extended to an infinite sequence by a fixed value beyond round $T$; rounds $1,\dots,T$ never read it.
-- source:
--   Cosson, Fusco, Gupta, Leonardi, Paes Leme, Russo, Contextual Search and Bilateral Trade with a Trace-Square-Root Potential, STOC 2027 submission manuscript (sha256 70eeb0d19227c9eee557cdff5598f97062f442373fcde3a3eb76a6cb65a2ad6c), §2, p.7 (total loss) and Theorem 2.4, p.10

import Mathlib
import Definitions.Def_CtxSearchTSR_Algorithm2

open Matrix

namespace CtxSearchTSR

/-!
# The expected total loss Σ_{t=1}^T 𝔼[ℓ_t] of Algorithm 2

Cosson, Fusco, Gupta, Leonardi, Paes Leme, Russo, *Contextual Search and Bilateral Trade with a
Trace-Square-Root Potential*, STOC 2027 submission (manuscript sha256 70eeb0d1…),
§2, p.7 (the total loss Σ_{t=1}^T 𝔼[ℓ_t]) and Theorem 2.4, p.10.

**Formalization Note.** The only randomness is the learner's signs ε_1, …, ε_T, i.i.d. uniform on
{−1, 1} (Algorithm 2, step 2). The expectation is therefore the average over the 2^T sign vectors
`Fin T → Bool`. A sign vector is extended to ℕ by `true` after round T − 1; rounds 0, …, T − 1
never read a sign beyond index T − 1, so the extension does not matter. By linearity,
Σ_t 𝔼[ℓ_t] = 𝔼[Σ_t ℓ_t].
-/

/-- Extend a finite sign vector to a sign sequence (by `true` beyond its length). -/
def extendSigns {T : ℕ} (ε : Fin T → Bool) : ℕ → Bool :=
  fun i => if h : i < T then ε ⟨i, h⟩ else true

/-- The loss ℓ = |**x**ᵀ**z** − P| of round `t` (0-based) of Algorithm 2 run against `z` and `X` with
the signs `ε`. -/
noncomputable def roundLoss {d : ℕ} (z : Fin d → ℝ) (X : ContextStrategy d) (ε : ℕ → Bool)
    (t : ℕ) : ℝ :=
  searchLoss z (X t (fun i => ε i.val))
    (price (run z X ε t) (X t (fun i => ε i.val)) (signOf (ε t)))

/-- The expected total loss Σ_{t=1}^T 𝔼[ℓ_t] of Algorithm 2 over `T` rounds, the expectation being
over the learner's i.i.d. uniform signs. -/
noncomputable def expectedTotalLoss {d : ℕ} (z : Fin d → ℝ) (X : ContextStrategy d) (T : ℕ) : ℝ :=
  ((2 : ℝ) ^ T)⁻¹ * ∑ ε : Fin T → Bool, ∑ t : Fin T, roundLoss z X (extendSigns ε) t.val

end CtxSearchTSR


