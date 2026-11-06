-- Prove2me | Definitions.Def_PrefixVR_run
-- name    : PrefixVR_run
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:36:38.579204+00:00
-- url     : https://prove2.me/theorems/fcca0ba9-86a7-4aa1-9a5f-336464136237
-- title:
--   Run, iterates, output and query log of Algorithm 1
-- statement:
--   Given component gradient maps $g_i=\nabla f_i$, a stepsize $\eta$, an initial point $x_1$ and an outcome $\omega$ of the horizon-$T$ sample space, the **run** of Algorithm 1 is the initialization followed by updates $t=1,2,\dots$, with every component-gradient query $(i,x)$ appended to a log. From it the module defines
--
--   1. the iterates $x_t$ and active estimates $v_t$ ($t\ge1$), and the prefix accumulator $h_{s,r}$ after update $t=sn+r$;
--   2. the returned point $x_{\mathrm{out}}=x_\tau$ after $T$ updates;
--   3. the query log of the whole run, of the initialization alone, and of a single update $t$; the number of component-gradient queries is the length of the log;
--   4. the movement energy $S_u=\mathbb E\|x_{u+1}-x_u\|^2$ for $u\ge1$ and $S_u=0$ for $u\le0$ (Lemma 1).
--
--   **Formalization Note** The log records each evaluation of one $\nabla f_i$ at one point as one query, also when the same pair is asked twice (p.4). Times are 1-based.
-- source:
--   Jiang, Wang, Yang, Li, Zhang, Memory-efficient Finite-sum Optimization without Full Gradient Refreshes (manuscript, sha256 ed33106a…), Algorithm 1, p.5 (PDF p.5); §3.4, p.7; Lemma 1, p.6 (definition of S_t)

import Mathlib
import Definitions.Def_PrefixVR_step
import Definitions.Def_PrefixVR_Sample

namespace PrefixVR

/-- The query-logging monad: a computation that appends every oracle query `(i, x)` (component
`i` at point `x`) to a log. -/
abbrev QueryM (n d : ℕ) : Type → Type :=
  StateM (List (Fin n × EuclideanSpace ℝ (Fin d)))

/-- **A logged component-gradient query** (§3, p.4: "A component-gradient query returns ∇fᵢ(x)
for a specified index i and point x. … We count an evaluation of one ∇fᵢ at one point as one
query"). It appends `(i, x)` to the log and returns `g i x`. -/
def logOracle {n d : ℕ} (g : Fin n → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (i : Fin n) (x : EuclideanSpace ℝ (Fin d)) : QueryM n d (EuclideanSpace ℝ (Fin d)) := do
  modify (fun l => l ++ [(i, x)])
  pure (g i x)

/-- **Algorithm 1 for `k` updates** with oracle `oracle`, stepsize `η`, initial point `x₁`,
output index `τ` and draw sequence `D` (`D (t − 1)` is the pair of draws of update `t`): the
initialization followed by updates `t = 1, …, k`. Its value is the state before update `k + 1`.
Jiang, Wang, Yang, Li, Zhang (manuscript, sha256 ed33106a…), Algorithm 1, p.5. -/
noncomputable def runUpTo {m : Type → Type} [Monad m] {n d : ℕ} [NeZero n]
    (oracle : Fin n → EuclideanSpace ℝ (Fin d) → m (EuclideanSpace ℝ (Fin d)))
    (η : ℝ) (x₁ : EuclideanSpace ℝ (Fin d)) (τ : ℕ) (D : ℕ → ℕ × Fin n) : ℕ → m (State d)
  | 0 => init oracle x₁
  | k + 1 => do
      let st ← runUpTo oracle η x₁ τ D k
      step oracle η (k + 1) τ (D k).1 (D k).2 st

/-- **The run of Algorithm 1** on the outcome `ω` of the horizon-`T` sample space, with
component-gradient maps `g` (`g i = ∇fᵢ`), stepsize `η`, initial point `x₁`, after `k` updates,
in the query-logging monad. -/
noncomputable def run {n d T : ℕ} [NeZero n]
    (g : Fin n → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (η : ℝ) (x₁ : EuclideanSpace ℝ (Fin d)) (ω : Sample n T) (k : ℕ) : QueryM n d (State d) :=
  runUpTo (logOracle g) η x₁ (tau ω) (drawSeq ω) k

/-- The state of Algorithm 1 before update `t` (1-based; `stateAt … 1` is the initial state,
`stateAt … (T + 1)` the final one). -/
noncomputable def stateAt {n d T : ℕ} [NeZero n]
    (g : Fin n → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (η : ℝ) (x₁ : EuclideanSpace ℝ (Fin d)) (ω : Sample n T) (t : ℕ) : State d :=
  ((run g η x₁ ω (t - 1)).run []).1

/-- The iterate `x_t` of Algorithm 1 (`t ≥ 1`; `x₁` is the input). -/
noncomputable def xIter {n d T : ℕ} [NeZero n]
    (g : Fin n → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (η : ℝ) (x₁ : EuclideanSpace ℝ (Fin d)) (ω : Sample n T) (t : ℕ) :
    EuclideanSpace ℝ (Fin d) :=
  (stateAt g η x₁ ω t).x

/-- The active estimate `v_t` of Algorithm 1 (`t ≥ 1`; `v₁ = (1/n) ∑ᵢ ∇fᵢ(x₁)`). -/
noncomputable def vIter {n d T : ℕ} [NeZero n]
    (g : Fin n → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (η : ℝ) (x₁ : EuclideanSpace ℝ (Fin d)) (ω : Sample n T) (t : ℕ) :
    EuclideanSpace ℝ (Fin d) :=
  (stateAt g η x₁ ω t).v

/-- The prefix accumulator after update `t = sn + r` (`t ≥ 1`), i.e. `h_{s,r}` (5). -/
noncomputable def hAfter {n d T : ℕ} [NeZero n]
    (g : Fin n → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (η : ℝ) (x₁ : EuclideanSpace ℝ (Fin d)) (ω : Sample n T) (t : ℕ) :
    EuclideanSpace ℝ (Fin d) :=
  (stateAt g η x₁ ω (t + 1)).h

/-- The returned point `x_out = x_τ` of Algorithm 1 with horizon `T` (line 22, p.5). -/
noncomputable def output {n d T : ℕ} [NeZero n]
    (g : Fin n → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (η : ℝ) (x₁ : EuclideanSpace ℝ (Fin d)) (ω : Sample n T) : EuclideanSpace ℝ (Fin d) :=
  (stateAt g η x₁ ω (T + 1)).xout

/-- The full query log of Algorithm 1 with horizon `T` on the outcome `ω`: every
component-gradient query `(i, x)` made by the initialization and by the updates `1, …, T`, in
order. Its length is the number `N_grad` of component-gradient queries (§3.4, p.7). -/
noncomputable def queryLog {n d T : ℕ} [NeZero n]
    (g : Fin n → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (η : ℝ) (x₁ : EuclideanSpace ℝ (Fin d)) (ω : Sample n T) :
    List (Fin n × EuclideanSpace ℝ (Fin d)) :=
  ((run g η x₁ ω T).run []).2

/-- The queries made by the initialization (line 1, p.5). -/
noncomputable def initLog {n d : ℕ}
    (g : Fin n → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (x₁ : EuclideanSpace ℝ (Fin d)) : List (Fin n × EuclideanSpace ℝ (Fin d)) :=
  ((init (logOracle g) x₁).run []).2

/-- The queries made by update `t ≥ 1` alone (lines 3–20, p.5), started from the state before
update `t`, with the draws of `ω` for that update. -/
noncomputable def updateLog {n d T : ℕ} [NeZero n]
    (g : Fin n → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (η : ℝ) (x₁ : EuclideanSpace ℝ (Fin d)) (ω : Sample n T) (t : ℕ) :
    List (Fin n × EuclideanSpace ℝ (Fin d)) :=
  ((step (logOracle g) η t (tau ω) (drawSeq ω (t - 1)).1 (drawSeq ω (t - 1)).2
      (stateAt g η x₁ ω t)).run []).2

/-- **The movement energy** `S_u := 𝔼‖x_{u+1} − x_u‖²` for `u ≥ 1` and `S_u := 0` for `u ≤ 0`
(Lemma 1, p.6), for Algorithm 1 with horizon `T`. -/
noncomputable def moveEnergy {n d : ℕ} [NeZero n]
    (g : Fin n → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (η : ℝ) (x₁ : EuclideanSpace ℝ (Fin d)) (T u : ℕ) : ℝ :=
  if 1 ≤ u then expect (fun ω : Sample n T => ‖xIter g η x₁ ω (u + 1) - xIter g η x₁ ω u‖ ^ 2)
  else 0

end PrefixVR


