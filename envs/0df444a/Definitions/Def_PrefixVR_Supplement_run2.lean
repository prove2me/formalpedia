-- Prove2me | Definitions.Def_PrefixVR_Supplement_run2
-- name    : PrefixVR_Supplement_run2
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:51:05.280504+00:00
-- url     : https://prove2.me/theorems/d3471da8-2494-4654-b7c6-8cfcb81d0376
-- title:
--   The run of Algorithm 2, its output $x_{\tau+1}$ and its gradient and proximal logs
-- statement:
--   The **run of Algorithm 2**: initialization $v_1=\frac1n\sum_{i=1}^n\nabla f_i(x_1)$ ($n$ gradient queries, the base's `PrefixVR.init`) followed by updates $t=1,\dots,T$ (`step2`), on an outcome of the sample space, with component gradients $\nabla f_i$ and proximal map $\operatorname{prox}_{\eta g}$. The module defines the iterates $x_t$, the returned point $x_{\rm out}=x_{\tau+1}$, and the two logs: every component-gradient query $(i,x)$ and every proximal evaluation, in order. Their lengths are $N_{\rm grad}$ and $N_{\rm prox}$.
--
--   **Formalization Note** The logging monad is a state monad over a pair of lists; the oracles append one entry per call. Times are 1-based: `stateAt2 … t` is the state before update $t$, and `output2` is the saved output after update $T$.
-- source:
--   Jiang, Wang, Yang, Li, Zhang, Memory-efficient Finite-sum Optimization without Full Gradient Refreshes (manuscript, sha256 ed33106a…), Algorithm 2, p.10 (PDF p.10); App. F, 'Batched query and proximal counts', p.25

import Mathlib
import Definitions.Def_PrefixVR_step
import Definitions.Def_PrefixVR_Supplement_step2
import Definitions.Def_PrefixVR_Supplement_Sample2

namespace PrefixVR.Supplement

open PrefixVR

/-- The logging monad of Algorithm 2: a computation that appends every component-gradient query
`(i, x)` to the first log and every proximal call `z` to the second. -/
abbrev LogM2 (n d : ℕ) : Type → Type :=
  StateM (List (Fin n × EuclideanSpace ℝ (Fin d)) × List (EuclideanSpace ℝ (Fin d)))

/-- A logged component-gradient query (§3, p.4: one evaluation of one `∇fᵢ` at one point is one
query): appends `(i, x)` to the gradient log and returns `gf i x`. -/
def logGrad {n d : ℕ} (gf : Fin n → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (i : Fin n) (x : EuclideanSpace ℝ (Fin d)) : LogM2 n d (EuclideanSpace ℝ (Fin d)) := do
  modify (fun l => (l.1 ++ [(i, x)], l.2))
  pure (gf i x)

/-- A logged proximal evaluation: appends `z` to the proximal log and returns `P z`. -/
def logProx {n d : ℕ} (P : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (z : EuclideanSpace ℝ (Fin d)) : LogM2 n d (EuclideanSpace ℝ (Fin d)) := do
  modify (fun l => (l.1, l.2 ++ [z]))
  pure (P z)

/-- **Algorithm 2 for `k` updates** with gradient oracle `oracle`, proximal oracle `proxO`,
stepsize `η`, batch size `b`, initial point `x₁`, output index `τ` and draw sequence `D`
(`D (t − 1)` holds the draws of update `t`): the initialization (line 2, p.10: `v₁ = (1/n) ∑ᵢ
∇fᵢ(x₁)`, the base's `PrefixVR.init`) followed by updates `t = 1, …, k`.
Jiang, Wang, Yang, Li, Zhang (manuscript, sha256 ed33106a…), Algorithm 2, p.10. -/
noncomputable def runUpTo2 {m : Type → Type} [Monad m] {n d : ℕ} [NeZero n]
    (oracle : Fin n → EuclideanSpace ℝ (Fin d) → m (EuclideanSpace ℝ (Fin d)))
    (proxO : EuclideanSpace ℝ (Fin d) → m (EuclideanSpace ℝ (Fin d)))
    (η : ℝ) (b : ℕ) (x₁ : EuclideanSpace ℝ (Fin d)) (τ : ℕ)
    (D : ℕ → (Fin b → ℕ) × (Fin b → Fin n)) : ℕ → m (State d)
  | 0 => init oracle x₁
  | k + 1 => do
      let st ← runUpTo2 oracle proxO η b x₁ τ D k
      step2 oracle proxO η b (k + 1) τ (D k).1 (D k).2 st

/-- **The run of Algorithm 2** on the outcome `ω`, with component-gradient maps `gf`
(`gf i = ∇fᵢ`), proximal map `P` (`P = prox_{ηg}`), stepsize `η`, batch size `b`, initial
point `x₁`, after `k` updates, in the logging monad. -/
noncomputable def run2 {n d T : ℕ} [NeZero n]
    (gf : Fin n → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (P : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (η : ℝ) (b : ℕ)
    (x₁ : EuclideanSpace ℝ (Fin d)) (ω : Sample2 n b T) (k : ℕ) : LogM2 n d (State d) :=
  runUpTo2 (logGrad gf) (logProx P) η b x₁ (tau2 ω) (drawSeq2 ω) k

/-- The state of Algorithm 2 before update `t` (1-based; `stateAt2 … (T + 1)` is final). -/
noncomputable def stateAt2 {n d T : ℕ} [NeZero n]
    (gf : Fin n → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (P : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (η : ℝ) (b : ℕ)
    (x₁ : EuclideanSpace ℝ (Fin d)) (ω : Sample2 n b T) (t : ℕ) : State d :=
  ((run2 gf P η b x₁ ω (t - 1)).run ([], [])).1

/-- The iterate `x_t` of Algorithm 2 (`t ≥ 1`; `x₁` is the input). -/
noncomputable def xIter2 {n d T : ℕ} [NeZero n]
    (gf : Fin n → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (P : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (η : ℝ) (b : ℕ)
    (x₁ : EuclideanSpace ℝ (Fin d)) (ω : Sample2 n b T) (t : ℕ) : EuclideanSpace ℝ (Fin d) :=
  (stateAt2 gf P η b x₁ ω t).x

/-- The returned point `x_out = x_{τ+1}` of Algorithm 2 with horizon `T` (line 19, p.10). -/
noncomputable def output2 {n d T : ℕ} [NeZero n]
    (gf : Fin n → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (P : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (η : ℝ) (b : ℕ)
    (x₁ : EuclideanSpace ℝ (Fin d)) (ω : Sample2 n b T) : EuclideanSpace ℝ (Fin d) :=
  (stateAt2 gf P η b x₁ ω (T + 1)).xout

/-- The full component-gradient query log of Algorithm 2 with horizon `T` on `ω` (initialization
and updates `1, …, T`, in order); its length is `N_grad`. -/
noncomputable def gradLog2 {n d T : ℕ} [NeZero n]
    (gf : Fin n → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (P : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (η : ℝ) (b : ℕ)
    (x₁ : EuclideanSpace ℝ (Fin d)) (ω : Sample2 n b T) :
    List (Fin n × EuclideanSpace ℝ (Fin d)) :=
  ((run2 gf P η b x₁ ω T).run ([], [])).2.1

/-- The full proximal-evaluation log of Algorithm 2 with horizon `T` on `ω`; its length is the
number of proximal evaluations `N_prox`. -/
noncomputable def proxLog2 {n d T : ℕ} [NeZero n]
    (gf : Fin n → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (P : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (η : ℝ) (b : ℕ)
    (x₁ : EuclideanSpace ℝ (Fin d)) (ω : Sample2 n b T) : List (EuclideanSpace ℝ (Fin d)) :=
  ((run2 gf P η b x₁ ω T).run ([], [])).2.2

end PrefixVR.Supplement


