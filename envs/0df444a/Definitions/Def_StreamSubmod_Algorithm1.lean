-- Prove2me | Definitions.Def_StreamSubmod_Algorithm1
-- name    : StreamSubmod_Algorithm1
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:26:04.477571+00:00
-- url     : https://prove2.me/theorems/5a4393a0-31c6-424c-b276-94f577b47d32
-- title:
--   Algorithm 1: StreamProcess (simplified)
-- statement:
--   Algorithm 1 receives an integer $p\ge1$, the approximation ratio $\alpha$ of OfflineAlg and an estimate $\tau$ of $f(\mathrm{OPT})$. It maintains solutions $S_1,\dots,S_p$, all starting empty. With $c=\alpha/(1+\alpha)$, each arriving element $e$ is added to one $S_i$ with $|S_i|<k$ and $f(e\mid S_i)\ge c\tau/k$, if there is one. After the stream ends, the algorithm post-processes $S_1,\dots,S_p$. The module defines:
--
--   1. `alg1Sets`, the contents of $S_1,\dots,S_p$ after a list of arrivals; the final sets $\hat S_i$ are its value on the whole stream;
--   2. `alg1Out`, the output for a seed of the offline algorithm;
--   3. `alg1Stored`, the number $\sum_i|S_i|$ of stored elements;
--   4. `alg1Queries`, the number of marginal values computed for one arrival, as counted by the step.
--
--   This is the simplified form of StreamProcess, which assumes access to the estimate $\tau$.
-- source:
--   Alaluf, Ene, Feldman, Nguyen & Suh, An Optimal Streaming Algorithm for Submodular Maximization with a Cardinality Constraint, arXiv:1911.12959v3, Algorithm 1, p.7

import Mathlib
import Definitions.Def_StreamSubmod_threshStep
import Definitions.Def_StreamSubmod_postProcess

namespace StreamSubmod

variable {E : Type} [DecidableEq E]

/-- Algorithm 1, StreamProcess (simplified) `(p, α)`, lines 1–5 (Alaluf, Ene, Feldman, Nguyen & Suh,
arXiv:1911.12959v3, p.7): the contents of `S_1, …, S_p` after the elements of the list `L` have
arrived, for the estimate `τ` of `f(OPT)`. The sets `Ŝ_i` of the paper are
`alg1Sets p f k α τ σ i` for the whole stream `σ`. -/
noncomputable def alg1Sets (p : ℕ) (f : Finset E → ℝ) (k : ℕ) (α τ : ℝ) (L : List E) :
    Fin p → Finset E :=
  L.foldl (fun S e => (threshStep f k (threshold α k τ) e S).1) (fun _ => ∅)

/-- The number of marginal values Algorithm 1 computes while processing the arriving element `e`,
when the elements of `L` have already arrived. It is the count made by `threshStep`. -/
noncomputable def alg1Queries (p : ℕ) (f : Finset E → ℝ) (k : ℕ) (α τ : ℝ) (L : List E) (e : E) :
    ℕ :=
  (threshStep f k (threshold α k τ) e (alg1Sets p f k α τ L)).2

/-- The number of elements stored in the solutions `S_1, …, S_p`, namely `∑ᵢ |S_i|`. -/
def alg1Stored {p : ℕ} (S : Fin p → Finset E) : ℕ :=
  ∑ i, (S i).card

/-- The output of Algorithm 1 on the stream `σ` when the offline algorithm has seed `ω`
(Algorithm 1, lines 6–7, p.7). -/
noncomputable def alg1Out {Ω : Type} [Fintype E] (p : ℕ) (f : Finset E → ℝ) (k : ℕ) (α τ : ℝ)
    (Off : Ω → Finset E → Finset E) (σ : List E) (ω : Ω) : Finset E :=
  postProcess f Off ω (alg1Sets p f k α τ σ)

end StreamSubmod


