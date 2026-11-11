-- Prove2me | Definitions.Def_PreservePast_IsPromised
-- name    : PreservePast_IsPromised
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T10:40:27.824319+00:00
-- url     : https://prove2.me/theorems/7113c911-2824-4eb1-aee9-d6ccfd9f8051
-- title:
--   Promised query (13)
-- statement:
--   Let $h=(h_1,\dots,h_K)$ be a history of tasks with loss increments $f_1,\dots,f_K$. A query $(x,p)$ with $x\in\mathbb R^n$, $p\in\mathbb R^m$ is **promised** (for rank $r$ and radius $R$) when $\|x\|=\|p\|=1$ and some update $H_*$ satisfies
--   $$
--   \operatorname{rank}H_*\le r,\qquad \|H_*\|_F\le R,\qquad H_*x=p,\qquad f_i(H_*)\le 0\quad(1\le i\le K).
--   $$
--   The promise guarantees that an exact, low-rank, bounded update exists that does not hurt any old task; the learner must find a comparable one from its retained memory.
--
--   **Formalization Note** Unit vectors are written $\sum_i x_i^2=1$, $\sum_j p_j^2=1$. $\|\cdot\|_F=(\sum_{ij}A_{ij}^2)^{1/2}$ is the published `LowRankMEG.frobNorm`.
-- source:
--   P. Xu, Information Required to Preserve Past Learning, STOC 2027 submission (held version, PDF sha256 48013ceb…d00fa), §3.1, p.6 (PDF p.8), (13)

import Mathlib
import Definitions.Def_LowRankMEG_frobNorm
import Definitions.Def_PreservePast_Task

open Matrix

namespace PreservePast

/-- **Promised query** (13). P. Xu, *Information Required to Preserve Past Learning*, STOC 2027 submission (held version,
PDF sha256 48013ceb…d00fa), §3.1, p.6 (PDF p.8): "A later query reveals unit vectors
x ∈ ℝⁿ and p ∈ ℝᵐ, and promises an update H_* with rank(H_*) ≤ r, ‖H_*‖_F ≤ R, H_*x = p,
f_i(H_*) ≤ 0 (1 ≤ i ≤ K) (13)."

`IsPromised r R h x p` says that `x` and `p` are Euclidean unit vectors and that some update of
rank at most `r` and Frobenius norm at most `R` fits `H_* x = p` exactly without increasing the
loss of any of the `K` old tasks of the history `h`.

**Formalization Note.** Vectors are `Fin n → ℝ`; the unit conditions are `Σ xᵢ² = 1`,
`Σ pⱼ² = 1`. The history is a `K`-tuple of tasks for the same checkpoint `W₀`. -/
def IsPromised {m n K : ℕ} {W₀ : Matrix (Fin m) (Fin n) ℝ} (r : ℕ) (R : ℝ)
    (h : Fin K → Task W₀) (x : Fin n → ℝ) (p : Fin m → ℝ) : Prop :=
  ∑ i, x i ^ 2 = 1 ∧ ∑ j, p j ^ 2 = 1 ∧
    ∃ Hs : Matrix (Fin m) (Fin n) ℝ, Hs.rank ≤ r ∧ LowRankMEG.frobNorm Hs ≤ R ∧ Hs *ᵥ x = p ∧
      ∀ i, (h i).lossInc Hs ≤ 0

end PreservePast


