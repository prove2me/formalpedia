-- Prove2me | Definitions.Def_WeakSignalBandit_BanditKernel
-- name    : WeakSignalBandit_BanditKernel
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:30:33.731985+00:00
-- url     : https://prove2.me/theorems/57133ea5-1fe4-4869-93ae-b8e4b51e2ade
-- title:
--   Transition kernel (A.14) of the scaled bandit state: $\Pi^n((q,s),(q+e_k/n,s+e_k\,ds/\sqrt n))=\bar\psi^n_k(q,s)P^n_k(ds)$
-- statement:
--   For the $n$-th experiment, with reward distributions $P^n_1,\dots,P^n_K$ and sampling function $\psi^n$, the transition kernel of the scaled state $z=(q,s)$ is
--   $$\Pi^n\big((q,s),(q+e_k/n,\ s+e_k\,ds/\sqrt n)\big)=\bar\psi^n_k(q,s)\,P^n_k(ds),\qquad k=1,\dots,K,$$
--   and zero elsewhere, where $e_k$ is the $k$-th unit vector and $\bar\psi^n(q,s)=\psi^n(nq,\sqrt n s)$. Equivalently, for a Borel set $B\subseteq\mathbb R^{2K}$,
--   $$\Pi^n(z,B)=\sum_{k=1}^K\bar\psi^n_k(z)\,P^n_k\{w:\ z+(e_k/n,\ w\,e_k/\sqrt n)\in B\}.$$
--   The scaled kernel is $K^n=n\Pi^n$.
--
--   This kernel is what the paper feeds into the Stroock–Varadhan diffusion approximation: its moments are computed in (A.18)–(A.25).
--
--   **Formalization Note** The kernel is a measure-valued function of $z$; a negative $\bar\psi^n_k$ (impossible for a sampling function) would count as $0$.
-- source:
--   Kuang, Wager, Weak signal asymptotics for sequentially randomized experiments, arXiv:2101.09855v7, (A.14) p.33

import Mathlib
import Definitions.Def_WeakSignalBandit_Experiment

open MeasureTheory

namespace WeakSignalBandit

variable {K : ℕ}

/-- The increment `(e_k/n, w e_k/√n)` of the scaled state when arm `k` is chosen and pays reward
`w`. -/
noncomputable def jump (n : ℕ) (k : Fin K) (w : ℝ) : State K :=
  mkState (Pi.single k (1 / (n : ℝ))) (Pi.single k (w / Real.sqrt n))

/-- The transition kernel `Π^n` of the scaled state `Z^n = (Q^n, S^n)` of the `n`-th experiment:
`Π^n((q, s), (q + e_k/n, s + e_k ds/√n)) = ψ̄^n_k(q, s) P^n_k(ds)`, `k = 1, …, K`, and zero elsewhere;
i.e. `Π^n(z, B) = Σ_k ψ̄^n_k(z) P^n_k{w : z + (e_k/n, w e_k/√n) ∈ B}`.
Kuang, Wager, *Weak signal asymptotics for sequentially randomized experiments*,
arXiv:2101.09855v7, (A.14) p.33.

**Formalization Note** `Pn k` is `P^n_k` and `ψ` is the pre-limit sampling function `ψ^n`, read at
`ψ̄^n(z) = ψ^n(nq, √n s)`. A negative `ψ̄^n_k` (impossible for a sampling function) would count
as `0`. The scaled kernel `K^n = nΠ^n` of (A.14) is `scaledKernel (banditKernel n Pn ψ) n`. -/
noncomputable def banditKernel (n : ℕ) (Pn : Fin K → Measure ℝ) (ψ : State K → Fin K → ℝ)
    (z : State K) : Measure (State K) :=
  ∑ k, ENNReal.ofReal (psiBar n ψ z k) • (Pn k).map (fun w => z + jump n k w)

end WeakSignalBandit


