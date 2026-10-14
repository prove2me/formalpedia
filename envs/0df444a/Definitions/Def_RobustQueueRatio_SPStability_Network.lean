-- Prove2me | Definitions.Def_RobustQueueRatio_SPStability_Network
-- name    : RobustQueueRatio_SPStability_Network
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T01:22:43.354783+00:00
-- url     : https://prove2.me/theorems/43f79115-7920-4dff-bdc8-b94137a46223
-- title:
--   Open multiclass queueing network primitives $(C,M,P,\alpha)$, with $Q=(I-P^\top)^{-1}$, $\lambda=Q\alpha$, $\rho=CM\lambda$
-- statement:
--   This definition sets up the **network primitives** of an open multiclass queueing network, as in §2 of Zhao, Gurvich and Hasenbein.
--
--   There are $J$ stations (servers) and $K$ job classes. Each class $k$ is served at exactly one station $s(k)$, and $C(j)=\{k: s(k)=j\}$ is the set of classes served at station $j$. The data are:
--
--   1. the class-to-station map $s$, encoded by the $J\times K$ **constituency matrix** $C$ with $C_{jk}=1$ if $s(k)=j$ and $C_{jk}=0$ otherwise;
--   2. the mean service times $m_k>0$, collected in the $K\times K$ diagonal matrix $M=\operatorname{diag}(m_1,\dots,m_K)$;
--   3. the **routing matrix** $P$, where $P_{kl}\ge 0$ is the probability that a class-$k$ job becomes a class-$l$ job after service, so that every row of $P$ sums to at most $1$;
--   4. the exogenous arrival rates $\alpha_k\ge 0$.
--
--   The network is **open**: the series $I+P+P^2+\cdots$ converges and $I-P^\top$ is invertible. From these data one defines
--
--   $$
--   Q=(I-P^\top)^{-1},\qquad \lambda=Q\alpha,\qquad \rho=CM\lambda,
--   $$
--
--   where $Q_{kl}$ is the expected number of visits to class $k$ starting from class $l$, $\lambda_k$ is the effective arrival rate to class $k$, and $\rho_j$ is the traffic intensity at station $j$.
--
--   These are the fixed data on which every reflection matrix $R_\Delta=(CMQ\Delta)^{-1}$ and drift $\theta_\Delta=R_\Delta(\rho-e)$ of the mission is built.
--
--   **Formalization Note.** Stations are `Fin J` and classes `Fin K`, so the paper's index $i$ is Lean's $i-1$. A network is a structure `Network J K` with fields `s`, `m`, `P`, `α` and the hypotheses above. Openness keeps both of the paper's clauses: summability of $n\mapsto P^n$ in the entrywise topology, and `IsUnit (1 - Pᵀ).det`. `Q` is Lean's matrix inverse `(1 - Pᵀ)⁻¹`, which is the genuine inverse because of that field. The renewal structure of the arrivals and the remark $K>J$ play no role in the results and are not recorded. The nominal-load condition $\rho<e$ is not part of the structure.
-- source:
--   Zhao, Gurvich & Hasenbein, A Hierarchical Approach to Robust Stability of Multiclass Queueing Networks, arXiv:2303.17746v3, p. 7, §2 "Network primitives"

import Mathlib

noncomputable section

namespace RobustQueueRatio.SPStability

open Matrix

/-- The network primitives `(C, M, P, α)` of an open multiclass queueing network
(Zhao, Gurvich & Hasenbein, *A Hierarchical Approach to Robust Stability of Multiclass Queueing
Networks*, arXiv:2303.17746v3, p. 7, §2 "Network primitives").

There are `J` stations and `K` classes. Stations are `Fin J`, classes are `Fin K`; the paper's
station `j ∈ {1, …, J}` is Lean's `j - 1`, and likewise for classes.

* `s k` is the station `s(k)` that serves class `k` (the many-to-one class-to-station map);
* `m k = m_k > 0` is the mean service time of class `k`;
* `P k l = P_kl ≥ 0` is the probability that a class-`k` job becomes a class-`l` job on service
  completion, so each row of `P` sums to at most one;
* the network is open: `I + P + P² + ⋯` converges and `I − P′` is invertible;
* `α k = α_k ≥ 0` is the exogenous arrival rate to class `k`.

**Formalization Note.** The renewal structure of the arrivals and the remark "`K > J`" play no role
in the matrix algebra this structure supports and are not recorded. Convergence of the Neumann
series is taken in the entrywise (product) topology on `K × K` matrices. -/
structure Network (J K : ℕ) where
  /-- The station `s(k)` serving class `k`. -/
  s : Fin K → Fin J
  /-- Mean service times `m_k`. -/
  m : Fin K → ℝ
  /-- The routing matrix `P`. -/
  P : Matrix (Fin K) (Fin K) ℝ
  /-- Exogenous arrival rates `α_k`. -/
  α : Fin K → ℝ
  m_pos : ∀ k, 0 < m k
  P_nonneg : ∀ k l, 0 ≤ P k l
  P_row_sum_le_one : ∀ k, ∑ l, P k l ≤ 1
  /-- Openness, first half: `I + P + P² + ⋯` is convergent. -/
  neumann_summable : Summable (fun n : ℕ => P ^ n)
  /-- Openness, second half: `I − P′` is invertible. -/
  isUnit_det_one_sub_transpose : IsUnit (1 - Pᵀ).det
  α_nonneg : ∀ k, 0 ≤ α k

namespace Network

variable {J K : ℕ} (N : Network J K)

/-- The `J × K` constituency matrix: `C j k = 1` if class `k` is served at station `j`
(`s(k) = j`), and `0` otherwise. -/
def C : Matrix (Fin J) (Fin K) ℝ := Matrix.of fun j k => if N.s k = j then 1 else 0

/-- The `K × K` diagonal matrix `M` of mean service times. -/
def M : Matrix (Fin K) (Fin K) ℝ := Matrix.diagonal N.m

/-- `Q = (I − P′)⁻¹`, the expected-visits matrix. -/
def Q : Matrix (Fin K) (Fin K) ℝ := (1 - N.Pᵀ)⁻¹

/-- The effective arrival rates `λ = Q α`. -/
def effArrival : Fin K → ℝ := N.Q *ᵥ N.α

/-- The traffic intensities `ρ = C M λ`, one per station. -/
def ρ : Fin J → ℝ := (N.C * N.M) *ᵥ N.effArrival

end Network

end RobustQueueRatio.SPStability

end


