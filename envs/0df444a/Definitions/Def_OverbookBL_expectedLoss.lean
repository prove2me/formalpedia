-- Prove2me | Definitions.Def_OverbookBL_expectedLoss
-- name    : OverbookBL_expectedLoss
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:54:43.870697+00:00
-- url     : https://prove2.me/theorems/63660348-9b59-4d7e-a9dd-a5a532a34426
-- title:
--   Benchmarks $\widehat{\mathrm{OPT}}_{\vec A}$, $\mathcal H_{\vec A}[t]$ and the expected loss $\mathbb E_{\vec A}[\widehat{\mathrm{OPT}}_{\vec A}-\mathrm{OBJ}_{\vec A}]$
-- statement:
--   For an arrival sequence $\vec A$ with type counts $N_j$:
--
--   1. the **clairvoyant general objective** $\widehat{\mathrm{OPT}}_{\vec A}$ is the optimal value of problem (1) with no past acceptances and the exact arrivals $N_j$, over all $0\le\vec x\le\vec N$;
--   2. the **clairvoyant index objective** $\mathcal H_{\vec A}[1]$ is the same optimum restricted to index solutions;
--   3. the **hybrid clairvoyant index objective** $\mathcal H_{\vec A}[t]$ is the optimal value of (1) over index solutions with the exact future arrivals $N[t,T]$ and the online index policy's acceptances $\vec x[t-1]$ in periods $1,\dots,t-1$ as past;
--   4. the **expected loss** of the online index policy is
--
--   $$
--   \mathbb E_{\vec A}\big[\widehat{\mathrm{OPT}}_{\vec A}-\mathrm{OBJ}_{\vec A}\big]=\sum_{\vec A\in[k]^T}\Big(\prod_t\lambda_{A_t}\Big)\big(\widehat{\mathrm{OPT}}_{\vec A}-\mathrm{OBJ}_{\vec A}\big).
--   $$
--
--   The main theorem bounds the expected loss by a constant; the hybrid objectives interpolate between $\mathcal H_{\vec A}[1]$ and the online objective.
--
--   **Formalization Note** All optima are finite maxima over boxes of integer vectors. $\mathcal H_{\vec A}[t]$ depends on the sample $\vec A'$ and the selection rule through $\vec x[t-1]$; $t$ is 1-based as in the paper.
-- source:
--   D. Freund and J. Zhao, Overbooking with bounded loss, arXiv:2204.11148v2 (26 Apr 2022), https://arxiv.org/abs/2204.11148v2, §2.1, pp.11–12; §3, p.12

import Definitions.Def_OverbookBL_runState

namespace OverbookBL

/-- Optimal value of problem (1) over all feasible vectors `0 ≤ x ≤ N`, with past accepted
arrivals `past` (Freund & Zhao, *Overbooking with bounded loss*, arXiv:2204.11148v2, p.10).

**Formalization Note** A finite maximum over the box `{x : xⱼ ≤ Nⱼ}`, which always contains `0`. -/
noncomputable def globOpt {k : ℕ} (I : Instance k) (B : ℕ) (past N : Fin k → ℕ) : ℝ :=
  (Fintype.piFinset (fun j => Finset.range (N j + 1))).sup'
    (Fintype.piFinset_nonempty.mpr (fun _ => Finset.nonempty_range_add_one)) (obj I B past)

open Classical in
/-- Optimal value of problem (1) over index solutions (Definition 1) only, with past accepted
arrivals `past` and future arrivals `N` (arXiv:2204.11148v2, p.11, "subject to finding an index
solution").

**Formalization Note** A finite maximum. For `k ≥ 1` the vector `0` is an index solution (threshold
index `0`), so the maximum is over a nonempty set; the fallback value `0` is reached only for
`k = 0`, which no `Instance` allows (`∑ⱼ λⱼ = 1`). -/
noncomputable def idxOpt {k : ℕ} (I : Instance k) (B : ℕ) (past N : Fin k → ℕ) : ℝ :=
  if h : ((Fintype.piFinset (fun j => Finset.range (N j + 1))).filter
      (fun x => ∃ e, IsIndexSol N x e)).Nonempty then
    ((Fintype.piFinset (fun j => Finset.range (N j + 1))).filter
      (fun x => ∃ e, IsIndexSol N x e)).sup' h (obj I B past)
  else 0

/-- Clairvoyant general objective `ÔPT_A⃗` (arXiv:2204.11148v2, p.11): the optimal value of
problem (1) with no past acceptances and the exact arrival counts `Nⱼ` of `A⃗`. -/
noncomputable def OPT {k T : ℕ} (I : Instance k) (B : ℕ) (A : Fin T → Fin k) : ℝ :=
  globOpt I B 0 (countFrom A 0)

/-- Clairvoyant index objective `H_A⃗[1]` (arXiv:2204.11148v2, p.11): the optimal value of problem
(1) over index solutions, with no past acceptances and the exact arrival counts `Nⱼ` of `A⃗`. -/
noncomputable def clairIdx {k T : ℕ} (I : Instance k) (B : ℕ) (A : Fin T → Fin k) : ℝ :=
  idxOpt I B 0 (countFrom A 0)

/-- Hybrid clairvoyant index objective `H_A⃗[t]` (arXiv:2204.11148v2, p.11), for the paper's
1-based period `t`: the optimal value of problem (1) over index solutions, with the online index
policy's acceptances `x⃗[t−1]` in periods `1, …, t−1` (on the arrival sequence `A` with sample `A'`
and selection rule `sel`) as past, and the exact future arrivals `N[t, T]` of `A`.

**Formalization Note** `t` is 1-based as in the paper and is meant for `1 ≤ t ≤ T`; the `ℕ`
subtraction `t − 1` makes `t = 0` a copy of `t = 1`, never used. `Hyb … 1 = clairIdx`, since
`x⃗[0] = 0`. -/
noncomputable def Hyb {k T : ℕ} (I : Instance k) (B : ℕ)
    (sel : ℕ → (Fin k → ℕ) → (Fin k → ℕ) → (Fin k → ℕ)) (A A' : Fin T → Fin k) (t : ℕ) : ℝ :=
  idxOpt I B (runState sel A A' (t - 1)) (countFrom A (t - 1))

/-- Expected loss `E_A⃗[ÔPT_A⃗ − OBJ_A⃗]` of the online index policy with selection rule `sel`,
capacity `B` and horizon `T` (arXiv:2204.11148v2, §3, p.12): the expectation over i.i.d. arrival
sequences `A⃗` with weight `∏ₜ λ_{Aₜ}`. -/
noncomputable def expectedLoss {k : ℕ} (I : Instance k) (B T : ℕ)
    (sel : ℕ → (Fin k → ℕ) → (Fin k → ℕ) → (Fin k → ℕ)) : ℝ :=
  ∑ A : Fin T → Fin k, seqWeight I A * (OPT I B A - OBJ I B sel A)

end OverbookBL


