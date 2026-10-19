-- Prove2me | Definitions.Def_CloudMWU_Bicriteria_Model
-- name    : CloudMWU_Bicriteria_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-19T04:20:38.658404+00:00
-- url     : https://prove2.me/theorems/a1e3f46b-4e65-424e-983a-c5a645ffa747
-- title:
--   §2, pp. 8–9 — the truncated simplex Δ_ε, the KL projection π_{Δ_ε}, the gains of Algorithm 1 and its runs; constants λ, c, c′, s̃, p̃
-- statement:
--   This file defines the multiplicative weight algorithm of the paper (Algorithm 1, p. 9) on top of the queueing model `CloudMWU.Bicriteria.Queue`.
--
--   Fix $N$ users, parameters $\varepsilon, \eta$ and SLAs $\beta = (\beta(1), \dots, \beta(N))$.
--
--   1. **Truncated simplex** (p. 9): $\Delta_\varepsilon = \{x \in \mathbb R^N : \sum_i x(i) = 1,\ x(i) \ge \varepsilon/N \ \forall i\}$.
--   2. **KL projection** (p. 9): for a coordinatewise positive $y$, $x = \pi_{\Delta_\varepsilon}(y)$ means that $x \in \Delta_\varepsilon$ and $x$ minimizes $\sum_i x(i) \log(x(i)/y(i))$ over $\Delta_\varepsilon$. It is defined as a predicate, not as a chosen minimizer.
--   3. **Active users** (p. 8): for an allocation sequence $h$ on loads $L$, $A_t = \{i : Q_t(i) > 0\}$, where $Q_t$ is the queue vector that $h$ itself produces.
--   4. **Gains** (Algorithm 1, line 5): with $\lambda = \varepsilon^2/(8N)$,
--   $$g_t(i) = \begin{cases} 1 + \lambda & i \in A_t,\ h_t(i) < \beta(i) \quad (A^1_t), \\ 1 & i \in A_t,\ h_t(i) \ge \beta(i) \quad (A^2_t), \\ 0 & i \notin A_t \quad (B_t). \end{cases}$$
--   5. **Update** (line 6): $\widehat h_{t+1}(i) = h_t(i)\, e^{\eta g_t(i)}$ and $h_{t+1} = \pi_{\Delta_\varepsilon}(\widehat h_{t+1})$.
--   6. **Runs**: a sequence $h$ is a run of Algorithm 1 on loads $L$ if $h_1 \in \Delta_\varepsilon$ is arbitrary and every $h_{t+1}$ is the KL projection of $\widehat h_{t+1}$ computed from $h_t$ and from the queues of $h$ at the start of step $t$.
--   7. **Constants**: $c = \varepsilon\eta/(4N)$ (Lemma 1), $c' = \varepsilon\eta\lambda/(2N)$ (Lemma 2), $\tilde s = \ln(N/\varepsilon)/(\varepsilon c)$ (proof of Theorem 3) and $\tilde p = 32 N^2/(\varepsilon^3\eta) \cdot \ln(N/\varepsilon)$ (Theorem 4).
--
--   The algorithm's feedback is honoured by construction: the gain of user $i$ depends only on whether its queue is non-empty and on how its current allocation compares with its SLA, never on a load or a queue length. Since the queue at the start of step $t$ depends only on the loads of earlier steps, $h_{t+1}$ never uses the load of step $t$ or later.
--
--   **Formalization Note** Time is 0-based: `h 0` is the paper's $h_1$. A run is any sequence satisfying the recursion; existence and uniqueness of the projection, and hence of the run from a given start, is the milestone `kl_projection_exists_unique`. All quantities are real numbers. The projection predicate requires $y(i)>0$ because the KL formula is undefined at $y(i)=0$ when $x(i)>0$; Algorithm 1 always projects a positive vector.
-- source:
--   Perez-Salazar, Menache, Singh, Toriello, Dynamic Resource Allocation in the Cloud with Near-Optimal Efficiency, arXiv:1809.02688v3, pp. 8–9, §2.1, Algorithm 1; p. 11, Lemma 1 (c); p. 12 (s̃); p. 13, Lemma 2 (c′); p. 10, Theorem 4 (p̃)

import Mathlib
import Definitions.Def_CloudMWU_Bicriteria_Queue

namespace CloudMWU.Bicriteria

open Finset

variable {N : ℕ}

/-- The truncated simplex `Δ_ε = {x : Σ_i x(i) = 1, x(i) ≥ ε/N ∀ i}` (p. 9). -/
def truncSimplex (N : ℕ) (ε : ℝ) : Set (Fin N → ℝ) :=
  {x | ∑ i, x i = 1 ∧ ∀ i, ε / (N : ℝ) ≤ x i}

/-- The KL objective `Σ_i x(i) log (x(i)/y(i))` (p. 9). -/
noncomputable def klObj (x y : Fin N → ℝ) : ℝ := ∑ i, x i * Real.log (x i / y i)

/-- `x = π_{Δ_ε}(y)` for a positive input `y`: `x ∈ Δ_ε` minimizes the KL
objective over `Δ_ε` (p. 9). Positivity keeps `Real.log (x i / y i)` on its
mathematical domain; Algorithm 1 always projects a positive vector. -/
def IsKLProj (ε : ℝ) (y x : Fin N → ℝ) : Prop :=
  (∀ i, 0 < y i) ∧ x ∈ truncSimplex N ε ∧
    ∀ x' ∈ truncSimplex N ε, klObj x y ≤ klObj x' y

/-- `λ = ε² / (8N)` (Algorithm 1, p. 9). -/
noncomputable def lam (N : ℕ) (ε : ℝ) : ℝ := ε ^ 2 / (8 * (N : ℝ))

/-- `c = εη / (4N)` (Lemma 1, p. 11). -/
noncomputable def cLem1 (N : ℕ) (ε η : ℝ) : ℝ := ε * η / (4 * (N : ℝ))

/-- `c' = εηλ / (2N)` (Lemma 2, p. 13). -/
noncomputable def cLem2 (N : ℕ) (ε η : ℝ) : ℝ := ε * η * lam N ε / (2 * (N : ℝ))

/-- `s̃ = ln(N/ε) / (εc)` with `c = εη/(4N)` (proof of Theorem 3, p. 12). -/
noncomputable def sTilde (N : ℕ) (ε η : ℝ) : ℝ :=
  Real.log ((N : ℝ) / ε) / (ε * cLem1 N ε η)

/-- `p̃ = 32 N² / (ε³ η) · ln(N/ε)` (Theorem 4, p. 10). -/
noncomputable def pTilde (N : ℕ) (ε η : ℝ) : ℝ :=
  32 * (N : ℝ) ^ 2 / (ε ^ 3 * η) * Real.log ((N : ℝ) / ε)

/-- Queue vector `Q_t` that the allocation sequence `h` itself induces on the loads `L`
(0-based: `runQueue h L t` is the queue at the start of step `t`, before `L t` arrives). -/
noncomputable def runQueue (h L : ℕ → Fin N → ℝ) (t : ℕ) (i : Fin N) : ℝ :=
  queue (fun τ => h τ i) (fun τ => L τ i) t

/-- The active users `A_t = {i : Q_t(i) > 0}` of the allocation sequence `h` (p. 8). -/
noncomputable def active (h L : ℕ → Fin N → ℝ) (t : ℕ) : Finset (Fin N) :=
  univ.filter (fun i => 0 < runQueue h L t i)

/-- The gain `g_t(i)` of Algorithm 1 (line 5, p. 9), computed from the current allocation `hv`
and the current queue vector `q`: `1 + λ` on `A¹_t` (active with `h_t(i) < β(i)`), `1` on `A²_t`
(active with `h_t(i) ≥ β(i)`), `0` on the inactive users `B_t`. -/
noncomputable def gain (N : ℕ) (ε : ℝ) (β hv q : Fin N → ℝ) (i : Fin N) : ℝ :=
  if 0 < q i then (if hv i < β i then 1 + lam N ε else 1) else 0

/-- `ĥ_{t+1}(i) = h_t(i) e^{η g_t(i)}` (line 6, p. 9). -/
noncomputable def boosted (ε η : ℝ) (β hv q : Fin N → ℝ) : Fin N → ℝ :=
  fun i => hv i * Real.exp (η * gain N ε β hv q i)

/-- `h` is a run of Algorithm 1 with parameters `ε, η`, SLAs `β`, on the loads `L`: `h 0` (the
paper's `h_1`) is any point of `Δ_ε`, and `h (t+1) = π_{Δ_ε}(ĥ_{t+1})`, where the gains are
computed from `h t` and from the queues that `h` itself has produced before step `t`. -/
def IsAlg1Run (ε η : ℝ) (β : Fin N → ℝ) (L h : ℕ → Fin N → ℝ) : Prop :=
  h 0 ∈ truncSimplex N ε ∧
    ∀ t, IsKLProj ε (boosted ε η β (h t) (runQueue h L t)) (h (t + 1))

end CloudMWU.Bicriteria


