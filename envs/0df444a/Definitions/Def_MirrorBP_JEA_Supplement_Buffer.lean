-- Prove2me | Definitions.Def_MirrorBP_JEA_Supplement_Buffer
-- name    : MirrorBP_JEA_Supplement_Buffer
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T02:46:15.829226+00:00
-- url     : https://prove2.me/theorems/0225aae1-9f9e-496c-83ad-96c524436c6d
-- title:
--   §5.1, pp. 21–22 — finite buffers: buffer profile, state space, buffer-feasible policies, normalization (23), Algorithm 1 with buffers
-- statement:
--   Objects of the finite-buffer setting of §5.1, built on the published joint entry-assignment model (`MirrorBP.JEA.Model`) and its MBP definitions (`MirrorBP.JEA.MBP`). Let $V$ be the finite node set, $m=|V|$, and $K$ the number of supply units.
--
--   1. **Buffer profile.** A subset $V_b\subseteq V$ of buffer-constrained nodes with scaled buffer sizes $\bar d_j\in(0,1)$ for $j\in V_b$, the convention $\bar d_j=1$ for $j\notin V_b$, and $\bar d_\Sigma:=\sum_{j\in V}\bar d_j>1$. Also $\bar d_{\min}=\min_j\bar d_j$ and $\bar d_g=\min\{1,\bar d_\Sigma-1\}$ (Appendix B.3.3).
--   2. **Buffer sizes.** The buffer of node $j$ holds $d_j=\bar d_jK$ supply units; the model with $K$ units exists when every $d_j$ is a whole number.
--   3. **States.** $q\in\mathbb Z_+^V$ with $\sum_jq_j=K$ and $q_j\le d_j$ for every $j$.
--   4. **Buffer feasibility and policies.** Serving a customer with pick-up $j$ and drop-off $k\ne j$ requires $q_k+1\le d_k$; dropping is always allowed. A feasible policy of §5.1 is a randomized, history-dependent policy of the base model (respecting (1)–(2)) that puts zero probability on decisions violating this constraint.
--   5. **Normalization (23).**
--   $$\bar q_j=\frac{q_j+\bar d_j\delta_K}{\tilde K},\qquad \delta_K=\sqrt K,\qquad \tilde K=K+\Big(\sum_{j\in V}\bar d_j\Big)\delta_K .$$
--   6. **Algorithm 1 with node-specific congestion functions.** For congestion functions $(f_j)_{j\in V}$, the MBP policy picks $(j^*,k^*)\in\arg\max_{j\in P(\tau),k\in D(\tau)}\{w_{j\tau k}+f_j(\bar q_j)-f_k(\bar q_k)\}$ over all of $P(\tau)\times D(\tau)$ (any tie-break), and serves with $(j^*,k^*)$ iff the score is nonnegative, $q_{j^*}>0$ and the drop-off buffer has room; otherwise it drops the customer.
--
--   These are the model and policy of Theorems 2 and 4.
--
--   **Formalization Note** Item 2 encodes the paper's $d_j=\bar d_jK$, $\bar d_j\triangleq d_j/K$ as a hypothesis `IntegralCapacity` used by the theorems; it is what makes "$q_j=d_j$" (a full buffer) meaningful. Policies are the published base class (history includes past decisions), restricted by the predicate `RespectsBuffers`. In item 6 the buffer check is the reading of Algorithm 1 in the finite-buffer setting: the selected assignment is rejected, not re-optimized, when it is infeasible.
-- source:
--   Kanoria, Qian, Blind Dynamic Resource Allocation in Closed Networks via Mirror Backpressure, arXiv:1903.02764v4, pp. 21–22, §5.1, (23), footnotes 6–7; p. 13, Algorithm 1; Appendix B.3.3, appendix p. 11 (PDF 44), notation d̄_Σ, d̄_g, d̄_min

import Mathlib
import Definitions.Def_MirrorBP_JEA_Model
import Definitions.Def_MirrorBP_JEA_MBP

namespace MirrorBP.JEA.Supplement

open Finset

variable {V Ty : Type} [Fintype V] [DecidableEq V] [Fintype Ty] [DecidableEq Ty]

/-- The finite-buffer data of §5.1, pp. 21–22: a subset `Vb ⊆ V` of buffer-constrained nodes with
scaled buffer sizes `d̄_j ∈ (0, 1)` for `j ∈ Vb`, the convention `d̄_j = 1` for `j ∉ Vb`, and
`∑_{j ∈ V} d̄_j > 1` (so that the buffers can hold all `K` supply units). -/
def IsBufferProfile (Vb : Finset V) (dbar : V → ℝ) : Prop :=
  (∀ j ∈ Vb, 0 < dbar j ∧ dbar j < 1) ∧ (∀ j, j ∉ Vb → dbar j = 1) ∧ 1 < ∑ j, dbar j

/-- `d̄_Σ = ∑_{j ∈ V} d̄_j` (Appendix B.3.3, appendix p. 11, PDF 44). -/
def dSum (dbar : V → ℝ) : ℝ := ∑ j, dbar j

/-- `d̄_min = min_{j ∈ V} d̄_j` (Appendix B.3.3, PDF 44; the value `0` for empty `V` is never used). -/
noncomputable def dMin (dbar : V → ℝ) : ℝ :=
  if h : (univ : Finset V).Nonempty then univ.inf' h dbar else 0

/-- `d̄_g = min{1, ∑_{j ∈ V} d̄_j − 1}` (Appendix B.3.3, PDF 44). -/
noncomputable def dGap (dbar : V → ℝ) : ℝ := min 1 (dSum dbar - 1)

/-- The buffer sizes `d_j = d̄_j K` are numbers of supply units (§5.1, p. 21: "denote the buffer size
by `d_j = d̄_j K`"; p. 22: `d̄_j ≜ d_j / K`). The finite-buffer model with `K` supply units is defined
exactly when every `d̄_j K` is a natural number (for `j ∉ Vb`, `d̄_j K = K`). -/
def IntegralCapacity (dbar : V → ℝ) (K : ℕ) : Prop :=
  ∀ j, ∃ n : ℕ, dbar j * (K : ℝ) = n

/-- The physical state space with finite buffers: queue-length vectors `q ∈ ℤ₊^V` with `1ᵀq = K`
and `q_j ≤ d_j = d̄_j K` for every node (for `j ∉ Vb` this is `q_j ≤ K`, automatic). -/
def BufStateSpace (dbar : V → ℝ) (K : ℕ) : Set (V → ℕ) :=
  {q | ∑ j, q j = K ∧ ∀ j, (q j : ℝ) ≤ dbar j * K}

/-- The buffer constraint on a decision at state `q` (§5.1): serving with `(j, k)` must not push the
drop-off queue `k` over its buffer size, i.e. `q_k + 1 ≤ d_k` unless `j = k` (a self-pair leaves the state
unchanged). Dropping is always allowed. Together with `Feasible` (constraints (1), (2)) this is
feasibility in the finite-buffer setting. -/
def FeasibleBuf (dbar : V → ℝ) (K : ℕ) (q : V → ℕ) : Decision V → Prop
  | none => True
  | some (j, k) => j = k ∨ (q k : ℝ) + 1 ≤ dbar k * K

/-- A policy of the base class (randomized, history dependent, respecting (1)–(2)) that also respects
the buffers: it puts zero probability on any decision violating `FeasibleBuf`. These are the feasible
policies of the finite-buffer setting of §5.1. -/
def RespectsBuffers {P D : Ty → Finset V} (dbar : V → ℝ) (K : ℕ) (π : Policy P D) : Prop :=
  ∀ t h q τ d, ¬ FeasibleBuf dbar K q d → π.act t h q τ d = 0

/-- `K̃ = K + (∑_{j ∈ V} d̄_j) δ_K` with `δ_K = √K`, display (23), p. 22. -/
noncomputable def KtB (dbar : V → ℝ) (K : ℕ) : ℝ :=
  (K : ℝ) + dSum dbar * Real.sqrt K

/-- The normalized queue lengths with finite buffers, display (23), p. 22:
`q̄_j = (q_j + d̄_j δ_K) / K̃`, `δ_K = √K`. When `d̄ ≡ 1` this is (9). -/
noncomputable def qbarB (dbar : V → ℝ) (K : ℕ) (q : V → ℕ) (j : V) : ℝ :=
  ((q j : ℝ) + dbar j * Real.sqrt K) / KtB dbar K

/-- The MBP score with node-specific congestion functions `f = (f_j)_{j ∈ V}` and normalization (23):
`w_{jτk} + f_j(q̄_j) − f_k(q̄_k)` (display (10) / Algorithm 1, p. 13, as used in §5.1). -/
noncomputable def scoreB (w : V → Ty → V → ℝ) (f : V → ℝ → ℝ) (dbar : V → ℝ) (K : ℕ)
    (q : V → ℕ) (τ : Ty) (j k : V) : ℝ :=
  w j τ k + f j (qbarB dbar K q j) - f k (qbarB dbar K q k)

/-- A tie-breaking rule for the argmax of Algorithm 1 with node-specific congestion functions: for every
state `q` and type `τ`, `sel q τ` is a pair of `P(τ) × D(τ)` (self-pairs allowed) maximizing `scoreB` over
the whole of `P(τ) × D(τ)`. -/
structure IsArgmaxSelB (P D : Ty → Finset V) (w : V → Ty → V → ℝ) (f : V → ℝ → ℝ) (dbar : V → ℝ)
    (K : ℕ) (sel : (V → ℕ) → Ty → V × V) : Prop where
  mem : ∀ q τ, (sel q τ).1 ∈ P τ ∧ (sel q τ).2 ∈ D τ
  max : ∀ q τ, ∀ j ∈ P τ, ∀ k ∈ D τ,
    scoreB w f dbar K q τ j k ≤ scoreB w f dbar K q τ (sel q τ).1 (sel q τ).2

/-- The MBP decision of Algorithm 1 (p. 13) in the finite-buffer setting of §5.1: with `(j*, k*) = sel q τ`
the argmax pair over all of `P(τ) × D(τ)`, serve with `(j*, k*)` iff its score is nonnegative, the origin
queue is non-empty (`q_{j*} > 0`) and the drop-off queue has room (`FeasibleBuf`); otherwise drop. The
argmax is not re-optimized over the feasible pairs. -/
noncomputable def mbpDecisionB (w : V → Ty → V → ℝ) (f : V → ℝ → ℝ) (dbar : V → ℝ) (K : ℕ)
    (sel : (V → ℕ) → Ty → V × V) (q : V → ℕ) (τ : Ty) : Decision V :=
  if 0 ≤ scoreB w f dbar K q τ (sel q τ).1 (sel q τ).2 ∧ 0 < q (sel q τ).1 ∧
      ((sel q τ).1 = (sel q τ).2 ∨ (q (sel q τ).2 : ℝ) + 1 ≤ dbar (sel q τ).2 * K)
  then some (sel q τ) else none

/-- The finite-buffer MBP policy (Algorithm 1 with congestion functions `f` and normalization (23)) as a
deterministic stationary Markov member of the base policy class; `hmem` (field `mem` of `IsArgmaxSelB`)
makes its decisions satisfy (1)–(2). -/
noncomputable def mbpPolicyB (P D : Ty → Finset V) (w : V → Ty → V → ℝ) (f : V → ℝ → ℝ)
    (dbar : V → ℝ) (K : ℕ) (sel : (V → ℕ) → Ty → V × V)
    (hmem : ∀ q τ, (sel q τ).1 ∈ P τ ∧ (sel q τ).2 ∈ D τ) : Policy P D where
  act _ _ q τ d := if d = mbpDecisionB w f dbar K sel q τ then 1 else 0
  nonneg _ _ q τ d := by split_ifs <;> norm_num
  sum_one _ _ q τ := by simp
  feasible _ _ q τ d hd := by
    rw [if_neg]
    rintro rfl
    apply hd
    unfold mbpDecisionB
    split_ifs with h
    · exact ⟨(hmem q τ).1, (hmem q τ).2, h.2.1⟩
    · trivial

end MirrorBP.JEA.Supplement


