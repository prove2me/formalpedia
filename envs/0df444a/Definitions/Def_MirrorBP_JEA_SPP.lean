-- Prove2me | Definitions.Def_MirrorBP_JEA_SPP
-- name    : MirrorBP_JEA_SPP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-23T03:57:38.56233+00:00
-- url     : https://prove2.me/theorems/9b3a0af3-f8dc-4e2d-8d7d-3b894f38c510
-- title:
--   §4 and Appendix A — the static planning problem SPP(φ) (11)–(13), its flow form and relaxed flow balance (29)–(32), acyclic flows, the dual g (15)
-- statement:
--   The linear programs of the analysis.
--
--   1. **SPP(φ)** ((11)–(13), p. 15). Maximize $\sum_{\tau, j \in \mathcal P(\tau), k \in \mathcal D(\tau)} w_{j\tau k}\phi_\tau x_{j\tau k}$ subject to flow balance $\sum \phi_\tau x_{j\tau k}(\mathbf e_j - \mathbf e_k) = \mathbf 0$ and the demand constraint $\sum_{j \in \mathcal P(\tau),k \in \mathcal D(\tau)} x_{j\tau k} \le 1$, $x_{j\tau k} \ge 0$ for every $\tau$. Its optimal value is $W^{\mathrm{SPP}}(\boldsymbol\phi)$.
--   2. **Flow form** (Appendix A, (29)–(31), PDF 34). The variables are flows $z_{j\tau k}$ (the correspondence is $z = \phi x$): maximize $\sum w_{j\tau k} z_{j\tau k}$ subject to $\sum z_{j\tau k}(\mathbf e_j - \mathbf e_k) = \mathbf 0$ (30) and $\sum_{j,k} z_{j\tau k} \le \phi_\tau$, $z_{j\tau k} \ge 0$ (31).
--   3. **Relaxed flow balance** (32). For a slack $r$ (the paper takes $r = K/T$),
--   $$\Big|\mathbf 1_S^\top \sum_{\tau, j \in \mathcal P(\tau), k \in \mathcal D(\tau)} z_{j\tau k}(\mathbf e_j - \mathbf e_k)\Big| \le r \qquad \forall S \subseteq V.$$
--   The value of the LP (29), (31), (32) is the relaxed value.
--   4. **Acyclic flows** (PDF 35). $\mathbf z$ is acyclic if there is no cycle $((j_1,\tau_1,j_2),\dots,(j_s,\tau_s,j_{s+1} = j_1))$ with $z_{j_r\tau_r j_{r+1}} > 0$ for all $r$; a self-pair $j = k$ with positive flow is a cycle of length one.
--   5. **Dual function** (15), p. 16:
--   $$g(\mathbf y) = \sum_{\tau\in\mathcal T} \phi_\tau \max_{j \in \mathcal P(\tau), k \in \mathcal D(\tau)} (w_{j\tau k} + y_j - y_k)^+,$$
--   the partial Lagrangian dual of SPP(φ) with the flow-balance constraints dualized.
--
--   **Formalization Note** Only entries with $j \in \mathcal P(\tau)$, $k \in \mathcal D(\tau)$ are read (the paper's convention $x_{j\tau' k} = 0$ for $\tau' \ne \tau$). Flow balance is stated node by node. $W^{\mathrm{SPP}}$ and the relaxed value are real suprema over sets that are nonempty ($x = 0$, resp. $z = 0$ when $\phi \ge 0$, $r \ge 0$) and on which the objective is bounded, so they are the LP optimal values. `ymax`/`ymin` are $\max_j y_j$ and $\min_j y_j$.
-- source:
--   Kanoria, Qian, Blind Dynamic Resource Allocation in Closed Networks via Mirror Backpressure, arXiv:1903.02764v4, p. 15, (11)–(13); p. 16, (15); Appendix A, appendix pp. 1–2 (PDF 34–35), (29)–(32) and acyclic flows

import Mathlib
import Definitions.Def_MirrorBP_JEA_Model

namespace MirrorBP.JEA

open Finset

variable {V Ty : Type} [Fintype V] [DecidableEq V] [Fintype Ty] [DecidableEq Ty]

/-- The net outflow of supply from a node set `S` under the flows `z`:
`1_Sᵀ (∑_{τ ∈ 𝒯, j ∈ P(τ), k ∈ D(τ)} z_{jτk} (e_j − e_k))`. Only the entries with `j ∈ P(τ)`,
`k ∈ D(τ)` are read (the paper's convention that other entries are zero). -/
def netOut (P D : Ty → Finset V) (z : V → Ty → V → ℝ) (S : Finset V) : ℝ :=
  ∑ τ, ∑ j ∈ P τ, ∑ k ∈ D τ, z j τ k * ((if j ∈ S then 1 else 0) - (if k ∈ S then 1 else 0))

/-- Feasibility for SPP(φ) in fraction form, (12)–(13), p. 15: flow balance
`∑_{τ, j ∈ P(τ), k ∈ D(τ)} φ_τ x_{jτk} (e_j − e_k) = 0` (coordinate by coordinate), and the demand
constraint `∑_{j ∈ P(τ), k ∈ D(τ)} x_{jτk} ≤ 1`, `x_{jτk} ≥ 0` for every type `τ`. -/
def sppFeasX (P D : Ty → Finset V) (φ : Ty → ℝ) (x : V → Ty → V → ℝ) : Prop :=
  (∀ i : V, netOut P D (fun j τ k => φ τ * x j τ k) {i} = 0) ∧
  (∀ τ, ∑ j ∈ P τ, ∑ k ∈ D τ, x j τ k ≤ 1) ∧
  (∀ τ, ∀ j ∈ P τ, ∀ k ∈ D τ, 0 ≤ x j τ k)

/-- The objective (11), p. 15: `∑_{τ, j ∈ P(τ), k ∈ D(τ)} w_{jτk} φ_τ x_{jτk}`. -/
def sppObjX (P D : Ty → Finset V) (w : V → Ty → V → ℝ) (φ : Ty → ℝ) (x : V → Ty → V → ℝ) : ℝ :=
  ∑ τ, ∑ j ∈ P τ, ∑ k ∈ D τ, w j τ k * φ τ * x j τ k

/-- `W^SPP(φ)`, the optimal value of the static planning problem SPP(φ), (11)–(13), p. 15–16. The
feasible set is nonempty (`x = 0`) and the objective is bounded on it (`0 ≤ x`, `∑ x ≤ 1` per type), so
this `sSup` is the LP's optimal value. -/
noncomputable def Wspp (P D : Ty → Finset V) (w : V → Ty → V → ℝ) (φ : Ty → ℝ) : ℝ :=
  sSup (sppObjX P D w φ '' {x | sppFeasX P D φ x})

/-- The demand constraint (31) of the flow form (Appendix A, appendix p. 1, PDF 34):
`∑_{j ∈ P(τ), k ∈ D(τ)} z_{jτk} ≤ φ_τ` and `z_{jτk} ≥ 0` for every type `τ`. -/
def demandZ (P D : Ty → Finset V) (φ : Ty → ℝ) (z : V → Ty → V → ℝ) : Prop :=
  (∀ τ, ∑ j ∈ P τ, ∑ k ∈ D τ, z j τ k ≤ φ τ) ∧ (∀ τ, ∀ j ∈ P τ, ∀ k ∈ D τ, 0 ≤ z j τ k)

/-- Feasibility for SPP(φ) in flow form, (30)–(31), Appendix A, PDF 34: exact flow balance
`∑ z_{jτk} (e_j − e_k) = 0` (coordinate by coordinate) and the demand constraint (31). -/
def sppFeasZ (P D : Ty → Finset V) (φ : Ty → ℝ) (z : V → Ty → V → ℝ) : Prop :=
  (∀ i : V, netOut P D z {i} = 0) ∧ demandZ P D φ z

/-- Feasibility for the relaxed LP of Appendix A: the demand constraint (31) and approximate flow
balance (32) with slack `r`, `|1_Sᵀ ∑ z_{jτk}(e_j − e_k)| ≤ r` for every `S ⊆ V` (the paper takes
`r = K/T`, PDF 34–35). -/
def relaxedFeasZ (P D : Ty → Finset V) (φ : Ty → ℝ) (r : ℝ) (z : V → Ty → V → ℝ) : Prop :=
  demandZ P D φ z ∧ ∀ S : Finset V, |netOut P D z S| ≤ r

/-- The flow-form objective (29): `∑_{τ, j ∈ P(τ), k ∈ D(τ)} w_{jτk} z_{jτk}`. -/
def objZ (P D : Ty → Finset V) (w : V → Ty → V → ℝ) (z : V → Ty → V → ℝ) : ℝ :=
  ∑ τ, ∑ j ∈ P τ, ∑ k ∈ D τ, w j τ k * z j τ k

/-- The value of the LP (29), (31), (32): maximize (29) subject to the demand constraint (31) and the
approximate flow balance (32) with slack `r`. For `φ ≥ 0` and `r ≥ 0` the feasible set is nonempty
(`z = 0`) and the objective is bounded on it (`0 ≤ z`, `∑ z ≤ φ_τ`), so this `sSup` is the LP's value. -/
noncomputable def relaxedValue (P D : Ty → Finset V) (w : V → Ty → V → ℝ) (φ : Ty → ℝ) (r : ℝ) : ℝ :=
  sSup (objZ P D w '' {z | relaxedFeasZ P D φ r z})

/-- A (directed) acyclic flow (Appendix A, appendix p. 2, PDF 35): there is no cycle
`((j₀, τ₀, j₁), (j₁, τ₁, j₂), …, (j_{s−1}, τ_{s−1}, j_s = j₀))`, `s ≥ 1`, of admissible pairs
(`j_r ∈ P(τ_r)`, `j_{r+1} ∈ D(τ_r)`) carrying positive flow `z_{j_r τ_r j_{r+1}} > 0` for all `r < s`.
A self-pair `j = k ∈ P(τ) ∩ D(τ)` with positive flow is a cycle of length `s = 1`. -/
def IsAcyclicFlow (P D : Ty → Finset V) (z : V → Ty → V → ℝ) : Prop :=
  ∀ (s : ℕ) (j : ℕ → V) (τ : ℕ → Ty), 0 < s → j s = j 0 →
    ¬ ∀ r < s, j r ∈ P (τ r) ∧ j (r + 1) ∈ D (τ r) ∧ 0 < z (j r) (τ r) (j (r + 1))

/-- The (partial) dual function (15), p. 16:
`g(y) = ∑_τ φ_τ max_{j ∈ P(τ), k ∈ D(τ)} (w_{jτk} + y_j − y_k)⁺`, with `(x)⁺ = max{0, x}`. (The inner
maximum is over the nonempty set `P(τ) × D(τ)`; the value `0` for an empty set is never used.) -/
noncomputable def gDual (P D : Ty → Finset V) (w : V → Ty → V → ℝ) (φ : Ty → ℝ) (y : V → ℝ) : ℝ :=
  ∑ τ, φ τ * (if h : (P τ ×ˢ D τ).Nonempty then
      (P τ ×ˢ D τ).sup' h (fun p => max 0 (w p.1 τ p.2 + y p.1 - y p.2)) else 0)

/-- `max_{j ∈ V} y_j` (the value `0` for empty `V` is never used). -/
noncomputable def ymax (y : V → ℝ) : ℝ :=
  if h : (univ : Finset V).Nonempty then univ.sup' h y else 0

/-- `min_{j ∈ V} y_j` (the value `0` for empty `V` is never used). -/
noncomputable def ymin (y : V → ℝ) : ℝ :=
  if h : (univ : Finset V).Nonempty then univ.inf' h y else 0

end MirrorBP.JEA


