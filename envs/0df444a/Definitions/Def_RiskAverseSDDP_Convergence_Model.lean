-- Prove2me | Definitions.Def_RiskAverseSDDP_Convergence_Model
-- name    : RiskAverseSDDP_Convergence_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-10T03:46:38.334749+00:00
-- url     : https://prove2.me/theorems/339e00aa-61ed-4760-8c17-0ca656292772
-- title:
--   (3.9)–(3.13), (H1), (H2), pp. 5–7 — the risk-averse multistage stochastic convex program and its recourse functions
-- statement:
--   This file sets up the problem (3.9) under the interstage independence assumption (H1).
--
--   **Data.** There are $T$ stages $t=1,\dots,T$, decisions $x_t\in\mathbb R^n$ and a given $x_0\in\mathbb R^n$. At each stage $t\ge2$ the random data $\xi_t$ takes one of $M$ values $\xi_{t,1},\dots,\xi_{t,M}$ with probabilities $\Phi_{t,j}$; $\xi_1$ is deterministic. A realization $\xi_{t,j}$ consists of a cost $f_t(\cdot,\Psi_{t,j})$ on $(\mathbb R^n)^t$ with values in $\mathbb R\cup\{+\infty\}$, a constraint function $g_t(x_0,\cdot,\Psi_{t,j})$ with $p$ components in $\mathbb R\cup\{+\infty\}$, matrices $A_{t,\tau,j}$ ($\tau=0,\dots,t$) and a right-hand side $b_{t,j}$. Each stage also has a compact set $\mathcal X_t\subseteq\mathbb R^n$ and a set $\mathcal P_t\subseteq\mathbb R^M$. The feasible set of stage $t$ is
--   $$
--   X_t(x_{0:t-1},\xi_{t,j})=\Big\{x_t\in\mathcal X_t:\ g_t(x_{0:t},\Psi_{t,j})\le0,\ \sum_{\tau=0}^tA_{t,\tau,j}x_\tau=b_{t,j}\Big\}.
--   $$
--
--   **Risk measures.** With $\mathcal D_t=\{p\in\mathbb R^M:\ p\ge0,\ \sum_jp_j\Phi_{t,j}=1\}$, the risk measure of stage $t$ in dual form (3.13) is $\rho_t(Z)=\sup_{p\in\mathcal P_t}\sum_{j=1}^Mp_j\Phi_{t,j}Z_j$.
--
--   **Dynamic programming equations (3.10)–(3.12).** $\mathcal Q_{T+1}\equiv0$ and, for $t=T,\dots,2$,
--   $$
--   \mathfrak Q_t(x_{1:t-1},\xi_{t,j})=\inf_{x_t\in X_t(x_{0:t-1},\xi_{t,j})}\ f_t(x_{1:t},\Psi_{t,j})+\mathcal Q_{t+1}(x_{1:t}),\qquad
--   \mathcal Q_t(x_{1:t-1})=\rho_t\big(\mathfrak Q_t(x_{1:t-1},\xi_t)\big).
--   $$
--   The first stage problem (3.12) has optimal value $\mathcal Q_1(x_0)=\mathfrak Q_1(x_0,\xi_1)=\inf\{f_1(x_1,\Psi_1)+\mathcal Q_2(x_1):\ x_1\in X_1(x_0,\xi_1)\}$, and $x_1$ is an **optimal solution of the first stage problem** if $x_1\in X_1(x_0,\xi_1)$ and $f_1(x_1,\Psi_1)+\mathcal Q_2(x_1)=\mathcal Q_1(x_0)$. The recourse functions are constructed by this backward recursion from the data, not postulated.
--
--   **Standing assumptions.** For $t=2,\dots,T$: $\Phi_{t,j}>0$, $\sum_j\Phi_{t,j}=1$, and $\mathcal P_t$ is a nonempty convex subset of $\mathcal D_t$.
--
--   **Assumption (H2)** (pp. 6–7), for $t=1,\dots,T$ and one $\varepsilon>0$: 1) $\mathcal X_t$ is nonempty, convex and compact; 2) every $f_t(\cdot,\Psi_{t,j})$ is proper, convex and lower semicontinuous; 3) every component of $g_t(x_0,\cdot,\Psi_{t,j})$ is convex and lower semicontinuous; 4.1) $[\mathcal X_1\times\dots\times\mathcal X_{t-1}]^\varepsilon\times\mathcal X_t\subseteq\operatorname{dom}f_t(\cdot,\Psi_{t,j})$; 4.2) $X_t(x_{0:t-1},\xi_{t,j})\ne\emptyset$ for every $x_{1:t-1}\in[\mathcal X_1\times\dots\times\mathcal X_{t-1}]^\varepsilon$; 5) if $t\ge2$, for every $j$ there is $\bar x_{t,j}=(\bar x_{t,j,1},\dots,\bar x_{t,j,t})\in\mathcal X_1\times\dots\times\mathcal X_{t-1}\times\operatorname{ri}(\mathcal X_t)\cap\operatorname{ri}(\{g_t(x_0,\cdot,\Psi_{t,j})\le0\})$ with $\bar x_{t,j,t}\in X_t(x_0,\bar x_{t,j,1},\dots,\bar x_{t,j,t-1},\xi_{t,j})$. Here $[\cdot]^\varepsilon$ is the $\varepsilon$-fattening in $\mathbb R^{n(t-1)}$ with the Euclidean norm.
--
--   **Formalization Note** Indices: stages keep the paper's numbers; realizations $j=1,\dots,M$ are `Fin M`; the deterministic stage 1 uses the data of the first index, and the other indices are never read there. The recourse function `Q s` takes a history of length $s$ and is the paper's $\mathcal Q_{s+1}$ ($1\le s\le T$, with `Q T` $=\mathcal Q_{T+1}\equiv0$); `Qf s j` is $\mathfrak Q_{s+1}(\cdot,\xi_{s+1,j})$ and `Q1` is $\mathcal Q_1(x_0)$ (`Q 0` is not used). All values are in `EReal`; infima are `+∞` on empty feasible sets; the weights $p_j\Phi_{t,j}$ are real numbers, and `EReal` multiplication has $0\cdot(\pm\infty)=0$. (H1) is built into the indexing (the data depend on $(t,j)$ only), so it is not a hypothesis. The measurability in (H2)-2) is automatic for finitely many realizations and is not restated. The paper's $\varepsilon$ of (H2)-4) is per stage; one common $\varepsilon$ is equivalent (take the minimum, 4.1) and 4.2) being monotone in $\varepsilon$). $\mathcal P_t\ne\emptyset$ is not printed; it holds because $\rho_t$ is a real-valued coherent risk measure, whose dual set is nonempty. The dimensions $p$ and the number of equality constraints do not depend on $t$ (padding with trivial constraints).
-- source:
--   Guigues, Convergence Analysis of Sampling-Based Decomposition Methods for Risk-Averse Multistage Stochastic Convex Programs, arXiv:1408.4439v4, pp. 5–7, (3.9)–(3.13), (H1), (H2)

import Mathlib
import Definitions.Def_RiskAverseSDDP_Convergence_Basic

namespace RiskAverseSDDP.Convergence

/-- The data of the risk-averse multistage stochastic convex program (3.9), p. 5, under the
interstage independence (H1), p. 5, with `T` stages, decisions in `ℝⁿ`, `M` realizations of
`ξ_t` per stage `t = 2, …, T`, `q` linear equality constraints and `p` nonlinear constraints
per stage. Stages carry the paper's numbering `t = 1, …, T`, and realizations are indexed by
`j ∈ Fin M` (the paper's `j = 1, …, M`). Entries at other stages are never read.
* `x0 ∈ ℝⁿ` the given initial decision `x_0`;
* `Xc t` the compact set `𝒳_t ⊆ ℝⁿ`;
* `f t j : (ℝⁿ)ᵗ → ℝ ∪ {+∞}` the cost `f_t(·, Ψ_{t,j})`;
* `g t j x₀ : (ℝⁿ)ᵗ → (ℝ ∪ {+∞})ᵖ` the constraint function `g_t(x_0, ·, Ψ_{t,j})`, componentwise;
* `A t j τ` the matrix `A_{t,τ,j}` (`τ = 0, …, t`, as a linear map) and `b t j` the right-hand
  side `b_{t,j}`;
* `Φ t j = ℙ(ξ_t = ξ_{t,j})`;
* `Prisk t ⊆ ℝᴹ` the set `𝒫_t` of the dual representation (3.13) of `ρ_t`.
Stage 1 is deterministic: its data are those of the realization `j = 0`
(`Fin M`'s first index), and the other indices are never read at stage 1. -/
structure Model (T n M q p : ℕ) where
  x0 : EuclideanSpace ℝ (Fin n)
  Xc : ℕ → Set (EuclideanSpace ℝ (Fin n))
  f : (t : ℕ) → Fin M → Hist n t → EReal
  g : (t : ℕ) → Fin M → EuclideanSpace ℝ (Fin n) → Hist n t → Fin p → EReal
  A : (t : ℕ) → Fin M → Fin (t + 1) → (EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin q))
  b : ℕ → Fin M → EuclideanSpace ℝ (Fin q)
  Φ : ℕ → Fin M → ℝ
  Prisk : ℕ → Set (Fin M → ℝ)

namespace Model

variable {T n M q p : ℕ} (D : Model T n M q p)

/-- The realizations of `ξ_t` that occur: only `j = 0` at the deterministic first stage, all of
`Fin M` at `t ≥ 2`. -/
def Rlz [NeZero M] (t : ℕ) : Set (Fin M) :=
  if t = 1 then {0} else Set.univ

/-- The feasible set of stage `s + 1` (p. 5):
`X_{s+1}(x_{0:s}, ξ_{s+1,j}) = {x_{s+1} ∈ 𝒳_{s+1} : g_{s+1}(x_{0:s+1}, Ψ_{s+1,j}) ≤ 0,
Σ_{τ=0}^{s+1} A_{s+1,τ,j} x_τ = b_{s+1,j}}`, for the history `x_{1:s}` and the given `x_0`. -/
def feas (s : ℕ) (j : Fin M) (x : Hist n s) : Set (EuclideanSpace ℝ (Fin n)) :=
  {y | y ∈ D.Xc (s + 1) ∧ (∀ i, D.g (s + 1) j D.x0 (x.snoc y) i ≤ 0) ∧
    ∑ τ : Fin (s + 2), D.A (s + 1) j τ
      (Fin.cons (α := fun _ => EuclideanSpace ℝ (Fin n)) D.x0 (fun i => (x.snoc y) i) τ) =
      D.b (s + 1) j}

/-- The product `𝒳_1 × … × 𝒳_s ⊆ ℝ^{ns}`. -/
def prodSet (s : ℕ) : Set (Hist n s) :=
  {x | ∀ i : Fin s, x i ∈ D.Xc (i.val + 1)}

/-- The set `𝒟_t = {π ∈ ℝᴹ : π ≥ 0, Σ_j π_j Φ_{t,j} = 1}` of (3.13), p. 6. -/
def dualSet (t : ℕ) : Set (Fin M → ℝ) :=
  {π | 0 ≤ π ∧ ∑ j, π j * D.Φ t j = 1}

/-- `Σ_j π_j Φ_{t,j} Z_j` for `Z ∈ (ℝ ∪ {±∞})ᴹ`, with the weights `π_j Φ_{t,j}` as real numbers
(the `EReal` product has `0 · (±∞) = 0`). -/
noncomputable def wsum (t : ℕ) (π : Fin M → ℝ) (Z : Fin M → EReal) : EReal :=
  ∑ j, ((π j * D.Φ t j : ℝ) : EReal) * Z j

/-- The risk measure in dual form (3.13), p. 6: `ρ_t(Z) = sup_{π ∈ 𝒫_t} Σ_j π_j Φ_{t,j} Z_j`,
a supremum in `ℝ ∪ {±∞}`. -/
noncomputable def rho (t : ℕ) (Z : Fin M → EReal) : EReal :=
  ⨆ π ∈ D.Prisk t, D.wsum t π Z

/-- The optimal value of the stage-`(s + 1)` problem with cost-to-go `V` ((3.11) for
`V = 𝒬_{s+2}`, (3.14) for `V = 𝒬^{k-1}_{s+2}`):
`inf {f_{s+1}(x_{1:s+1}, Ψ_{s+1,j}) + V(x_{1:s+1}) : x_{s+1} ∈ X_{s+1}(x_{0:s}, ξ_{s+1,j})}`,
an infimum in `ℝ ∪ {±∞}` (`+∞` on an empty feasible set). -/
noncomputable def stageVal (s : ℕ) (j : Fin M) (V : Hist n (s + 1) → EReal) (x : Hist n s) :
    EReal :=
  ⨅ y ∈ D.feas s j x, (D.f (s + 1) j (x.snoc y) + V (x.snoc y))

/-- The dynamic programming recursion (3.10)–(3.11), (3.13), run for `r` levels:
`Qaux 0 s ≡ 0` and `Qaux (r + 1) s (x_{1:s}) = ρ_{s+1}(j ↦ inf_{x_{s+1} ∈ X_{s+1}(x_{0:s},
ξ_{s+1,j})} f_{s+1}(x_{1:s+1}, Ψ_{s+1,j}) + Qaux r (s + 1) (x_{1:s+1}))`. -/
noncomputable def Qaux : ℕ → (s : ℕ) → Hist n s → EReal
  | 0, _, _ => 0
  | r + 1, s, x => D.rho (s + 1) (fun j => D.stageVal s j (Qaux r (s + 1)) x)

/-- The recourse function `𝒬_{s+1}` of (3.10), a function of the history `x_{1:s}`, for
`s = 1, …, T`: `Q T = 𝒬_{T+1} ≡ 0` and, for `1 ≤ s < T`,
`𝒬_{s+1}(x_{1:s}) = ρ_{s+1}(𝔔_{s+1}(x_{1:s}, ξ_{s+1}))`. (The value at `s = 0` is not the
first-stage value; that is `Q1`.) -/
noncomputable def Q (s : ℕ) : Hist n s → EReal :=
  D.Qaux (T - s) s

/-- The stage value function `𝔔_{s+1}(x_{1:s}, ξ_{s+1,j})` of (3.11), p. 6:
`inf {F_{s+1}(x_{1:s+1}, Ψ_{s+1,j}) := f_{s+1}(x_{1:s+1}, Ψ_{s+1,j}) + 𝒬_{s+2}(x_{1:s+1}) :
x_{s+1} ∈ X_{s+1}(x_{0:s}, ξ_{s+1,j})}`. -/
noncomputable def Qf (s : ℕ) (j : Fin M) (x : Hist n s) : EReal :=
  D.stageVal s j (D.Q (s + 1)) x

/-- The optimal value `𝒬_1(x_0) = 𝔔_1(x_0, ξ_1)` of the first stage problem (3.12), p. 6. -/
noncomputable def Q1 [NeZero M] : EReal :=
  D.Qf 0 0 (Hist.empty n)

/-- `x₁` is an optimal solution of the first stage problem (3.12):
`x₁ ∈ X_1(x_0, ξ_1)` and `F_1(x₁, Ψ_1) = f_1(x₁, Ψ_1) + 𝒬_2(x₁) = 𝒬_1(x_0)`. -/
def IsFirstStageOptimal [NeZero M] (x₁ : EuclideanSpace ℝ (Fin n)) : Prop :=
  x₁ ∈ D.feas 0 0 (Hist.empty n) ∧
    D.f 1 0 ((Hist.empty n).snoc x₁) + D.Q 1 ((Hist.empty n).snoc x₁) = D.Q1

/-- The standing assumptions on the probabilities and the risk sets, for `t = 2, …, T`:
`Φ_{t,j} > 0` and `Σ_j Φ_{t,j} = 1` ((H1), p. 5, and p. 6); `𝒫_t` is a convex subset of `𝒟_t`
((3.13), p. 6); and `𝒫_t ≠ ∅` (implicit: `ρ_t` is a real-valued coherent risk measure, whose
dual set is nonempty). -/
def Standing : Prop :=
  ∀ t, 2 ≤ t → t ≤ T →
    (∀ j, 0 < D.Φ t j) ∧ ∑ j, D.Φ t j = 1 ∧
    D.Prisk t ⊆ D.dualSet t ∧ Convex ℝ (D.Prisk t) ∧ (D.Prisk t).Nonempty

/-- Assumption (H2), pp. 6–7, for `t = s + 1 = 1, …, T`, with one `ε > 0` for all stages:
1) `𝒳_t` is nonempty, convex and compact;
2) for every realization `j`, `f_t(·, Ψ_{t,j})` is proper, convex and lower semicontinuous;
3) for every `j`, each component of `g_t(x_0, ·, Ψ_{t,j})` is convex and lower semicontinuous;
4.1) for every `j`, `[𝒳_1 × … × 𝒳_{t-1}]^ε × 𝒳_t ⊆ dom f_t(·, Ψ_{t,j})`;
4.2) for every `j` and every `x_{1:t-1} ∈ [𝒳_1 × … × 𝒳_{t-1}]^ε`,
     `X_t(x_{0:t-1}, ξ_{t,j}) ≠ ∅`;
5) if `t ≥ 2`, for every `j` there is `x̄_{t,j} = (x̄_{1:t-1}, x̄_t) ∈ 𝒳_1 × … × 𝒳_{t-1} × ri(𝒳_t)`
   with `x̄_{t,j} ∈ ri({g_t(x_0, ·, Ψ_{t,j}) ≤ 0})` and `x̄_t ∈ X_t(x_0, x̄_{1:t-1}, ξ_{t,j})`.
The fattening is the closed `ε`-thickening in `ℝ^{n(t-1)}` with the Euclidean norm. The
measurability of `f_t(x_{1:t}, ·)` in 2) is automatic for finitely many realizations and is
not restated. -/
def H2 [NeZero M] (ε : ℝ) : Prop :=
  0 < ε ∧ ∀ s, s < T →
    ((D.Xc (s + 1)).Nonempty ∧ Convex ℝ (D.Xc (s + 1)) ∧ IsCompact (D.Xc (s + 1))) ∧
    (∀ j ∈ Rlz (M := M) (s + 1),
      EProper (D.f (s + 1) j) ∧ EConvex (D.f (s + 1) j) ∧ LowerSemicontinuous (D.f (s + 1) j)) ∧
    (∀ j ∈ Rlz (M := M) (s + 1), ∀ i,
      EConvex (fun z => D.g (s + 1) j D.x0 z i) ∧
        LowerSemicontinuous (fun z => D.g (s + 1) j D.x0 z i)) ∧
    (∀ j ∈ Rlz (M := M) (s + 1), ∀ x ∈ Metric.cthickening ε (D.prodSet s),
      ∀ y ∈ D.Xc (s + 1), D.f (s + 1) j (x.snoc y) < ⊤) ∧
    (∀ j ∈ Rlz (M := M) (s + 1), ∀ x ∈ Metric.cthickening ε (D.prodSet s),
      (D.feas s j x).Nonempty) ∧
    (1 ≤ s → ∀ j : Fin M, ∃ xb : Hist n s, ∃ yb : EuclideanSpace ℝ (Fin n),
      xb ∈ D.prodSet s ∧ yb ∈ intrinsicInterior ℝ (D.Xc (s + 1)) ∧
      xb.snoc yb ∈ intrinsicInterior ℝ {z : Hist n (s + 1) | ∀ i, D.g (s + 1) j D.x0 z i ≤ 0} ∧
      yb ∈ D.feas s j xb)

end Model

end RiskAverseSDDP.Convergence


