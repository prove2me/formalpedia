-- Prove2me | Definitions.Def_VeinottBaseStock_Model
-- name    : VeinottBaseStock_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-27T19:37:47.777279+00:00
-- url     : https://prove2.me/theorems/c14e4886-1117-464e-9f9d-0e4e6bb31cc5
-- title:
--   Veinott's multi-product nonstationary inventory model: data, standing assumptions, policies and the cost (2.4) (§2)
-- statement:
--   This file sets up the infinite-horizon, multi-product, nonstationary inventory model of Veinott (1965, §2).
--
--   There are $n$ products and $m$ demand classes. Vectors are compared componentwise: $u \le v$ means $u_j \le v_j$ for every coordinate. In period $i = 1, 2, \dots$ the data are
--
--   1. a set $X_i \subseteq \mathbb{R}^n$ of admissible initial inventory vectors $x_i$ (a negative coordinate is a backlog);
--   2. a set $Y_i \subseteq \mathbb{R}^n$ of admissible inventory vectors $y_i$ after ordering;
--   3. a Borel set $\mathfrak{D}_i \subseteq \mathbb{R}^m$ of possible demand vectors, and the law $\Phi_i$ of the demand vector $D_i$;
--   4. an $n$-vector $q_i(x) \in [-\infty, +\infty]^n$ of Borel functions: the order must satisfy $y_i \ge q_i(x_i)$;
--   5. a Borel map $s_i(y, t) \in \mathbb{R}^n$, the stock at the end of the period, so that $x_{i+1} = s_i(y_i, D_i)$;
--   6. an ordering cost vector $c_i$ (ordering $y_i - x_i$ costs $c_i \cdot (y_i - x_i)$), a Borel holding and shortage cost $g_i(y, t)$, and a discount factor $\alpha_i \ge 0$.
--
--   From these the paper defines
--   $$W_i(y,t) = c_i\, y + g_i(y,t) - \alpha_i\, c_{i+1}\, s_i(y,t), \qquad L_i(y) = \int_{\mathfrak{D}_i} g_i(y,t)\, d\Phi_i(t), \qquad G_i(y) = \int_{\mathfrak{D}_i} W_i(y,t)\, d\Phi_i(t),$$
--   and $\beta_1 = 1$, $\beta_i = \prod_{j=1}^{i-1} \alpha_j$ for $i > 1$.
--
--   The **standing assumptions** of §2 are: $\alpha_i \ge 0$; $\mathfrak{D}_i$ is Borel; $q_i$, $s_i$, $g_i$ are Borel; $s_i(y,t) \in X_{i+1}$ for $y \in Y_i$ and $t \in \mathfrak{D}_i$; $\Phi_i$ is a probability distribution carried by $\mathfrak{D}_i$; the integrals $L_i(y)$ and $G_i(y)$ exist and are finite for every $y$; and there are constants $\gamma_i$ with $G_i(y) \ge \gamma_i$ for all $y$ and $i$ and $\sum_i |\beta_i \gamma_i| < \infty$. The demands $D_1, D_2, \dots$ are independent random vectors on a probability space, $D_i$ has law $\Phi_i$ and takes its values in $\mathfrak{D}_i$.
--
--   An **ordering policy** chooses the inventory level after ordering in period $i$ as a Borel function of the past demands $D_1, \dots, D_{i-1}$; with the initial vector $x_1$ fixed, the inventories $x_i$ and $y_i$ are then determined recursively by $x_{i+1} = s_i(y_i, D_i)$. It is **feasible** if its values lie in $Y_i$ and, for every possible demand history (all $D_j \in \mathfrak{D}_j$), $y_i \ge q_i(x_i)$. Its **cost** is
--   $$f(x_1 \mid \bar Y) = \sum_{i=1}^{\infty} \beta_i\, E\, G_i(y_i) \in (-\infty, +\infty], \tag{2.4}$$
--   and a feasible policy is **optimal** if its cost is at most that of every feasible policy.
--
--   These definitions are the common ground of every statement of the mission: the one-period functions $G_i$, the discounting $\beta_i$, the feasibility constraints and the expected discounted cost.
--
--   **Formalization Note.** Periods are 0-based: Lean index $k$ is the paper's period $k+1$ (so `β 0 = 1`). Vectors are `Fin n → ℝ` with the product order; `q k` is valued in `Fin n → EReal` and compared with `coeVec y`, the coordinatewise coercion. $\Phi_i$ is a `Measure` and "Borel" is `Measurable` on all of $\mathbb{R}^n$ (for $q_i$, which the paper defines on $X_i$, this is a harmless strengthening: any Borel function on $X_i$ can be extended). The constants $\gamma_i$ are a field of the model. Policies are functions of the past demands only (`Pol n m`); the paper notes (§5, p. 219) that "there is no loss in generality in restricting our attention to ordering policies $\bar Y$ such that $\bar Y_i(H_i) = \bar Y_i(\bar D_i)$", because with $x_1$ fixed the history is a function of the past demands. The range condition "the range of $\bar Y_i$ is $Y_i$" is read as range $\subseteq Y_i$. The cost is computed without junk values: `excess` is the $[0,\infty]$-valued series $\sum_i \int \beta_i (G_i(y_i) - \gamma_i)\, dP$ (lower Lebesgue integrals and an `ENNReal` sum; each integrand is nonnegative because $\beta_i \ge 0$ and $G_i \ge \gamma_i$), and `cost` adds the finite real number $\sum_i \beta_i \gamma_i$ in `EReal`. Its value does not depend on the choice of the constants $\gamma_i$.
-- source:
--   Veinott, Optimal Policy for a Multi-Product, Dynamic, Nonstationary Inventory Problem, Management Science 12(3):206–222 (1965), pp. 207–210, §2 (model, standing assumptions, (2.4), optimality); p. 208 footnote 3 (vector order); p. 219, §5 (restriction to policies of the past demands)

import Mathlib

open MeasureTheory ProbabilityTheory

namespace VeinottBaseStock

/-- The data of Veinott's multi-product, dynamic, nonstationary inventory model (§2, pp. 207–210).
There are `n` products and `m` demand classes. Periods are indexed from `0`: Lean period `k` is the
paper's period `k + 1`.

* `X k` — admissible initial inventory vectors `x_{k+1}` (a negative coordinate is a backlog);
* `Y k` — admissible inventory vectors after ordering, `y_{k+1}`;
* `Dset k` — the set `𝔇_{k+1}` of values of the demand vector `D_{k+1}`;
* `q k` — the extended-real lower bound on `y` after ordering: `y_{k+1} ≥ q_{k+1}(x_{k+1})`;
* `s k y t` — the end-of-period stock vector `s_{k+1}(y, t) = x_{k+2}`;
* `c k` — the linear ordering cost vector `c_{k+1}`; ordering `y - x` costs `c_{k+1} ⬝ (y - x)`;
* `g k y t` — the holding and shortage cost `g_{k+1}(y, t)`;
* `α k` — the discount factor `α_{k+1}`;
* `Φ k` — the probability law of `D_{k+1}`;
* `γ k` — the constants `γ_{k+1}` of the lower-bound assumption on `G_{k+1}` (p. 210). -/
structure Model (n m : ℕ) where
  X : ℕ → Set (Fin n → ℝ)
  Y : ℕ → Set (Fin n → ℝ)
  Dset : ℕ → Set (Fin m → ℝ)
  q : ℕ → (Fin n → ℝ) → (Fin n → EReal)
  s : ℕ → (Fin n → ℝ) → (Fin m → ℝ) → (Fin n → ℝ)
  c : ℕ → Fin n → ℝ
  g : ℕ → (Fin n → ℝ) → (Fin m → ℝ) → ℝ
  α : ℕ → ℝ
  Φ : ℕ → Measure (Fin m → ℝ)
  γ : ℕ → ℝ

/-- A real vector read coordinatewise as an extended-real vector, so that it can be compared with
`q k x`. -/
def coeVec {n : ℕ} (y : Fin n → ℝ) : Fin n → EReal := fun j => ((y j : ℝ) : EReal)

variable {n m : ℕ}

/-- `W_{k+1}(y, t) = c_{k+1} y + g_{k+1}(y, t) - α_{k+1} c_{k+2} s_{k+1}(y, t)` (p. 209). -/
def Model.W (M : Model n m) (k : ℕ) (y : Fin n → ℝ) (t : Fin m → ℝ) : ℝ :=
  M.c k ⬝ᵥ y + M.g k y t - M.α k * (M.c (k + 1) ⬝ᵥ M.s k y t)

/-- `L_{k+1}(y) = ∫_{𝔇_{k+1}} g_{k+1}(y, t) dΦ_{k+1}(t)` (p. 209). -/
noncomputable def Model.L (M : Model n m) (k : ℕ) (y : Fin n → ℝ) : ℝ :=
  ∫ t in M.Dset k, M.g k y t ∂(M.Φ k)

/-- `G_{k+1}(y) = ∫_{𝔇_{k+1}} W_{k+1}(y, t) dΦ_{k+1}(t)` (p. 209). -/
noncomputable def Model.G (M : Model n m) (k : ℕ) (y : Fin n → ℝ) : ℝ :=
  ∫ t in M.Dset k, M.W k y t ∂(M.Φ k)

/-- The discount to period `k + 1`: `β_1 = 1`, `β_{k+1} = α_1 ⋯ α_k` (p. 209). -/
def Model.β (M : Model n m) (k : ℕ) : ℝ := ∏ j ∈ Finset.range k, M.α j

/-- The standing assumptions of §2 (pp. 207–210). -/
structure Model.Standing (M : Model n m) : Prop where
  /-- `0 ≤ α_i` (p. 209). -/
  alpha_nonneg : ∀ k, 0 ≤ M.α k
  /-- `𝔇_i` is a Borel set (p. 209). -/
  dset_measurableSet : ∀ k, MeasurableSet (M.Dset k)
  /-- `q_i` is a Borel function (p. 209). -/
  q_measurable : ∀ k, Measurable (M.q k)
  /-- `s_i(·,·)` is a Borel function (p. 209). -/
  s_measurable : ∀ k, Measurable (Function.uncurry (M.s k))
  /-- `g_i(·,·)` is a Borel function (p. 209). -/
  g_measurable : ∀ k, Measurable (Function.uncurry (M.g k))
  /-- The range of `s_i` is `X_{i+1}` (p. 208). -/
  s_mem : ∀ k, ∀ y ∈ M.Y k, ∀ t ∈ M.Dset k, M.s k y t ∈ M.X (k + 1)
  /-- `Φ_i` is a probability distribution (p. 207). -/
  isProbabilityMeasure : ∀ k, IsProbabilityMeasure (M.Φ k)
  /-- `D_i` takes values in `𝔇_i`, so its law is concentrated on `𝔇_i` (p. 207). -/
  Φ_compl_Dset : ∀ k, M.Φ k (M.Dset k)ᶜ = 0
  /-- The integral `L_i(y)` exists and is finite for every `y` (p. 209). -/
  g_integrableOn : ∀ k y, IntegrableOn (M.g k y) (M.Dset k) (M.Φ k)
  /-- The integral `G_i(y)` exists and is finite for every `y` (p. 209). -/
  W_integrableOn : ∀ k y, IntegrableOn (M.W k y) (M.Dset k) (M.Φ k)
  /-- `G_i(y) ≥ γ_i` for all `y` and `i` (p. 210). -/
  G_ge : ∀ k y, M.γ k ≤ M.G k y
  /-- `∑_i |β_i γ_i| < ∞` (p. 210). -/
  summable_β_γ : Summable fun k => |M.β k * M.γ k|

/-- The demand process (p. 207): `D_1, D_2, …` are independent random vectors on a probability
space `(Ω, P)`, `D_i` has law `Φ_i` and takes its values in `𝔇_i`. Lean's `D k` is `D_{k+1}`. -/
structure Model.IsDemandProcess (M : Model n m) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (D : ℕ → Ω → Fin m → ℝ) : Prop where
  measurable : ∀ k, Measurable (D k)
  indep : iIndepFun D P
  law : ∀ k, P.map (D k) = M.Φ k
  mem : ∀ k ω, D k ω ∈ M.Dset k

/-- An ordering policy in non-anticipative form: `Ŷ k d̄` is the inventory vector after ordering
in Lean period `k` (paper period `k + 1`) as a function of the demands `d̄ = (D_1, …, D_k)` of the
previous periods (the paper's `Ȳ_{k+1}(D̄_{k+1})`, §5, p. 219). -/
abbrev Pol (n m : ℕ) : Type := (k : ℕ) → (Fin k → Fin m → ℝ) → (Fin n → ℝ)

/-- The inventory vector after ordering in period `k` under the policy `Ŷ` along the demand path
`d`: `y_{k+1} = Ŷ_{k+1}(d_1, …, d_k)`. -/
def Model.orderSeq (_M : Model n m) (Ŷ : Pol n m) (d : ℕ → Fin m → ℝ) (k : ℕ) : Fin n → ℝ :=
  Ŷ k (fun j : Fin k => d j)

/-- The initial inventory vector of period `k` under `Ŷ` along `d`, from the fixed initial vector
`x₁`: `x_1 = x₁`, `x_{k+2} = s_{k+1}(y_{k+1}, d_{k+1})`. -/
def Model.stateSeq (M : Model n m) (Ŷ : Pol n m) (x₁ : Fin n → ℝ) (d : ℕ → Fin m → ℝ) :
    ℕ → Fin n → ℝ
  | 0 => x₁
  | k + 1 => M.s k (M.orderSeq Ŷ d k) (d k)

/-- A feasible ordering policy (pp. 208–209): every decision rule is a Borel function with values
in `Y_i`, and for every possible history (every demand path with `d_i ∈ 𝔇_i`) the order satisfies
`y_i ≥ q_i(x_i)`. -/
structure Model.Feasible (M : Model n m) (x₁ : Fin n → ℝ) (Ŷ : Pol n m) : Prop where
  measurable : ∀ k, Measurable (Ŷ k)
  mem_Y : ∀ k z, Ŷ k z ∈ M.Y k
  q_le : ∀ d : ℕ → Fin m → ℝ, (∀ j, d j ∈ M.Dset j) →
    ∀ k, M.q k (M.stateSeq Ŷ x₁ d k) ≤ coeVec (M.orderSeq Ŷ d k)

/-- The part of the cost (2.4) above the constants `γ_i`:
`∑_k E[β_{k+1} (G_{k+1}(y_{k+1}) - γ_{k+1})] ∈ [0, ∞]`, with the random `y_{k+1}` obtained by
running `Ŷ` along the demand process. -/
noncomputable def Model.excess (M : Model n m) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (D : ℕ → Ω → Fin m → ℝ) (Ŷ : Pol n m) : ENNReal :=
  ∑' k, ∫⁻ ω, ENNReal.ofReal (M.β k * (M.G k (M.orderSeq Ŷ (fun j => D j ω) k) - M.γ k)) ∂P

/-- The expected discounted cost (2.4), `f(x_1 | Ŷ) = ∑_i β_i E G_i(y_i)` with `+∞` allowed:
the extended-real sum of `excess` and the finite real series `∑_i β_i γ_i`. -/
noncomputable def Model.cost (M : Model n m) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (D : ℕ → Ω → Fin m → ℝ) (Ŷ : Pol n m) : EReal :=
  ((M.excess P D Ŷ : ENNReal) : EReal) + ((∑' k, M.β k * M.γ k : ℝ) : EReal)

/-- A policy is optimal (p. 210) if it is feasible and its cost is at most the cost of every
feasible policy. -/
def Model.IsOptimal (M : Model n m) (x₁ : Fin n → ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (D : ℕ → Ω → Fin m → ℝ) (Ŷ : Pol n m) : Prop :=
  M.Feasible x₁ Ŷ ∧ ∀ Ŷ' : Pol n m, M.Feasible x₁ Ŷ' → M.cost P D Ŷ ≤ M.cost P D Ŷ'

end VeinottBaseStock


