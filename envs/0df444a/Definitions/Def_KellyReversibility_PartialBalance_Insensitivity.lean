-- Prove2me | Definitions.Def_KellyReversibility_PartialBalance_Insensitivity
-- name    : KellyReversibility_PartialBalance_Insensitivity
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T04:00:13.07468+00:00
-- url     : https://prove2.me/theorems/6bee9dce-507a-440f-bec1-e854e4e4110e
-- title:
--   Reduced descriptions $n_j=f_j(x_j)$, the two assumptions of p. 204, and the rates (9.31)
-- statement:
--   The setting of Kelly's Theorem 9.9. A spatial process $\mathbf x=(x_1,\dots,x_J)$ has state space $\mathcal X_1\times\cdots\times\mathcal X_J$; for each site $j$ a function $f_j:\mathcal X_j\to\mathcal N_j$ gives a less detailed description $n_j=f_j(x_j)$, and $\mathbf n=f(\mathbf x)=(f_1(x_1),\dots,f_J(x_J))$.
--
--   1. **First assumption** (p. 204): the transition rates $q(\mathbf x,T_j^y\mathbf x)$ depend on $\mathbf x_{G-j}$ only through $\mathbf n_{G-j}$.
--   2. **Second assumption (9.29)**: the equilibrium distribution $\pi(x_j;\mathbf x_{G-j})$ of the truncated process $x_j$ (sites other than $j$ frozen at $\mathbf x_{G-j}$) can be written
--   $$\pi(x_j;\mathbf x_{G-j})=\pi(n_j;\mathbf n_{G-j})\,P_j(x_j\mid n_j),\qquad \pi(n_j;\mathbf n_{G-j})=\sum_{x_j':f_j(x_j')=n_j}\pi(x_j';\mathbf x_{G-j}),$$
--   with $P_j(x_j\mid n_j)$ not depending on $\mathbf x_{G-j}$.
--   3. **The reduced rates (9.31)**:
--   $$q(\mathbf n,T_j^m\mathbf n)=\sum_{x_j:f_j(x_j)=n_j}P_j(x_j\mid n_j)\sum_{y:f_j(y)=m}q(\mathbf x,T_j^y\mathbf x),$$
--   where the sites other than $j$ of $\mathbf x$ are any states with $f_i(x_i)=n_i$.
--
--   **Formalization Note** $P_j(x_j\mid n_j)$ is a function $P_j$ on $\mathcal X_j$, read at $n_j=f_j(x_j)$. In (9.31) the sites other than $j$ are represented through a section $s_i$ of $f_i$ ($f_i(s_i(m))=m$); under the first assumption the value does not depend on the section chosen.
-- source:
--   Kelly, Reversibility and Stochastic Networks, Wiley 1979, pp. 203–204, assumptions before (9.29), Eqs. (9.29), (9.31)

import Mathlib
import Definitions.Def_KellyReversibility_PartialBalance_Core
import Definitions.Def_KellyReversibility_PartialBalance_Spatial

namespace KellyReversibility.PartialBalance

open Function

variable {ι : Type*} [DecidableEq ι] {X N : ι → Type*}

/-- The **reduced description** `n = f(x) = (f_1(x_1), …, f_J(x_J))` (§9.4, p. 204) of a state
`x` of a spatial process, where `f_j : 𝒳_j → N_j`. -/
def reduce (f : ∀ i, X i → N i) (x : ∀ i, X i) : ∀ i, N i := fun i => f i (x i)

/-- The **first assumption** of p. 204 on the truncated process `x_j`: the transition rates
`q(x, T_j^y x)` depend on `x_{G−j}` only through `n_{G−j} = f(x)_{G−j}`. -/
def RatesFactorThrough (q : (∀ i, X i) → (∀ i, X i) → ℝ) (f : ∀ i, X i → N i) (j : ι) :
    Prop :=
  ∀ (x x' : ∀ i, X i) (y : X j), x j = x' j → (∀ i, i ≠ j → f i (x i) = f i (x' i)) →
    q x (update x j y) = q x' (update x' j y)

/-- The **second assumption** (9.29) of p. 204 on the truncated process `x_j`: for every
`x_{G−j}`, the equilibrium distribution `π(x_j; x_{G−j})` of the process at site `j` with the
other sites frozen at `x_{G−j}` has the form `π(n_j; n_{G−j}) P_j(x_j | n_j)`, where
`π(n_j; n_{G−j}) = ∑_{x_j' : f_j(x_j') = n_j} π(x_j'; x_{G−j})`, `n_j = f_j(x_j)`, and
`P j x_j` stands for `P_j(x_j | f_j(x_j))`. -/
def SufficientReduction [∀ i, Fintype (X i)] [∀ i, DecidableEq (N i)]
    (q : (∀ i, X i) → (∀ i, X i) → ℝ) (f : ∀ i, X i → N i) (P : ∀ i, X i → ℝ) (j : ι) :
    Prop :=
  ∀ (x : ∀ i, X i) (p : X j → ℝ), IsTheEquilibriumDist (frozenRates q j x) p →
    ∀ y : X j, p y = (∑ y' ∈ Finset.univ.filter (fun y' => f j y' = f j y), p y') * P j y

/-- The **reduced rates (9.31)** (p. 204):
`q(n, T_j^m n) = ∑_{x_j : f_j(x_j) = n_j} P_j(x_j | n_j) ∑_{y : f_j(y) = m} q(x, T_j^y x)`,
where `x` is a state with `f(x) = n`, for `m ≠ n_j`. The self-rate is zero by the book's
convention `q(n,n) = 0` (§1.1, p. 3). The sites other than `j` are represented by
`x_i = s_i(n_i)` for a section `s_i` of `f_i` (`f_i (s_i m) = m`); under the first assumption
the value does not depend on that choice. -/
noncomputable def reducedRate [∀ i, Fintype (X i)] [∀ i, DecidableEq (N i)]
    (q : (∀ i, X i) → (∀ i, X i) → ℝ) (f : ∀ i, X i → N i) (P : ∀ i, X i → ℝ)
    (s : ∀ i, N i → X i) (n : ∀ i, N i) (j : ι) (m : N j) : ℝ :=
  if m = n j then 0 else
    ∑ xj ∈ Finset.univ.filter (fun xj => f j xj = n j),
      P j xj * ∑ y ∈ Finset.univ.filter (fun y => f j y = m),
        q (update (fun i => s i (n i)) j xj) (update (fun i => s i (n i)) j y)

end KellyReversibility.PartialBalance


