-- Prove2me | Definitions.Def_HTInsensBW_PhaseType_Model
-- name    : HTInsensBW_PhaseType_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-18T20:13:52.226001+00:00
-- url     : https://prove2.me/theorems/28dfbede-a2c6-4f19-80d9-750b0a4535bf
-- title:
--   §2, §6, pp. 5–7, 22–23 — class-D phase-type laws, network, weighted proportionally fair allocation (2)–(4), CTMC rates (60), stationarity, critical links Ls
-- statement:
--   The connection-level model of a bandwidth-sharing network with phase-type file sizes, from Wang, Maguluri, Srikant and Ying, §2 (pp. 5–7) and §6 (pp. 22–23).
--
--   1. **Class $\mathcal D$ of phase-type laws (p. 22, (54)–(57)).** A law in $\mathcal D$ is the absorption time of a Markov chain whose transient phases are split into blocks $b=1,\dots,B$; block $b$ is an Erlang chain of length $\ell_b\ge1$ with rate $\mu^{(b)}>0$, the rates of different blocks are distinct, and the initial law $\pi$ (on the transient phases, with no mass on the absorbing state) is nonnegative, sums to $1$, and is strictly positive on the first phase of every block. The subgenerator $S$ is block diagonal, each block upper bidiagonal with $-\mu^{(b)}$ on the diagonal and $\mu^{(b)}$ on the superdiagonal. The completion rate from phase $k$ is $\sum_{k'}(-S)_{k,k'}$, the mean size is
--   $$\frac1{\mu}=\pi(-S)^{-1}\mathbf 1,$$
--   and the phase-load vector at arrival rate $\lambda$ is $\boldsymbol\rho=\lambda(-S)^{-T}\pi^T$ (62).
--   2. **Network (p. 5).** Links $\ell\in\{1,\dots,L\}$ with capacities $C_\ell$, routes $r\in\{1,\dots,R\}$, a routing matrix $H=(h_{\ell r})$ ($h_{\ell r}=1$ iff $\ell\in r$), weights $\kappa_r$, a base arrival-rate vector $\boldsymbol\lambda^{(0)}$, and a law $(\pi_r,S_r)\in\mathcal D$ for every route. The route load is $\rho^{(0)}_r=\lambda^{(0)}_r/\mu_r$.
--   3. **Heavy traffic (pp. 6–7).** $\mathcal L_s=\{\ell:\sum_{r:\ell\in r}\rho^{(0)}_r=C_\ell\}$ is the set of critically loaded links, $\delta_\ell=C_\ell-\sum_{r:\ell\in r}\rho^{(0)}_r$ the capacity surplus, and $\kappa_{\min}=\min_r\kappa_r$, $\kappa_{\max}=\max_r\kappa_r$.
--   4. **Weighted proportionally fair allocation ((2)–(4), pp. 5–6).** Given route counts $n_r$, the per-flow rates $x$ solve
--   $$\max_x\ \sum_r\kappa_r n_r\log x_r\quad\text{s.t.}\quad\sum_{r:\ell\in r}n_rx_r\le C_\ell\ \ \forall\ell,\qquad x\ge0,\qquad x_r=0\text{ when }n_r=0 .$$
--   Lagrange multipliers (5) are $p_\ell\ge0$ with complementary slackness and $x_r=\kappa_r/\sum_{\ell:\ell\in r}p_\ell$ on active routes. The unused bandwidth of link $\ell$ is $U_\ell=C_\ell-\sum_{r:\ell\in r}n_rx_r$.
--   5. **The flow-count process ((58)–(60), p. 23).** The state $\mathbf n=(n_{r,k})$ counts flows on route $r$ in phase $k$; $n_r=\sum_kn_{r,k}$. In the $\epsilon$-th system the arrival rates are $\boldsymbol\lambda^{(\epsilon)}=(1-\epsilon)\boldsymbol\lambda^{(0)}$ and the transition rates are
--   $$q_{\mathbf n\mathbf n'}=\begin{cases}\lambda^{(\epsilon)}_r\pi_{r,k}&\mathbf n'=\mathbf n+\mathbf e^{(r,k)},\\ n_{r,k_1}x_r(S_r)_{k_1,k_2}&\mathbf n'=\mathbf n-\mathbf e^{(r,k_1)}+\mathbf e^{(r,k_2)},\ k_1\neq k_2,\\ n_{r,k}x_r\sum_{k'}(-S_r)_{k,k'}&\mathbf n'=\mathbf n-\mathbf e^{(r,k)},\ n_{r,k}>0,\\ 0&\text{otherwise},\end{cases}$$
--   with $x$ the allocation at the route counts $(n_r)$.
--   6. **Drift and stationarity.** The drift of $V$ is $\Delta V(\mathbf n)=\sum_{\mathbf n'\neq\mathbf n}q_{\mathbf n\mathbf n'}(V(\mathbf n')-V(\mathbf n))$ (14). A stationary distribution is a nonnegative $\pi$ of total mass $1$ satisfying the global balance equations $\pi_{\mathbf n}\sum_{\mathbf n'}q_{\mathbf n\mathbf n'}=\sum_{\mathbf n'}\pi_{\mathbf n'}q_{\mathbf n'\mathbf n}$. The weighted flow count is $\sum_r\kappa_rn_r$.
--
--   These objects are shared by every statement of the mission; the goal (Theorem 4) needs nothing else.
--
--   **Formalization Note** Phases of route $r$ are pairs (block, position), both 0-based. The allocation problem is a predicate `IsWPFAllocation` on route totals; theorems take an allocation function $x$ with the hypothesis that $x(m)$ satisfies it for every $m$. Competitors in the optimality clause are positive on active routes (a zero rate there has objective $-\infty$). Diagonal rates are $0$, the convention of the reused `KellyStochasticNetworks.FullBalance`, so the drift may sum over all $\mathbf n'$. The matrix inverse in $1/\mu$ and $\boldsymbol\rho$ is the genuine inverse because $-S$ is upper triangular with positive diagonal. $\kappa_{\min},\kappa_{\max}$ are $\inf/\sup$ over the finite route set (nonempty under the theorems' hypotheses). The standing assumptions (0/1 routing matrix, full row rank, positivity, heavy traffic) are hypotheses of the theorems, not part of these definitions.
-- source:
--   Wang, Maguluri, Srikant, Ying, Heavy-traffic insensitive bounds for weighted proportionally fair bandwidth sharing policies, arXiv:1808.02120v2, pp. 5–7, 9, 22–23, §2 ((2)–(5), (7)–(8)), (14), §6 ((54)–(60), (62))

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Balance

namespace HTInsensBW.PhaseType

open Matrix

/-- **The class `D` of phase-type file-size laws** (Wang, Maguluri, Srikant, Ying, Heavy-traffic
insensitive bounds for weighted proportionally fair bandwidth sharing policies, arXiv:1808.02120v2,
p. 22, (54)–(56)). The transient phases form `B` blocks; block `b` is an Erlang chain of length
`len b` with rate `rate b` (the page's `µ^(b)_r`, pairwise distinct). The initial law `init`
(the page's row vector `π_r`, with `π_0 = 0` on the absorbing state) is nonnegative, sums to `1`,
and is strictly positive on the first phase of every block.

**Formalization Note** Phase `(b, i)` is the `i`-th phase (0-based) of block `b` (0-based). -/
structure PhaseTypeD where
  /-- number of blocks `B_r` -/
  B : ℕ
  /-- block sizes -/
  len : Fin B → ℕ
  len_pos : ∀ b, 0 < len b
  /-- the block rates `µ^(b)_r` -/
  rate : Fin B → ℝ
  rate_pos : ∀ b, 0 < rate b
  /-- "with distinct `µ^(b)_r`'s for different `b`'s" -/
  rate_inj : Function.Injective rate
  /-- the initial distribution `π_r` over the transient phases -/
  init : (Σ b : Fin B, Fin (len b)) → ℝ
  init_nonneg : ∀ k, 0 ≤ init k
  init_first_pos : ∀ b, 0 < init ⟨b, ⟨0, len_pos b⟩⟩
  init_sum : ∑ k, init k = 1

/-- The transient phases of a class-`D` law: pairs (block, position in the block). -/
abbrev Phase (D : PhaseTypeD) : Type := Σ b : Fin D.B, Fin (D.len b)

/-- The subgenerator `S_r` of (55)–(56), p. 22: block diagonal, each block upper bidiagonal with
`-µ^(b)_r` on the diagonal and `µ^(b)_r` on the superdiagonal. -/
noncomputable def subgen (D : PhaseTypeD) : Matrix (Phase D) (Phase D) ℝ :=
  Matrix.of fun k k' =>
    if k.1 = k'.1 ∧ (k'.2 : ℕ) = k.2 then -D.rate k.1
    else if k.1 = k'.1 ∧ (k'.2 : ℕ) = k.2 + 1 then D.rate k.1
    else 0

/-- The absorption (completion) rate from phase `k`, `Σ_{k'} (-S_r)_{k,k'}` (the vector `s_r` of
(54) and the completion rate in (60), p. 23). It equals the block rate on the last phase of a block
and `0` elsewhere. -/
noncomputable def exitRate (D : PhaseTypeD) (k : Phase D) : ℝ :=
  ∑ k', -(subgen D k k')

/-- The mean file size `1/µ_r = π_r (-S_r)^{-1} 1` of (57), p. 22. (`-S_r` is upper triangular
with nonzero diagonal, hence invertible, so the matrix inverse is the genuine one.) -/
noncomputable def meanSize (D : PhaseTypeD) : ℝ :=
  D.init ⬝ᵥ ((-subgen D)⁻¹ *ᵥ fun _ => 1)

/-- The phase-load vector `ρ_r = λ_r (-S_r)^{-T} π_r^T` of (62), p. 23, for arrival rate `lam`. -/
noncomputable def phaseLoad (D : PhaseTypeD) (lam : ℝ) : Phase D → ℝ :=
  lam • (D.init ᵥ* (-subgen D)⁻¹)

/-- **A bandwidth-sharing network** (pp. 5–7, 22): `L` links and `R` routes, the routing matrix
`H` (`h_ℓr = 1` iff link `ℓ` is on route `r`), link capacities `C`, the weights `κ` of the weighted
proportionally fair policy, the base arrival-rate vector `λ^(0)` (`lam0`), and the class-`D`
file-size law `D r` of every route. The standing assumptions (0/1 entries, full row rank,
positivity, heavy traffic) are hypotheses of the theorems, not fields. -/
structure BWNetwork (L R : ℕ) where
  H : Matrix (Fin L) (Fin R) ℝ
  C : Fin L → ℝ
  κ : Fin R → ℝ
  lam0 : Fin R → ℝ
  D : Fin R → PhaseTypeD

variable {L R : ℕ}

/-- The (route, phase) coordinates `(r, k)` of the state, (58)–(59), p. 23. -/
abbrev Idx (N : BWNetwork L R) : Type := Σ r : Fin R, Phase (N.D r)

/-- A state of the flow-count process: the number `n_{r,k}` of flows on route `r` in phase `k`. -/
abbrev State (N : BWNetwork L R) : Type := Idx N → ℕ

/-- The number of flows on route `r`, `n_r = Σ_k n_{r,k}` (p. 23). -/
def routeCount (N : BWNetwork L R) (n : State N) (r : Fin R) : ℕ :=
  ∑ k : Phase (N.D r), n ⟨r, k⟩

/-- The load `ρ^(0)_r = λ^(0)_r / µ_r` of route `r` under `λ^(0)`, with the mean of (57). -/
noncomputable def routeLoad0 (N : BWNetwork L R) (r : Fin R) : ℝ :=
  N.lam0 r * meanSize (N.D r)

/-- The set `L_s` of critically loaded links, (7), p. 6: `Σ_{r : ℓ ∈ r} ρ^(0)_r = C_ℓ`. -/
noncomputable def critical (N : BWNetwork L R) : Finset (Fin L) :=
  Finset.univ.filter fun ℓ => ∑ r, N.H ℓ r * routeLoad0 N r = N.C ℓ

/-- The capacity surplus `δ_ℓ = C_ℓ - Σ_{r : ℓ ∈ r} ρ^(0)_r` of link `ℓ` (p. 7). -/
noncomputable def slack (N : BWNetwork L R) (ℓ : Fin L) : ℝ :=
  N.C ℓ - ∑ r, N.H ℓ r * routeLoad0 N r

/-- `κ_min = min_r κ_r` (a finite minimum over the routes). -/
noncomputable def kappaMin (N : BWNetwork L R) : ℝ := ⨅ r, N.κ r

/-- `κ_max = max_r κ_r` (a finite maximum over the routes). -/
noncomputable def kappaMax (N : BWNetwork L R) : ℝ := ⨆ r, N.κ r

/-- **Weighted proportionally fair allocation**, (2)–(4), p. 5–6. Given route counts `m`, the
per-flow rates `x` solve `max Σ_r κ_r m_r log x_r` subject to `Σ_{r : ℓ ∈ r} m_r x_r ≤ C_ℓ`,
`x ≥ 0`, and `x_r = 0` when `m_r = 0`.

**Formalization Note** The optimum is positive on every active route (a zero rate there has
objective `-∞`), so the competitors `y` are taken positive on active routes; inactive routes carry
weight `m_r = 0` in every sum, so their competitor values are irrelevant. -/
def IsWPFAllocation (N : BWNetwork L R) (m : Fin R → ℕ) (x : Fin R → ℝ) : Prop :=
  (∀ r, m r = 0 → x r = 0) ∧ (∀ r, 0 < m r → 0 < x r) ∧
  (∀ ℓ, ∑ r, N.H ℓ r * (m r : ℝ) * x r ≤ N.C ℓ) ∧
  ∀ y : Fin R → ℝ, (∀ r, 0 < m r → 0 < y r) → (∀ ℓ, ∑ r, N.H ℓ r * (m r : ℝ) * y r ≤ N.C ℓ) →
    ∑ r, N.κ r * (m r : ℝ) * Real.log (y r) ≤ ∑ r, N.κ r * (m r : ℝ) * Real.log (x r)

/-- **Lagrange (KKT) multipliers** of the allocation problem, (5), p. 6: `p_ℓ ≥ 0`, complementary
slackness with the capacity constraints, and `x_r = κ_r / Σ_{ℓ : ℓ ∈ r} p_ℓ` on active routes. -/
def IsKKTMultiplier (N : BWNetwork L R) (m : Fin R → ℕ) (x : Fin R → ℝ) (p : Fin L → ℝ) : Prop :=
  (∀ ℓ, 0 ≤ p ℓ) ∧ (∀ ℓ, p ℓ * (N.C ℓ - ∑ r, N.H ℓ r * (m r : ℝ) * x r) = 0) ∧
  ∀ r, 0 < m r → x r = N.κ r / ∑ ℓ, N.H ℓ r * p ℓ

/-- The unused bandwidth `U_ℓ = C_ℓ - Σ_{r : ℓ ∈ r} n_r x_r` on link `ℓ` in state `n` (p. 9),
with the allocation `x` evaluated at the route totals. -/
noncomputable def unused (N : BWNetwork L R) (x : (Fin R → ℕ) → Fin R → ℝ) (n : State N)
    (ℓ : Fin L) : ℝ :=
  N.C ℓ - ∑ r, N.H ℓ r * (routeCount N n r : ℝ) * x (routeCount N n) r

/-- `n + e^(r,k)`. -/
def addOne (N : BWNetwork L R) (n : State N) (i : Idx N) : State N :=
  Function.update n i (n i + 1)

/-- `n - e^(r,k)` (used only where `n_{r,k} > 0`). -/
def subOne (N : BWNetwork L R) (n : State N) (i : Idx N) : State N :=
  Function.update n i (n i - 1)

/-- **The transition rates (60)** of the flow-count process of the `ε`-th system, p. 23, with
arrival rates `λ^(ε) = (1 - ε) λ^(0)` (p. 6):
* `n → n + e^(r,k)` at rate `λ^(ε)_r π_{r,k}`;
* `n → n - e^(r,k₁) + e^(r,k₂)`, `k₁ ≠ k₂`, at rate `n_{r,k₁} x_r (S_r)_{k₁,k₂}`;
* `n → n - e^(r,k)`, `n_{r,k} > 0`, at rate `n_{r,k} x_r Σ_{k'} (-S_r)_{k,k'}`;
* `0` otherwise.

**Formalization Note** The allocation `x` is evaluated at the route totals `n_r` (the policy
"allocates rates according to the `N_r(t)`'s", p. 23). The diagonal rate `q_{nn}` is `0` (the
convention of `KellyStochasticNetworks.FullBalance`), not `-Σ_{n' ≠ n} q_{nn'}`. -/
noncomputable def rates (N : BWNetwork L R) (x : (Fin R → ℕ) → Fin R → ℝ) (ε : ℝ)
    (n n' : State N) : ℝ :=
  if n' = n then 0 else
    (∑ i : Idx N, if n' = addOne N n i then (1 - ε) * N.lam0 i.1 * (N.D i.1).init i.2 else 0)
    + (∑ r : Fin R, ∑ k₁ : Phase (N.D r), ∑ k₂ : Phase (N.D r),
        if k₁ ≠ k₂ ∧ 0 < n ⟨r, k₁⟩ ∧ n' = addOne N (subOne N n ⟨r, k₁⟩) ⟨r, k₂⟩
        then (n ⟨r, k₁⟩ : ℝ) * x (routeCount N n) r * subgen (N.D r) k₁ k₂ else 0)
    + (∑ i : Idx N, if 0 < n i ∧ n' = subOne N n i
        then (n i : ℝ) * x (routeCount N n) i.1 * exitRate (N.D i.1) i.2 else 0)

/-- The drift `ΔV(n) = Σ_{n' ≠ n} q_{nn'} (V(n') - V(n))` of a function `V` under rates `q`
((14), p. 9; Lemma 10, p. 37). With the diagonal convention `q_{nn} = 0` the sum may run over all
`n'`. -/
noncomputable def drift {S : Type*} (q : S → S → ℝ) (V : S → ℝ) (n : S) : ℝ :=
  ∑' n', q n n' * (V n' - V n)

/-- `π` is a **stationary probability distribution** for the rates `q` (with zero diagonal):
nonnegative, total mass `1`, and the global balance equations
`π_j Σ_k q_{jk} = Σ_k π_k q_{kj}`. -/
def IsStationary {S : Type*} (q : S → S → ℝ) (π : S → ℝ) : Prop :=
  (∀ n, 0 ≤ π n) ∧ HasSum π 1 ∧ KellyStochasticNetworks.FullBalance π q

/-- The weighted flow count `Σ_r κ_r n_r = Σ_{r,k} κ_r n_{r,k}`. -/
noncomputable def wsum (N : BWNetwork L R) (n : State N) : ℝ :=
  ∑ r, N.κ r * (routeCount N n r : ℝ)

end HTInsensBW.PhaseType


