-- Prove2me | Definitions.Def_MaxPressure_FluidStab_Network
-- name    : MaxPressure_FluidStab_Network
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T20:36:05.508986+00:00
-- url     : https://prove2.me/theorems/03c12ceb-3e0a-4637-9cf1-946af359a4ff
-- title:
--   §§2–5, pp. 199–203 — network data, R (5), allocations 𝒜 (1)–(2), extreme allocations ℰ, pressure (6), EAA, LP (9)–(13), Assumption 2, fluid model (14)–(18), (20), Definition 4
-- statement:
--   This file fixes the objects of §§2–5 of Dai and Lin, *Maximum pressure policies in stochastic processing networks*.
--
--   A **stochastic processing network** has buffers $0,1,\dots,I$ (Buffer $0$ is the outside world, $\mathcal I=\{1,\dots,I\}$ the internal buffers), activities $\mathcal J=\{1,\dots,J\}$ and processors $\mathcal K=\{1,\dots,K\}$. Its data are: the 0–1 **resource consumption matrix** $A=(A_{kj})$, with $A_{kj}=1$ iff activity $j$ needs processor $k$; the 0–1 **constituency indicators** $B_{ji}$, with $B_{ji}=1$ iff activity $j$ processes buffer $i$; the set of **input processors**; the mean processing requirements $m_j$; and the **routing matrices** $P^j$, nonnegative $(I+1)\times(I+1)$ matrices with $P^j_{00}=0$. Activity $j$ is an **input activity** if its constituency is $\{0\}$ and a **service activity** if it does not contain $0$.
--
--   The **standing assumptions** of §2 are collected in one predicate: $A$ and $B$ are 0–1; every constituency is nonempty; every activity is an input or a service activity; every activity needs a processor; a processor processes only input activities (input processor) or only service activities (service processor); there is at least one input activity; every input processor has at least one activity; $m_j>0$; $P^j\ge0$ and $P^j_{00}=0$.
--
--   With $\mu_j=1/m_j$, the **input-output matrix** (5) is
--   $$R_{ij}=\mu_j\Big(B_{ji}-\sum_{i'\in\mathcal I\cup\{0\}}B_{ji'}P^j_{i'i}\Big),\qquad i\in\mathcal I,\ j\in\mathcal J.$$
--   The **allocation set** $\mathcal A$ consists of the $a\in\mathbb R^J_+$ with (1) $\sum_jA_{kj}a_j\le1$ for every processor $k$ and (2) $\sum_jA_{kj}a_j=1$ for every input processor $k$; $\mathcal E$ is the set of its extreme points. The **network pressure** (6) of $a$ at $z\in\mathbb R^I$ is $p(a,z)=z\cdot Ra$. Buffer $i$ is a **constituent buffer** of $a$ if $\sum_ja_jB_{ji}>0$.
--
--   **Assumption 1 (EAA).** For every $z\in\mathbb R^I_+$ there is $a^*\in\mathcal E$ with $p(a^*,z)=\max_{a\in\mathcal E}p(a,z)$ and $z_i>0$ for every constituent buffer $i$ of $a^*$.
--
--   **The static planning LP** (9)–(13): $(x,\rho)$ is feasible if $Rx=0$, $\sum_jA_{kj}x_j\le\rho$ for every service processor $k$, $\sum_jA_{kj}x_j=1$ for every input processor $k$, and $x\ge0$.
--
--   **Assumption 2.** There is $x\ge0$ with $Rx>0$ (every component strictly positive).
--
--   **Fluid model.** A pair $(\bar Z,\bar T)$ of paths, $\bar Z(t)\in\mathbb R^I$, $\bar T(t)\in\mathbb R^J$, is a fluid model solution if for all $t\ge0$, $0\le s\le t$:
--   $$\bar Z_i(t)=\bar Z_i(0)+\sum_{i'\in\mathcal I\cup\{0\}}\sum_{j\in\mathcal J}\bar T_j(t)\mu_jB_{ji'}P^j_{i'i}-\sum_{j\in\mathcal J}\bar T_j(t)\mu_jB_{ji}\quad(14)$$
--   $\bar Z_i(t)\ge0$ (15); $\sum_jA_{kj}(\bar T_j(t)-\bar T_j(s))=t-s$ for input processors (16) and $\le t-s$ for all processors (17); $\bar T$ is nondecreasing with $\bar T(0)=0$ (18). A time $t>0$ is **regular** if $\bar Z$ and $\bar T$ are differentiable at $t$. The **maximum pressure fluid model equation** (20) says that at every regular $t$,
--   $$R\dot{\bar T}(t)\cdot\bar Z(t)=\max_{a\in\mathcal E}Ra\cdot\bar Z(t).$$
--
--   **Definition 4.** A fluid model is **stable** if there is $\delta>0$ such that every fluid model solution with $|\bar Z(0)|\le1$ has $\bar Z(t)=0$ for $t\ge\delta$.
--
--   These are the objects every statement of the mission is about.
--
--   **Formalization Note** Indices are 0-based: internal buffers are `Fin I`, buffers $0..I$ are `Fin (I+1)` with Buffer 0 the index `0` and internal buffer `i` the index `i.succ`; activities `Fin J`, processors `Fin K`. Two standing assumptions are added and disclosed: every input processor has an activity (without it (2) is infeasible), and $m_j>0$ (the page sets $\mu_j=1/m_j$; Lean's $1/0=0$ would silently zero a column of $R$). The row sums of $P^j$ are not imposed; the statements of this mission never use them. "$\max_{a\in\mathcal E}$" is encoded as attained domination (`IsGreatest` of the image, or an explicit maximizer), never as a supremum, so an empty $\mathcal E$ cannot be hidden by a junk value. Paths are functions on $\mathbb R$ evaluated only at $t\ge0$; monotonicity of $\bar T$ is on $[0,\infty)$. The norm $|\cdot|$ of Definition 4, which the page leaves unspecified, is the Euclidean norm (the one the proof of Theorem 5 uses); every norm on $\mathbb R^I$ gives an equivalent notion of stability.
-- source:
--   Dai & Lin, Maximum pressure policies in stochastic processing networks, Oper. Res. 53(2) (2005), pp. 199–203: §2.1–2.3, §2.5, (1)–(4), p. 199–200; (5), (6), p. 201; (9)–(13), Assumption 1, p. 202; (14)–(18), p. 202; regular points, (20), Assumption 2, Definition 4, p. 203

import Mathlib

namespace MaxPressure.FluidStab

open Matrix

/-!
Dai and Lin (2005), *Maximum pressure policies in stochastic processing networks*, §§2–5
(pp. 199–203): the network data, the input-output matrix (5), the allocation set 𝒜 of (1)–(2),
its extreme points ℰ, the network pressure (6), the EAA Assumption (Assumption 1), the static
planning LP (9)–(13), Assumption 2, the fluid model (14)–(18), regular points, the maximum
pressure fluid model equation (20) and fluid model stability (Definition 4).

Index conventions. Internal buffers `1, …, I` are `Fin I`; buffers `0, …, I` (with the outside,
Buffer 0) are `Fin (I + 1)`, Buffer 0 being `0` and internal buffer `i : Fin I` being `i.succ`.
Activities `1, …, J` are `Fin J` and processors `1, …, K` are `Fin K` (0-based: the paper's label
`n` is the index `n - 1`). Time is real; paths are only evaluated at `t ≥ 0`, and every condition
quantifies over `t ≥ 0` (or `0 ≤ s ≤ t`).
-/

/-- The data of a stochastic processing network (§2.1–§2.3, §2.5, pp. 199–200):
* `A k j = 1` iff activity `j` requires processor `k` (the resource consumption matrix);
* `B j i = 1` iff activity `j` processes buffer `i` (column `0` is Buffer 0);
* `inputProc k` says that processor `k` is an input processor (the others are service
  processors);
* `m j` is the mean processing requirement of activity `j`, (3);
* `P j` is the routing matrix `P^j` of activity `j`, (4), indexed by buffers `0, …, I`. -/
structure Network (I J K : ℕ) where
  A : Matrix (Fin K) (Fin J) ℝ
  B : Matrix (Fin J) (Fin (I + 1)) ℝ
  inputProc : Fin K → Prop
  m : Fin J → ℝ
  P : Fin J → Matrix (Fin (I + 1)) (Fin (I + 1)) ℝ

variable {I J K : ℕ}

/-- Activity `j` is an **input activity** (p. 199): its constituency is `ℬ_j = {0}`. -/
def IsInputActivity (N : Network I J K) (j : Fin J) : Prop :=
  N.B j 0 = 1 ∧ ∀ i : Fin I, N.B j i.succ = 0

/-- Activity `j` is a **service activity** (p. 199): `0 ∉ ℬ_j`. -/
def IsServiceActivity (N : Network I J K) (j : Fin J) : Prop :=
  N.B j 0 = 0

/-- The standing assumptions of §2 (pp. 199–200), plus two disclosed ones:
1. `A` and `B` are 0–1 matrices;
2. every constituency is nonempty (p. 199);
3. every activity is an input activity or a service activity (p. 199);
4. every activity needs at least one processor (p. 199);
5. a processor processes input activities only (input processor) or service activities only
   (service processor) (p. 199);
6. there is at least one input activity (p. 200);
7. (disclosed) every input processor has at least one activity — presupposed by "the input
   processors are never idle", (2); without it `𝒜 = ∅`;
8. (disclosed) `m_j > 0` — the page sets `μ_j = 1/m_j`;
9. the routing matrices are nonnegative with `P^j_{00} = 0` (from `Φ^j_{00}(ℓ) = 0` and (4)). -/
def Network.Standing (N : Network I J K) : Prop :=
  (∀ k j, N.A k j = 0 ∨ N.A k j = 1) ∧
  (∀ j i, N.B j i = 0 ∨ N.B j i = 1) ∧
  (∀ j, ∃ i, N.B j i = 1) ∧
  (∀ j, IsInputActivity N j ∨ IsServiceActivity N j) ∧
  (∀ j, ∃ k, N.A k j = 1) ∧
  (∀ k j, N.A k j = 1 → (N.inputProc k ↔ IsInputActivity N j)) ∧
  (∃ j, IsInputActivity N j) ∧
  (∀ k, N.inputProc k → ∃ j, N.A k j = 1) ∧
  (∀ j, 0 < N.m j) ∧
  (∀ j i i', 0 ≤ N.P j i i') ∧
  (∀ j, N.P j 0 0 = 0)

/-- The processing rate `μ_j = 1/m_j` (p. 200). -/
noncomputable def μ (N : Network I J K) (j : Fin J) : ℝ := 1 / N.m j

/-- The input-output matrix (5), p. 201:
`R_ij = μ_j (B_ji − ∑_{i' ∈ ℐ ∪ {0}} B_ji' P^j_{i'i})` for internal buffers `i` and activities `j`. -/
noncomputable def R (N : Network I J K) : Matrix (Fin I) (Fin J) ℝ :=
  fun i j => μ N j * (N.B j i.succ - ∑ i' : Fin (I + 1), N.B j i' * N.P j i' i.succ)

/-- The allocation set `𝒜` (p. 200): the allocations `a ∈ ℝ^J_+` satisfying (1)
`∑_j A_kj a_j ≤ 1` for each processor `k` and (2) `∑_j A_kj a_j = 1` for each input
processor `k`. -/
def allocSet (N : Network I J K) : Set (Fin J → ℝ) :=
  {a | (∀ j, 0 ≤ a j) ∧ (∀ k, ∑ j, N.A k j * a j ≤ 1) ∧
    (∀ k, N.inputProc k → ∑ j, N.A k j * a j = 1)}

/-- The set `ℰ` of extreme allocations: the extreme points of `𝒜` (p. 200). -/
def extremeAllocs (N : Network I J K) : Set (Fin J → ℝ) :=
  Set.extremePoints ℝ (allocSet N)

/-- The total network pressure (6), p. 201: `p(a, z) = z · Ra`. -/
noncomputable def pressure (N : Network I J K) (a : Fin J → ℝ) (z : Fin I → ℝ) : ℝ :=
  z ⬝ᵥ (R N *ᵥ a)

/-- The constituent buffers of an allocation `a` (p. 202): the internal buffers `i` with
`∑_j a_j B_ji > 0`. -/
def constituentBuffers (N : Network I J K) (a : Fin J → ℝ) : Set (Fin I) :=
  {i | 0 < ∑ j, a j * N.B j i.succ}

/-- **Assumption 1 (EAA Assumption)**, p. 202: for every buffer-level vector `z ∈ ℝ^I_+` there is
an extreme allocation `a* ∈ ℰ` maximizing the network pressure over `ℰ`,
`p(a*, z) = max_{a ∈ ℰ} p(a, z)`, such that `z_i > 0` for every constituent buffer `i` of `a*`. -/
def EAA (N : Network I J K) : Prop :=
  ∀ z : Fin I → ℝ, (∀ i, 0 ≤ z i) →
    ∃ a ∈ extremeAllocs N,
      (∀ a' ∈ extremeAllocs N, pressure N a' z ≤ pressure N a z) ∧
      ∀ i ∈ constituentBuffers N a, 0 < z i

/-- `(x, ρ)` is a feasible solution of the static planning LP (9)–(13), p. 202:
(10) `Rx = 0`; (11) `∑_j A_kj x_j ≤ ρ` for each service processor `k`;
(12) `∑_j A_kj x_j = 1` for each input processor `k`; (13) `x ≥ 0`. -/
def LPFeasible (N : Network I J K) (x : Fin J → ℝ) (ρ : ℝ) : Prop :=
  R N *ᵥ x = 0 ∧
  (∀ k, ¬ N.inputProc k → ∑ j, N.A k j * x j ≤ ρ) ∧
  (∀ k, N.inputProc k → ∑ j, N.A k j * x j = 1) ∧
  ∀ j, 0 ≤ x j

/-- **Assumption 2**, p. 203: there is an `x ≥ 0` with `Rx > 0` (componentwise, every internal
buffer). -/
def Assumption2 (N : Network I J K) : Prop :=
  ∃ x : Fin J → ℝ, (∀ j, 0 ≤ x j) ∧ ∀ i, 0 < (R N *ᵥ x) i

/-- `(Z̄, T̄)` is a **fluid model solution** (14)–(18), p. 202:
(14) `Z̄_i(t) = Z̄_i(0) + ∑_{i' ∈ ℐ∪{0}} ∑_j T̄_j(t) μ_j B_ji' P^j_{i'i} − ∑_j T̄_j(t) μ_j B_ji`
for `t ≥ 0`; (15) `Z̄_i(t) ≥ 0` for `t ≥ 0`; (16) `∑_j A_kj (T̄_j(t) − T̄_j(s)) = t − s` for
`0 ≤ s ≤ t` and each input processor `k`; (17) the same with `≤` for every processor `k`;
(18) `T̄` is nondecreasing (on `[0, ∞)`) and `T̄(0) = 0`. -/
def IsFluidSolution (N : Network I J K) (Zb : ℝ → Fin I → ℝ) (Tb : ℝ → Fin J → ℝ) : Prop :=
  (∀ t, 0 ≤ t → ∀ i : Fin I,
    Zb t i = Zb 0 i
      + ∑ i' : Fin (I + 1), ∑ j : Fin J, Tb t j * μ N j * N.B j i' * N.P j i' i.succ
      - ∑ j : Fin J, Tb t j * μ N j * N.B j i.succ) ∧
  (∀ t, 0 ≤ t → ∀ i, 0 ≤ Zb t i) ∧
  (∀ s t, 0 ≤ s → s ≤ t → ∀ k, N.inputProc k →
    ∑ j, N.A k j * (Tb t j - Tb s j) = t - s) ∧
  (∀ s t, 0 ≤ s → s ≤ t → ∀ k, ∑ j, N.A k j * (Tb t j - Tb s j) ≤ t - s) ∧
  MonotoneOn Tb (Set.Ici 0) ∧ Tb 0 = 0

/-- A time `t > 0` is a **regular point** of `(Z̄, T̄)` (p. 203) if the solution is
differentiable at `t`. -/
def IsRegular {n m : ℕ} (Zb : ℝ → Fin n → ℝ) (Tb : ℝ → Fin m → ℝ) (t : ℝ) : Prop :=
  0 < t ∧ DifferentiableAt ℝ Zb t ∧ DifferentiableAt ℝ Tb t

/-- The **maximum pressure fluid model equation** (20), p. 203: at each regular time `t`,
`R Ṫ(t) · Z̄(t) = max_{a ∈ ℰ} Ra · Z̄(t)`, i.e. `p(Ṫ(t), Z̄(t))` is the greatest element of
`{p(a, Z̄(t)) : a ∈ ℰ}` (attained, and dominating). -/
def MPFluidEq (N : Network I J K) (Zb : ℝ → Fin I → ℝ) (Tb : ℝ → Fin J → ℝ) : Prop :=
  ∀ t, IsRegular Zb Tb t →
    IsGreatest ((fun a => pressure N a (Zb t)) '' extremeAllocs N)
      (pressure N (deriv Tb t) (Zb t))

/-- A fluid model, given as the predicate `FM` on pairs `(Z̄, T̄)` that singles out its
solutions, is **stable** (Definition 4, p. 203) if there is a constant `δ > 0` such that every
fluid model solution with `|Z̄(0)| ≤ 1` has `Z̄(t) = 0` for `t ≥ δ`. The norm `|·|` is the
Euclidean norm. -/
def FluidStable {n m : ℕ} (FM : (ℝ → Fin n → ℝ) → (ℝ → Fin m → ℝ) → Prop) : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ ∀ Zb Tb, FM Zb Tb → Real.sqrt (∑ i, Zb 0 i ^ 2) ≤ 1 →
    ∀ t, δ ≤ t → Zb t = 0

end MaxPressure.FluidStab


