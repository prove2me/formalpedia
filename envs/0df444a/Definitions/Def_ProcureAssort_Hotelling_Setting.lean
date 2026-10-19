-- Prove2me | Definitions.Def_ProcureAssort_Hotelling_Setting
-- name    : ProcureAssort_Hotelling_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-18T17:29:59.039046+00:00
-- url     : https://prove2.me/theorems/a5b65b0f-97c0-437f-b586-abf7a34343c0
-- title:
--   §2–§4.2, App. B, F.1–F.2, pp. 7–24, 38, 40–42 — types, virtual costs (Def. 3.1), Cent, DecLin, OPT, Hotelling GCS, Q(p), demand, A(θ) (13), θ^u, reachability
-- statement:
--   This file fixes the model of Saban and Weintraub's procurement problem with $n$ suppliers of differentiated products and the general Hotelling demand model.
--
--   **Types and probabilities (§2, p. 7).** Supplier $i \in N = \{1,\dots,n\}$ has a private cost $\theta_i$ in a finite set $\Theta_i \subset \mathbb R$, distributed with pmf $f_i$; $F_i(c) = \sum_{b \in \Theta_i, b \le c} f_i(b)$. A profile is $\theta \in \Theta = \prod_i \Theta_i$, with $f(\theta) = \prod_i f_i(\theta_i)$ and $f_{-i}(\theta_{-i}) = \prod_{j \ne i} f_j(\theta_j)$. Expectations are finite sums $\mathbb E_\theta[g] = \sum_\theta f(\theta) g(\theta)$.
--
--   **Virtual costs (Definition 3.1, p. 13).** $\rho_i(c) = \max\{\theta' \in \Theta_i : \theta' < c\}$, and $\rho_i(c) = c$ when no such element exists;
--   $$v_i(c) = c + \frac{F_i(\rho_i(c))}{f_i(c)}\,(c - \rho_i(c)), \qquad v(\theta) = (v_1(\theta_1), \dots, v_n(\theta_n)).$$
--
--   **Interim quantities and utilities ((4), (5), pp. 12–13).** For a function $g$ of profiles, the interim expectation for supplier $i$ of type $c$ is $\sum_{\theta_{-i}} f_{-i}(\theta_{-i})\, g(c, \theta_{-i})$; with $g = x_i$ it is $X_i(c)$, with $g = t_i$ it is $T_i(c)$. The interim utility of type $\theta_i$ reporting $\theta_i'$ is $U_i(\theta_i' \mid \theta_i) = \sum_{\theta_{-i}} f_{-i}(\theta_{-i}) \big(t_i(\theta_i', \theta_{-i}) - \theta_i x_i(\theta_i', \theta_{-i})\big)$.
--
--   **Cent (p. 13).** A pair of allocation and transfer functions $(x, t)$ is feasible if it satisfies (IC) $U_i(\theta_i\mid\theta_i) \ge U_i(\theta_i'\mid\theta_i)$, (IR) $U_i(\theta_i \mid \theta_i) \ge 0$ and (Feas) $x(\theta) \in \mathcal X$; its objective is $\mathbb E_\theta[GCS(x(\theta)) - \sum_i t_i(\theta)]$, and $OPT(Cent)$ is the supremum of the objective over feasible pairs.
--
--   **Consumer surplus and demand ((1)–(2), p. 9).** $CS(x, p) = GCS(x) - \sum_i p_i x_i$. A vector $y$ is a demand for assortment $Q$ and prices $p$ if $y \in \mathcal X$, $y_i = 0$ for $i \notin Q$, and $y$ maximizes $CS(\cdot, p)$ over such vectors.
--
--   **DecLin (pp. 18–21).** A triple (assortment $q(\theta)$, unit prices $p(\theta)$, allocation $x(\theta)$) is feasible if $(x, t)$ with $t_i = p_i x_i$ satisfies (IC), (IR), (Feas), and $x(\theta)$ is a demand for $(q(\theta), p(\theta))$ (Demand). Its objective is $\mathbb E_\theta[CS(x(\theta), p(\theta))]$, and $OPT(DecLin)$ is the supremum over feasible triples.
--
--   **General Hotelling model (§3.2.1, pp. 15–16; App. F.1, p. 40).** Suppliers sit at locations $\ell_1 < \dots < \ell_n$ in $[0,1]$, consumers are uniform on $[0,1]$, the transportation cost is $\delta$. Then
--   $$GCS(x) = -\delta \sum_{i} \int_{x_1 + \dots + x_{i-1}}^{x_1 + \dots + x_i} |u - \ell_i|\, du,$$
--   minus $\delta$ times the transportation cost when consecutive blocks of consumers are served in location order (for $n = 2$, $\ell = (0, 1)$ on the simplex this is Example 2.1's $-\frac{\delta}{2}(x_1^2 + x_2^2)$). The active set at prices $p$ is $Q(p) = \{i : p_i \le \min_{k \ne i}(p_k + \delta|\ell_k - \ell_i|)\}$, and the Hotelling demand gives $0$ to inactive suppliers and to an active supplier $i$ the amount $\ell_i$ (if leftmost active) or $\frac{p_L - p_i + \delta|\ell_i - \ell_L|}{2\delta}$ (with $L$ its left active neighbour), plus $1 - \ell_i$ (if rightmost active) or $\frac{p_R - p_i + \delta|\ell_R - \ell_i|}{2\delta}$ (with $R$ its right active neighbour). $Q(\theta) = Q(v(\theta))$ and $x^\star(\theta)$ is the Hotelling demand at prices $v(\theta)$; $t^\star$ are the transfers of Appendix B (p. 38).
--
--   **Proof objects (App. F, pp. 41–42).** $A(\theta)$ is the matrix (13) on the active set in location order: $1$ between consecutive active suppliers, minus the number of active neighbours on the diagonal, $0$ elsewhere. $c^* = \min_{1 \le i \le n-1}(\ell_{i+1} - \ell_i)$. $\theta^u_i$ is the largest $c \in \Theta_i$ such that some profile with $\theta_i = c$ has $i \in Q(\theta)$. A profile $\theta$ is reachable from $\theta'$ if there is a sequence $\theta' = \theta_0, \dots, \theta_K = \theta$ with $Q(\theta_k) \subseteq Q(\theta_{k-1})$ and the subprofiles on $Q(\theta_k)$ of $\theta_{k-1}$ and $\theta_k$ differing in at most one component.
--
--   **Formalization Note** Suppliers are `Fin n`, 0-indexed; a profile is a dependent function `(i : Fin n) → Θ i`. $OPT$ is a real `sSup` (which is $0$ on an empty or unbounded set; in the Hotelling instance both value sets are nonempty and bounded above by $0$). The paper writes $GCS$ explicitly only for $n = 2$; for general $n$ the order-preserving assignment is the cost-minimizing one, so the formula above is the paper's total transportation cost. (Demand) $x(\theta) = d(q(\theta), p(\theta))$ is read as consumer optimality, the defining property (2) of $d$. $\theta^u_i$ is the `sSup` of a finite set of reals ($0$ if that set is empty, which Theorem 4.1's Condition 1 excludes).
-- source:
--   Saban & Weintraub, Procurement Mechanisms for Assortments of Differentiated Products, SSRN 3453144 (author version of 2020-03-03; Oper. Res. doi:10.1287/opre.2020.2053), §2 pp. 7–9 (types, (1), (2)), §3.1 pp. 12–13 ((4), Cent, Definition 3.1, (5)), §3.2.1 pp. 15–16 (Q(p), Hotelling split), §4 p. 18 and §4.2 pp. 20–21 (DecLin), Appendix B p. 38 (t⋆), Appendix F.1–F.2 pp. 40–42 ((13), c*, θ^u, Lemma F.2 (2))

import Mathlib

namespace ProcureAssort.Hotelling

/-! Saban & Weintraub, *Procurement Mechanisms for Assortments of Differentiated Products*
(SSRN 3453144). Suppliers are `Fin n` (0-indexed: Lean's supplier `i` is the paper's supplier
`i + 1`), ordered by location. The type set of supplier `i` is a finite set `Θ i` of reals; its
pmf is `f i`. -/

/-- A type profile `θ ∈ Θ = Π_i Θ_i` (§2, p. 7). -/
abbrev Profile {n : ℕ} (Θ : Fin n → Finset ℝ) := (i : Fin n) → ↥(Θ i)

/-- `f(θ) = Π_i f_i(θ_i)` (§2, p. 7). -/
noncomputable def prob {n : ℕ} {Θ : Fin n → Finset ℝ} (f : Fin n → ℝ → ℝ) (θ : Profile Θ) : ℝ :=
  ∏ i, f i (θ i)

/-- `f_{-i}(θ_{-i}) = Π_{j ≠ i} f_j(θ_j)` (§2, p. 7). -/
noncomputable def probOthers {n : ℕ} {Θ : Fin n → Finset ℝ} (f : Fin n → ℝ → ℝ) (i : Fin n)
    (θ : Profile Θ) : ℝ :=
  ∏ j ∈ Finset.univ.erase i, f j (θ j)

/-- The expectation `E_θ[g(θ)] = Σ_θ f(θ) g(θ)`. -/
noncomputable def expect {n : ℕ} {Θ : Fin n → Finset ℝ} (f : Fin n → ℝ → ℝ)
    (g : Profile Θ → ℝ) : ℝ :=
  ∑ θ : Profile Θ, prob f θ * g θ

/-- The interim expectation `Σ_{θ_{-i}} f_{-i}(θ_{-i}) g(c, θ_{-i})` for supplier `i` of type `c`,
as in (4) and (5), p. 13. With `g θ = x θ i` it is `X_i(c)`, with `g θ = t θ i` it is `T_i(c)`. -/
noncomputable def interim {n : ℕ} {Θ : Fin n → Finset ℝ} (f : Fin n → ℝ → ℝ)
    (g : Profile Θ → ℝ) (i : Fin n) (c : ℝ) : ℝ :=
  ∑ θ : Profile Θ, if ((θ i : ℝ) = c) then probOthers f i θ * g θ else 0

/-- The interim utility `U_i(θ'_i | θ_i)` of (4), p. 12, of supplier `i` with true cost `cost`
reporting `report`, under allocation `x` and transfers `t` (`t_i = p_i x_i`). -/
noncomputable def utility {n : ℕ} {Θ : Fin n → Finset ℝ} (f : Fin n → ℝ → ℝ)
    (x t : Profile Θ → Fin n → ℝ) (i : Fin n) (report cost : ℝ) : ℝ :=
  interim f (fun θ => t θ i - cost * x θ i) i report

/-- The constraints (IC), (IR), (Feas) of the centralized problem Cent, p. 13. -/
def IsCentFeasible {n : ℕ} {Θ : Fin n → Finset ℝ} (f : Fin n → ℝ → ℝ)
    (X : Set (Fin n → ℝ)) (x t : Profile Θ → Fin n → ℝ) : Prop :=
  (∀ i, ∀ a ∈ Θ i, ∀ b ∈ Θ i, utility f x t i b a ≤ utility f x t i a a) ∧
  (∀ i, ∀ a ∈ Θ i, 0 ≤ utility f x t i a a) ∧
  (∀ θ, x θ ∈ X)

/-- The objective of Cent, `E_θ[GCS(x(θ)) − Σ_i t_i(θ)]`, p. 13. -/
noncomputable def centObj {n : ℕ} {Θ : Fin n → Finset ℝ} (f : Fin n → ℝ → ℝ)
    (GCS : (Fin n → ℝ) → ℝ) (x t : Profile Θ → Fin n → ℝ) : ℝ :=
  expect f (fun θ => GCS (x θ) - ∑ i, t θ i)

/-- `OPT(Cent)`: the supremum of the objective of Cent over its feasible set. -/
noncomputable def optCent {n : ℕ} (Θ : Fin n → Finset ℝ) (f : Fin n → ℝ → ℝ)
    (GCS : (Fin n → ℝ) → ℝ) (X : Set (Fin n → ℝ)) : ℝ :=
  sSup {r | ∃ x t : Profile Θ → Fin n → ℝ, IsCentFeasible f X x t ∧ r = centObj f GCS x t}

/-- Consumer surplus `CS(x, p) = GCS(x) − Σ_i p_i x_i`, (1), p. 9. -/
def CS {n : ℕ} (GCS : (Fin n → ℝ) → ℝ) (y p : Fin n → ℝ) : ℝ :=
  GCS y - ∑ i, p i * y i

/-- `y` is a consumer-optimal consumption vector for assortment `Q` and prices `p`:
`y ∈ argmax {CS(z, p) : z ∈ X, z_i = 0 ∀ i ∉ Q}`, (2), p. 9. -/
def IsDemand {n : ℕ} (GCS : (Fin n → ℝ) → ℝ) (X : Set (Fin n → ℝ)) (Q : Finset (Fin n))
    (p y : Fin n → ℝ) : Prop :=
  y ∈ X ∧ (∀ i ∉ Q, y i = 0) ∧
    ∀ z ∈ X, (∀ i ∉ Q, z i = 0) → CS GCS z p ≤ CS GCS y p

/-- The constraints of DecLin, p. 21: (IC), (IR) with transfers `p_i x_i`, (Feas), and (Demand)
read as consumer optimality of `x(θ)` for the assortment `q(θ)` and prices `p(θ)`. -/
def IsDecLinFeasible {n : ℕ} {Θ : Fin n → Finset ℝ} (f : Fin n → ℝ → ℝ)
    (GCS : (Fin n → ℝ) → ℝ) (X : Set (Fin n → ℝ)) (q : Profile Θ → Finset (Fin n))
    (p x : Profile Θ → Fin n → ℝ) : Prop :=
  IsCentFeasible f X x (fun θ i => p θ i * x θ i) ∧ ∀ θ, IsDemand GCS X (q θ) (p θ) (x θ)

/-- The objective of DecLin, `E_θ[CS(x(θ), p(θ))]`, p. 21. -/
noncomputable def decLinObj {n : ℕ} {Θ : Fin n → Finset ℝ} (f : Fin n → ℝ → ℝ)
    (GCS : (Fin n → ℝ) → ℝ) (p x : Profile Θ → Fin n → ℝ) : ℝ :=
  expect f (fun θ => CS GCS (x θ) (p θ))

/-- `OPT(DecLin)`: the supremum of the objective of DecLin over its feasible set. -/
noncomputable def optDecLin {n : ℕ} (Θ : Fin n → Finset ℝ) (f : Fin n → ℝ → ℝ)
    (GCS : (Fin n → ℝ) → ℝ) (X : Set (Fin n → ℝ)) : ℝ :=
  sSup {r | ∃ (q : Profile Θ → Finset (Fin n)) (p x : Profile Θ → Fin n → ℝ),
    IsDecLinFeasible f GCS X q p x ∧ r = decLinObj f GCS p x}

/-- The consumption set with no outside option, `X = {x : x ≥ 0, 1'x = 1}`, p. 9. -/
def simplex (n : ℕ) : Set (Fin n → ℝ) :=
  {x | (∀ i, 0 ≤ x i) ∧ ∑ i, x i = 1}

/-- The predecessor `ρ_i(c) = max {θ' ∈ Θ_i : θ' < c}`, and `ρ_i(c) = c` if there is none
(Definition 3.1, p. 13). -/
noncomputable def pred {n : ℕ} (Θ : Fin n → Finset ℝ) (i : Fin n) (c : ℝ) : ℝ :=
  if h : ((Θ i).filter (· < c)).Nonempty then ((Θ i).filter (· < c)).max' h else c

/-- The cdf `F_i(c) = Σ_{b ∈ Θ_i, b ≤ c} f_i(b)` (§2, p. 7). -/
noncomputable def cdfF {n : ℕ} (Θ : Fin n → Finset ℝ) (f : Fin n → ℝ → ℝ) (i : Fin n)
    (c : ℝ) : ℝ :=
  ∑ b ∈ (Θ i).filter (· ≤ c), f i b

/-- The virtual cost `v_i(c) = c + F_i(ρ_i(c)) / f_i(c) · (c − ρ_i(c))` (Definition 3.1, p. 13). -/
noncomputable def virtualCost {n : ℕ} (Θ : Fin n → Finset ℝ) (f : Fin n → ℝ → ℝ) (i : Fin n)
    (c : ℝ) : ℝ :=
  c + cdfF Θ f i (pred Θ i c) / f i c * (c - pred Θ i c)

/-- The vector of virtual costs `v(θ) = (v_1(θ_1), …, v_n(θ_n))`. -/
noncomputable def vvec {n : ℕ} (Θ : Fin n → Finset ℝ) (f : Fin n → ℝ → ℝ) (θ : Profile Θ) :
    Fin n → ℝ :=
  fun i => virtualCost Θ f i (θ i)

/-- Gross consumer surplus of the general Hotelling model (§3.2.1, pp. 15–16; Example 2.1, p. 10):
minus `δ` times the total transportation cost when the consumers, uniform on `[0,1]`, are assigned
to the suppliers in location order, supplier `i` serving the block of length `x_i` after the blocks
of suppliers `k < i`. -/
noncomputable def hotGCS {n : ℕ} (ℓ : Fin n → ℝ) (δ : ℝ) (x : Fin n → ℝ) : ℝ :=
  -(δ * ∑ i : Fin n, ∫ u in (∑ k ∈ Finset.univ.filter (· < i), x k)..(∑ k ∈ Finset.univ.filter (· ≤ i), x k),
      |u - ℓ i|)

/-- The set of suppliers with positive demand at prices `p`,
`Q(p) = {i : p_i ≤ min_{k ≠ i} (p_k + δ|ℓ_k − ℓ_i|)}` (p. 15). -/
noncomputable def hotQ {n : ℕ} (ℓ : Fin n → ℝ) (δ : ℝ) (p : Fin n → ℝ) : Finset (Fin n) :=
  Finset.univ.filter (fun i => ∀ j, p i - p j ≤ δ * |ℓ j - ℓ i|)

/-- The Hotelling demand at prices `p` (pp. 15–16, Appendix F.1 p. 40): `0` off `Q(p)`; an active
supplier gets `ℓ_i` (if leftmost active) or `(p_L − p_i + δ|ℓ_i − ℓ_L|)/(2δ)` from its left active
neighbour `L`, plus `1 − ℓ_i` (if rightmost active) or `(p_R − p_i + δ|ℓ_R − ℓ_i|)/(2δ)` from its
right active neighbour `R`. -/
noncomputable def hotDemand {n : ℕ} (ℓ : Fin n → ℝ) (δ : ℝ) (p : Fin n → ℝ) (i : Fin n) : ℝ :=
  if i ∈ hotQ ℓ δ p then
    (if h : ((hotQ ℓ δ p).filter (· < i)).Nonempty then
        (p (((hotQ ℓ δ p).filter (· < i)).max' h) - p i
          + δ * |ℓ i - ℓ (((hotQ ℓ δ p).filter (· < i)).max' h)|) / (2 * δ)
      else ℓ i) +
    (if h : ((hotQ ℓ δ p).filter (i < ·)).Nonempty then
        (p (((hotQ ℓ δ p).filter (i < ·)).min' h) - p i
          + δ * |ℓ (((hotQ ℓ δ p).filter (i < ·)).min' h) - ℓ i|) / (2 * δ)
      else 1 - ℓ i)
  else 0

/-- The centralized-optimal assortment `Q(θ) = Q(v(θ))` (p. 16, p. 40). -/
noncomputable def activeSet {n : ℕ} (Θ : Fin n → Finset ℝ) (f : Fin n → ℝ → ℝ)
    (ℓ : Fin n → ℝ) (δ : ℝ) (θ : Profile Θ) : Finset (Fin n) :=
  hotQ ℓ δ (vvec Θ f θ)

/-- The centralized allocation `x⋆(θ)`: the Hotelling demand at virtual-cost prices (p. 40). -/
noncomputable def xstar {n : ℕ} (Θ : Fin n → Finset ℝ) (f : Fin n → ℝ → ℝ) (ℓ : Fin n → ℝ)
    (δ : ℝ) (θ : Profile Θ) : Fin n → ℝ :=
  hotDemand ℓ δ (vvec Θ f θ)

/-- The transfers `t⋆_i(θ^j_i, θ_{-i}) = θ^j_i x_i(θ^j_i, θ_{-i}) + Σ_{k>j} (θ^k_i − θ^{k−1}_i)
x_i(θ^k_i, θ_{-i})` of Appendix B, p. 38, for an allocation `x`. -/
noncomputable def tstar {n : ℕ} (Θ : Fin n → Finset ℝ) (x : Profile Θ → Fin n → ℝ)
    (θ : Profile Θ) (i : Fin n) : ℝ :=
  (θ i : ℝ) * x θ i +
    ∑ b : ↥(Θ i), if (θ i : ℝ) < (b : ℝ) then ((b : ℝ) - pred Θ i b) * x (Function.update θ i b) i
      else 0

/-- `i` and `j` are distinct elements of `Q` with no element of `Q` strictly between them. -/
def Adjacent {n : ℕ} (Q : Finset (Fin n)) (i j : Fin n) : Prop :=
  i ∈ Q ∧ j ∈ Q ∧ i ≠ j ∧ ∀ k ∈ Q, ¬ (min i j < k ∧ k < max i j)

instance {n : ℕ} (Q : Finset (Fin n)) (i j : Fin n) : Decidable (Adjacent Q i j) := by
  unfold Adjacent; infer_instance

/-- The matrix `A(θ)` of (13), p. 41, indexed by the active set `Q = Q(θ)` in location order:
entry `1` between consecutive active suppliers, minus the number of active neighbours on the
diagonal, `0` elsewhere and outside `Q` (rows `−1 1 / 1 −2 1 / … / 1 −1`). -/
noncomputable def pathA {n : ℕ} (Q : Finset (Fin n)) (i j : Fin n) : ℝ :=
  if i ∈ Q ∧ j ∈ Q then
    (if i = j then -(((Q.filter (fun k => Adjacent Q i k)).card : ℕ) : ℝ)
      else if Adjacent Q i j then 1 else 0)
  else 0

/-- `c* = min_{1 ≤ i ≤ n−1} (ℓ_{i+1} − ℓ_i)` (Theorem 4.1, p. 24). -/
noncomputable def cstar {n : ℕ} (ℓ : Fin n → ℝ) (hn : 2 ≤ n) : ℝ :=
  (Finset.univ : Finset (Fin (n - 1))).inf' ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
    (fun i => ℓ ⟨i.val + 1, by have := i.isLt; omega⟩ - ℓ ⟨i.val, by have := i.isLt; omega⟩)

/-- `θ^u_i`: the largest `c ∈ Θ_i` for which some profile `θ` with `θ_i = c` has `i ∈ Q(θ)`
(Appendix F.2, p. 42). -/
noncomputable def thetaU {n : ℕ} (Θ : Fin n → Finset ℝ) (f : Fin n → ℝ → ℝ) (ℓ : Fin n → ℝ)
    (δ : ℝ) (i : Fin n) : ℝ :=
  sSup {c | c ∈ Θ i ∧ ∃ θ : Profile Θ, (θ i : ℝ) = c ∧ i ∈ activeSet Θ f ℓ δ θ}

/-- `θ` is reachable from `θ'` (Lemma F.2 (2), p. 42): there is a sequence
`θ' = θ_0, θ_1, …, θ_K = θ` with `Q(θ_k) ⊆ Q(θ_{k−1})` and the subprofiles of `θ_{k−1}` and `θ_k`
on `Q(θ_k)` differing in at most one component. -/
def Reachable {n : ℕ} (Θ : Fin n → Finset ℝ) (f : Fin n → ℝ → ℝ) (ℓ : Fin n → ℝ) (δ : ℝ)
    (θ' θ : Profile Θ) : Prop :=
  ∃ (K : ℕ) (s : ℕ → Profile Θ), s 0 = θ' ∧ s K = θ ∧
    ∀ k, 1 ≤ k → k ≤ K →
      activeSet Θ f ℓ δ (s k) ⊆ activeSet Θ f ℓ δ (s (k - 1)) ∧
      ∀ j₁ ∈ activeSet Θ f ℓ δ (s k), ∀ j₂ ∈ activeSet Θ f ℓ δ (s k),
        s k j₁ ≠ s (k - 1) j₁ → s k j₂ ≠ s (k - 1) j₂ → j₁ = j₂

end ProcureAssort.Hotelling


