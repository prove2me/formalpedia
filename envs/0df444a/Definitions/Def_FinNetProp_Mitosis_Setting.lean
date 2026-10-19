-- Prove2me | Definitions.Def_FinNetProp_Mitosis_Setting
-- name    : FinNetProp_Mitosis_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-18T22:14:49.439802+00:00
-- url     : https://prove2.me/theorems/5c64b352-ecf3-4325-b385-f6ffae1e4db0
-- title:
--   §2–§4, Definitions 2.1–2.2, Axioms 3.1–3.5, 4.1, pp. 2801–2804 — financial networks, payment matrices, the system (2.1), bankruptcy rules and the six axioms
-- statement:
--   The model of Csóka and Herings for bankruptcy rules on financial networks.
--
--   1. **Financial networks.** Agents are natural numbers. A *financial network* $F = (N, z, L)$ consists of a nonempty finite set of agents $N \subseteq \mathbb N$, an endowment vector $z \in \mathbb R^N_{++}$ (every $z_i > 0$), and a nonnegative liability matrix $L \in \mathbb R^{N \times N}_+$ with $L_{ii} = 0$; $L_{ij}$ is the liability of agent $i$ toward agent $j$. The class of all financial networks is $\mathfrak F$.
--
--   2. **Relative liabilities.** For $i, j \in N$,
--   $$\Pi_{ij} = \begin{cases} 0, & L_{ij} = 0,\\ \dfrac{L_{ij}}{\sum_{k \in N} L_{ik}}, & \text{otherwise.}\end{cases}$$
--
--   3. **Payment matrices.** $\mathcal M(N)$ is the set of nonnegative $N \times N$ matrices with zero diagonal; $P_{ij}$ is the amount paid by $i$ to $j$. For $P \in \mathcal M(N)$ the *asset value* and *equity* of $i \in N$ are
--   $$a_i(N,z,P) = z_i + \sum_{j \in N} P_{ji}, \qquad e_i(N,z,P) = a_i(N,z,P) - \sum_{j \in N} P_{ij}.$$
--   Rows are compared by $P_i < P'_i$ iff $P_{ij} \le P'_{ij}$ for all $j \in N$ and $P_{ik} < P'_{ik}$ for some $k \in N$.
--
--   4. **Bankruptcy rules (Definition 2.1).** A bankruptcy rule $b$ assigns to every $F = (N,z,L) \in \mathfrak F$ a payment matrix $b(F) \in \mathcal M(N)$.
--
--   5. **The system (2.1) (Definition 2.2).** $P$ solves (2.1) for $F$ if $P \in \mathcal M(N)$ and
--   $$P_{ij} = \min\Big\{\Pi_{ij}\Big(z_i + \sum_{k \in N} P_{ki}\Big),\ L_{ij}\Big\}, \qquad i, j \in N.$$
--   The proportional rule $p$ assigns to $F$ the unique solution of (2.1).
--
--   6. **The axioms (§3, §4).** For a bankruptcy rule $b$:
--      - *Claims boundedness* (Axiom 3.1): $b(F) \le L$.
--      - *Limited liability* (Axiom 3.2): $e_i(N,z,b(F)) \ge 0$ for all $i \in N$.
--      - *Priority of creditors* (Axiom 3.3): if $b_i(F) < L_i$ then $e_i(N,z,b(F)) = 0$.
--      - *Continuity* (Axiom 3.4): $b(F^n) \to b(F)$ whenever $F^n \to F$, where $F^n = (N^n, z^n, L^n) \to F$ means that $N^n = N$ for all large $n$, $z^n \to z$ and $L^n \to L$.
--      - *Impartiality* (Axiom 3.5): $L_{ij} = L_{ik}$ implies $b_{ij}(F) = b_{ik}(F)$, for $i, j, k \in N$.
--      - *Invariance to mitosis* (Axiom 4.1): for $j \in N$ and a finite $K \subseteq \mathbb N \setminus N$, let $F' = (N', z', L')$ be the network in which $j$ is split into the $|K|+1$ identical agents $\{j\} \cup K$:
--   $$N' = N \cup K,\quad z'_k = \frac{z_j}{|K|+1},\quad L'_{ki} = \frac{L_{ji}}{|K|+1},\quad L'_{ik} = \frac{L_{ij}}{|K|+1},\quad L'_{k\ell} = 0,$$
--   for $k, \ell \in \{j\} \cup K$, $i \in N \setminus \{j\}$, with $z'_i = z_i$ and $L'_{hi} = L_{hi}$ for $h, i \in N \setminus \{j\}$. Then
--   $$\sum_{k \in \{j\} \cup K} b_{ki}(F') = b_{ji}(F),\qquad \sum_{k \in \{j\} \cup K} b_{ik}(F') = b_{ij}(F),\qquad b_{hi}(F') = b_{hi}(F)$$
--   for $h, i \in N \setminus \{j\}$.
--
--   7. **Auxiliary objects.** The split payment matrix $P'$ of (A.1) (p. 2808): $P'_{ki} = P_{ji}/(|K|+1)$, $P'_{ik} = P_{ij}/(|K|+1)$, $P'_{k\ell} = 0$ and $P'_{hi} = P_{hi}$, for $k, \ell \in \{j\} \cup K$ and $h, i \in N \setminus \{j\}$. A network has *rational liabilities* if every $L_{ij}$ is a rational number.
--
--   These definitions are shared by every statement of the mission.
--
--   **Formalization Note** Endowments, liabilities and payment matrices are functions on $\mathbb N$ (resp. $\mathbb N \times \mathbb N$) that vanish outside $N$ (resp. $N \times N$); this is part of the network structure and of membership in $\mathcal M(N)$, so a network is determined by its data on $N$ and a rule cannot read anything outside it. $\Pi$ is written with the case split of the page. Continuity is stated sequentially, exactly in the form of the convergence criterion of p. 2803 (the topology on $\mathfrak F$ — discrete on populations, Euclidean on data — is first countable, so sequential continuity is continuity); convergence of $z^n$, $L^n$ and $b(F^n)$ is coordinatewise. The split network $F'$ is given by a predicate that pins every coordinate of $F'$ on $N' \times N'$ as Axiom 4.1 lists, so $F'$ is unique; $K$ is a finite set disjoint from $N$ and may be empty, as on the page. The divisor $|K|+1$ is computed in $\mathbb R$.
-- source:
--   Csóka, Herings, An Axiomatization of the Proportional Rule in Financial Networks, Management Science 67(5), 2021, pp. 2801–2804, §2 (Π, 𝓜(N), a_i, e_i, row order), Definitions 2.1, 2.2, (2.1), §3 Axioms 3.1–3.5 and the convergence criterion p. 2803, Axiom 4.1 p. 2804; (A.1) p. 2808

import Mathlib

namespace FinNetProp.Mitosis

open Filter Topology

/-- A financial network `(N, z, L)` (Csóka–Herings 2021, §2, p. 2801). Agents are natural numbers;
the population `N` is a nonempty finite set of agents; endowments `z` are strictly positive on `N`;
the liability matrix `L` is nonnegative with zero diagonal. Both are stored as functions on `ℕ` that
vanish outside `N` (resp. `N × N`), so a network is determined by `(N, z, L)` restricted to `N`. -/
structure FinNet where
  N : Finset ℕ
  N_nonempty : N.Nonempty
  z : ℕ → ℝ
  L : ℕ → ℕ → ℝ
  z_pos : ∀ i ∈ N, 0 < z i
  L_nonneg : ∀ i j, 0 ≤ L i j
  L_diag : ∀ i, L i i = 0
  z_out : ∀ i, i ∉ N → z i = 0
  L_out : ∀ i j, (i ∉ N ∨ j ∉ N) → L i j = 0

/-- `𝓜(N)` (p. 2801): nonnegative matrices with zero diagonal on `N × N`, stored as functions on
`ℕ × ℕ` that vanish outside `N × N`. -/
def InM (N : Finset ℕ) (P : ℕ → ℕ → ℝ) : Prop :=
  (∀ i j, 0 ≤ P i j) ∧ (∀ i, P i i = 0) ∧ (∀ i j, (i ∉ N ∨ j ∉ N) → P i j = 0)

/-- The relative liability matrix `Π` (p. 2801): `Π_ij = 0` if `L_ij = 0`, and
`L_ij / ∑_{k ∈ N} L_ik` otherwise. -/
noncomputable def relLiab (F : FinNet) (i j : ℕ) : ℝ :=
  if F.L i j = 0 then 0 else F.L i j / ∑ k ∈ F.N, F.L i k

/-- Asset value `a_i(N, z, P) = z_i + ∑_{j ∈ N} P_ji` (p. 2801). -/
def assetValue (F : FinNet) (P : ℕ → ℕ → ℝ) (i : ℕ) : ℝ :=
  F.z i + ∑ j ∈ F.N, P j i

/-- Equity `e_i(N, z, P) = a_i(N, z, P) − ∑_{j ∈ N} P_ij` (p. 2801). -/
def equity (F : FinNet) (P : ℕ → ℕ → ℝ) (i : ℕ) : ℝ :=
  assetValue F P i - ∑ j ∈ F.N, P i j

/-- Definition 2.1 (p. 2801): a bankruptcy rule assigns to every financial network `F` a payment
matrix in `𝓜(N)`. -/
structure BankruptcyRule where
  toFun : FinNet → ℕ → ℕ → ℝ
  mem : ∀ F : FinNet, InM F.N (toFun F)

instance : CoeFun BankruptcyRule (fun _ => FinNet → ℕ → ℕ → ℝ) := ⟨BankruptcyRule.toFun⟩

/-- `P` is a solution of the system (2.1) for `F` (Definition 2.2, p. 2801):
`P ∈ 𝓜(N)` and `P_ij = min {Π_ij (z_i + ∑_{k ∈ N} P_ki), L_ij}` for all `i, j ∈ N`. -/
def IsPropSolution (F : FinNet) (P : ℕ → ℕ → ℝ) : Prop :=
  InM F.N P ∧ ∀ i ∈ F.N, ∀ j ∈ F.N,
    P i j = min (relLiab F i j * (F.z i + ∑ k ∈ F.N, P k i)) (F.L i j)

/-- The strict row order of p. 2801: `P_i < Q_i` iff `P_ij ≤ Q_ij` for all `j ∈ N` and
`P_ik < Q_ik` for some `k ∈ N`. -/
def RowLt (N : Finset ℕ) (P Q : ℕ → ℕ → ℝ) (i : ℕ) : Prop :=
  (∀ j ∈ N, P i j ≤ Q i j) ∧ ∃ k ∈ N, P i k < Q i k

/-- Axiom 3.1 (Claims Boundedness, p. 2803): `b(F) ≤ L`. -/
def ClaimsBounded (b : BankruptcyRule) : Prop :=
  ∀ F : FinNet, ∀ i ∈ F.N, ∀ j ∈ F.N, b F i j ≤ F.L i j

/-- Axiom 3.2 (Limited Liability, p. 2803): `e_i(N, z, b(F)) ≥ 0` for every `i ∈ N`. -/
def LimitedLiability (b : BankruptcyRule) : Prop :=
  ∀ F : FinNet, ∀ i ∈ F.N, 0 ≤ equity F (b F) i

/-- Axiom 3.3 (Priority of Creditors, p. 2803): if `b_i(F) < L_i` (strict row order) then
`e_i(N, z, b(F)) = 0`. -/
def PriorityOfCreditors (b : BankruptcyRule) : Prop :=
  ∀ F : FinNet, ∀ i ∈ F.N, RowLt F.N (b F) F.L i → equity F (b F) i = 0

/-- Convergence of a sequence of financial networks (p. 2803): eventually `N^n = N`, and
`z^n → z`, `L^n → L` coordinatewise. -/
def NetConverges (Fs : ℕ → FinNet) (F : FinNet) : Prop :=
  (∀ᶠ n in atTop, (Fs n).N = F.N) ∧
  (∀ i, Tendsto (fun n => (Fs n).z i) atTop (𝓝 (F.z i))) ∧
  (∀ i j, Tendsto (fun n => (Fs n).L i j) atTop (𝓝 (F.L i j)))

/-- Axiom 3.4 (Continuity, p. 2803), in sequential form: `b(F^n) → b(F)` coordinatewise whenever
`F^n → F`. -/
def RuleContinuous (b : BankruptcyRule) : Prop :=
  ∀ (Fs : ℕ → FinNet) (F : FinNet), NetConverges Fs F →
    ∀ i j, Tendsto (fun n => b (Fs n) i j) atTop (𝓝 (b F i j))

/-- Axiom 3.5 (Impartiality, p. 2803): `L_ij = L_ik` implies `b_ij(F) = b_ik(F)`. -/
def Impartial (b : BankruptcyRule) : Prop :=
  ∀ F : FinNet, ∀ i ∈ F.N, ∀ j ∈ F.N, ∀ k ∈ F.N, F.L i j = F.L i k → b F i j = b F i k

/-- `F'` is the network obtained from `F` by splitting agent `j` into the identical agents
`{j} ∪ K` (Axiom 4.1, p. 2804). Every coordinate of `F'` on `N' × N'` is pinned down. -/
def IsSplit (F : FinNet) (j : ℕ) (K : Finset ℕ) (F' : FinNet) : Prop :=
  F'.N = F.N ∪ K ∧
  (∀ k ∈ insert j K, F'.z k = F.z j / ((K.card : ℝ) + 1)) ∧
  (∀ i ∈ F.N.erase j, F'.z i = F.z i) ∧
  (∀ k ∈ insert j K, ∀ i ∈ F.N.erase j, F'.L k i = F.L j i / ((K.card : ℝ) + 1)) ∧
  (∀ k ∈ insert j K, ∀ i ∈ F.N.erase j, F'.L i k = F.L i j / ((K.card : ℝ) + 1)) ∧
  (∀ k ∈ insert j K, ∀ l ∈ insert j K, F'.L k l = 0) ∧
  (∀ h ∈ F.N.erase j, ∀ i ∈ F.N.erase j, F'.L h i = F.L h i)

/-- Axiom 4.1 (Invariance to Mitosis, p. 2804). -/
def InvariantToMitosis (b : BankruptcyRule) : Prop :=
  ∀ F : FinNet, ∀ j ∈ F.N, ∀ K : Finset ℕ, Disjoint K F.N → ∀ F' : FinNet, IsSplit F j K F' →
    (∀ i ∈ F.N.erase j, ∑ k ∈ insert j K, b F' k i = b F j i) ∧
    (∀ i ∈ F.N.erase j, ∑ k ∈ insert j K, b F' i k = b F i j) ∧
    (∀ h ∈ F.N.erase j, ∀ i ∈ F.N.erase j, b F' h i = b F h i)

/-- The split payment matrix `P'` of (A.1) (p. 2808), zero outside `N' × N'`. -/
noncomputable def splitPay (N : Finset ℕ) (P : ℕ → ℕ → ℝ) (j : ℕ) (K : Finset ℕ) :
    ℕ → ℕ → ℝ := fun a c =>
  if a ∈ insert j K ∧ c ∈ N.erase j then P j c / ((K.card : ℝ) + 1)
  else if a ∈ N.erase j ∧ c ∈ insert j K then P a j / ((K.card : ℝ) + 1)
  else if a ∈ N.erase j ∧ c ∈ N.erase j then P a c
  else 0

/-- All liabilities of `F` are rational numbers. -/
def RationalLiabilities (F : FinNet) : Prop :=
  ∀ i j, ∃ q : ℚ, F.L i j = q

end FinNetProp.Mitosis


