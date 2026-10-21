-- Prove2me | Definitions.Def_CollatNet_Termination_Model
-- name    : CollatNet_Termination_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T05:50:22.546397+00:00
-- url     : https://prove2.me/theorems/9898d592-d72f-4554-a003-bea042b2bbee
-- title:
--   §2.1–2.3, §4, §5.1, pp. 6–30 — collateralized clearing at π ≡ 1: Round 1, freed-collateral Round 2, N rounds of full termination, selective termination, shortfalls, net worth
-- statement:
--   This file sets up the collateralized payment network of Ghamami, Glasserman and Young, with the collateral asset valued at the constant price $\pi \equiv 1$. It covers Round 1, Round 2 with freed collateral and no derivatives termination, the $N$ rounds of full contract termination, Round 2 of selective termination, the default sets, the payment shortfalls and the net worth.
--
--   **Data.** A finite set $\mathcal N$ of nodes (banks), with $N = |\mathcal N|$. For $i, j \in \mathcal N$:
--
--   1. $\bar p_{ij} \ge 0$ is the payment due from $i$ to $j$, and $L_i = \bar p_i = \sum_{k} \bar p_{ik}$ is node $i$'s total obligation;
--   2. $c_i \ge 0$ is the cash held by $i$;
--   3. $m_{ij} \ge 0$ is the margin (collateral) posted by $i$ for its obligations to $j$;
--   4. $v_{ij} \ge 0$ is the value to $j$ of its derivative contracts with $i$, which $i$ owes to $j$ when the contracts are terminated; $v_i = \sum_j v_{ij}$.
--
--   The diagonals vanish ($\bar p_{ii} = m_{ii} = v_{ii} = 0$), and obligations are netted: $\bar p_{ij}\bar p_{ji} = 0$ and $v_{ij} v_{ji} = 0$. A proportion with a zero denominator is $0$.
--
--   **Round 1.** Given payments $p^{(1)}$, node $i$ has assets $A^{(1)}_i = c_i + \sum_k p^{(1)}_{ki}$, and the default set is $D^{(1)} = \{i : A^{(1)}_i < L_i\}$. A creditor $j$ of a defaulting node $i$ first seizes $\Delta_{ij} = m_{ij} \wedge \bar p_{ij}$; the rest of $i$'s assets is shared pro rata over the residual claims, with proportions $a^{(1)}_{ij} = [\bar p_{ij} - m_{ij}]^+ / \sum_k [\bar p_{ik} - m_{ik}]^+$. Clearing payments are payments $0 \le p^{(1)}$ with
--   $$
--   p^{(1)}_{ij} = \begin{cases} \bar p_{ij} \wedge \big[m_{ij} + a^{(1)}_{ij} A^{(1)}_i\big], & i \in D^{(1)},\\ \bar p_{ij}, & i \notin D^{(1)}. \end{cases}
--   $$
--   The collateral returned after Round 1 is $r_i = \sum_j (m_{ij} - \Delta_{ij})$ for $i \in D^{(1)}$ and $r_i = \sum_{j \in D^{(1)}} m_{ij}$ for $i \notin D^{(1)}$.
--
--   **Freed-collateral Round 2 without derivative termination (§2.3).** Remaining obligations are $\bar p^{(2)}_{ij}=\bar p_{ij}-p^{(1)}_{ij}$, and payments satisfy
--   $$
--   p^{(2)}_{ij}=\bar p^{(2)}_{ij}\wedge a^{(2)}_{ij}\left(r_i+\sum_k p^{(2)}_{ki}\right),\qquad a^{(2)}_{ij}=\frac{\bar p^{(2)}_{ij}}{\sum_k\bar p^{(2)}_{ik}},
--   $$
--   with $a^{(2)}_{ij}=0$ when its denominator is zero. These objects state the complete Proposition 2.1.
--
--   **Rounds $m = 2, \dots, R$ under full termination.** Here $R = \max(2, N)$. Let $D^{(l)}$ be the nodes that default in round $l$ and not before, and $S_n$ the nodes that survive rounds $1, \dots, n$. At the start of round $m$, node $i$ holds cash $c^{(m)}_i$ and returned collateral $r^{(m)}_i$, and owes
--   $$
--   \bar p^{(m)}_{ij} = \begin{cases} v_{ij} + \bar p^{(m-1)}_{ij} - p^{(m-1)}_{ij}, & i \text{ or } j \in D^{(m-1)},\ i, j \in S_{m-2},\\ \bar p^{(m-1)}_{ij} - p^{(m-1)}_{ij}, & i \text{ or } j \notin S_{m-2},\\ 0, & i, j \in S_{m-1}. \end{cases}
--   $$
--   Its assets are $A^{(m)}_i = c^{(m)}_i + r^{(m)}_i + \sum_k p^{(m)}_{ki}$, and $D^{(m)} = \{i \in S_{m-1} : A^{(m)}_i < \sum_k \bar p^{(m)}_{ik}\}$. Seizure is $\Delta^{(m)}_{ij} = m_{ij} \wedge \bar p^{(m)}_{ij}$ for $i \in D^{(m)}$, $j \in S_{m-1}$, and $0$ otherwise. The proportions are $a^{(m)}_{ij} = [\bar p^{(m)}_{ij} - \Delta^{(m)}_{ij}] / \sum_k [\bar p^{(m)}_{ik} - \Delta^{(m)}_{ik}]$, and clearing payments are payments $0 \le p^{(m)}$ with
--   $$
--   p^{(m)}_{ij} = \bar p^{(m)}_{ij} \wedge \big[\Delta^{(m)}_{ij} + a^{(m)}_{ij} A^{(m)}_i\big].
--   $$
--   Collateral returned for round $m+1$ is $\sum_{j \in S_{m-1}} (m_{ij} - \Delta^{(m)}_{ij})$ for $i \in D^{(m)}$, $\sum_{j \in D^{(m)}} m_{ij}$ for $i \in S_m$, and $0$ for nodes that defaulted earlier. Cash evolves by $c^{(2)}_i = c_i + \sum_k p^{(1)}_{ki} - \sum_k (p^{(1)}_{ik} - \Delta_{ik})$ and
--   $$
--   c^{(m+1)}_i = c^{(m)}_i + r^{(m)}_i + \sum_k p^{(m)}_{ki} - \sum_k \big(p^{(m)}_{ik} - \Delta^{(m)}_{ik}\big).
--   $$
--   The round-2 obligations are therefore $\bar p^{(2)}_{ij} = v_{ij} + \bar p_{ij} - p^{(1)}_{ij}$ if $i$ or $j \in D^{(1)}$, and $0$ otherwise.
--
--   **Selective termination** shares Round 1. In Round 2 only the defaulted node's own contracts are accelerated: $\bar q^{(2)}_{ij} = v_{ij} + \bar p_{ij} - p^{(1)}_{ij}$ if $i \in D^{(1)}$, and $0$ otherwise. Cash and returned collateral are those of full termination, and the round-2 clearing payments $q^{(2)}$ solve the same equation with $\bar q^{(2)}$ in place of $\bar p^{(2)}$.
--
--   **Outcomes.** The default sets are $D^f = \bigcup_{l=1}^{R} D^{(l)}$ and $D^s = D^{(1)}$. The payment shortfalls are
--   $$
--   L^f = \sum_{i \in D^f} \big(v_i + \bar p_i - p_i\big), \qquad L^s = \sum_{i \in D^{(1)}} \big(v_i + \bar p_i - q_i\big),
--   $$
--   with $p_i = \sum_{l=1}^{R} \sum_j p^{(l)}_{ij}$ and $q_i = \sum_j p^{(1)}_{ij} + \sum_j q^{(2)}_{ij}$. The net worth at the end of Round 1 is $e_i = c_i + r_i + \sum_k p^{(1)}_{ki} - \sum_k \bar p_{ik}$.
--
--   These objects are the setting of the comparison between full and selective contract termination (Lemma 5.1, Proposition 5.2).
--
--   **Formalization Note.** Every collateral price is $1$ (case (i) of Proposition 5.2), so prices do not appear and collateral shares count as cash. Sums over $k \ne i$ are written over all $k$; the zero diagonals make these equal. Clearing payments are required to be nonnegative, i.e. they lie in the box $[0, \bar p]$ in which the paper's fixed-point argument works (proof of Proposition 2.1, p. 40). Without this, negative circular "payments" would satisfy the fixed-point equations. The cash recursion is a disclosed repair of p. 24, whose literal form $c^{(m)}_i = c^{(m-1)}_i + \sum_k p^{(m-1)}_{ki} - \sum_k p^{(m-1)}_{ik}$ drops unsold returned collateral and deducts seized collateral from cash; with the literal form Proposition 5.2 (i) fails on a four-node network. The round count is $R = \max(2, N)$, which equals $N$ for $N \ge 2$ (a one-node network has no obligations). A payment sequence is indexed by rounds $\ell \in \mathbb N$; only $\ell = 1, \dots, R$ are used. Collateral returned to nodes that defaulted before round $m-1$ is $0$, a case the page leaves unstated.
-- source:
--   Ghamami, Glasserman & Young, Collateralized networks, accepted manuscript (Management Science 68(3), 2022; LSE Research Online 107496, version November 2020), pp. 6–30 (PDF 7–31), §2.1–2.3 (2), (5)–(9), (11)–(14); §4 (26)–(30) and the cash recursion of p. 24 (repaired); §5.1 (34), (35), (39); App. A.9 (63), (64), (66), p. 44 (PDF 45)

import Mathlib

namespace CollatNet.Termination

open Finset

/-- The data of a collateralized network (§2.1, p. 6; §2.2, p. 7; §4, p. 23), valued at the
constant collateral price `π ≡ 1`: `pbar i j` = p̄_ij, the payment due from `i` to `j`; `c i` = c_i,
the cash held by `i`; `m i j` = m_ij, the margin (collateral) posted by `i` for its obligations to `j`;
`v i j` = v_ij, the value to `j` of its derivative contracts with `i`, owed by `i` to `j` on
termination. -/
structure Network (ι : Type*) where
  pbar : ι → ι → ℝ
  c : ι → ℝ
  m : ι → ι → ℝ
  v : ι → ι → ℝ

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Standing assumptions of §2.1–2.2 and §4: nonnegative data, zero diagonals (`m_ii = 0`, and the
paper's sums over `k ≠ i`), and netting `p̄_ij p̄_ji = 0`, `v_ij v_ji = 0`. -/
def Network.Standing (X : Network ι) : Prop :=
  (∀ i j, 0 ≤ X.pbar i j) ∧ (∀ i, 0 ≤ X.c i) ∧ (∀ i j, 0 ≤ X.m i j) ∧ (∀ i j, 0 ≤ X.v i j) ∧
  (∀ i, X.pbar i i = 0) ∧ (∀ i, X.m i i = 0) ∧ (∀ i, X.v i i = 0) ∧
  (∀ i j, X.pbar i j * X.pbar j i = 0) ∧ (∀ i j, X.v i j * X.v j i = 0)

/-- `L_i = p̄_i = Σ_k p̄_ik`, node `i`'s total first-round obligation (2). -/
def oblTot (X : Network ι) (i : ι) : ℝ := ∑ k, X.pbar i k

/-- `v_i = Σ_j v_ij`, node `i`'s total termination liability (35). -/
def vTot (X : Network ι) (i : ι) : ℝ := ∑ j, X.v i j

/-- The number of rounds `R = max 2 N`, `N = |ι|` (Prop. 4.1: rounds `m = 1, …, N`; at least two). -/
def numRounds (ι : Type*) [Fintype ι] : ℕ := max 2 (Fintype.card ι)

/-- Pro rata proportions of a claim matrix `o`: `o_ij / Σ_k o_ik`, and `0` when the denominator is
`0` ((6), (13), (65)). -/
noncomputable def ratio (o : ι → ι → ℝ) (i j : ι) : ℝ :=
  if ∑ k, o i k = 0 then 0 else o i j / ∑ k, o i k

/-! ### Round 1 (§2.2, (5)–(9), (12)) -/

/-- `A^(1)_i = c_i + Σ_k p^(1)_ki` (7). -/
def assets1 (X : Network ι) (p : ι → ι → ℝ) (i : ι) : ℝ := X.c i + ∑ k, p k i

/-- The first-round default set `D = D^(1) = {i : A^(1)_i < L_i}` (8). -/
noncomputable def D1 (X : Network ι) (p : ι → ι → ℝ) : Finset ι :=
  univ.filter (fun i => assets1 X p i < oblTot X i)

/-- `a^(1)_ij = [p̄_ij − m_ij]^+ / Σ_k [p̄_ik − m_ik]^+`, `0` if the denominator is `0` (6). -/
noncomputable def a1 (X : Network ι) (i j : ι) : ℝ :=
  ratio (fun i k => max (X.pbar i k - X.m i k) 0) i j

/-- First-round clearing payments (9), taken in the box `[0, p̄]`:
`p^(1)_ij = p̄_ij ∧ [m_ij + a^(1)_ij A^(1)_i]` for `i ∈ D`, `p̄_ij` for `i ∉ D`. -/
def Clears1 (X : Network ι) (p : ι → ι → ℝ) : Prop :=
  ∀ i j, 0 ≤ p i j ∧
    p i j = if i ∈ D1 X p then min (X.pbar i j) (X.m i j + a1 X i j * assets1 X p i)
      else X.pbar i j

/-- Collateral seized in Round 1, `Δ_ij = m_ij ∧ p̄_ij` for `i ∈ D`, `0` otherwise (5). -/
noncomputable def seized1 (X : Network ι) (p : ι → ι → ℝ) (i j : ι) : ℝ :=
  if i ∈ D1 X p then min (X.m i j) (X.pbar i j) else 0

/-! ### Freed collateral without derivative termination (§2.3, (11)–(14)) -/

/-- The remaining ordinary obligation in Round 2, `p̄^(2)_ij = p̄_ij − p^(1)_ij` (11). -/
def baseObl2 (X : Network ι) (p1 : ι → ι → ℝ) (i j : ι) : ℝ :=
  X.pbar i j - p1 i j

/-- Collateral returned after Round 1, `r_i` (12). -/
noncomputable def returned2 (X : Network ι) (p1 : ι → ι → ℝ) (i : ι) : ℝ :=
  if i ∈ D1 X p1 then ∑ j, (X.m i j - seized1 X p1 i j)
  else ∑ j ∈ D1 X p1, X.m i j

/-- Round-2 clearing without derivative termination, (13)–(14), with a zero-denominator
proportion equal to zero. -/
def ClearsBase2 (X : Network ι) (p1 p2 : ι → ι → ℝ) : Prop :=
  ∀ i j, 0 ≤ p2 i j ∧
    p2 i j = min (baseObl2 X p1 i j)
      (ratio (baseObl2 X p1) i j * (returned2 X p1 i + ∑ k, p2 k i))

/-! ### Rounds `m ≥ 2` (§4, (26)–(30)) -/

/-- The state at the start of a round `m ≥ 2`: cash `c^(m)`, returned collateral `r^(m)`,
obligations `p̄^(m)`, and the survivors `S_{m−1}` of rounds `1, …, m − 1`. -/
structure RoundState (ι : Type*) where
  cash : ι → ℝ
  ret : ι → ℝ
  obl : ι → ι → ℝ
  alive : Finset ι

/-- `A^(m)_i = c^(m)_i + r^(m)_i + Σ_k p^(m)_ki` (28) at `π^(m) = 1`. -/
def assetsAt (s : RoundState ι) (x : ι → ι → ℝ) (i : ι) : ℝ :=
  s.cash i + s.ret i + ∑ k, x k i

/-- `D^(m) = {i ∈ S_{m−1} : A^(m)_i < Σ_k p̄^(m)_ik}` (29). -/
noncomputable def defaultsAt (s : RoundState ι) (x : ι → ι → ℝ) : Finset ι :=
  s.alive.filter (fun i => assetsAt s x i < ∑ k, s.obl i k)

/-- `Δ^(m)_ij = m_ij ∧ p̄^(m)_ij` for `i ∈ D^(m)`, `j ∈ S_{m−1}`, `0` otherwise (27), at
`π^(m) = 1`. -/
noncomputable def seizedAt (X : Network ι) (s : RoundState ι) (x : ι → ι → ℝ) (i j : ι) : ℝ :=
  if i ∈ defaultsAt s x ∧ j ∈ s.alive then min (X.m i j) (s.obl i j) else 0

/-- `a^(m)_ij = [p̄^(m)_ij − Δ^(m)_ij] / Σ_k [p̄^(m)_ik − Δ^(m)_ik]`, `0` if the denominator is
`0`. -/
noncomputable def propAt (X : Network ι) (s : RoundState ι) (x : ι → ι → ℝ) (i j : ι) : ℝ :=
  ratio (fun i k => s.obl i k - seizedAt X s x i k) i j

/-- Clearing payments of a round `m ≥ 2` (30), taken in the box `[0, p̄^(m)]`:
`p^(m)_ij = p̄^(m)_ij ∧ [Δ^(m)_ij + a^(m)_ij A^(m)_i]`. -/
def ClearsAt (X : Network ι) (s : RoundState ι) (x : ι → ι → ℝ) : Prop :=
  ∀ i j, 0 ≤ x i j ∧
    x i j = min (s.obl i j) (seizedAt X s x i j + propAt X s x i j * assetsAt s x i)

/-- The state at the start of Round 2 under full termination, from first-round payments `p1`:
cash `c^(2)_i = c_i + Σ_k p^(1)_ki − Σ_k (p^(1)_ik − Δ_ik)` (repaired recursion: seized collateral
is not paid out of cash), returned collateral `r_i` (12), obligations `p̄^(2)` (63), survivors
`S_1 = N \ D^(1)`. -/
noncomputable def initFT (X : Network ι) (p1 : ι → ι → ℝ) : RoundState ι where
  cash i := X.c i + ∑ k, p1 k i - ∑ k, (p1 i k - seized1 X p1 i k)
  ret i := returned2 X p1 i
  obl i j := if i ∈ D1 X p1 ∨ j ∈ D1 X p1 then X.v i j + X.pbar i j - p1 i j else 0
  alive := univ \ D1 X p1

/-- The state at the start of Round 2 under selective termination: as `initFT`, except that the
obligations are `q̄^(2)` (64): `v_ij + p̄_ij − p^(1)_ij` if `i ∈ D^(1)`, `0` otherwise. -/
noncomputable def initST (X : Network ι) (p1 : ι → ι → ℝ) : RoundState ι :=
  { initFT X p1 with
    obl := fun i j => if i ∈ D1 X p1 then X.v i j + X.pbar i j - p1 i j else 0 }

/-- One round of full termination: from the state of round `m` and its payments `x = p^(m)`, the
state of round `m + 1`: cash `c^(m+1)_i = c^(m)_i + r^(m)_i + Σ_k p^(m)_ki − Σ_k (p^(m)_ik − Δ^(m)_ik)`
(repaired recursion), returned collateral `r^(m+1)` (p. 25; `0` for nodes that defaulted before
round `m`), obligations `p̄^(m+1)` (26), survivors `S_m = S_{m−1} \ D^(m)`. -/
noncomputable def nextFT (X : Network ι) (s : RoundState ι) (x : ι → ι → ℝ) : RoundState ι where
  cash i := s.cash i + s.ret i + ∑ k, x k i - ∑ k, (x i k - seizedAt X s x i k)
  ret i := if i ∈ defaultsAt s x then ∑ j ∈ s.alive, (X.m i j - seizedAt X s x i j)
    else if i ∈ s.alive then ∑ j ∈ defaultsAt s x, X.m i j else 0
  obl i j := if i ∈ s.alive ∧ j ∈ s.alive then
      (if i ∈ defaultsAt s x ∨ j ∈ defaultsAt s x then X.v i j + s.obl i j - x i j else 0)
    else s.obl i j - x i j
  alive := s.alive \ defaultsAt s x

/-- The full-termination state at the start of round `k + 2`, given payments `p ℓ` of round `ℓ`
(`p 1` = Round 1, `p (k + 2)` = round `k + 2`). -/
noncomputable def stateFT (X : Network ι) (p : ℕ → ι → ι → ℝ) : ℕ → RoundState ι
  | 0 => initFT X (p 1)
  | k + 1 => nextFT X (stateFT X p k) (p (k + 2))

/-- `p` is a sequence of full-termination clearing payments for rounds `1, …, R`
(`R = numRounds ι`): Round 1 clears (9), and every round `m = k + 2 ≤ R` clears (30) in the state
built from the earlier rounds. Values `p ℓ` for `ℓ = 0` or `ℓ > R` are unconstrained and unused. -/
def ClearsFT (X : Network ι) (p : ℕ → ι → ι → ℝ) : Prop :=
  Clears1 X (p 1) ∧ ∀ k, k + 2 ≤ numRounds ι → ClearsAt X (stateFT X p k) (p (k + 2))

/-- The full-termination default set `D^f = ⋃_{l=1}^{R} D^(l)` (34). -/
noncomputable def Df (X : Network ι) (p : ℕ → ι → ι → ℝ) : Finset ι :=
  D1 X (p 1) ∪
    (range (numRounds ι - 1)).biUnion (fun k => defaultsAt (stateFT X p k) (p (k + 2)))

/-- Round-2 clearing payments under full termination ((30) at `m = 2`). -/
def round2FT (X : Network ι) (p1 : ι → ι → ℝ) : Set (ι → ι → ℝ) :=
  {x | ClearsAt X (initFT X p1) x}

/-- Round-2 clearing payments under selective termination ((66)). -/
def round2ST (X : Network ι) (p1 : ι → ι → ℝ) : Set (ι → ι → ℝ) :=
  {x | ClearsAt X (initST X p1) x}

/-- The full-termination payment shortfall `L^f = Σ_{i ∈ D^f} (v_i + p̄_i − p_i)`,
`p_i = Σ_{l=1}^{R} Σ_j p^(l)_ij` (35). -/
noncomputable def shortfallFT (X : Network ι) (p : ℕ → ι → ι → ℝ) : ℝ :=
  ∑ i ∈ Df X p, (vTot X i + oblTot X i - ∑ l ∈ Icc 1 (numRounds ι), ∑ j, p l i j)

/-- The selective-termination payment shortfall `L^s = Σ_{i ∈ D^(1)} (v_i + p̄_i − q_i)`,
`q_i = Σ_j q^(1)_ij + Σ_j q^(2)_ij`, with `q^(1) = p^(1)` (35). -/
noncomputable def shortfallST (X : Network ι) (p1 q2 : ι → ι → ℝ) : ℝ :=
  ∑ i ∈ D1 X p1, (vTot X i + oblTot X i - ∑ j, p1 i j - ∑ j, q2 i j)

/-- Net worth at the end of Round 1, `e_i = c_i + r_i + Σ_k p^(1)_ki − Σ_k p̄_ik` (39) at
`π^(1) = 1`, with `r_i` the returned collateral (12). -/
noncomputable def netWorth (X : Network ι) (p1 : ι → ι → ℝ) (i : ι) : ℝ :=
  X.c i + (initFT X p1).ret i + ∑ k, p1 k i - oblTot X i

end CollatNet.Termination


