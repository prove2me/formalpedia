-- Prove2me | Definitions.Def_HiringLP_Parallel_Model
-- name    : HiringLP_Parallel_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T06:44:12.855161+00:00
-- url     : https://prove2.me/theorems/2184c4c2-ecf5-4303-a0ec-886ca26623d3
-- title:
--   §3.2, §5.1–5.3, pp. 12–13, 22–24 — Parallel Offering instances, LP_par, ALG_par and its expected reward, v*_j, D_j and D̃_j
-- statement:
--   The Parallel Offering problem of Epstein and Ma (§3.2) and the objects of its analysis (§5).
--
--   **Instance.** A firm fills $k$ positions from $n$ candidates within $T$ offering rounds. Candidate $i\in[n]$ accepts an offer for position $j\in[k]$ with probability $p_{ij}$ and then contributes the value $v_{ij}$. An instance $I=(k,T,n,p,v)$ is valid when
--   $$1\le k\le T\le n,\qquad p\in[0,1]^{n\times k},\qquad v\in\mathbb R_+^{n\times k}.$$
--
--   **Acceptance decisions.** Before the rounds start, each candidate $i$ has decided the set $A_i\subseteq[k]$ of positions whose offer they would accept. The law of $A_i$ is any distribution on subsets of $[k]$ with $\mathbb P(j\in A_i)=p_{ij}$; decisions may be correlated across the positions of one candidate and are independent across candidates.
--
--   **The linear program** $\mathrm{LP}_{\mathrm{par}}(I)$ (p. 22):
--   $$\max\ \sum_{j=1}^k\sum_{i=1}^n v_{ij}y_{ij}p_{ij}\quad\text{s.t.}\quad \sum_i y_{ij}\le T\ \forall j\ (6),\quad \sum_i y_{ij}p_{ij}\le1\ \forall j\ (7),\quad \sum_j y_{ij}\le 1\ \forall i\ (8),\quad 0\le y_{ij}\le1.$$
--   $L^*_j=\sum_i v_{ij}y_{ij}p_{ij}$, so the objective is $\sum_j L^*_j$.
--
--   **The algorithm $\mathrm{ALG}_{\mathrm{par}}$** (p. 23). Take an optimal solution $y$, round it to a random 0/1 matrix $Y$ with a GKPS rounding $\mu$ of $y$ on the bipartite graph candidates $\times$ positions, and put candidate $i$ on the list of position $j$ iff $Y_{ij}=1$. Each list is ordered by decreasing $v_{ij}$ (ties in any order). All lists run in parallel: in each round every unfilled position sends an offer to the next candidate on its list, until a candidate accepts, the list ends, or $T$ rounds have passed. Candidate $i$ is therefore hired for position $j$ iff $i$ is on list $j$, $j\in A_i$, no candidate before $i$ on list $j$ accepts $j$, and fewer than $T$ candidates precede $i$ on list $j$. $R_{\mathrm{ALG}_{\mathrm{par}}}(I)$ is the expected total value of the hires, $Y$ and the acceptance decisions being independent; $L_j$ is the expected value of the candidate hired for position $j$.
--
--   **Analysis objects** (p. 23). With $P_{ij}=\mathbf 1\{j\in A_i\}$, $D_j=\{i:P_{ij}Y_{ij}=1\}$ and $v^*_j(S)=\max_{i\in S}v_{ij}$ (with $v^*_j(\emptyset)=0$). $\tilde D_j=\{i:P_{ij}\tilde Y_{ij}=1\}$ uses independent Bernoulli variables $\tilde Y_{ij}$ with mean $y_{ij}$, so the events $i\in\tilde D_j$ are independent across $i$ with probabilities $y_{ij}p_{ij}$.
--
--   **Sequential Offering LP** (p. 21), for Lemma 9: for an instance with $n$ candidates (acceptance probabilities $p_i$, values $v_i$), $k$ positions and at most $T'$ offers,
--   $$\mathrm{LP}_{\mathrm{seq}}=\max\sum_i v_iy_ip_i\quad\text{s.t.}\quad\sum_i y_i\le T',\quad\sum_i y_ip_i\le k,\quad 0\le y_i\le1.$$
--   For a Parallel Offering instance whose positions are identical ($v_{ij}=w_i$, $p_{ij}=q_i$), $I'$ is the Sequential Offering instance with the same candidates, the same $k$ and $T'=kT$.
--
--   **Formalization Note** All randomness is finite: expectations are explicit sums over the rounded edge set $Y$ (weight $\mu(Y)$) and over acceptance profiles $(A_i)_{i\in[n]}$ (weight $\prod_i \mathrm{acc}_i(A_i)$). The list order of position $j$ is a permutation `ord j` of the candidates (rank `(ord j).symm i`); the order hypothesis is $v_{ij}\le v_{lj}$ whenever $l$ precedes $i$. $R_{\mathrm{ALG}_{\mathrm{par}}}$ and $L_j$ are defined from the run, not by the formula $\mathbb E\,v^*_j(D)$. $\mathrm{LP}_{\mathrm{par}}(I)$ and $\mathrm{LP}_{\mathrm{seq}}$ are suprema of the objective over the feasible set; both sets are nonempty ($y=0$) and bounded.
-- source:
--   Epstein, Ma, Selection and Ordering Policies for Hiring Pipelines via Linear Programming, arXiv:2210.04059v3, pp. 12–13 §3.2; p. 20 §4.6; p. 21 LPseq; p. 22 §5.1 (6)–(8); p. 23 §5.2–5.3; p. 24 §5.4

import Mathlib
import Definitions.Def_HiringLP_Parallel_GKPS

namespace HiringLP.Parallel

open Finset

/-- An instance `I = (k, T, n, p, v)` of the Parallel Offering problem (§3.2, pp. 12–13): `n`
candidates, `k` positions, `T` offering rounds, acceptance probabilities `p i j` and values
`v i j` of candidate `i` for position `j`. -/
structure Instance (n k : ℕ) where
  T : ℕ
  p : Fin n → Fin k → ℝ
  v : Fin n → Fin k → ℝ

/-- `I ∈ 𝓘_par` (p. 13): `1 ≤ k ≤ T ≤ n`, `p ∈ [0,1]^{n×k}`, `v ∈ ℝ₊^{n×k}`. -/
def Instance.Valid {n k : ℕ} (I : Instance n k) : Prop :=
  1 ≤ k ∧ k ≤ I.T ∧ I.T ≤ n ∧ (∀ i j, 0 ≤ I.p i j ∧ I.p i j ≤ 1) ∧ ∀ i j, 0 ≤ I.v i j

/-- The acceptance decisions (p. 13): `acc i A` is the probability that the set of positions whose
offer candidate `i` would accept is exactly `A`. Decisions may be correlated across the positions
of one candidate; candidate `i` accepts an offer for position `j` with probability `p i j`.
Independence across candidates is built into `accProb`. -/
def AccLaw {n k : ℕ} (I : Instance n k) (acc : Fin n → Finset (Fin k) → ℝ) : Prop :=
  (∀ i A, 0 ≤ acc i A) ∧ (∀ i, ∑ A, acc i A = 1) ∧
    ∀ i j, ∑ A ∈ univ.filter (fun A : Finset (Fin k) => j ∈ A), acc i A = I.p i j

/-- Probability of the acceptance profile `A` (candidate `i` would accept exactly the positions
`A i`), the candidates deciding independently. -/
def accProb {n k : ℕ} (acc : Fin n → Finset (Fin k) → ℝ) (A : Fin n → Finset (Fin k)) : ℝ :=
  ∏ i, acc i (A i)

/-- The feasible set of `LP_par(I)` (p. 22): constraints (6), (7), (8) and `0 ≤ y_ij ≤ 1`. -/
def LPFeasible {n k : ℕ} (I : Instance n k) (y : Fin n → Fin k → ℝ) : Prop :=
  (∀ j, ∑ i, y i j ≤ (I.T : ℝ)) ∧ (∀ j, ∑ i, y i j * I.p i j ≤ 1) ∧
    (∀ i, ∑ j, y i j ≤ 1) ∧ ∀ i j, 0 ≤ y i j ∧ y i j ≤ 1

/-- The objective of `LP_par(I)` (p. 22): `Σ_j Σ_i v_ij y_ij p_ij`. -/
def LPobj {n k : ℕ} (I : Instance n k) (y : Fin n → Fin k → ℝ) : ℝ :=
  ∑ j, ∑ i, I.v i j * y i j * I.p i j

/-- `y` is an optimal solution of `LP_par(I)`. -/
def IsLPOpt {n k : ℕ} (I : Instance n k) (y : Fin n → Fin k → ℝ) : Prop :=
  LPFeasible I y ∧ ∀ y', LPFeasible I y' → LPobj I y' ≤ LPobj I y

/-- The optimal value `LP_par(I)`. -/
noncomputable def LPpar {n k : ℕ} (I : Instance n k) : ℝ :=
  sSup (LPobj I '' {y | LPFeasible I y})

/-- `L*_j = Σ_i v_ij y_ij p_ij` (p. 23). -/
def Lstar {n k : ℕ} (I : Instance n k) (y : Fin n → Fin k → ℝ) (j : Fin k) : ℝ :=
  ∑ i, I.v i j * y i j * I.p i j

/-- In the list of position `j`, candidate `l` is offered before candidate `i`: `ord j` lists the
candidates, `(ord j).symm i` is the rank of `i`. -/
abbrev before {n k : ℕ} (ord : Fin k → Equiv.Perm (Fin n)) (j : Fin k) (l i : Fin n) : Prop :=
  (ord j).symm l < (ord j).symm i

/-- The lists are run in decreasing order of `v_ij` (p. 23); ties in any order. -/
def IsValueOrder {n k : ℕ} (I : Instance n k) (ord : Fin k → Equiv.Perm (Fin n)) : Prop :=
  ∀ j l i, before ord j l i → I.v i j ≤ I.v l j

/-- The run of `ALG_par` (pp. 13, 23) for the rounded matrix `Y` (`Y_ij = 1` iff `(i, j) ∈ Y`, so
candidate `i` is on the list of position `j`) and the acceptance profile `A`: candidate `i` is hired
for position `j` iff `i` is on list `j`, would accept `j`, no member of list `j` offered before `i`
accepts `j`, and `i`'s offer is sent within the `T` rounds (fewer than `T` members of list `j`
precede `i`). -/
abbrev hired {n k : ℕ} (I : Instance n k) (ord : Fin k → Equiv.Perm (Fin n))
    (Y : Finset (Fin n × Fin k)) (A : Fin n → Finset (Fin k)) (i : Fin n) (j : Fin k) : Prop :=
  (i, j) ∈ Y ∧ j ∈ A i ∧ (∀ l, (l, j) ∈ Y → before ord j l i → j ∉ A l) ∧
    (univ.filter (fun l => (l, j) ∈ Y ∧ before ord j l i)).card < I.T

/-- `R_ALG_par(I)`: the expected total value of the accepted offers when `Y ~ μ` (the rounding of
the LP solution), independently the acceptance profile `A ~ ∏_i acc i`, and the lists are run in
the orders `ord`. -/
def algReward {n k : ℕ} (I : Instance n k) (acc : Fin n → Finset (Fin k) → ℝ)
    (μ : Finset (Fin n × Fin k) → ℝ) (ord : Fin k → Equiv.Perm (Fin n)) : ℝ :=
  ∑ Y, μ Y * ∑ A : Fin n → Finset (Fin k), accProb acc A *
    ∑ j, ∑ i, if hired I ord Y A i j then I.v i j else 0

/-- `L_j`: the expected value of the candidate hired for position `j` by the run. -/
def Lpos {n k : ℕ} (I : Instance n k) (acc : Fin n → Finset (Fin k) → ℝ)
    (μ : Finset (Fin n × Fin k) → ℝ) (ord : Fin k → Equiv.Perm (Fin n)) (j : Fin k) : ℝ :=
  ∑ Y, μ Y * ∑ A : Fin n → Finset (Fin k), accProb acc A *
    ∑ i, if hired I ord Y A i j then I.v i j else 0

/-- `v*_j(S) = max_{i ∈ S} v_ij`, and `0` for `S = ∅`. -/
noncomputable def vstar {n k : ℕ} (I : Instance n k) (j : Fin k) (S : Finset (Fin n)) : ℝ :=
  if h : S.Nonempty then S.sup' h (fun i => I.v i j) else 0

/-- `E(v*_j(D))` with `D_j = {i : P_ij Y_ij = 1}`: `Y ~ μ`, `P_ij = 1` iff `j ∈ A i`. -/
noncomputable def EvD {n k : ℕ} (I : Instance n k) (acc : Fin n → Finset (Fin k) → ℝ)
    (μ : Finset (Fin n × Fin k) → ℝ) (j : Fin k) : ℝ :=
  ∑ Y, μ Y * ∑ A : Fin n → Finset (Fin k), accProb acc A *
    vstar I j (univ.filter (fun i => (i, j) ∈ Y ∧ j ∈ A i))

/-- `E(v*_j(D̃))` with `D̃_j = {i : P_ij Ỹ_ij = 1}`, the `Ỹ_ij` independent Bernoulli(`y_ij`):
the events `i ∈ D̃_j` are independent across `i` with probabilities `y_ij p_ij`. -/
noncomputable def EvDtilde {n k : ℕ} (I : Instance n k) (y : Fin n → Fin k → ℝ) (j : Fin k) : ℝ :=
  ∑ S : Finset (Fin n),
    (∏ i, if i ∈ S then y i j * I.p i j else 1 - y i j * I.p i j) * vstar I j S

/-- An instance of the Sequential Offering problem (§4.6, p. 20): `n` candidates with acceptance
probabilities `p i` and values `v i`, `k` positions, at most `T` offers. -/
structure SeqInstance (n : ℕ) where
  k : ℕ
  T : ℕ
  p : Fin n → ℝ
  v : Fin n → ℝ

/-- The feasible set of `LP_seq(I)` (p. 21). -/
def SeqFeasible {n : ℕ} (I : SeqInstance n) (y : Fin n → ℝ) : Prop :=
  ∑ i, y i ≤ (I.T : ℝ) ∧ ∑ i, y i * I.p i ≤ (I.k : ℝ) ∧ ∀ i, 0 ≤ y i ∧ y i ≤ 1

/-- The objective of `LP_seq(I)` (p. 21): `Σ_i v_i y_i p_i`. -/
def SeqObj {n : ℕ} (I : SeqInstance n) (y : Fin n → ℝ) : ℝ := ∑ i, I.v i * y i * I.p i

/-- The optimal value `LP_seq(I)`. -/
noncomputable def LPseq {n : ℕ} (I : SeqInstance n) : ℝ :=
  sSup (SeqObj I '' {y | SeqFeasible I y})

/-- For an instance with identical positions (`v_ij = w_i`, `p_ij = q_i`), the Sequential Offering
instance `I'` with the same candidates, the same `k` positions and a budget of `kT` offers (p. 24). -/
def seqOfIdentical {n k : ℕ} (I : Instance n k) (q w : Fin n → ℝ) : SeqInstance n :=
  ⟨k, k * I.T, q, w⟩

end HiringLP.Parallel


