-- Prove2me | Definitions.Def_MusicStreaming_Axioms_Setting
-- name    : MusicStreaming_Axioms_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T01:17:38.669001+00:00
-- url     : https://prove2.me/theorems/95561bed-596a-42c9-87b5-36a97d3bf405
-- title:
--   §2–§3, pp. 7–13 — streaming problems, indices and rewards, pro-rata, user-centric, weighted indices, and the axioms
-- statement:
--   This module fixes the model of Bergantiños and Moreno-Ternero for sharing a music streaming platform's revenue among artists.
--
--   1. **Streaming problem** (p. 7). There are $n$ artists $N$ and a finite set $M$ of users. For artist $i$ and user $j$, $t_{ij}\in\mathbb N$ is the number of times $j$ streamed content of $i$. Each user pays $1$, so the amount to share is $m=|M|$.
--   2. **Totals and lists** (p. 8). $T_i=\sum_{j\in M}t_{ij}$ (streams of artist $i$), $T^j=\sum_{i\in N}t_{ij}$ (streams of user $j$), and $L^j=\{i\in N: t_{ij}>0\}$ (the artists $j$ played).
--   3. **Index and reward** (p. 8). An index $I$ assigns to every problem a vector $I(N,M,t)\in\mathbb R^N$; it is a *popularity index* if on every problem with at least one user it is nonnegative with $\sum_{i\in N}I_i>0$. Artist $i$ is paid
--   $$R^I_i(N,M,t)=\frac{I_i(N,M,t)}{\sum_{i'\in N}I_{i'}(N,M,t)}\,m .$$
--   4. **Pro-rata, user-centric, weighted indices** (pp. 9–10). $P_i=T_i$; $U_i=\sum_{j\in M}t_{ij}/T^j$; and for a weight function $\omega(j,x)$ of a user $j$ and a streaming profile $x\in\mathbb N^N$, $I^\omega_i=\sum_{j\in M}\omega(j,t_{\cdot j})\,t_{ij}$, where $t_{\cdot j}=(t_{ij})_{i\in N}$.
--   5. **Axioms** (pp. 11–13).
--      - *Homogeneity*: if $t_{ij}=\lambda t_{i'j}$ for all $j\in M$, with $\lambda\ge 0$, then $I_i=\lambda I_{i'}$.
--      - *Additivity*: if $M$ is the disjoint union of $M^1$ and $M^2$ and $t$ restricts to $t^1$, $t^2$ on them, then $I(N,M,t)=I(N,M^1,t^1)+I(N,M^2,t^2)$.
--      - *Equal individual impact of similar users*: if $j,j'\in M$ and $t_{ij}=t_{ij'}$, then $I_i(N,M\setminus\{j\},t_{-j})=I_i(N,M\setminus\{j'\},t_{-j'})$.
--      - *Equal global impact of users*: for $j,j'\in M$, $\sum_i I_i(N,M\setminus\{j\},t_{-j})=\sum_i I_i(N,M\setminus\{j'\},t_{-j'})$.
--      - *Reasonable lower bound*: for every $C\subseteq M$, with $L^C=\bigcup_{j\in C}L^j$, $\sum_{i\in L^C}R^I_i\ge |C|$.
--      - *Click-fraud-proofness*: if $t$ and $t'$ have the same users and differ only in the column of one user $j\in M$, then $|R^I_i(t)-R^I_i(t')|\le 1$ for every artist $i$.
--
--   These are the objects of Theorem 1 and of the two further axioms of §3.
--
--   **Formalization Note** Artists are indexed $0,\dots,n-1$ (index $i$ is the paper's artist $i+1$). Users are named by natural numbers, and a problem is a finitely supported table $t:\mathbb N\to\mathbb N^{N}$ whose support is the user set $M$; so every user in $M$ has played some artist ($L^j\neq\varnothing$, the paper's standing assumption, p. 19), streams are natural numbers, and the problem with $M\setminus\{j\}$ and $t_{-j}$ is $t$ with column $j$ erased. Positivity of the index is required only on problems with at least one user; the empty problem has $m=0$ and nothing to share. Additivity is stated for disjoint user sets: the printed axiom only says $M=M^1\cup M^2$, under which (taking $M^1=M^2=M$) it would force $I=2I$, and the paper's proofs split disjointly. A weight system's positivity is a separate hypothesis wherever it is used. Division in $R^I$ and in $U$ is Lean's total division, but $T^j>0$ for every user in $M$, and $R^I=0$ on the empty problem.
-- source:
--   Bergantiños, Moreno-Ternero, Revenue sharing at music streaming platforms, arXiv:2310.11861v1, pp. 7–13, §2 (streaming problems, indices, rewards, P, U, I^ω) and §3 (axioms)

import Mathlib

namespace MusicStreaming.Axioms

/-- A streaming problem with `n` artists (`Fin n`; index `i` is the paper's artist `i + 1`).
Users are named by natural numbers. `t j i` is the number of times user `j` streamed artist `i`
(the paper's `t_ij`, p. 7). The user set `M` is `t.support`: exactly the users with a nonzero
column, so every user in `M` has played some artist (the standing assumption `L^j ≠ ∅`, p. 19).
The empty problem `t = 0` has no users. -/
abbrev Problem (n : ℕ) := ℕ →₀ (Fin n → ℕ)

variable {n : ℕ}

/-- `T_i = ∑_{j ∈ M} t_ij`, the total streams of artist `i` (p. 8). -/
def artistTotal (t : Problem n) (i : Fin n) : ℕ := ∑ j ∈ t.support, t j i

/-- `T^j = ∑_{i ∈ N} t_ij`, the total streams of user `j` (p. 8). -/
def userTotal (t : Problem n) (j : ℕ) : ℕ := ∑ i, t j i

/-- `L^j = {i ∈ N : t_ij > 0}`, the artists user `j` played (p. 8). -/
def listened (t : Problem n) (j : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun i => 0 < t j i)

/-- An index assigns to every problem a real vector over the artists (p. 8). -/
abbrev Index (n : ℕ) := Problem n → Fin n → ℝ

/-- The requirements on a popularity index (p. 8): on every problem with at least one user, the
index is a nonnegative vector with positive sum. Nothing is required at the empty problem. -/
def IsIndex (I : Index n) : Prop :=
  ∀ t : Problem n, t ≠ 0 → (∀ i, 0 ≤ I t i) ∧ 0 < ∑ i, I t i

/-- The reward `R^I_i = I_i / ∑_{i'} I_{i'} · m` of artist `i`, with `m = |M|` (p. 8). -/
noncomputable def reward (I : Index n) (t : Problem n) (i : Fin n) : ℝ :=
  I t i / (∑ i', I t i') * t.support.card

/-- The pro-rata index `P_i = T_i` (p. 9). -/
def proRata : Index n := fun t i => (artistTotal t i : ℝ)

/-- The user-centric index `U_i = ∑_{j ∈ M} t_ij / T^j` (p. 9). -/
noncomputable def userCentric : Index n :=
  fun t i => ∑ j ∈ t.support, (t j i : ℝ) / userTotal t j

/-- The weighted index `I^ω_i = ∑_{j ∈ M} ω(j, t.j) t_ij` of a weight system
`ω : users × profiles → ℝ` (p. 9). A weight system is required to be positive separately. -/
def weightedIndex (ω : ℕ → (Fin n → ℕ) → ℝ) : Index n :=
  fun t i => ∑ j ∈ t.support, ω j (t j) * t j i

/-- Homogeneity (p. 11): if `t_ij = c · t_i'j` for every user `j ∈ M`, with `c ≥ 0`, then
`I_i = c · I_i'`. -/
def Homogeneity (I : Index n) : Prop :=
  ∀ (t : Problem n) (i i' : Fin n) (c : ℝ), 0 ≤ c →
    (∀ j ∈ t.support, (t j i : ℝ) = c * t j i') → I t i = c * I t i'

/-- Additivity (p. 11), for a problem split into two problems with disjoint user sets. -/
def Additivity (I : Index n) : Prop :=
  ∀ t₁ t₂ : Problem n, Disjoint t₁.support t₂.support → I (t₁ + t₂) = I t₁ + I t₂

/-- Equal individual impact of similar users (p. 11): if users `j, j' ∈ M` streamed artist `i`
equally often, removing either of them leaves the same index value for `i`. -/
def EqualIndividualImpact (I : Index n) : Prop :=
  ∀ (t : Problem n) (i : Fin n) (j j' : ℕ), j ∈ t.support → j' ∈ t.support →
    t j i = t j' i → I (t.erase j) i = I (t.erase j') i

/-- Equal global impact of users (p. 11): removing any user `j ∈ M` leaves the same total of the
index. -/
def EqualGlobalImpact (I : Index n) : Prop :=
  ∀ (t : Problem n) (j j' : ℕ), j ∈ t.support → j' ∈ t.support →
    ∑ i, I (t.erase j) i = ∑ i, I (t.erase j') i

/-- Reasonable lower bound (p. 12): for every set `C ⊆ M` of users, the artists `L^C` they played
receive in total at least `|C|`. -/
def ReasonableLowerBound (I : Index n) : Prop :=
  ∀ (t : Problem n) (C : Finset ℕ), C ⊆ t.support →
    (C.card : ℝ) ≤ ∑ i ∈ C.biUnion (listened t), reward I t i

/-- Click-fraud-proofness (p. 13): if two problems with the same user set differ only in the
column of one user `j ∈ M`, no artist's reward changes by more than `1`. -/
def ClickFraudProof (I : Index n) : Prop :=
  ∀ (t t' : Problem n) (j : ℕ), t'.support = t.support → j ∈ t.support →
    (∀ j', j' ≠ j → t' j' = t j') → ∀ i, |reward I t i - reward I t' i| ≤ 1

end MusicStreaming.Axioms


