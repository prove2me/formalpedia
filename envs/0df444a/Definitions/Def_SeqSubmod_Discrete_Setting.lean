-- Prove2me | Definitions.Def_SeqSubmod_Discrete_Setting
-- name    : SeqSubmod_Discrete_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-19T04:13:19.575599+00:00
-- url     : https://prove2.me/theorems/96a75b43-b92e-4879-9bba-d2206eba30d6
-- title:
--   §5.1–5.2, pp. 16–17 — discrete sequences, domination, marginal value, sequence-non-decreasing (10), sequence-submodular (11), Assumption 2, the α-greedy condition (13)
-- statement:
--   This file fixes the model of §5 of Alaei, Makhdoumi and Malekian: functions of finite sequences of actions, and the greedy condition of Theorem 3.
--
--   Let $\mathcal S$ be a finite set of **actions**. A **discrete sequence** is a finite tuple $A=(s_1,\dots,s_k)$ with $k\ge 0$ and $s_i\in\mathcal S$; the empty sequence is $\emptyset$, the length is $|A|=k$, and $\mathbb H^D(\mathcal S)$ is the set of all discrete sequences. The **concatenation** $A\perp B$ lists the elements of $A$ followed by those of $B$, and the **refinement** $H_{[1,i]}=(s_1,\dots,s_i)$ is the prefix of length $i$ (with $H_{[1,0]}=\emptyset$). A sequence $A$ is **dominated** by $B$, written $A\prec B$, if $A$ is obtained from $B$ by removing some of its elements, keeping the order of the rest.
--
--   For a **discrete sequence function** $u:\mathbb H^D(\mathcal S)\to\mathbb R$:
--
--   1. the **marginal value** of $B$ after $A$ is $u(B\mid A)=u(A\perp B)-u(A)$;
--   2. $u$ is **sequence-non-decreasing**, (10), if $u(A)\le u(B)$ whenever $A\prec B$, and $u(\emptyset)=0$;
--   3. $u$ is **sequence-submodular**, (11), if for all $A,B,C$ with $A\prec B$,
--   $$u(C\mid A)\ \ge\ u(C\mid B);$$
--   4. **Assumption 2** holds if $u$ is both sequence-non-decreasing and sequence-submodular;
--   5. for $\alpha\in\mathbb R$, a sequence $H=(s_1,\dots,s_T)$ is **$\alpha$-greedy** if condition (13) holds at every position: for all $i\in\{1,\dots,T\}$,
--   $$u\big(s_i\mid H_{[1,i-1]}\big)\ \ge\ \alpha\,\max_{s\in\mathcal S} u\big(s\mid H_{[1,i-1]}\big).$$
--
--   These are the objects of Theorem 3: under Assumption 2, every $\alpha$-greedy sequence of length $T$ achieves a $1-e^{-\alpha}$ fraction of the best value of a sequence of length at most $T$. With $\alpha=1$, condition (13) describes the plain greedy algorithm (Algorithm 3 of the paper).
--
--   **Formalization Note** Sequences are Lean lists `List S` with `[Fintype S]`; concatenation is `++` and domination is `List.Sublist` (`A <+ B`), the subsequence order, not the prefix or subset order. `marginal u B A` is $u(B\mid A)$, with the arguments in the paper's order. In `IsAlphaGreedy`, Lean's 0-based `H[i]` is the paper's $s_{i+1}$ and `H.take i` is $H_{[1,i]}$, so the condition at Lean index $i$ is (13) at the paper's index $i+1$. The maximum over $\mathcal S$ is `Finset.univ.sup'`, which needs `[Nonempty S]`; for empty $\mathcal S$ the only sequence is $\emptyset$ and nothing is lost.
-- source:
--   Alaei, Makhdoumi & Malekian, Maximizing sequence-submodular functions and its application to online advertising, arXiv:1009.4153v4, pp. 8, 16–17, Definition 5, §5.1–5.2, (10), (11), Assumption 2, (13)

import Mathlib

namespace SeqSubmod.Discrete

/-- The marginal value `u(B|A) = u(A⊥B) − u(A)` (p. 17), with the arguments in the paper's
order: `marginal u B A` is the gain of appending `B` after `A`. Discrete sequences over the
action set `S` are lists, `A⊥B` is `A ++ B`, and the empty sequence `∅` is `[]`. -/
def marginal {S : Type*} (u : List S → ℝ) (B A : List S) : ℝ := u (A ++ B) - u A

/-- (10), p. 16: `u` is sequence-non-decreasing if `u(A) ≤ u(B)` whenever `A ≺ B`, and
`u(∅) = 0`. Domination `A ≺ B` ("we can remove some elements of `B` to obtain `A`",
Definition 5, p. 8) is `List.Sublist A B` (written `A <+ B`: delete elements, keep the order). -/
def IsSeqNonDecreasing {S : Type*} (u : List S → ℝ) : Prop :=
  (∀ A B : List S, List.Sublist A B → u A ≤ u B) ∧ u [] = 0

/-- (11), p. 17: `u` is sequence-submodular if `u(C|A) ≥ u(C|B)` for all `A, B, C`
with `A ≺ B`. -/
def IsSeqSubmodular {S : Type*} (u : List S → ℝ) : Prop :=
  ∀ A B C : List S, List.Sublist A B → marginal u C B ≤ marginal u C A

/-- Assumption 2, p. 17: `u` is sequence-non-decreasing and sequence-submodular. -/
def Assumption2 {S : Type*} (u : List S → ℝ) : Prop :=
  IsSeqNonDecreasing u ∧ IsSeqSubmodular u

/-- Condition (13), p. 17, at every position of `H`:
`u(s_i | H_{[1,i−1]}) ≥ α · max_{s ∈ S} u(s | H_{[1,i−1]})` for all `i ∈ {1, …, |H|}`.
Lean's 0-based `H[i]` is the paper's `s_{i+1}`, and `H.take i` is the refinement
`H_{[1,i]}` (so `H.take 0 = ∅ = H_{[1,0]}`); the condition below at Lean index `i` is (13)
at the paper's index `i + 1`. The maximum over the finite action set `S` is
`Finset.univ.sup'`, which needs `S` nonempty. -/
def IsAlphaGreedy {S : Type*} [Fintype S] [Nonempty S] (u : List S → ℝ) (α : ℝ)
    (H : List S) : Prop :=
  ∀ (i : ℕ) (hi : i < H.length),
    α * Finset.univ.sup' Finset.univ_nonempty (fun s : S => marginal u [s] (H.take i))
      ≤ marginal u [H[i]] (H.take i)

end SeqSubmod.Discrete


