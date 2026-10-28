-- Prove2me | Definitions.Def_NSWApxHard_Reduction_Welfare
-- name    : NSWApxHard_Reduction_Welfare
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-24T09:32:10.829883+00:00
-- url     : https://prove2.me/theorems/b7b6153e-c487-42b3-85d1-20d597a1a7a3
-- title:
--   Allocations of indivisible items, additive utilities and Nash social welfare (p. 1); the NSW gap decision problem
-- statement:
--   **Allocations and Nash social welfare** (Lee, p. 1). Let $A$ be a finite set of $n$ agents and $B$ a finite set of items, and let every agent $a$ have a utility $u_{a,i}$ for every item $i$. An *allocation* is a partition $\{B_a\}_{a\in A}$ of $B$, recorded as a map $x : B\to A$ sending every item to the agent who receives it ($B_a = x^{-1}(a)$). Agent $a$'s utility is additive,
--   $$u_a(x)=\sum_{i\in B_a}u_{a,i},$$
--   and the *Nash social welfare* of $x$ is the geometric mean of the agents' utilities,
--   $$\mathrm{NSW}(x)=\Big(\prod_{a\in A}u_a(x)\Big)^{1/n}.$$
--   An allocation is *optimal* when no allocation has larger Nash social welfare.
--
--   **The decision problem.** An input $P$ consists of natural numbers $n$ (agents), $m$ (items), natural-number utilities $u_{a,i}$ for $a<n$, $i<m$, and a natural-number threshold $T$. Its *welfare threshold* is $\tau = T^{1/n}$, so that $\mathrm{NSW}(x)\ge\tau$ exactly when the product of the utilities is at least $T$. Inputs are written in binary: every natural number $k$ is encoded self-delimitingly (each binary digit of $k$, least significant first, preceded by a $1$, then a final $0$), and the input is the code of $n$, $m$, $T$ followed by the codes of the utilities, row by row. For a factor $\mu$:
--   1. $P$ is a **Yes-instance** if $n\ge1$, $n\le m$, $T\ge1$ and some allocation has $\mathrm{NSW}(x)\ge\tau$;
--   2. $P$ is a **No-instance for $\mu$** if $n\ge1$, $n\le m$, $T\ge1$ and every allocation has $\mathrm{NSW}(x)\le\tau/\mu$.
--
--   These are the objects of the paper's problem statement and of its hardness conclusion: "NP-hard to approximate within $\mu$" is rendered as the NP-hardness of distinguishing Yes-instances from No-instances for $\mu$.
--
--   **Formalization Note** The paper's utilities are non-negative reals; the decision problem uses natural numbers, a subclass, so hardness for it is hardness for the paper's problem. The conditions $n\ge1$ and $T\ge1$ exclude degenerate inputs that would be Yes- and No-instances at once (no agents gives the empty product $1$; $T=0$ gives $\tau=0$). With $n=0$ the exponent $1/n$ is $0$ in Lean, so $\mathrm{NSW}=1$; this case is excluded from both instance sets. $\mathrm{NSW}$ uses the real power `rpow`, which is the usual power on the non-negative products that occur here.
-- source:
--   Lee, APX-Hardness of Maximizing Nash Social Welfare with Indivisible Items, arXiv:1507.01159v1, p. 1, §1 (problem statement, n ⩽ m, allocation, u_a(A), Nash social welfare); p. 5, §2 (conclusion: NP-hard to approximate within µ)

import Mathlib

namespace NSWApxHard.Reduction

open Finset

section Generic

variable {A B : Type} [Fintype A] [Fintype B] [DecidableEq A]

/-- Additive utility of agent `a` under the allocation `x` (Lee, p. 1): `x` sends every item to
exactly one agent (the partition `{B_a}`), and `u_a(x) = ∑_{i ∈ B_a} u a i`. -/
def utility (u : A → B → ℝ) (x : B → A) (a : A) : ℝ :=
  ∑ i ∈ univ.filter (fun i => x i = a), u a i

/-- Nash social welfare of the allocation `x` (Lee, p. 1): the geometric mean
`(∏_a u_a(x))^{1/n}` of the agents' utilities, `n = |A|`. -/
noncomputable def nsw (u : A → B → ℝ) (x : B → A) : ℝ :=
  (∏ a, utility u x a) ^ ((1 : ℝ) / Fintype.card A)

/-- `x` maximizes the Nash social welfare over all allocations. -/
def IsOptimal (u : A → B → ℝ) (x : B → A) : Prop :=
  ∀ y : B → A, nsw u y ≤ nsw u x

end Generic

/-- Self-delimiting binary code of a natural number: each binary digit of `k` (least significant
first, as in `Nat.bits`) is preceded by `true`, and the code ends with `false`. Its length is
`2 ⌈log₂ (k + 1)⌉ + 1`. -/
def natBits (k : ℕ) : List Bool :=
  (Nat.bits k).flatMap (fun b => [true, b]) ++ [false]

/-- An input of the Nash-social-welfare decision problem: `n` agents, `m` items, natural-number
utilities `u a i`, and a natural-number threshold `T` for the product of the utilities. -/
structure NSWInput where
  n : ℕ
  m : ℕ
  u : Fin n → Fin m → ℕ
  T : ℕ

namespace NSWInput

/-- The binary encoding of an input: `n`, `m`, `T`, then the utilities `u a i` row by row (agent
`a = 0, …, n-1`, and within a row item `i = 0, …, m-1`), every number by `natBits`. -/
def enc (P : NSWInput) : List Bool :=
  natBits P.n ++ natBits P.m ++ natBits P.T ++
    (List.ofFn fun a : Fin P.n => (List.ofFn fun i : Fin P.m => natBits (P.u a i)).flatten).flatten

/-- Nash social welfare of the allocation `x` (item `i` goes to agent `x i`) in the input `P`. -/
noncomputable def nswOf (P : NSWInput) (x : Fin P.m → Fin P.n) : ℝ :=
  nsw (fun a i => (P.u a i : ℝ)) x

/-- The welfare threshold `τ = T^{1/n}` of the input: `nswOf x ≥ τ` iff the product of the
utilities is at least `T`. -/
noncomputable def tau (P : NSWInput) : ℝ :=
  (P.T : ℝ) ^ ((1 : ℝ) / P.n)

end NSWInput

/-- The encoding of NSW inputs used for the complexity statements. -/
def encNSW (P : NSWInput) : List Bool := P.enc

/-- Yes-instances of the gap problem: at least one agent, `n ≤ m` (Lee, p. 1), `T ≥ 1`, and some
allocation has Nash social welfare at least `τ`. -/
def nswYes (P : NSWInput) : Prop :=
  1 ≤ P.n ∧ P.n ≤ P.m ∧ 1 ≤ P.T ∧ ∃ x : Fin P.m → Fin P.n, P.tau ≤ P.nswOf x

/-- No-instances of the gap problem for the factor `μ`: at least one agent, `n ≤ m`, `T ≥ 1`, and
every allocation has Nash social welfare at most `τ / μ`. -/
def nswNo (μ : ℝ) (P : NSWInput) : Prop :=
  1 ≤ P.n ∧ P.n ≤ P.m ∧ 1 ≤ P.T ∧ ∀ x : Fin P.m → Fin P.n, P.nswOf x ≤ P.tau / μ

end NSWApxHard.Reduction


