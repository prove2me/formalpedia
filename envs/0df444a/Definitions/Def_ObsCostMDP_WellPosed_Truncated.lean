-- Prove2me | Definitions.Def_ObsCostMDP_WellPosed_Truncated
-- name    : ObsCostMDP_WellPosed_Truncated
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-13T20:50:45.737982+00:00
-- url     : https://prove2.me/theorems/fe86ff5c-bee6-494e-8c72-083d42deabb4
-- title:
--   Problems 3.6 and 3.9 — the truncated QVI (3.7), property (3.5), the penalised problem (3.8) and the restriction of F
-- statement:
--   This file sets up the finite (time-truncated) problems of Section 3 of Reisinger and Tam.
--
--   Fix a truncation time $N\ge1$, a finite state space $X$ ($|X|=L$) and a finite nonempty action set $A$ ($|A|=d$). A truncated vector is $u\in\mathbb R^{N\times L\times d}$ with entries $u^n_{a,l}$, $n\in\{1,\dots,N\}$. A **truncated driver** is a family $\tilde F_a:\mathbb R^{N\times L\times d}\to\mathbb R^{N\times L}$, $a\in A$. It has **property (3.5)** with constant $\beta>0$ if for all $u,v$ and every index $(\bar n,\bar a,\bar l)$ with $u^{\bar n}_{\bar a,\bar l}-v^{\bar n}_{\bar a,\bar l}=\max_{n,a,l}(u^n_{a,l}-v^n_{a,l})\ge0$,
--
--   $$\tilde F_{\bar a}(u)^{\bar n}_{\bar l}-\tilde F_{\bar a}(v)^{\bar n}_{\bar l}\ge\beta\big(u^{\bar n}_{\bar a,\bar l}-v^{\bar n}_{\bar a,\bar l}\big).$$
--
--   For substochastic matrices $Q_1,\dots,Q_N$ and $c\in\mathbb R^{L\times d}$, the truncated inspection operator is $(\mathcal Mu)^n_l=(Q_n\overline{u^1-c})_l$ with $(\overline{u^1-c})_l=\max_{a\in A}(u^1_{a,l}-c_{a,l})$. The **truncated QVI (3.7)** of Problem 3.6 is $\min\{\tilde F_a(u),u_a-\mathcal Mu\}=0$ elementwise for every $a$; sub- and supersolutions replace $=0$ by $\le0$ and $\ge0$.
--
--   A **penalisation function** is $\pi:\mathbb R\to\mathbb R$ continuous, non-decreasing, with $\pi=0$ on $(-\infty,0]$ and $\pi>0$ on $(0,\infty)$. For $\rho\ge0$, the **penalised problem (3.8)** of Problem 3.9 is
--
--   $$\tilde F_a(u)-\rho\,\pi(\mathcal Mu-u_a)=0\quad\text{elementwise, for every }a\in A,$$
--
--   and its sub- and supersolutions replace $=0$ by $\le0$ and $\ge0$.
--
--   Finally, the **restriction** of a driver $F$ of Problem 3.1 to $\{1,\dots,N\}$ is $\tilde F_a(u)^n_x:=F_a(n,x,u(n,x),u_a)$, where the function argument $u_a$ is extended by $0$ outside $\{1,\dots,N\}$.
--
--   These objects carry the paper's existence proof: the penalised problems approximate the truncated QVI, which in turn approximates (3.1).
--
--   **Formalization Note** The time set $\{1,\dots,N\}$ is `Fin N` shifted by one: the index $k$ stands for time $k+1$, so $u^1$ is `u 0` and $Q_n$ is `Q (n-1)`; $N\ge1$ is required (`NeZero N`). The time boundary condition $u_a(N,\cdot)=\mathcal Mu(N,\cdot)$ of Problem 3.6 is not part of the predicate for (3.7), because (3.8) does not encode it. The extension by $0$ in the restriction is the convention of Theorem 3.13 ("trivially defining $u^N_a(n,x)=0$ for $n>N$"); it also sets the value at time $0$ to $0$. "Is the maximum" in (3.5) is stated as $u^n_{a,l}-v^n_{a,l}\le u^{\bar n}_{\bar a,\bar l}-v^{\bar n}_{\bar a,\bar l}$ for all $(n,a,l)$.
-- source:
--   Reisinger & Tam, Markov decision processes with observation costs: framework and computation with a penalty scheme, arXiv:2201.07908v3, p. 17, restriction F̃, Lemma 3.5 (3.5) and Problem 3.6 (3.7); p. 18, Problem 3.9 (3.8)

import Mathlib
import Definitions.Def_ObsCostMDP_WellPosed_QVI

namespace ObsCostMDP.WellPosed

/-- A **truncated driver** `F̃ = (F̃_a)_{a∈A}`, `F̃_a : ℝ^{N×L×d} → ℝ^{N×L}` (Reisinger–Tam,
arXiv:2201.07908v3, p. 17). A truncated vector `u ∈ ℝ^{N×L×d}` is `u : Fin N → X → A → ℝ`.
**Formalization Note**: the truncated time set `{1, …, N}` is `Fin N` shifted by one: the index
`k : Fin N` is the time `k + 1`, so the first time slice `u¹` is `u 0`. -/
abbrev TDriver (N : ℕ) (X A : Type*) := A → (Fin N → X → A → ℝ) → (Fin N → X → ℝ)

/-- **Property (3.5)** (Lemma 3.5, p. 17) with constant `β > 0`: for all `u, v ∈ ℝ^{N×L×d}` and
every index `(n̄, l̄, ā)` with `u^{n̄}_{ā,l̄} − v^{n̄}_{ā,l̄} = max_{n,a,l}(u^n_{a,l} − v^n_{a,l}) ≥ 0`,
`F̃_ā(u)^{n̄}_{l̄} − F̃_ā(v)^{n̄}_{l̄} ≥ β (u^{n̄}_{ā,l̄} − v^{n̄}_{ā,l̄})`.
"Is the maximum" is written as `∀ n l a, u n l a − v n l a ≤ u n̄ l̄ ā − v n̄ l̄ ā`. -/
def Property35 {N : ℕ} {X A : Type*} (Ft : TDriver N X A) (β : ℝ) : Prop :=
  0 < β ∧
  ∀ (u v : Fin N → X → A → ℝ) (nb : Fin N) (lb : X) (ab : A),
    (∀ n l a, u n l a - v n l a ≤ u nb lb ab - v nb lb ab) → 0 ≤ u nb lb ab - v nb lb ab →
      β * (u nb lb ab - v nb lb ab) ≤ Ft ab u nb lb - Ft ab v nb lb

/-- Substochastic family `{Q_n}` indexed by truncated time (`k : Fin N` is the time `k + 1`). -/
def IsSubstochasticT {N : ℕ} {X : Type*} [Fintype X] (Q : Fin N → Matrix X X ℝ) : Prop :=
  ∀ n, (∀ x y, 0 ≤ Q n x y) ∧ ∀ x, ∑ y, Q n x y ≤ 1

/-- The truncated inspection operator (p. 17): `(Mu)^n_l = (Q_n \overline{u¹ − c})_l` with
`(\overline{u¹ − c})_y = max_{a∈A}(u¹_{a,y} − c_{a,y})`; `u¹` is the first time slice `u 0`. -/
def tInspection {N : ℕ} [NeZero N] {X A : Type*} [Fintype X] [Fintype A] [Nonempty A]
    (Q : Fin N → Matrix X X ℝ) (c : A → X → ℝ) (u : Fin N → X → A → ℝ) (n : Fin N) (l : X) : ℝ :=
  ∑ y, Q n l y * actMax (fun a => u 0 y a - c a y)

/-- The left side of the truncated QVI (3.7), p. 17: `min {F̃_a(u)^n_l, u^n_{a,l} − (Mu)^n_l}`. -/
def tResidual {N : ℕ} [NeZero N] {X A : Type*} [Fintype X] [Fintype A] [Nonempty A]
    (Ft : TDriver N X A) (Q : Fin N → Matrix X X ℝ) (c : A → X → ℝ) (u : Fin N → X → A → ℝ)
    (n : Fin N) (l : X) (a : A) : ℝ :=
  min (Ft a u n l) (u n l a - tInspection Q c u n l)

/-- Subsolution of (3.7) (Proposition 3.8, p. 17): `min {F̃_a(u), u_a − Mu} ≤ 0` elementwise, all `a`. -/
def IsTSubsolution {N : ℕ} [NeZero N] {X A : Type*} [Fintype X] [Fintype A] [Nonempty A]
    (Ft : TDriver N X A) (Q : Fin N → Matrix X X ℝ) (c : A → X → ℝ)
    (u : Fin N → X → A → ℝ) : Prop :=
  ∀ n l a, tResidual Ft Q c u n l a ≤ 0

/-- Supersolution of (3.7): `min {F̃_a(u), u_a − Mu} ≥ 0` elementwise, all `a`. -/
def IsTSupersolution {N : ℕ} [NeZero N] {X A : Type*} [Fintype X] [Fintype A] [Nonempty A]
    (Ft : TDriver N X A) (Q : Fin N → Matrix X X ℝ) (c : A → X → ℝ)
    (u : Fin N → X → A → ℝ) : Prop :=
  ∀ n l a, 0 ≤ tResidual Ft Q c u n l a

/-- `u` solves the truncated QVI (3.7) of Problem 3.6: `min {F̃_a(u), u_a − Mu} = 0` elementwise,
for every `a`. **Formalization Note**: the time boundary condition `u_a(N, ·) = Mu(N, ·)` of
Problem 3.6 is *not* part of this predicate; the penalised problem (3.8) does not encode it. -/
def IsTSolution {N : ℕ} [NeZero N] {X A : Type*} [Fintype X] [Fintype A] [Nonempty A]
    (Ft : TDriver N X A) (Q : Fin N → Matrix X X ℝ) (c : A → X → ℝ)
    (u : Fin N → X → A → ℝ) : Prop :=
  ∀ n l a, tResidual Ft Q c u n l a = 0

/-- A **penalisation function** (Problem 3.9, p. 18): `π : ℝ → ℝ` continuous, non-decreasing,
`π = 0` on `(−∞, 0]` and `π > 0` on `(0, ∞)`. -/
def IsPenalty (pen : ℝ → ℝ) : Prop :=
  Continuous pen ∧ Monotone pen ∧ (∀ t ≤ 0, pen t = 0) ∧ ∀ t, 0 < t → 0 < pen t

/-- The penalised residual (3.8), p. 18: `F̃_a(u)^n_l − ρ π((Mu)^n_l − u^n_{a,l})`. -/
def penResidual {N : ℕ} [NeZero N] {X A : Type*} [Fintype X] [Fintype A] [Nonempty A]
    (Ft : TDriver N X A) (Q : Fin N → Matrix X X ℝ) (c : A → X → ℝ) (pen : ℝ → ℝ) (ρ : ℝ)
    (u : Fin N → X → A → ℝ) (n : Fin N) (l : X) (a : A) : ℝ :=
  Ft a u n l - ρ * pen (tInspection Q c u n l - u n l a)

/-- Subsolution of (3.8) (Proposition 3.10, p. 18): penalised residual `≤ 0` everywhere. -/
def IsPenSubsolution {N : ℕ} [NeZero N] {X A : Type*} [Fintype X] [Fintype A] [Nonempty A]
    (Ft : TDriver N X A) (Q : Fin N → Matrix X X ℝ) (c : A → X → ℝ) (pen : ℝ → ℝ) (ρ : ℝ)
    (u : Fin N → X → A → ℝ) : Prop :=
  ∀ n l a, penResidual Ft Q c pen ρ u n l a ≤ 0

/-- Supersolution of (3.8): penalised residual `≥ 0` everywhere. -/
def IsPenSupersolution {N : ℕ} [NeZero N] {X A : Type*} [Fintype X] [Fintype A] [Nonempty A]
    (Ft : TDriver N X A) (Q : Fin N → Matrix X X ℝ) (c : A → X → ℝ) (pen : ℝ → ℝ) (ρ : ℝ)
    (u : Fin N → X → A → ℝ) : Prop :=
  ∀ n l a, 0 ≤ penResidual Ft Q c pen ρ u n l a

/-- `u` solves the penalised problem (3.8) of Problem 3.9: `F̃_a(u) − ρ π(Mu − u_a) = 0`
elementwise, for every `a`. -/
def IsPenSolution {N : ℕ} [NeZero N] {X A : Type*} [Fintype X] [Fintype A] [Nonempty A]
    (Ft : TDriver N X A) (Q : Fin N → Matrix X X ℝ) (c : A → X → ℝ) (pen : ℝ → ℝ) (ρ : ℝ)
    (u : Fin N → X → A → ℝ) : Prop :=
  ∀ n l a, penResidual Ft Q c pen ρ u n l a = 0

/-- Zero extension of a truncated vector to `ℕ × X → ℝ^A` (the convention of Theorem 3.13,
"trivially defining `u_a(n, x) = 0` for `n > N`"): time `m ∈ {1, …, N}` reads `u (m − 1)`,
every other time (`m = 0` and `m > N`) gives `0`. -/
def zeroExt {N : ℕ} {X A : Type*} (u : Fin N → X → A → ℝ) (m : ℕ) (y : X) (a : A) : ℝ :=
  if h : 1 ≤ m ∧ m ≤ N then u ⟨m - 1, by omega⟩ y a else 0

/-- The **restriction** `F̃` of a driver `F` of Problem 3.1 to `{1, …, N}` (p. 17):
`F̃_a(u)^n_x := F_a(n, x, u(n, x), u_a)`, where the function argument `u_a` is the zero extension
of the truncated `u_a` to `ℕ × X` (see `zeroExt`); the truncated index `k : Fin N` is time `k + 1`. -/
def restrictDriver {X A : Type*} (F : Driver X A) (N : ℕ) : TDriver N X A :=
  fun a u k x => F a (k.val + 1) x (u k x) (fun m y => zeroExt u m y a)

end ObsCostMDP.WellPosed


