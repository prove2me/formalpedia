-- Prove2me | Definitions.Def_OpenPitMIP_UltPit_Setting
-- name    : OpenPitMIP_UltPit_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T12:41:55.650163+00:00
-- url     : https://prove2.me/theorems/b1bc3612-6831-4f9c-8e46-46396d5de63b
-- title:
--   §2.1 and §4.1, pp. 1426–1431 — the PCPSP-C instance, formulation (1)–(7), integrality (10)/(11), minimal optimality, U-PIT (12)–(14), pit limits
-- statement:
--   This file fixes the model of §2.1 of Rivera Letelier, Espinoza, Goycoolea, Moreno and Muñoz, the **precedence-constrained production scheduling problem with clusters** (PCPSP-C), together with the ultimate pit limit problem of §4.1.
--
--   **Instance.** $\mathcal B$ is a finite set of blocks, $\mathcal D$ a finite set of destinations, $\mathcal C$ a finite set of clusters and $\mathcal T = \{1, \dots, T\}$ the periods. Each block $b$ lies in the cluster $c(b)$. For $b \in \mathcal B$, $d \in \mathcal D$, the number $p_{b,d}$ (possibly negative) is the value of sending $b$ to $d$, and with a discount rate $r$ the value in period $t$ is
--   $$p_{b,d,t} = \frac{p_{b,d}}{(1+r)^t}.$$
--   $q_b$ is the weight of block $b$, $U_t$ the mining capacity and $U^d_t$ the capacity of destination $d$ in period $t$; $Gy \le g$ is a system of $m$ side constraints. A relation $b_1 \prec b_2$ on blocks ("$b_1$ must be extracted no later than $b_2$") induces a relation on clusters: $c_1 \prec c_2$ if some block of $c_1$ precedes some block of $c_2$. The arc set $\mathcal A$ is the transitive reduction: $(c, c') \in \mathcal A$ iff $c' \prec c$ and there is no $c''$ with $c' \prec c'' \prec c$. The closure and reverse closure are $cl(c) = \{c\} \cup \{c' : c' \prec c\}$ and $rcl(c) = \{c\} \cup \{c' : c \prec c'\}$; $b(S)$ is the set of blocks on a set of clusters $S$, $q(S) = \sum_{b \in b(S)} q_b$, and $w_{c,t} = \sum_{t'=1}^{t} x_{c,t'}$.
--
--   **Standing assumptions** (p. 1426): the clusters partition $\mathcal B$ (each cluster is nonempty), $\prec$ induces a strict partial order on clusters, $r > 0$, and $q_b \ge 0$.
--
--   **Formulation (1)–(7).** A pair $(x, y)$, $x = (x_{c,t})$, $y = (y_{b,d,t})$, is feasible if
--   $$x_{c(b),t} = \sum_{d} y_{b,d,t}, \quad \sum_{t} x_{c,t} \le 1, \quad \sum_{t'=1}^{t} x_{c,t'} \le \sum_{t'=1}^{t} x_{c',t'}\ \ ((c,c') \in \mathcal A), \quad Gy \le g, \quad y \ge 0,$$
--   and $x$ satisfies the integrality condition: full integrality (10), $x_{c,t} \in \{0,1\}$, or partial integrality (11), $\sum_{t'=1}^t x_{c,t'} > 0 \Rightarrow \sum_{t'=1}^t x_{c',t'} = 1$ for $(c, c') \in \mathcal A$. The objective (1) is $\sum_b \sum_d \sum_t p_{b,d,t}\, y_{b,d,t}$. The mining and destination capacity rows (8), (9) are $\sum_b \sum_d q_b y_{b,d,t} \le U_t$ and $\sum_b q_b y_{b,d,t} \le U^d_t$. A feasible pair is **optimal** if no feasible pair has a larger objective, and an optimal pair is **minimal** (p. 1431) if every optimal $(x', y')$ with $x' \le x$ and $y' \le y$ componentwise equals $(x, y)$.
--
--   **U-PIT (12)–(14).** With $p_{b,*} = \max_{d} p_{b,d}$ and $\bar p_c = \sum_{b \in c} p_{b,*}$, the ultimate pit limit problem is the linear program
--   $$\max \sum_{c} \bar p_c x_c \quad \text{s.t.}\quad x_c \le x_{c'}\ \ ((c,c') \in \mathcal A), \qquad x_c \in [0,1].$$
--   Optimal and minimal optimal solutions are defined as above, for the componentwise order on $[0,1]^{\mathcal C}$. The **pit limit** of a vector $x$ is $\{c : x_c > 0\}$, and a set of blocks $P$ is a **pit** if $b_1 \prec b_2$ and $b_2 \in P$ imply $b_1 \in P$.
--
--   These objects are the vocabulary of Theorem 1, the preprocessing result of §4.1, and of the companion claims of §2 and §4.
--
--   **Formalization Note** Periods are `Fin T`; index $t$ stands for period $t+1$, so the discount is $(1+r)^{t+1}$ and $\sum_{t'=1}^{t}$ is a sum over `Finset.Iic t`. The block relation is primitive and the cluster relation and $\mathcal A$ are derived from it. The integrality condition is a parameter `κ ∈ {F, P}`. The maximum defining $p_{b,*}$ needs at least one destination; every statement using $\bar p$ assumes `Nonempty D`. Orders on $x$ and $y$ are the pointwise orders on functions. Both optimal-solution notions quantify over the whole feasible set of the respective problem.
-- source:
--   Oper. Res. 68(5), §2.1 (pp. 1426–1427), formulation (1)–(11); §4.1 (p. 1431), minimality, (12)–(14), pit limit

import Mathlib

namespace OpenPitMIP.UltPit

/-- The integrality condition (7): full integrality (10) gives PCPSP-F, partial integrality (11)
gives PCPSP-P (Oper. Res. 68(5), p. 1427). -/
inductive Integrality
  | F
  | P

/-- An instance of the PCPSP-C (§2.1, pp. 1426–1427): blocks `B`, destinations `D`, clusters `C`,
the periods `𝒯 = {1, …, T}` as `Fin T` (index `t` is period `t + 1`), and `m` side constraints
`Gy ≤ g`. `clu b` is `c(b)`, `bprec b₁ b₂` is `b₁ ≺ b₂`, `p b d` is `p_{b,d}`, `r` the discount
rate, `q b` the weight `q_b`, `U t` and `Ud d t` the capacities `U_t`, `U_t^d`. -/
structure PCPSPC (B D C : Type) [Fintype B] [Fintype D] [Fintype C] (T m : ℕ) where
  clu : B → C
  bprec : B → B → Prop
  p : B → D → ℝ
  r : ℝ
  q : B → ℝ
  U : Fin T → ℝ
  Ud : D → Fin T → ℝ
  G : Fin m → B → D → Fin T → ℝ
  g : Fin m → ℝ

namespace PCPSPC

variable {B D C : Type} [Fintype B] [Fintype D] [Fintype C] {T m : ℕ}

/-- Cluster precedence `c₁ ≺ c₂`: some block of `c₁` precedes some block of `c₂` (p. 1426). -/
def cprec (I : PCPSPC B D C T m) (c₁ c₂ : C) : Prop :=
  ∃ b₁ b₂, I.clu b₁ = c₁ ∧ I.clu b₂ = c₂ ∧ I.bprec b₁ b₂

/-- The arc set `𝒜`, the transitive reduction of `≺` on clusters (pp. 1426–1427):
`(c, c') ∈ 𝒜` iff `c' ≺ c` immediately (a cluster's out-neighbours are its precedents). -/
def arc (I : PCPSPC B D C T m) (c c' : C) : Prop :=
  I.cprec c' c ∧ ¬ ∃ c'', I.cprec c' c'' ∧ I.cprec c'' c

/-- The standing assumptions of §2.1 (p. 1426): the clusters partition `𝓑` (so each is nonempty),
`≺` induces a (strict) partial order on clusters, the discount rate is positive, and weights
(amounts of material) are nonnegative. -/
structure Standing (I : PCPSPC B D C T m) : Prop where
  clu_surjective : Function.Surjective I.clu
  strictOrder : IsStrictOrder C I.cprec
  r_pos : 0 < I.r
  q_nonneg : ∀ b, 0 ≤ I.q b

open Classical in
/-- `cl(c) = {c} ∪ {c' ∈ 𝒞 : c' ≺ c}` (p. 1427). -/
noncomputable def cl (I : PCPSPC B D C T m) (c : C) : Finset C :=
  Finset.univ.filter (fun c' => c' = c ∨ I.cprec c' c)

open Classical in
/-- `rcl(c) = {c} ∪ {c' ∈ 𝒞 : c ≺ c'}` (p. 1427). -/
noncomputable def rcl (I : PCPSPC B D C T m) (c : C) : Finset C :=
  Finset.univ.filter (fun c' => c' = c ∨ I.cprec c c')

open Classical in
/-- The closure of a set of clusters, `cl(S) = ⋃_{c ∈ S} cl(c)` (used as `cl({c₁, c₂})`, p. 1433). -/
noncomputable def clSet (I : PCPSPC B D C T m) (S : Finset C) : Finset C :=
  S.biUnion I.cl

open Classical in
/-- `b(S) = {b ∈ 𝓑 : b ∈ c, c ∈ S}`, the blocks on a set of clusters (p. 1432). -/
noncomputable def blocksOf (I : PCPSPC B D C T m) (S : Finset C) : Finset B :=
  Finset.univ.filter (fun b => I.clu b ∈ S)

/-- `q(S) = ∑_{c ∈ S} ∑_{b ∈ c} q_b` (p. 1432). -/
noncomputable def qSet (I : PCPSPC B D C T m) (S : Finset C) : ℝ :=
  ∑ b ∈ I.blocksOf S, I.q b

/-- The cumulative variable `w_{c,t} = ∑_{t'=1}^{t} x_{c,t'}`, display (17), p. 1432. -/
def cum (x : C → Fin T → ℝ) (c : C) (t : Fin T) : ℝ :=
  ∑ t' ∈ Finset.Iic t, x c t'

/-- `p_{b,d,t} = p_{b,d} / (1 + r)^t` (p. 1426); index `t : Fin T` is period `t + 1`. -/
noncomputable def value (I : PCPSPC B D C T m) (b : B) (d : D) (t : Fin T) : ℝ :=
  I.p b d / (1 + I.r) ^ (t.val + 1)

/-- The objective (1), `∑_b ∑_d ∑_t p_{b,d,t} y_{b,d,t}`. -/
noncomputable def objective (I : PCPSPC B D C T m) (y : B → D → Fin T → ℝ) : ℝ :=
  ∑ b, ∑ d, ∑ t, I.value b d t * y b d t

/-- The integrality condition (7): (10) for `F`, (11) for `P` (p. 1427). -/
def IntegralityHolds (I : PCPSPC B D C T m) : Integrality → (C → Fin T → ℝ) → Prop
  | .F, x => ∀ c t, x c t = 0 ∨ x c t = 1
  | .P, x => ∀ c c', I.arc c c' → ∀ t, 0 < cum x c t → cum x c' t = 1

/-- `(x, y)` is feasible for the PCPSP-C with integrality `κ`: constraints (2)–(7), p. 1427. -/
def Feasible (I : PCPSPC B D C T m) (κ : Integrality)
    (x : C → Fin T → ℝ) (y : B → D → Fin T → ℝ) : Prop :=
  (∀ b t, x (I.clu b) t = ∑ d, y b d t) ∧
  (∀ c, ∑ t, x c t ≤ 1) ∧
  (∀ c c', I.arc c c' → ∀ t, cum x c t ≤ cum x c' t) ∧
  (∀ i, ∑ b, ∑ d, ∑ t, I.G i b d t * y b d t ≤ I.g i) ∧
  (∀ b d t, 0 ≤ y b d t) ∧
  I.IntegralityHolds κ x

/-- The mining capacity rows (8): `∑_b ∑_d q_b y_{b,d,t} ≤ U_t` (p. 1427). -/
def MiningCap (I : PCPSPC B D C T m) (y : B → D → Fin T → ℝ) : Prop :=
  ∀ t, ∑ b, ∑ d, I.q b * y b d t ≤ I.U t

/-- The destination capacity rows (9): `∑_b q_b y_{b,d,t} ≤ U_t^d` (p. 1427). -/
def DestCap (I : PCPSPC B D C T m) (y : B → D → Fin T → ℝ) : Prop :=
  ∀ d t, ∑ b, I.q b * y b d t ≤ I.Ud d t

/-- `(x, y)` is an optimal solution of the PCPSP-C with integrality `κ`: it is feasible and its
objective (1) is at least that of every feasible solution. -/
def Optimal (I : PCPSPC B D C T m) (κ : Integrality) (x : C → Fin T → ℝ)
    (y : B → D → Fin T → ℝ) : Prop :=
  I.Feasible κ x y ∧ ∀ x' y', I.Feasible κ x' y' → I.objective y' ≤ I.objective y

/-- Minimal optimal (p. 1431), for the componentwise order on `(x, y)`: every optimal `(x', y')`
with `x' ≤ x` and `y' ≤ y` equals `(x, y)`. -/
def MinimalOptimal (I : PCPSPC B D C T m) (κ : Integrality) (x : C → Fin T → ℝ)
    (y : B → D → Fin T → ℝ) : Prop :=
  I.Optimal κ x y ∧ ∀ x' y', I.Optimal κ x' y' → x' ≤ x → y' ≤ y → x' = x ∧ y' = y

/-- `p̄_c = ∑_{b ∈ c} p_{b,∗}` with `p_{b,∗} = max_{d ∈ 𝒟} p_{b,d}` (pp. 1426, 1431). -/
noncomputable def pbar [Nonempty D] (I : PCPSPC B D C T m) (c : C) : ℝ :=
  ∑ b ∈ I.blocksOf {c}, Finset.univ.sup' Finset.univ_nonempty (I.p b)

/-- Feasibility for U-PIT, constraints (13)–(14) (p. 1431): `x_c ≤ x_{c'}` for `(c, c') ∈ 𝒜`
and `x_c ∈ [0, 1]`. -/
def UPitFeasible (I : PCPSPC B D C T m) (x : C → ℝ) : Prop :=
  (∀ c c', I.arc c c' → x c ≤ x c') ∧ ∀ c, 0 ≤ x c ∧ x c ≤ 1

/-- The U-PIT objective (12), `∑_{c ∈ 𝒞} p̄_c x_c` (p. 1431). -/
noncomputable def UPitObjective [Nonempty D] (I : PCPSPC B D C T m) (x : C → ℝ) : ℝ :=
  ∑ c, I.pbar c * x c

/-- `x` is an optimal solution of the linear program U-PIT (12)–(14). -/
def UPitOptimal [Nonempty D] (I : PCPSPC B D C T m) (x : C → ℝ) : Prop :=
  I.UPitFeasible x ∧ ∀ x', I.UPitFeasible x' → I.UPitObjective x' ≤ I.UPitObjective x

/-- `x` is a minimal optimal solution of U-PIT (p. 1431): every optimal `x' ≤ x` equals `x`. -/
def UPitMinimalOptimal [Nonempty D] (I : PCPSPC B D C T m) (x : C → ℝ) : Prop :=
  I.UPitOptimal x ∧ ∀ x', I.UPitOptimal x' → x' ≤ x → x' = x

/-- The pit limit associated with `x`, `{c ∈ 𝒞 : x_c > 0}` (p. 1431). -/
def pitLimit (x : C → ℝ) : Set C := {c | 0 < x c}

/-- A pit in `𝓑` (p. 1426): `b₁ ≺ b₂ ∧ b₂ ∈ P ⇒ b₁ ∈ P`. -/
def IsPit (I : PCPSPC B D C T m) (P : Set B) : Prop :=
  ∀ b₁ b₂, I.bprec b₁ b₂ → b₂ ∈ P → b₁ ∈ P

end PCPSPC

end OpenPitMIP.UltPit


