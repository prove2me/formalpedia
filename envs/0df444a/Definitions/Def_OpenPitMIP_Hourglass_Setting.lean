-- Prove2me | Definitions.Def_OpenPitMIP_Hourglass_Setting
-- name    : OpenPitMIP_Hourglass_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T10:55:47.798668+00:00
-- url     : https://prove2.me/theorems/56645ddb-fe3d-4ac1-9969-b4dbe598706d
-- title:
--   §2.1, §5 and §5.2, pp. 1426–1435 — the PCPSP-C (1)–(7), integrality (10)/(11), capacities (8)/(9), w, q(S), cl, rcl, the set MK (24)–(28) and the hourglass sums
-- statement:
--   This file fixes the model of the **precedence-constrained production scheduling problem with clusters** (PCPSP-C) of Rivera Letelier, Espinoza, Goycoolea, Moreno and Muñoz, the **mode-knapsack set** MK, and the sums used by their hourglass production cuts.
--
--   **Instance.** There are finite sets $\mathcal B$ of blocks, $\mathcal D$ of destinations and $\mathcal C$ of clusters, and periods $\mathcal T=\{1,\dots,T\}$. Each block $b$ lies in the cluster $c(b)$. A precedence relation $b_1\prec b_2$ on blocks induces one on clusters: $c_1\prec c_2$ if some block of $c_1$ precedes some block of $c_2$. The arc set $\mathcal A$ is the transitive reduction of $\prec$ on clusters: $(c,c')\in\mathcal A$ iff $c'\prec c$ and no $c''$ satisfies $c'\prec c''\prec c$. Each block has values $p_{b,d}$, discounted as $p_{b,d,t}=p_{b,d}/(1+r)^t$, and a weight $q_b$; $U_t$ and $U^d_t$ are the mining and destination capacities, and $Gy\le g$ are $m$ general side constraints.
--
--   **Standing assumptions** (§2.1, p. 1426): the clusters partition $\mathcal B$ (each cluster is nonempty), $\prec$ induces a strict partial order on clusters, $r>0$, and $q_b\ge 0$.
--
--   **Feasibility.** $(x,y)$ is feasible for the PCPSP-C with integrality condition $\kappa$ when
--   $$x_{c(b),t}=\sum_{d}y_{b,d,t},\quad \sum_t x_{c,t}\le 1,\quad \sum_{t'=1}^{t}x_{c,t'}\le\sum_{t'=1}^{t}x_{c',t'}\ ((c,c')\in\mathcal A),\quad Gy\le g,\quad y\ge 0,$$
--   together with **full integrality** (10) $x_{c,t}\in\{0,1\}$ (the PCPSP-F) or **partial integrality** (11): $\sum_{t'\le t}x_{c,t'}>0$ implies $\sum_{t'\le t}x_{c',t'}=1$ for $(c,c')\in\mathcal A$ (the PCPSP-P). The **mining capacity rows** (8) are $\sum_b\sum_d q_b y_{b,d,t}\le U_t$ and the **destination capacity rows** (9) are $\sum_b q_b y_{b,d,t}\le U^d_t$.
--
--   **Derived quantities.** $w_{c,t}=\sum_{t'=1}^{t}x_{c,t'}$ (17); $cl(c)=\{c\}\cup\{c':c'\prec c\}$, $rcl(c)=\{c\}\cup\{c':c\prec c'\}$; $b(S)$ the blocks on a set $S$ of clusters and $q(S)=\sum_{b\in b(S)}q_b$. For a set $S$ of **blocks**, as in Theorem 8, $q(S)=\sum_{b\in S}q_b$. Finally $\sum_{s=t_1}^{t}y_{b,d,s}$ and $\sum_{s=t_1}^{t}U^d_s$ are the shipments of block $b$ to $d$ and the capacity of $d$ over periods $t_1,\dots,t$.
--
--   **The set MK** (§5.2.1, p. 1433). Given a directed acyclic graph $G=(\mathcal B,\mathcal A)$, weights $q\in\mathbb R^{\mathcal B}$ and a capacity $U$, a vector $(x,y^P,y^W)\in\mathbb R^{\mathcal B}\times\mathbb R^{\mathcal B}\times\mathbb R^{\mathcal B}$ lies in MK iff
--   $$\sum_{b}q_b y^P_b\le U,\quad y^P_b+y^W_b=x_b,\quad x_b\le 1,\quad x_b>0\Rightarrow x_{b'}=1\ ((b,b')\in\mathcal A),\quad y^P_b,y^W_b\ge 0.$$
--   In MK, $b'\prec b$ means that $G$ has a directed path from $b$ to $b'$, and $cl(b)$, $rcl(b)$ are defined from this order.
--
--   These objects are the common language of the production cuts of §5.2.
--
--   **Formalization Note** Periods are `Fin T`, index $t$ standing for period $t+1$. Cluster precedence is derived from the block relation, as on p. 1426, and $\mathcal A$ is its covering relation. In MK an arc `A b b'` is $(b,b')\in\mathcal A$, so $b'$ is a predecessor of $b$; the hypotheses that $G$ is acyclic, $q>0$ and $U>0$ are binders of the theorems about MK, not part of the definition.
-- source:
--   Oper. Res. 68(5), §2.1 (pp. 1426–1427), (1)–(11); §5 preamble (p. 1432), (17), b(C), q(S), cl, rcl; §5.2.1 (p. 1433), MK (24)–(28); §5.2.3 (p. 1435), Theorem 8 notation

import Mathlib

namespace OpenPitMIP.Hourglass

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

end PCPSPC

/-- The mode-knapsack mixed-integer set MK, (24)–(28), p. 1433. `A b b'` is the arc `(b, b') ∈ 𝒜`
of the DAG `G = (𝓑, 𝒜)`; `b'` is then a precedent of `b`. A point is `(x, y^P, y^W)`. -/
def MK {B : Type} [Fintype B] (A : B → B → Prop) (q : B → ℝ) (U : ℝ) :
    Set ((B → ℝ) × (B → ℝ) × (B → ℝ)) :=
  {v | ∑ b, q b * v.2.1 b ≤ U ∧
    (∀ b, v.2.1 b + v.2.2 b = v.1 b) ∧
    (∀ b, v.1 b ≤ 1) ∧
    (∀ b b', A b b' → 0 < v.1 b → v.1 b' = 1) ∧
    (∀ b, 0 ≤ v.2.1 b ∧ 0 ≤ v.2.2 b)}

/-- Precedence in MK: `b' ≺ b` iff there is a directed path from `b` to `b'` in `𝒜`. -/
def mkPrec {B : Type} (A : B → B → Prop) (b' b : B) : Prop :=
  Relation.TransGen A b b'

open Classical in
/-- `rcl(b) = {b} ∪ {b' : b ≺ b'}` in the DAG. -/
noncomputable def mkRcl {B : Type} [Fintype B] (A : B → B → Prop) (b : B) : Finset B :=
  Finset.univ.filter (fun b' => b' = b ∨ mkPrec A b b')

open Classical in
/-- `cl(b) = {b} ∪ {b' : b' ≺ b}` in the DAG. -/
noncomputable def mkCl {B : Type} [Fintype B] (A : B → B → Prop) (b : B) : Finset B :=
  Finset.univ.filter (fun b' => b' = b ∨ mkPrec A b' b)

namespace PCPSPC

variable {B D C : Type} [Fintype B] [Fintype D] [Fintype C] {T m : ℕ}

/-- The weight of a set of blocks, `q(S) = ∑_{b ∈ S} q_b`. In Theorem 8 (p. 1435) `S` is a set of
blocks and `q(S ∪ {c̄})` is the weight of the blocks of `S` together with the blocks of `c̄`. -/
noncomputable def qBlocks (I : PCPSPC B D C T m) (S : Finset B) : ℝ :=
  ∑ b ∈ S, I.q b

/-- `∑_{s=t₁}^{t} y_{b,d,s}`, the amount of block `b` sent to destination `d` in periods
`t₁, …, t` (p. 1435). -/
def ySum (y : B → D → Fin T → ℝ) (b : B) (d : D) (t₁ t : Fin T) : ℝ :=
  ∑ s ∈ Finset.Icc t₁ t, y b d s

/-- `∑_{s=t₁}^{t} U_s^d`, the capacity of destination `d` over periods `t₁, …, t` (p. 1435). -/
def Ucum (I : PCPSPC B D C T m) (d : D) (t₁ t : Fin T) : ℝ :=
  ∑ s ∈ Finset.Icc t₁ t, I.Ud d s

end PCPSPC

end OpenPitMIP.Hourglass


