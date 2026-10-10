-- Prove2me | Definitions.Def_OpenPitMIP_Extraction_Setting
-- name    : OpenPitMIP_Extraction_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T13:42:49.253332+00:00
-- url     : https://prove2.me/theorems/acadea2a-e594-42f4-a6a1-e1dbf5934d75
-- title:
--   §2.1 and §5, pp. 1426–1433 — the PCPSP-C (1)–(7), integrality (10)/(11), capacities (8)/(9), w, q(S), cl, Q_t and f-/p-incompatibility
-- statement:
--   This file fixes the model of the **precedence-constrained production scheduling problem with clusters** (PCPSP-C) of Rivera Letelier, Espinoza, Goycoolea, Moreno and Muñoz, and the quantities used by their extraction cuts.
--
--   **Instance.** There are finite sets $\mathcal B$ of blocks, $\mathcal D$ of destinations and $\mathcal C$ of clusters, and periods $\mathcal T=\{1,\dots,T\}$. Each block $b$ lies in the cluster $c(b)$. A precedence relation $b_1\prec b_2$ ("$b_1$ must be extracted no later than $b_2$") is given on blocks, and induces one on clusters: $c_1\prec c_2$ if some block of $c_1$ precedes some block of $c_2$. The arc set $\mathcal A$ is the transitive reduction of $\prec$ on clusters: $(c,c')\in\mathcal A$ iff $c'\prec c$ and no $c''$ satisfies $c'\prec c''\prec c$. Each block has values $p_{b,d}$, discounted as $p_{b,d,t}=p_{b,d}/(1+r)^t$, and a weight $q_b$; $U_t$ and $U^d_t$ are the mining and destination capacities, and $Gy\le g$ are $m$ general side constraints.
--
--   **Standing assumptions** (§2.1, p. 1426): the clusters partition $\mathcal B$ (each cluster is nonempty), $\prec$ induces a strict partial order on clusters, $r>0$, and $q_b\ge 0$.
--
--   **Feasibility.** $(x,y)$ is feasible for the PCPSP-C with integrality condition $\kappa$ when
--   $$x_{c(b),t}=\sum_{d}y_{b,d,t},\quad \sum_t x_{c,t}\le 1,\quad \sum_{t'=1}^{t}x_{c,t'}\le\sum_{t'=1}^{t}x_{c',t'}\ ((c,c')\in\mathcal A),\quad Gy\le g,\quad y\ge 0,$$
--   together with **full integrality** (10) $x_{c,t}\in\{0,1\}$ (the PCPSP-F) or **partial integrality** (11): $\sum_{t'\le t}x_{c,t'}>0$ implies $\sum_{t'\le t}x_{c',t'}=1$ for $(c,c')\in\mathcal A$ (the PCPSP-P). The **mining capacity rows** (8) are $\sum_b\sum_d q_b y_{b,d,t}\le U_t$ and the destination rows (9) are $\sum_b q_b y_{b,d,t}\le U^d_t$.
--
--   **Derived quantities.** $w_{c,t}=\sum_{t'=1}^{t}x_{c,t'}$ (17); $cl(c)=\{c\}\cup\{c':c'\prec c\}$, $rcl(c)=\{c\}\cup\{c':c\prec c'\}$, $cl(S)=\bigcup_{c\in S}cl(c)$; $b(S)$ the blocks on $S$ and $q(S)=\sum_{b\in b(S)}q_b$; $Q_t=\sum_{t'=1}^{t}U_{t'}$ and $Q_{t_1,t_2}=\sum_{t'=t_1}^{t_2}U_{t'}$. Two clusters $c_1,c_2$, neither preceding the other, are **f-incompatible** in time $t$ if $q(cl(\{c_1,c_2\}))>Q_t$ and **p-incompatible** in time $t$ if $q(cl(\{c_1,c_2\})\setminus\{c_1,c_2\})>Q_t$.
--
--   These objects are the common language of every extraction cut of §5.1.
--
--   **Formalization Note** Periods are `Fin T`, index $t$ standing for period $t+1$. The paper never defines the closure of a set of clusters; it is taken as the union $cl(c_1)\cup cl(c_2)$. Incomparability of $c_1,c_2$ is part of the definition of incompatibility, as the page defines incompatibility only for such pairs. Cluster precedence is derived from the block relation, as on p. 1426.
-- source:
--   Oper. Res. 68(5), §2.1 (pp. 1426–1427), (1)–(11); §5 preamble (p. 1432), (17), b(C), q(S), cl, rcl; Theorems 2–3 (pp. 1432–1433), Q_t, Q_{t1,t2}; §5.1.3 (p. 1433), f-/p-incompatibility

import Mathlib
import Definitions.Def_OpenPitMIP_UltPit_Setting

namespace OpenPitMIP.Extraction

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
def IntegralityHolds (I : PCPSPC B D C T m) : OpenPitMIP.UltPit.Integrality → (C → Fin T → ℝ) → Prop
  | .F, x => ∀ c t, x c t = 0 ∨ x c t = 1
  | .P, x => ∀ c c', I.arc c c' → ∀ t, 0 < cum x c t → cum x c' t = 1

/-- `(x, y)` is feasible for the PCPSP-C with integrality `κ`: constraints (2)–(7), p. 1427. -/
def Feasible (I : PCPSPC B D C T m) (κ : OpenPitMIP.UltPit.Integrality)
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

namespace PCPSPC

variable {B D C : Type} [Fintype B] [Fintype D] [Fintype C] {T m : ℕ}

/-- `Q_t = ∑_{t'=1}^{t} U_{t'}`, the cumulative mining capacity up to period `t` (Theorem 2,
p. 1432); index `t : Fin T` is period `t + 1`. -/
def Qcum (I : PCPSPC B D C T m) (t : Fin T) : ℝ :=
  ∑ t' ∈ Finset.Iic t, I.U t'

/-- `Q_{t₁,t₂} = ∑_{t'=t₁}^{t₂} U_{t'}`, the mining capacity of periods `t₁` through `t₂`
(Theorem 3, p. 1433). -/
def Qint (I : PCPSPC B D C T m) (t₁ t₂ : Fin T) : ℝ :=
  ∑ t' ∈ Finset.Icc t₁ t₂, I.U t'

/-- `c₁` and `c₂` are f-incompatible in time `t` (§5.1.3, p. 1433): neither precedes the other,
and `q(cl({c₁, c₂})) > Q_t`, where `cl({c₁, c₂}) = cl(c₁) ∪ cl(c₂)`. -/
def FIncompatible [DecidableEq C] (I : PCPSPC B D C T m) (t : Fin T) (c₁ c₂ : C) : Prop :=
  ¬ I.cprec c₁ c₂ ∧ ¬ I.cprec c₂ c₁ ∧ I.Qcum t < I.qSet (I.clSet {c₁, c₂})

/-- `c₁` and `c₂` are p-incompatible in time `t` (§5.1.3, p. 1433): neither precedes the other,
and `q(cl({c₁, c₂}) \ {c₁, c₂}) > Q_t`. -/
def PIncompatible [DecidableEq C] (I : PCPSPC B D C T m) (t : Fin T) (c₁ c₂ : C) : Prop :=
  ¬ I.cprec c₁ c₂ ∧ ¬ I.cprec c₂ c₁ ∧ I.Qcum t < I.qSet (I.clSet {c₁, c₂} \ {c₁, c₂})

end PCPSPC

end OpenPitMIP.Extraction


