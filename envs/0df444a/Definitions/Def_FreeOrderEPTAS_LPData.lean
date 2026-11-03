-- Prove2me | Definitions.Def_FreeOrderEPTAS_LPData
-- name    : FreeOrderEPTAS_LPData
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:24:20.43204+00:00
-- url     : https://prove2.me/theorems/1cc94926-e256-41cc-8740-c77b215ad63b
-- title:
--   The linear program (LP) as data
-- statement:
--   The linear feasibility problem (LP) has a variable $y_{(i,t),j}$ for each machine $i$, class $t$ and job $j\in J_t$:
--   $$\text{(S1) } y_{(i,t),j}\in[0,1],\quad \text{(S2) }\sum_{i}y_{(i,\rho(j)),j}\le1,\quad \text{(S3) }\sum_{j\in J_t}y_{(i,t),j}\in[N^\downarrow_{it},N^\uparrow_{it}],$$
--   $$\text{(S4) }\sum_{j\in J_t}\ell_{ijd}\,y_{(i,t),j}\ge(1-\xi)\,S^\downarrow_{idt}\quad(d\in A_i,\ \mathcal T^{(t)}_{id}=0).$$
--   `LPData` records the data of such a problem, and `Vars`, `S1`–`S4`, `MeetsS123`, `Feasible` and `size` are read from it. The size is the number of variables, plus constraints, plus coefficients.
--
--   This is the common input of the LP solver and of the dependent rounding.
--
--   **Formalization Note** Job $j$ meets exactly one pair-vertex per machine, namely $(i,\rho(j))$, so the variable is written `y i j` and $J_t=\{j:\rho(j)=t\}$.
-- source:
--   Segev & Singla, Efficient Approximation Schemes for Stochastic Probing and Selection-Stopping Problems, arXiv:2007.13121v3, §2.4, p.11

import Mathlib
import Definitions.Def_FreeOrderEPTAS_SCInstance

namespace FreeOrderEPTAS

/-- The linear feasibility problem (LP) of §2.4 (arXiv:2007.13121v3, p.11) as data.

**Formalization Note.** Job `j` is joined to exactly one pair-vertex `(i, t)` for each machine `i`,
namely `t = ρ(j)` (p.11), so the variable `y_{(i,t),j}` with `j ∈ J_t` is written `y i j`, and
`J_t = {j : ρ j = t}`. `small i d t` is the side condition `d ∈ A_i, T^(t)_id = 0` of (S4). -/
structure LPData where
  /-- Machines. -/
  m : ℕ
  /-- Dimensions. -/
  D : ℕ
  /-- Jobs. -/
  n : ℕ
  /-- Classes. -/
  T : ℕ
  /-- The class `ρ(j)` of job `j`. -/
  ρ : Fin n → Fin T
  /-- The loads `ℓ_ijd`. -/
  ℓ : Fin m → Fin n → Fin D → ℝ
  /-- The triples constrained by (S4). -/
  small : Fin m → Fin D → Fin T → Bool
  /-- The lower bounds `N↓_it`. -/
  Nlo : Fin m → Fin T → ℕ
  /-- The upper bounds `N↑_it`. -/
  Nhi : Fin m → Fin T → ℕ
  /-- The small-load guesses `S↓_idt`. -/
  Slo : Fin m → Fin D → Fin T → ℝ
  /-- The parameter `ξ`. -/
  ξ : ℝ

namespace LPData

/-- The variables `y_{(i,ρ(j)),j}`. -/
abbrev Vars (P : LPData) : Type := Fin P.m → Fin P.n → ℝ

/-- (S1): `y_{(i,t),j} ∈ [0, 1]`. -/
def S1 (P : LPData) (y : P.Vars) : Prop :=
  ∀ i j, y i j ∈ Set.Icc (0 : ℝ) 1

/-- (S2): `∑_{i ∈ [m]} y_{(i,ρ(j)),j} ≤ 1`. -/
def S2 (P : LPData) (y : P.Vars) : Prop :=
  ∀ j, ∑ i, y i j ≤ 1

/-- (S3): `∑_{j ∈ J_t} y_{(i,t),j} ∈ [N↓_it, N↑_it]`. -/
def S3 (P : LPData) (y : P.Vars) : Prop :=
  ∀ i t, (∑ j with P.ρ j = t, y i j) ∈ Set.Icc (P.Nlo i t : ℝ) (P.Nhi i t : ℝ)

/-- (S4): `∑_{j ∈ J_t} ℓ_ijd y_{(i,t),j} ≥ (1 - ξ) · S↓_idt` on the small triples. -/
def S4 (P : LPData) (y : P.Vars) : Prop :=
  ∀ i d t, P.small i d t = true → (1 - P.ξ) * P.Slo i d t ≤ ∑ j with P.ρ j = t, P.ℓ i j d * y i j

/-- A vector meeting (S1)–(S3), the hypothesis of the rounding (p.12). -/
def MeetsS123 (P : LPData) (y : P.Vars) : Prop :=
  P.S1 y ∧ P.S2 y ∧ P.S3 y

/-- A feasible solution of (LP). -/
def Feasible (P : LPData) (y : P.Vars) : Prop :=
  P.MeetsS123 y ∧ P.S4 y

/-- The instance size: variables, plus constraints of (S1)–(S4), plus coefficients. -/
def size (P : LPData) : ℕ :=
  P.m * P.n + (P.m * P.n + P.n + P.m * P.T + P.m * P.D * P.T) + P.m * P.n * (P.D + 2)

end LPData

/-- The real vector of a rounded binary vector. -/
def toVars (P : LPData) (Y : Assignment P.m P.n) : P.Vars :=
  fun i j => bit (Y i j)

end FreeOrderEPTAS


