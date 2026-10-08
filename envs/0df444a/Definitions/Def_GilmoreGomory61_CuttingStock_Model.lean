-- Prove2me | Definitions.Def_GilmoreGomory61_CuttingStock_Model
-- name    : GilmoreGomory61_CuttingStock_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T07:39:37.782926+00:00
-- url     : https://prove2.me/theorems/42975e84-b2aa-40dd-94f0-b24663eb975e
-- title:
--   pp. 850–851 — cutting-stock activities and the linear-programming relaxation
-- statement:
--   A **cutting-stock instance** specifies ordered piece lengths $\ell_i$, integer demands $N_i$, stock lengths $L_j$, and costs $c_j$. A **cutting activity** chooses one stock length and nonnegative integer counts $a_i$ of pieces to cut from it, subject to
--
--   $$
--   \sum_i \ell_i a_i\le L_j.
--   $$
--
--   Each activity contributes $a_i$ to demand $i$ and costs $c_j$. There is also a zero-cost surplus column with coefficient $-1$ in each demand row. A feasible solution assigns nonnegative real weights with finite support to all activities and surplus columns such that
--
--   $$
--   \sum_p a_i(p)z_p-z_{\mathrm{surplus},i}=N_i\quad\text{for every }i.
--   $$
--
--   Its objective is the total weighted stock cost. These definitions fix the model for every pricing and optimality statement in the mission.
--
--   **Formalization Note** Indices start at zero. The zero cutting pattern is allowed. Finite support represents the paper's finite activity list while permitting every pattern allowed by its length inequality. The variables are real because the paper drops integrality on p. 851. The bin-packing configuration LP `KKBinPacking.Shared.ConfigLP` is a one-stock, unit-cost special case and is not used here.
-- source:
--   Gilmore and Gomory, A linear programming approach to the cutting-stock problem, Oper. Res. 9(6) (1961), pp. 850–851, (1)–(3)

import Mathlib

namespace GilmoreGomory61.CuttingStock

/-- The ordered piece lengths, demands, stock lengths, and stock costs on p. 850. -/
structure Instance (m k : ℕ) where
  ℓ : Fin m → ℝ
  N : Fin m → ℕ
  L : Fin k → ℝ
  c : Fin k → ℝ

/-- The length consumed by the pattern in (6). -/
def patLen {m k : ℕ} (I : Instance m k) (a : Fin m → ℕ) : ℝ :=
  ∑ i, I.ℓ i * (a i : ℝ)

/-- A stock length together with a nonnegative integer cutting pattern fitting that stock. -/
def Activity {m k : ℕ} (I : Instance m k) :=
  {p : Fin k × (Fin m → ℕ) // patLen I p.2 ≤ I.L p.1}

/-- Activity columns and the surplus variables of (2). -/
def Col {m k : ℕ} (I : Instance m k) := Activity I ⊕ Fin m

/-- The coefficient column in (2): activity counts or a surplus column `-eᵢ`. -/
def colVec {m k : ℕ} (I : Instance m k) : Col I → Fin m → ℝ
  | Sum.inl p => fun i => (p.1.2 i : ℝ)
  | Sum.inr i' => fun i => if i = i' then -1 else 0

/-- Cost coefficient in (1); surplus variables have zero cost. -/
def colCost {m k : ℕ} (I : Instance m k) : Col I → ℝ
  | Sum.inl p => I.c p.1.1
  | Sum.inr _ => 0

/-- The real relaxation of (2)–(3), with finitely supported column weights. -/
def Feasible {m k : ℕ} (I : Instance m k) (z : Col I →₀ ℝ) : Prop :=
  (∀ j, 0 ≤ z j) ∧
  ∀ i, (z.sum fun j v => colVec I j i * v) = (I.N i : ℝ)

/-- Objective (1) on a finitely supported solution. -/
def cost {m k : ℕ} (I : Instance m k) (z : Col I →₀ ℝ) : ℝ :=
  z.sum fun j v => colCost I j * v

end GilmoreGomory61.CuttingStock


