-- Prove2me | Definitions.Def_PochetWolsey_BacklogStartup_Horizon
-- name    : PochetWolsey_BacklogStartup_Horizon
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T02:29:40.956993+00:00
-- url     : https://prove2.me/theorems/3ce194fb-9b3e-4c5f-8c6d-ae22576c530e
-- title:
--   Finite-horizon coordinates and binary decisions
-- statement:
--   Let $n$ be a finite horizon. A period vector has $n$ real coordinates, labelled $1,\ldots,n$; a stock vector has $n+1$ real coordinates, labelled $0,\ldots,n$. Extend each by zero outside its index range. For a demand vector $d$, put
--   $$d_{kl}=\sum_{t=k}^l d_t.$$
--   A binary vector has every coordinate in $\{0,1\}$, and a unit-box vector has every coordinate in $[0,1]$.
--
--   These conventions supply the common finite-dimensional coordinates for the start-up and joint formulations.
--
--   **Formalization Note** The arrays use `Fin n` and `Fin (n+1)`. The period accessor shifts Lean's zero-based array index by one. Empty interval sums are zero; all out-of-range accessors return zero. The separate setup accessor uses the given initial state $y_0$ at time zero. Switch-off arrays are labelled $0,\ldots,n-1$, so $w_0$ is a decision coordinate.
-- source:
--   Pochet and Wolsey, Production Planning by Mixed Integer Programming, Springer 2006, pp. 304, 319, 330–331 (PDF 317, 332, 343–344), Sections 10.1, 10.4, 10.6; initial setup datum: p. 138 (PDF 155), Section 4.3.6

import Mathlib

namespace PochetWolsey.BacklogStartup

noncomputable section

/-- A period vector has coordinates 1,...,n; its extension is zero elsewhere. -/
def period {n : ℕ} (v : Fin n → ℝ) (t : ℕ) : ℝ :=
  if h : 1 ≤ t ∧ t ≤ n then v ⟨t - 1, by omega⟩ else 0

/-- Setup state at time zero is input data (printed p. 138), not a zero default. -/
def setupState {n : ℕ} (y0 : ℝ) (y : Fin n → ℝ) (t : ℕ) : ℝ :=
  if t = 0 then y0 else period y t

/-- Switch-offs are indexed 0,...,n-1, as required by w_(t-1) for t=1,...,n. -/
def switchOff {n : ℕ} (w : Fin n → ℝ) (t : ℕ) : ℝ :=
  period w (t + 1)

/-- A stock vector has coordinates 0,...,n. -/
def stock {n : ℕ} (v : Fin (n + 1) → ℝ) (t : ℕ) : ℝ :=
  if h : t ≤ n then v ⟨t, by omega⟩ else 0

def demandSum {n : ℕ} (d : Fin n → ℝ) (k l : ℕ) : ℝ :=
  ∑ t ∈ Finset.Icc k l, period d t

def Binary {n : ℕ} (v : Fin n → ℝ) : Prop := ∀ t, v t = 0 ∨ v t = 1

def UnitBox {n : ℕ} (v : Fin n → ℝ) : Prop := ∀ t, 0 ≤ v t ∧ v t ≤ 1

end
end PochetWolsey.BacklogStartup


