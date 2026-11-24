-- Prove2me | Definitions.Def_ShapeMoment_LogConcave_Supplement_IFRModel
-- name    : ShapeMoment_LogConcave_Supplement_IFRModel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T22:08:30.136396+00:00
-- url     : https://prove2.me/theorems/ba4d143e-6409-41ab-a96d-ba1fbbec1df4
-- title:
--   (5a)–(5e), p. 7 — the tail-coordinate IFR moment problem (DMP-IFR′)
-- statement:
--   Fix $n,m\in\mathbb N$, moments $q_0,\dots,q_m\in\mathbb R$, objective coefficients $f_1,\dots,f_n\in\mathbb R$, and support points $w_j=j$ with $w_0^i=0$ for every $i$. The problem (DMP-IFR′) in tail coordinates $y=(y_1,\dots,y_n)$, with $y_{n+1}=0$, is
--   $$\max_{y\in\mathbb R^n}\ \sum_{j=1}^n f_j\,(y_j-y_{j+1})$$
--   subject to
--   1. (5b) $\sum_{j=1}^n (w_j^i-w_{j-1}^i)\,y_j=q_i$ for $i\in[0,m]$;
--   2. (5c) $y_{j-1}y_{j+1}\le y_j^2$ for $j\in(1,n)$;
--   3. (5d) $y_j-y_{j+1}\ge 0$ for $j\in[1,n)$;
--   4. (5e) $y_j\ge 0$ for $j\in[1,n]$.
--
--   A feasible maximizer is a feasible $y$ whose objective value is at least that of every feasible point. With $y_j=\sum_{k\ge j}x_k$ this is the moment problem over IFR distributions (Lemma 2.6).
--
--   **Formalization Note** The convention $w_0^i=0$ is applied at every order, including $i=0$, so the zeroth equation reads $y_1=q_0$ (Lean's $0^0=1$ is not used). Indices are one-based through the zero extension of the base mission (`ext`), so $y_0=y_{n+1}=0$.
-- source:
--   Chen, He, Jiang, Ryan & Zhang, The discrete moment problem with nonconvex shape constraints, arXiv:1708.02079v1, p. 7, (DMP-IFR′), (5a)–(5e), and the convention 'f_0, w_0 are set to 0'

import Definitions.Def_ShapeMoment_LogConcave_DiscreteMoment

open scoped BigOperators

namespace ShapeMoment.LogConcave.Supplement

/-- The coefficient `w_j^i - w_{j-1}^i` of `y_j` in (5b), with the paper's convention
`w_0^i = 0` for every `i` (including `i = 0`). Here `w j = j.val + 1`, so
`w_{j-1} = j.val` for `j.val ≥ 1`. -/
def ifrCoeff {n : ℕ} (i : ℕ) (j : Fin n) : ℝ :=
  w j ^ i - (if j.val = 0 then 0 else (j.val : ℝ) ^ i)

/-- Feasible region of (DMP-IFR′), constraints (5b)–(5e), in tail coordinates
`y_1, …, y_n` (one-based through `ext`, so `y_0 = y_{n+1} = 0`). -/
def feasIFRPrime (n m : ℕ) (q : ℕ → ℝ) : Set (Fin n → ℝ) :=
  {y | (∀ i ≤ m, ∑ j, ifrCoeff i j * y j = q i) ∧
    (∀ j : ℕ, 1 < j → j < n → ext y (j - 1) * ext y (j + 1) ≤ ext y j ^ 2) ∧
    (∀ j : ℕ, 1 ≤ j → j < n → 0 ≤ ext y j - ext y (j + 1)) ∧
    (∀ j, 0 ≤ y j)}

/-- The objective (5a), `∑_{j=1}^n f_j (y_j - y_{j+1})` with `y_{n+1} = 0`. -/
def ifrObjective {n : ℕ} (f : Fin n → ℝ) (y : Fin n → ℝ) : ℝ :=
  ∑ j : Fin n, f j * (ext y (j.val + 1) - ext y (j.val + 2))

/-- A feasible maximizer of the objective (5a) over `S`. -/
def IsIFRMaxSol {n : ℕ} (f : Fin n → ℝ) (S : Set (Fin n → ℝ))
    (y : Fin n → ℝ) : Prop :=
  y ∈ S ∧ ∀ z ∈ S, ifrObjective f z ≤ ifrObjective f y

end ShapeMoment.LogConcave.Supplement


