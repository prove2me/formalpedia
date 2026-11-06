-- Prove2me | Definitions.Def_FracTruthSched_FracMech
-- name    : FracTruthSched_FracMech
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:28:14.958233+00:00
-- url     : https://prove2.me/theorems/487703e7-392e-4963-a328-ee91cd47c2d1
-- title:
--   Deterministic fractional mechanism $(x,P)$ on $n$ machines
-- statement:
--   There are $n$ machines and a finite set of tasks. An **input** $t=(t_{ij})$ gives each machine $i$ a value (processing time) $t_{ij}$ for each task $j$; the row $t_i$ is machine $i$'s private type. A **deterministic fractional mechanism** consists of an **allocation function** $x$, which assigns to every input $t$ a fraction $x_{ij}(t)$ of each task $j$ to each machine $i$, and **payments** $P_i(t)$ to every machine $i$.
--
--   Machine $i$'s utility at input $t$ is its payment minus its processing cost, $P_i(t)-t_i\cdot x_i(t)$ with $t_i\cdot x_i(t)=\sum_j t_{ij}x_{ij}(t)$.
--
--   This is the object of the paper's lower bound: no continuity, task independence or other regularity is assumed of $x$ or $P$, and payments may have any sign.
--
--   **Formalization Note.** Machines are `Fin n`, tasks a type `τ` (`Fin m`, or the core tasks of $MC_\ell$). Both functions are total on real matrices; that $x$ is a fractional allocation is the separate predicate `IsFeasibleOn`, imposed only on admissible inputs.
-- source:
--   Anastasiadis et al., Tight bounds for fractional and randomized truthful scheduling, arXiv:2611.06642v1, §2.1, p.3

import Mathlib

set_option autoImplicit false

namespace FracTruthSched

/-- A **deterministic fractional mechanism** on `n` machines with task set `τ`
(Anastasiadis et al., *Tight bounds for fractional and randomized truthful scheduling*,
arXiv:2611.06642v1, §2.1, p.3): an allocation function `x` assigning to every input `t` and every
machine `i` the fraction `x t i j` of task `j` given to `i`, and a payment function `P`, `P t i`
being the payment to machine `i`. An input `t : Fin n → τ → ℝ` has row `t i` = the type (values)
of machine `i`.

**Formalization Note.** Machines are `Fin n` (0-based), tasks the type `τ` (`Fin m` for an input
with `m` tasks; the core tasks of `MC_ℓ` for graph inputs). Both functions are total; that the
allocation is a fractional allocation is the separate predicate `IsFeasibleOn`, imposed only on the
admissible inputs (nonnegative, §2.2, p.4). Payments are arbitrary real numbers, of any sign. -/
structure FracMech (n : ℕ) (τ : Type*) where
  /-- the allocation function `x_ij(t)` -/
  x : (Fin n → τ → ℝ) → Fin n → τ → ℝ
  /-- the payments `P_i(t)` -/
  P : (Fin n → τ → ℝ) → Fin n → ℝ

end FracTruthSched


