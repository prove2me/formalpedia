-- Prove2me | Definitions.Def_MultimodularDocks_udf
-- name    : MultimodularDocks_udf
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:34:45.55898+00:00
-- url     : https://prove2.me/theorems/1df7872e-8d5f-4448-9a2b-77198b49f8bd
-- title:
--   User dissatisfaction function $c_X(d,b)$ of an arrival sequence (weighted)
-- statement:
--   A customer arriving at a station either wants to **rent** a bike ($X_t=-1$) or to **return** one ($X_t=1$). For a station that starts with $d$ empty docks and $b$ bikes and an arrival sequence $X=(X_1,\dots,X_s)$, let $\delta_{X(t)}$ be the number of open docks after the first $t$ arrivals:
--
--   $$
--   \delta_{X(0)}(d,b)=d,\qquad \delta_{X(t)}(d,b)=\max\{0,\min\{d+b,\ \delta_{X(t-1)}(d,b)-X_t\}\}.
--   $$
--
--   Customer $t$ experiences an out-of-stock event if they return a bike at a full station ($X_t=1$, $\delta_{X(t-1)}=0$) or rent a bike at an empty station ($X_t=-1$, $\delta_{X(t-1)}=d+b$). For a weight $\eta$, the **user dissatisfaction function** is
--
--   $$
--   c_X(d,b)=\bigl|\{\tau: X_\tau=1,\ \delta_{X(\tau-1)}(d,b)=0\}\bigr|+\eta\,\bigl|\{\tau: X_\tau=-1,\ \delta_{X(\tau-1)}(d,b)=d+b\}\bigr|.
--   $$
--
--   With $\eta=1$ it counts the out-of-stock events, which is the paper's main-text UDF.
--
--   **Formalization Note** Arrivals form the type `Arrival` with constructors `rent` ($-1$) and `ret` ($+1$); a sequence is a list processed from the left, carrying $(\delta,\text{cost})$. The weight $\eta$ goes on rentals at an empty station, as in the proof of Lemma 2.1 (p.39); the sentence on p.39 that attaches $\eta$ to "the first term" names the other term. The two forms are exchanged by $d\leftrightarrow b$, $X\leftrightarrow -X$.
-- source:
--   Freund, Henderson, Shmoys, Minimizing Multimodular Functions and Allocating Capacity in Bike-Sharing Systems, arXiv:1611.09304v5, §2 p.9 and App. B.1, pp.38–39 (recursive UDF definition, weighted case)

import Mathlib

namespace MultimodularDocks

/-- A customer arrival at a station (Freund, Henderson, Shmoys, arXiv:1611.09304v5, §2, p.9):
`rent` is a customer arriving to rent a bike (`X_t = −1`), `ret` a customer arriving to return
a bike (`X_t = 1`). -/
inductive Arrival
  | rent
  | ret
  deriving DecidableEq

/-- The value `X_t ∈ {±1}` of an arrival (p.9): `rent ↦ −1`, `ret ↦ 1`. -/
def Arrival.val : Arrival → ℤ
  | .rent => -1
  | .ret => 1

/-- One step of the recursive UDF (arXiv:1611.09304v5, App. B.1, pp.38–39). The state is the
pair (number `δ` of open docks, accumulated cost) after the arrivals so far, at a station with
`d` empty docks and `b` bikes initially. On arrival `x`,
`δ ← max 0 (min (d + b) (δ − x))`, and the cost grows by `1` if `x` is a return and `δ = 0`
(station full: no dock), by `η` if `x` is a rental and `δ = d + b` (station empty: no bike). -/
def udfStep (η : ℝ) (d b : ℤ) (s : ℤ × ℝ) (x : Arrival) : ℤ × ℝ :=
  (max 0 (min (d + b) (s.1 - x.val)),
   s.2 + match x with
     | .ret => if s.1 = 0 then 1 else 0
     | .rent => if s.1 = d + b then η else 0)

/-- **The (weighted) user dissatisfaction function** `c_X(d, b)` of an arrival sequence
`X = (X_1, …, X_s)` (Freund, Henderson, Shmoys, arXiv:1611.09304v5, §2 p.9 and App. B.1,
pp.38–39): starting from `δ_{X(0)}(d, b) = d` and `c_{X(0)}(d, b) = 0`,
`δ_{X(t)} = max{0, min{d + b, δ_{X(t−1)} − X_t}}` and
`c_{X(t)} = c_{X(t−1)} + 1{X_t = 1, δ_{X(t−1)} = 0} + η·1{X_t = −1, δ_{X(t−1)} = d + b}`.
`η = 1` is the unweighted UDF of the main text, which counts out-of-stock events.

**Formalization Note** The sequence is a `List Arrival` in time order, processed by `foldl`.
The weight `η` multiplies the stock-out of a renter at an empty station, as in the proof of
Lemma 2.1 (p.39, "the penalty of a stock-out is η ≥ 0 if the station is empty"); the sentence
on p.39 saying "the first term is multiplied by η" names the other term, and the two forms are
exchanged by the symmetry `d ↔ b`, `X ↔ −X`. The function is defined for all integers `d, b`;
only `d, b ≥ 0` is used. -/
def udf (η : ℝ) (d b : ℤ) (X : List Arrival) : ℝ :=
  (X.foldl (udfStep η d b) (d, 0)).2

end MultimodularDocks


