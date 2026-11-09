-- Prove2me | Definitions.Def_OnlineCarpoolingLei_Oblivious_Model
-- name    : OnlineCarpoolingLei_Oblivious_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:41:13.651395+00:00
-- url     : https://prove2.me/theorems/4abf595c-9e29-4430-a69e-13926afb9159
-- title:
--   Online carpooling model: edges, signed trajectories, $M_T$, receiving gap, online rules on a uniform tape
-- statement:
--   Let $n\ge2$ and $[n]=\{1,\dots,n\}$. An **edge** is an ordered pair $(u,v)$ of distinct vertices, represented by the vector $e=\mathbf 1_u-\mathbf 1_v\in\mathbb Z^n$; repetitions and parallel edges are allowed. Write $\langle x,y\rangle=\sum_i x(i)y(i)$, $\|x\|^2=\langle x,x\rangle$ and, for $S\subseteq[n]$, $x(S)=\sum_{i\in S}x(i)$. An edge **crosses** $S$ if exactly one of its endpoints lies in $S$.
--
--   Given edges $e_1,e_2,\dots$ and signs $\varepsilon_t\in\{-1,+1\}$, the **discrepancy trajectory** is
--   $$d_0=0,\qquad d_t=d_{t-1}+\varepsilon_t e_t\quad(t\ge1),$$
--   so $d_t\in\mathbb Z^n$. The quantity of interest is
--   $$M_T=\max_{0\le t\le T}\|d_t\|_\infty .$$
--   The **receiver** $a_t$ and **sender** $b_t$ are defined by $\varepsilon_t e_t=\mathbf 1_{a_t}-\mathbf 1_{b_t}$, and the **receiving gap** of a trajectory is $\max_{1\le t\le T}\big(d_t(a_t)-d_t(b_t)\big)$, measured after the update.
--
--   A **randomized online algorithm** is a rule that, at step $t$, sees only the edges $e_1,\dots,e_t$ revealed so far and the values $U_1,\dots,U_t$ of a tape of independent random variables uniform on $[0,1)$, and outputs the sign $\varepsilon_t$; it never revises earlier signs, and it takes no horizon $T$ as input. The rule is required to be measurable in the tape values. An oblivious input is fixed in advance, so all probabilities are over the tape only.
--
--   These objects are the setting of every statement of the mission: Theorem 1.2 bounds $M_T$ for such an algorithm, Proposition 3.4 bounds the receiving gap of the algorithm of Section 3, and Lemmas 4.1–4.2 analyse arbitrary trajectories with a bounded receiving gap.
--
--   **Formalization Note** Vertices are `Fin n`. An input is an infinite sequence `E : ℕ → Edge n` and `E t` is the paper's $e_{t+1}$ (likewise `ε t` is $\varepsilon_{t+1}$ and `u t` is $U_{t+1}$); a finite input $e_1,\dots,e_T$ is its first $T$ entries. The rule's step $t+1$ receives `Fin (t+1)`-indexed prefixes, so causality and horizon independence hold by construction. $M_T$ is a natural number. `IsUniformTape P U` says the $U_t$ are measurable, mutually independent, and each has law the Lebesgue measure on $[0,1)$.
-- source:
--   Yuhao Lei, STOC 2027 submission #416 (October 2026), Section 1.1 (1.1)–(1.2), p.2 (PDF p.2); Section 2 and (2.1), pp.4–5 (PDF pp.4–5); Section 3.2, p.6 (PDF p.6)

import Mathlib

/-!
Yuhao Lei, *Online carpooling against an oblivious adversary*, STOC 2027 submission #416
(October 2026), §1.1 (p.2), §2 (pp.4–5), §3.2 (p.6): edges, signed trajectories, the
maximum discrepancy `M_T`, the receiving gap, and randomized online algorithms driven by a
uniform tape.

Indexing convention: an input is a sequence `E : ℕ → Edge n`, and `E t` is the paper's
edge `e_{t+1}`; likewise `ε t` is the sign `ε_{t+1}` and the tape value `u t` is `U_{t+1}`.
The discrepancy after `t` edges is `traj E ε t`, the paper's `d_t`.
-/

namespace OnlineCarpoolingLei.Oblivious

open MeasureTheory ProbabilityTheory

/-- An edge on `[n]` (encoded as `Fin n`): an ordered pair of distinct vertices `u ≠ v`. -/
structure Edge (n : ℕ) where
  u : Fin n
  v : Fin n
  ne : u ≠ v

/-- The integer edge vector `e = 1_u − 1_v`. -/
def Edge.vecZ {n : ℕ} (e : Edge n) : Fin n → ℤ :=
  fun i => (if i = e.u then 1 else 0) - (if i = e.v then 1 else 0)

/-- The edge vector `e = 1_u − 1_v` in `ℝⁿ`. -/
def Edge.vecR {n : ℕ} (e : Edge n) : Fin n → ℝ := fun i => (e.vecZ i : ℝ)

/-- The standard inner product `⟨x, y⟩ = ∑ᵢ x(i) y(i)` on `ℝⁿ`. -/
def ip {n : ℕ} (x y : Fin n → ℝ) : ℝ := ∑ i, x i * y i

/-- The squared Euclidean norm `‖x‖² = ∑ᵢ x(i)²`. -/
def sqNorm {n : ℕ} (x : Fin n → ℝ) : ℝ := ∑ i, x i ^ 2

/-- `x(S) = ∑_{i ∈ S} x(i)` for an integer vector. -/
def setSum {n : ℕ} (x : Fin n → ℤ) (S : Finset (Fin n)) : ℤ := ∑ i ∈ S, x i

/-- An edge crosses `S` if exactly one of its endpoints belongs to `S`. -/
def Edge.Crosses {n : ℕ} (e : Edge n) (S : Finset (Fin n)) : Prop := Xor (e.u ∈ S) (e.v ∈ S)

/-- A sequence of signs `ε t ∈ {−1, +1}` (`ε t` is the sign of the edge `E t`). -/
def IsSignSeq (ε : ℕ → ℤ) : Prop := ∀ t, ε t = 1 ∨ ε t = -1

/-- The trajectory (1.1): `d₀ = 0` and `d_{t+1} = d_t + ε_{t+1} e_{t+1}`
(in this file's indexing, `traj E ε (t+1) = traj E ε t + ε t • (E t).vecZ`). -/
def traj {n : ℕ} (E : ℕ → Edge n) (ε : ℕ → ℤ) : ℕ → Fin n → ℤ
  | 0 => 0
  | t + 1 => traj E ε t + ε t • (E t).vecZ

/-- The receiver of the edge `E t` (the paper's `a_{t+1}`): the endpoint whose discrepancy
increases, i.e. `ε e = 1_a − 1_b`. -/
def receiver {n : ℕ} (E : ℕ → Edge n) (ε : ℕ → ℤ) (t : ℕ) : Fin n :=
  if ε t = 1 then (E t).u else (E t).v

/-- The sender of the edge `E t` (the paper's `b_{t+1}`). -/
def sender {n : ℕ} (E : ℕ → Edge n) (ε : ℕ → ℤ) (t : ℕ) : Fin n :=
  if ε t = 1 then (E t).v else (E t).u

/-- The receiving gap `max_{1 ≤ t ≤ T} (d_t(a_t) − d_t(b_t))` is at most `g`, the difference
being measured after the update. -/
def GapAtMost {n : ℕ} (E : ℕ → Edge n) (ε : ℕ → ℤ) (T : ℕ) (g : ℤ) : Prop :=
  ∀ t < T, traj E ε (t + 1) (receiver E ε t) - traj E ε (t + 1) (sender E ε t) ≤ g

/-- The maximum (1.2): `M_T = max_{0 ≤ t ≤ T} ‖d_t‖_∞`, a natural number. -/
def maxDisc {n : ℕ} (d : ℕ → Fin n → ℤ) (T : ℕ) : ℕ :=
  (Finset.range (T + 1)).sup fun t => Finset.univ.sup fun i => (d t i).natAbs

/-- A randomized online orientation rule on `[n]`, driven by a tape of reals. At step `t + 1`
it sees only the first `t + 1` edges and the first `t + 1` tape values, and outputs the sign
of the current edge (`true` means `ε = +1`). The rule takes no horizon: one rule serves every
`T`, and decisions are never revised. -/
structure OnlineAlgorithm (n : ℕ) where
  sign : (t : ℕ) → (Fin (t + 1) → Edge n) → (Fin (t + 1) → ℝ) → Bool

/-- The rule is measurable in the tape values, for every fixed edge prefix. -/
def OnlineAlgorithm.IsMeasurable {n : ℕ} (A : OnlineAlgorithm n) : Prop :=
  ∀ (t : ℕ) (E : Fin (t + 1) → Edge n), Measurable (A.sign t E)

/-- The signs produced by `A` on the input `E` with tape `u`: `ε t` is the sign of `E t`. -/
def OnlineAlgorithm.signs {n : ℕ} (A : OnlineAlgorithm n) (E : ℕ → Edge n) (u : ℕ → ℝ) :
    ℕ → ℤ :=
  fun t => if A.sign t (fun i => E i.1) (fun i => u i.1) then 1 else -1

/-- The discrepancy trajectory produced by `A` on input `E` with tape `u`. -/
def OnlineAlgorithm.disc {n : ℕ} (A : OnlineAlgorithm n) (E : ℕ → Edge n) (u : ℕ → ℝ) :
    ℕ → Fin n → ℤ :=
  traj E (A.signs E u)

/-- `U₁, U₂, …` (here `U 0, U 1, …`) are independent random variables, each uniform on `[0,1)`. -/
def IsUniformTape {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (U : ℕ → Ω → ℝ) : Prop :=
  (∀ t, Measurable (U t)) ∧ iIndepFun U P ∧
    ∀ t, P.map (U t) = volume.restrict (Set.Ico (0 : ℝ) 1)

end OnlineCarpoolingLei.Oblivious


