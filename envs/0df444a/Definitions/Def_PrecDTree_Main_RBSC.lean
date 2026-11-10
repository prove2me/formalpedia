-- Prove2me | Definitions.Def_PrecDTree_Main_RBSC
-- name    : PrecDTree_Main_RBSC
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T03:49:52.554324+00:00
-- url     : https://prove2.me/theorems/8dd3db57-1e6f-4035-b71e-d0f1e6c2451e
-- title:
--   Partial Red-Blue Set Cover (Problem 4.1) and the LP (2)–(10)
-- statement:
--   An instance $I=(R,B,\mathcal S,t)$ of **Partial-RBSC** has disjoint sets $R$ of $k$ red and $B$ of $n$ blue elements, a family $\mathcal S$ of $m$ subsets of $R\cup B$ and an integer target $t$; write $R_S=S\cap R$, $B_S=S\cap B$, $\mathrm{cov}(\mathcal C,X)=\bigcup\mathcal C\cap X$. A cover $\mathcal C\subseteq\mathcal S$ with $|\mathrm{cov}(\mathcal C,B)|\ge t$ is sought minimizing the red cost $|\mathrm{cov}(\mathcal C,R)|$; $\mathrm{OPT}(I)$ is the minimum. For a guess $K$ the LP has variables $y_r,x_S,z_u,a_{u,S}$ ($u\in B_S$), $y_{r,q}$ ($r,q\in R$), all in $[0,1]$, and constraints
--   $$\textstyle\sum_r y_r\le K,\ \ \sum_u z_u=t\ (2);\quad \sum_{S:u\in B_S}a_{u,S}=z_u\ (3);\quad a_{u,S}\le x_S\ (4);\quad \sum_{u\in B_S}a_{u,S}\le t\,x_S\ (5);$$
--   $$\textstyle x_S\le y_r\ (r\in R_S)\ (6);\quad \sum_{S:r\in R_S,u\in B_S}a_{u,S}\le y_r\ (7);\quad \sum_{S:r\in R_S}\sum_{u\in B_S}a_{u,S}\le t\,y_r\ (8);\quad x_S\le y_{r,q}\ (r,q\in R_S)\ (9);\quad \sum_q y_{r,q}\le K\,y_r\ (10).$$
--
--   **Formalization Note.** `RBInstance` has `R = Fin k`, `B = Fin n` (disjoint by typing), sets indexed by `Fin m` with red part `red S` and blue part `blue S`, and `t : ℕ`. `Feasible` is $|\mathrm{cov}(\mathcal S,B)|\ge t$, under which `opt` (an `sInf` over $\mathbb N$) is a minimum. `LPSol` carries all variables as real functions (`a u S` is used only for `u ∈ blue S`); `LPFeasible I K s` is exactly (2)–(10) with the ranges.
-- source:
--   Szyfelbein, Dereniowski, Precedence-Constrained Decision Trees and Coverings, arXiv:2602.21312 (STOC 2027 submission version, sha256 aafd336d…), p. 8, Problem 4.1; pp. 9–10, LP (2)–(10)

import Mathlib

set_option autoImplicit false

/-!
# Partial Red-Blue Set Cover (Problem 4.1) and the LP (2)–(10)

Szyfelbein, Dereniowski, *Precedence-Constrained Decision Trees and Coverings*, arXiv:2602.21312
(STOC 2027 submission version), p. 8 (Problem 4.1), pp. 9–10 (variables and LP (2)–(10)).

An instance has `k` red elements `R = Fin k`, `n` blue elements `B = Fin n` (disjoint by typing),
`m` sets indexed by `Fin m`, set `S` having red part `R_S = red S` and blue part `B_S = blue S`,
and a target `t`. A cover is a set of indices `C : Finset (Fin m)`.
-/

namespace PrecDTree.Main

/-- A Partial-RBSC instance `(R, B, S, t)`. -/
structure RBInstance where
  k : ℕ
  n : ℕ
  m : ℕ
  t : ℕ
  red : Fin m → Finset (Fin k)
  blue : Fin m → Finset (Fin n)

namespace RBInstance

variable (I : RBInstance)

/-- `cov(C, R)`, the red elements covered by `C`. -/
def redCov (C : Finset (Fin I.m)) : Finset (Fin I.k) := C.biUnion I.red

/-- `cov(C, B)`, the blue elements covered by `C`. -/
def blueCov (C : Finset (Fin I.m)) : Finset (Fin I.n) := C.biUnion I.blue

/-- Some cover reaches the target: `|cov(S, B)| ≥ t`. -/
def Feasible : Prop := I.t ≤ (I.blueCov Finset.univ).card

/-- `OPT(I)`: the least red cost `|cov(C, R)|` over covers with `|cov(C, B)| ≥ t`. -/
noncomputable def opt : ℕ :=
  sInf {c | ∃ C : Finset (Fin I.m), I.t ≤ (I.blueCov C).card ∧ (I.redCov C).card = c}

end RBInstance

/-- A point of the LP: `y_r`, `x_S`, `z_u`, `a_{u,S}` (used for `u ∈ B_S` only) and `y_{r,q}`. -/
structure LPSol (I : RBInstance) where
  y : Fin I.k → ℝ
  x : Fin I.m → ℝ
  z : Fin I.n → ℝ
  a : Fin I.n → Fin I.m → ℝ
  yy : Fin I.k → Fin I.k → ℝ

/-- The LP (2)–(10) for the guess `K`, with every variable in `[0, 1]` (p. 9). -/
def LPFeasible (I : RBInstance) (K : ℕ) (s : LPSol I) : Prop :=
  -- variable ranges
  (∀ r, 0 ≤ s.y r ∧ s.y r ≤ 1) ∧ (∀ S, 0 ≤ s.x S ∧ s.x S ≤ 1) ∧
  (∀ u, 0 ≤ s.z u ∧ s.z u ≤ 1) ∧ (∀ S, ∀ u ∈ I.blue S, 0 ≤ s.a u S ∧ s.a u S ≤ 1) ∧
  (∀ r q, 0 ≤ s.yy r q ∧ s.yy r q ≤ 1) ∧
  -- (2)
  (∑ r, s.y r ≤ (K : ℝ)) ∧ (∑ u, s.z u = (I.t : ℝ)) ∧
  -- (3)
  (∀ u, ∑ S ∈ Finset.univ.filter (fun S => u ∈ I.blue S), s.a u S = s.z u) ∧
  -- (4)
  (∀ S, ∀ u ∈ I.blue S, s.a u S ≤ s.x S) ∧
  -- (5)
  (∀ S, ∑ u ∈ I.blue S, s.a u S ≤ (I.t : ℝ) * s.x S) ∧
  -- (6)
  (∀ S, ∀ r ∈ I.red S, s.x S ≤ s.y r) ∧
  -- (7)
  (∀ r u, ∑ S ∈ Finset.univ.filter (fun S => r ∈ I.red S ∧ u ∈ I.blue S), s.a u S ≤ s.y r) ∧
  -- (8)
  (∀ r, ∑ S ∈ Finset.univ.filter (fun S => r ∈ I.red S), ∑ u ∈ I.blue S, s.a u S ≤
      (I.t : ℝ) * s.y r) ∧
  -- (9)
  (∀ S, ∀ r ∈ I.red S, ∀ q ∈ I.red S, s.x S ≤ s.yy r q) ∧
  -- (10)
  (∀ r, ∑ q, s.yy r q ≤ (K : ℝ) * s.y r)

end PrecDTree.Main


