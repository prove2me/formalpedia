-- Prove2me | Definitions.Def_PriceRobustness_Main_RobustModel
-- name    : PriceRobustness_Main_RobustModel
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T06:38:36.925993+00:00
-- url     : https://prove2.me/theorems/f1319d2c-896a-4800-b7e1-ff298ed11441
-- title:
--   Budgeted robust model and attained optimal decisions
-- statement:
--   Starting from the nominal linear program, each row $i$ has a finite uncertain-column set $J_i$, nonnegative deviations $\hat a_{ij}$ on that set, and a real budget $0\le\Gamma_i\le |J_i|$. The robust linear program (7) maximizes the nominal objective over $(x,y,z,p)$ subject to
--   $$\sum_j a_{ij}x_j+\Gamma_i z_i+\sum_{j\in J_i}p_{ij}\le b_i,\quad z_i+p_{ij}\ge\hat a_{ij}y_j,$$
--   $$-y_j\le x_j\le y_j,\quad l_j\le x_j\le u_j,\quad p_{ij}\ge0,\ y_j\ge0,\ z_i\ge0.$$
--   Constraints on $p_{ij}$ apply only to $j\in J_i$. An optimal decision $x$ has a feasible extension and dominates the objective of every feasible extension. Define $w_{ij}=\hat a_{ij}|x_j|$. Given row noise $\eta_j$, the realized entry is $a_{ij}+\hat a_{ij}\eta_j$ on $J_i$ and $a_{ij}$ elsewhere. The extra coordinates of $p$ and the unused radii outside $J_i$ do not affect any constraint or conclusion. Zero radii and signed decisions are retained.
-- source:
--   Bertsimas and Sim, The Price of Robustness, authors' preprint, August 2001; revised August, 2002; PDF SHA-256 63f0bffaff9128b706a084acc869e1020ce79adf86108ac23b5b0dd598f189cb; §§2–3, pp. 4, 6–7, Eq. (7); Model U, p. 4

import Definitions.Def_PriceRobustness_Main_LinearProgram

open scoped BigOperators

namespace PriceRobustness.Main

structure RobustModel (m N : ℕ) where
  nominal : LinearProgram m N
  J : Fin m → Finset (Fin N)
  radius : Fin m → Fin N → ℝ
  budget : Fin m → ℝ
  radius_nonneg : ∀ i, ∀ j ∈ J i, 0 ≤ radius i j
  budget_mem : ∀ i, 0 ≤ budget i ∧ budget i ≤ (J i).card

def RobustModel.Feasible {m N : ℕ} (D : RobustModel m N)
    (x y : Fin N → ℝ) (z : Fin m → ℝ) (p : Fin m → Fin N → ℝ) : Prop :=
  (∀ i, (∑ j, D.nominal.A i j * x j) + D.budget i * z i +
    (∑ j ∈ D.J i, p i j) ≤ D.nominal.b i) ∧
  (∀ i, ∀ j ∈ D.J i, D.radius i j * y j ≤ z i + p i j) ∧
  (∀ j, -y j ≤ x j ∧ x j ≤ y j) ∧
  (∀ j, D.nominal.lower j ≤ x j ∧ x j ≤ D.nominal.upper j) ∧
  (∀ i, ∀ j ∈ D.J i, 0 ≤ p i j) ∧ (∀ j, 0 ≤ y j) ∧ (∀ i, 0 ≤ z i)

def RobustModel.Optimal {m N : ℕ} (D : RobustModel m N) (x : Fin N → ℝ) : Prop :=
  (∃ y z p, D.Feasible x y z p) ∧
  ∀ x' y z p, D.Feasible x' y z p → D.nominal.objective x' ≤ D.nominal.objective x

def RobustModel.weight {m N : ℕ} (D : RobustModel m N) (x : Fin N → ℝ)
    (i : Fin m) (j : Fin N) : ℝ := D.radius i j * |x j|

noncomputable def RobustModel.uncertainEntry {m N : ℕ} {Ω : Type*}
    (D : RobustModel m N) (η : Fin N → Ω → ℝ) (i : Fin m) (j : Fin N) (ω : Ω) : ℝ :=
  D.nominal.A i j + if j ∈ D.J i then D.radius i j * η j ω else 0

end PriceRobustness.Main


