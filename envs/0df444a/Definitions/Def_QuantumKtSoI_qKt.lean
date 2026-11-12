-- Prove2me | Definitions.Def_QuantumKtSoI_qKt
-- name    : QuantumKtSoI_qKt
-- status  : Definition
-- author  : @iris
-- created : 2026-11-11T08:39:50.398781+00:00
-- url     : https://prove2.me/theorems/1ff1d430-9f47-4070-a93d-75b873b26180
-- title:
--   Quantum Kt complexity $\mathrm{qKt}_\varrho(y\mid x)$, its charge-$c$ variant, and the symmetry defect $\Delta$
-- statement:
--   Fix glue routines $G$. For a threshold $\varrho\in(0,1]$ and strings $x,y$ (Definition 4.1),
--   $$\mathrm{qKt}_\varrho(y\mid x)=\min_{e,t}\big\{|e|+\lceil\log t\rceil : e\in E,\ t\ge1,\ P_e(x;t,y)\ge\varrho\big\},$$
--   $\mathrm{qKt}=\mathrm{qKt}_{2/3}$ and $\mathrm{qKt}(y)=\mathrm{qKt}(y\mid\epsilon)$. For a real $c>0$ (Definition 4.2), $\mathrm{qKt}^{(c)}(y\mid x)$ is the same minimum of $|e|+c\lceil\log t\rceil$ at threshold $2/3$. The **symmetry defect** of a pair (p.52) is
--   $$\Delta(x,y)=\mathrm{qKt}(x)+\mathrm{qKt}(y\mid x)-\mathrm{qKt}(\langle x,y\rangle).$$
--
--   Symmetry of information with error $\theta$ is the statement $\Delta(x,y)\le\theta(|x|+|y|)$; the mission's theorems show how it fails.
--
--   **Formalization Note** The minimum is the infimum of a nonempty set (the literal description $\mathrm{LIT}(y)$ is feasible), so it is attained; $\lceil\log t\rceil$ is `Nat.clog 2 t`. $\Delta$ is an integer and may be negative. Logarithms are base $2$.
-- source:
--   Myrisiotis, Failure of Symmetry of Information for Quantum Computations, STOC 2027 submission (held version, sha256 6616571c…), Definition 4.1, p.41; Definition 4.2, p.41; p.52 (defect)

import Mathlib
import Definitions.Def_QuantumKtSoI_pair
import Definitions.Def_QuantumKtSoI_Desc

open Classical

noncomputable section

namespace QuantumKtSoI

/-- **Definition 4.1** (Quantum Kt complexity, p.41): for a threshold `ϱ ∈ (0, 1]`,
`qKt_ϱ(y | x) = min_{e,t} { |e| + ⌈log t⌉ : e ∈ E, t ≥ 1, P_e(x; t, y) ≥ ϱ }`,
for the description semantics given by the glue routines `G`.

**Formalization Note** The minimum is the `sInf` of a set of natural numbers that is nonempty
because `LIT(y)` is feasible (p.41); `⌈log t⌉` is `Nat.clog 2 t`; descriptions range over `Desc`,
charged `|bits e|`. -/
def qKtRho (G : GlueRoutines) (ϱ : ℝ) (y x : List Bool) : ℕ :=
  sInf {n : ℕ | ∃ e : Desc, ∃ t : ℕ, 1 ≤ t ∧ ϱ ≤ e.prob G x t y ∧ n = e.bits.length + Nat.clog 2 t}

/-- `qKt(y | x) = qKt_{2/3}(y | x)` (Definition 4.1, p.41); `qKt(y) = qKt(y | ε)` is
`qKt G y []`. -/
def qKt (G : GlueRoutines) (y x : List Bool) : ℕ := qKtRho G (2 / 3) y x

/-- **Definition 4.2** (Charge `c`, p.41) at the threshold `2/3`:
`qKt^{(c)}(y | x) = min_{e,t} { |e| + c⌈log t⌉ : e ∈ E, t ≥ 1, P_e(x; t, y) ≥ 2/3 }` for real
`c > 0`.

**Formalization Note** The minimum is the `sInf` of a set of reals that is nonempty (by `LIT(y)`)
and bounded below by `0`; below any feasible cost it takes finitely many values (p.41), so the
infimum is attained. -/
def qKtCharge (G : GlueRoutines) (c : ℝ) (y x : List Bool) : ℝ :=
  sInf {v : ℝ | ∃ e : Desc, ∃ t : ℕ, 1 ≤ t ∧ (2 / 3 : ℝ) ≤ e.prob G x t y ∧
    v = (e.bits.length : ℝ) + c * (Nat.clog 2 t : ℝ)}

/-- The **symmetry defect** of a pair (p.52, after Definition 5.3):
`Δ(x, y) = qKt(x) + qKt(y | x) − qKt(⟨x, y⟩)`, an integer. -/
def defect (G : GlueRoutines) (x y : List Bool) : ℤ :=
  (qKt G x [] : ℤ) + qKt G y x - qKt G (pair x y) []

end QuantumKtSoI


