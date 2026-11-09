-- Prove2me | Definitions.Def_MultiNashRepair_Regret
-- name    : MultiNashRepair_Regret
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T22:27:08.628951+00:00
-- url     : https://prove2.me/theorems/d6ab87e6-3c01-4392-9852-c6f32213fe8c
-- title:
--   Deviation gains, deficits, regret and the scaled satisfaction $\varsigma=m(1-\mathrm{Reg}(x))$
-- statement:
--   Fix an $m$-player game with action sets $A_i=\{0,\dots,n_i-1\}$ and payoff functions $u_i$, extended multilinearly to mixed profiles $x=(x_1,\dots,x_m)$. Write $x[j\leftarrow y_j]$ for the profile with $x_j$ replaced by $y_j$ and $e_a$ for the unit vector of a pure action $a$.
--
--   1. The **deviation gain** $g_{i,a}(x)=u_i(x[i\leftarrow e_a])-u_i(x)$ and the **deficit** $d_{i,a}(x)=1-g_{i,a}(x)$.
--   2. For a mixed deviation $b_i$, the deficit $d_{i,b_i}(x)=1-u_i(x[i\leftarrow b_i])+u_i(x)$.
--   3. The **regret** $r_i(x)=\max_{a\in A_i} g_{i,a}(x)$, the **maximum regret** $\mathrm{Reg}(x)=\max_i r_i(x)$, $q_i(x)=1-r_i(x)$ and $q(x)=1-\mathrm{Reg}(x)$.
--   4. The **scaled satisfaction** $$\varsigma = m\,q(x)=m\bigl(1-\mathrm{Reg}(x)\bigr),$$ so that $\varsigma\ge\sigma$ exactly when $x$ is a $(1-\sigma/m)$-approximate Nash equilibrium.
--   5. The **replacement difference** $\Delta_{j,b}g_{i,a}(x)=g_{i,a}(x[j\leftarrow e_b])-g_{i,a}(x)$.
--   6. A real number is *rational* if it equals the image of some $q\in\mathbb Q$.
--
--   These are the quantities of §2 and §3.1 in which the algorithm and every bound are written.
--
--   **Formalization Note** Maxima are suprema over finite index types; they are maxima whenever $m\ge1$ and every $n_i>0$, which every statement assumes. $e_a$ is the published `pureStrategy`.
-- source:
--   J. Tang, S. Ding, C. Fang, Breaking the One-Player Extension Barrier: History-Aware Repair for Multiplayer Approximate Nash Equilibria, arXiv:2611.06076 (preprint; held version, sha256 34b911ed…5c14), §2, p.5 (g, d, r, Reg, q, (2.1)); §3.1, p.6 (Δ_{j,b} g_{i,a})

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_DGPNash_NashMap_nashMap
import Definitions.Def_DGPNash_WellSupported_Equilibria
import Definitions.Def_NashAmplification_Filtering_Model

open NashAmplification.Filtering (Mixed Utility Tuple)

noncomputable section

namespace MultiNashRepair

variable {m : ℕ} {n : Fin m → ℕ}

/-- The unit vector `e_a` of a pure action `a ∈ A_j` (Tang, Ding, Fang, arXiv:2611.06076, §2,
p.5: "We identify a pure action a ∈ A_j with its unit vector e_a"); the published
`DGPNash.WellSupported.pureStrategy` at the action type `Fin (n j)`. -/
abbrev ePure {j : Fin m} (a : Fin (n j)) : Fin (n j) → ℝ :=
  DGPNash.WellSupported.pureStrategy (S := fun i => Fin (n i)) a

/-- The deviation gain `g_{i,a}(x) = u_i(x[i ← e_a]) − u_i(x)` (§2, p.5). -/
def gain (u : Utility n) (x : Mixed n) (i : Fin m) (a : Fin (n i)) : ℝ :=
  DGPNash.NashMap.purePayoff u x i a - AGT.expectedPayoff u x i

/-- The deficit `d_{i,a}(x) = 1 − g_{i,a}(x)` (§2, p.5). -/
def deficit (u : Utility n) (x : Mixed n) (i : Fin m) (a : Fin (n i)) : ℝ :=
  1 - gain u x i a

/-- The deficit of a mixed deviation, `d_{i,b_i}(x) = 1 − u_i(x[i ← b_i]) + u_i(x)` (§2, p.5),
the affine extension of `d_{i,a}`. -/
def deficitMix (u : Utility n) (x : Mixed n) (i : Fin m) (b : Fin (n i) → ℝ) : ℝ :=
  1 - AGT.expectedPayoff u (Function.update x i b) i + AGT.expectedPayoff u x i

/-- The regret `r_i(x) = max_{a ∈ A_i} u_i(x[i ← e_a]) − u_i(x)` (§2, p.5).

**Formalization Note.** The maximum is a supremum over the finite type `Fin (n i)`; it is the
maximum whenever `0 < n i`, which every statement assumes (nonempty action sets). -/
def regret (u : Utility n) (x : Mixed n) (i : Fin m) : ℝ :=
  ⨆ a : Fin (n i), gain u x i a

/-- The maximum regret `Reg(x) = max_i r_i(x)` (§2, p.5). A supremum over `Fin m`, the maximum
whenever `1 ≤ m`, which every statement assumes. -/
def Reg (u : Utility n) (x : Mixed n) : ℝ :=
  ⨆ i : Fin m, regret u x i

/-- `q_i(x) = min_a d_{i,a}(x) = 1 − r_i(x)` (§2, p.5). -/
def qi (u : Utility n) (x : Mixed n) (i : Fin m) : ℝ :=
  1 - regret u x i

/-- `q(x) = min_i q_i(x) = 1 − Reg(x)` (§2, p.5). -/
def q (u : Utility n) (x : Mixed n) : ℝ :=
  1 - Reg u x

/-- The scaled satisfaction `ς = σ^{(k)} = m · q(x) = m (1 − Reg(x))` ((2.1), p.5). The stopping
test `ς ≥ σ` is `Reg(x) ≤ 1 − σ/m`. -/
def scaled (u : Utility n) (x : Mixed n) : ℝ :=
  (m : ℝ) * q u x

/-- The scalar replacement difference `Δ_{j,b} g_{i,a}(x) = g_{i,a}(x[j ← e_b]) − g_{i,a}(x)`
(§3.1, p.6). -/
def repl (u : Utility n) (x : Mixed n) (j : Fin m) (b : Fin (n j)) (i : Fin m)
    (a : Fin (n i)) : ℝ :=
  gain u (Function.update x j (ePure b)) i a - gain u x i a

/-- A real number is rational. -/
def IsRat (r : ℝ) : Prop :=
  ∃ q : ℚ, (q : ℝ) = r

end MultiNashRepair


