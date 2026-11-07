-- Prove2me | Definitions.Def_TIEMaximin_Deficient
-- name    : TIEMaximin_Deficient
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:40:43.350197+00:00
-- url     : https://prove2.me/theorems/eba2bb7e-912a-4b6e-a6e7-a6525b8b9161
-- title:
--   High and low goods, deficient agents, parameters $p,q,a,k$, retained suballocation $h$
-- statement:
--   Fix $\alpha\in(0,1)$. The **high goods** of agent $i$ are $H_i=\{g:v_i(g)\ge\alpha\,\mathrm{TPS}_i\}$ and the **low goods** are $L_i=M\setminus H_i$. Agent $i$ is **deficient** if $\sum_{g\in H_i}x_{ig}<1$; then $p_i=1-\sum_{g\in H_i}x_{ig}$ is her probability of not receiving a high good, and $p_i=0$ otherwise. Further $a_i=n-|H_i|$, $q_i=np_i$ and $k_i=\max\{2,\lceil2q_i\rceil\}$.
--
--   The **retained high-good suballocation** $h$ has $h_{ig}=x_{ig}$ on $H_i$ and $0$ elsewhere for a deficient agent. For any other agent, $h_i$ is $x_i$ truncated at total mass one in descending order of $v_i$.
--
--   These parameters fix which agents need compensation in the mechanism, and how much.
--
--   **Formalization Note** Deficiency uses the second form of Definition 3.7. The truncation is written in the closed form $h_{ig}=\min\{x_{ig},\max\{0,1-\sum_{g'\text{ before }g}x_{ig'}\}\}$, which agrees with the three steps of Definition 3.8 since $\sum_g x_{ig}=m/n\ge1$. Parameters are defined for all agents and read only on deficient ones; $a_i$ is an integer and $k_i$ a natural number.
-- source:
--   M. Ma, B. Tao, F. Wang, Truthful-in-Expectation Mechanism with Constant Maximin-Share Guarantee, arXiv:2609.35670 (version of 2026-11-03, sha256 4e68de70…), Definitions 3.6–3.8, pp.14–15; eq. (8), p.16

import Mathlib
import Definitions.Def_TIEMaximin_Shares
import Definitions.Def_TIEMaximin_Rule

namespace TIEMaximin

open Finset

/-- **High goods** `H_i = {g : v_i(g) ≥ α TPS_i}` (Definition 3.6, p.14 of arXiv:2609.35670, version
of 2026-11-03, sha256 4e68de70…).

**Formalization Note.** The threshold is non-strict. When `TPS_i = 0` every good is high. -/
noncomputable def high {n m : ℕ} (α : ℝ) (v : Fin n → Fin m → ℝ) (i : Fin n) : Finset (Fin m) :=
  {g | α * tps n (v i) ≤ v i g}

/-- **Low goods** `L_i = M ∖ H_i` (Definition 3.6, p.14 of arXiv:2609.35670, version of 2026-11-03,
sha256 4e68de70…). -/
noncomputable def low {n m : ℕ} (α : ℝ) (v : Fin n → Fin m → ℝ) (i : Fin n) : Finset (Fin m) :=
  univ \ high α v i

/-- **Deficient agents** (Definition 3.7, p.14): agent `i` is deficient if `Σ_{g ∈ H_i} x_ig < 1`.

arXiv:2609.35670 (version of 2026-11-03, sha256 4e68de70…), Definition 3.7, p.14: "Equivalently,
agent i is deficient if Σ_{g∈H_i} x_ig < 1".

**Formalization Note.** This is the second of the two forms of Definition 3.7; the first (`|H_i| < t_i`,
with `t_i` of Definition 3.5) is checked against it in `Solutions/verification/TIEMaximin_deficient.lean`. -/
def IsDeficient {n m : ℕ} (α : ℝ) (v : Fin n → Fin m → ℝ) (i : Fin n) : Prop :=
  ∑ g ∈ high α v i, xRule v i g < 1

open Classical in
/-- **The set `D` of deficient agents** (Definition 3.7, p.14 of arXiv:2609.35670, version of
2026-11-03, sha256 4e68de70…). -/
noncomputable def defSet {n m : ℕ} (α : ℝ) (v : Fin n → Fin m → ℝ) : Finset (Fin n) :=
  {i | IsDeficient α v i}

open Classical in
/-- **The probability `p_i` of not receiving a high good** (Definition 3.7, p.14):
`p_i = 1 − Σ_{g ∈ H_i} x_ig` for a deficient agent and `p_i = 0` otherwise (arXiv:2609.35670, version
of 2026-11-03, sha256 4e68de70…). -/
noncomputable def pDef {n m : ℕ} (α : ℝ) (v : Fin n → Fin m → ℝ) (i : Fin n) : ℝ :=
  if IsDeficient α v i then 1 - ∑ g ∈ high α v i, xRule v i g else 0

/-- `q_i = n p_i` of (8), p.16 (arXiv:2609.35670, version of 2026-11-03, sha256 4e68de70…). -/
noncomputable def qDef {n m : ℕ} (α : ℝ) (v : Fin n → Fin m → ℝ) (i : Fin n) : ℝ :=
  (n : ℝ) * pDef α v i

/-- `a_i = n − |H_i|` of (8), p.16, as an integer (arXiv:2609.35670, version of 2026-11-03, sha256
4e68de70…).

**Formalization Note.** Defined for every agent, read only on deficient ones; integer-valued, so there
is no truncated subtraction. -/
noncomputable def aDef {n m : ℕ} (α : ℝ) (v : Fin n → Fin m → ℝ) (i : Fin n) : ℤ :=
  (n : ℤ) - (#(high α v i) : ℤ)

/-- **The compensation parameter** `k_i = max{2, ⌈2 q_i⌉}` of (8), p.16 (arXiv:2609.35670, version of
2026-11-03, sha256 4e68de70…).

**Formalization Note.** A natural number. `q_i ≥ 0` for every agent, so `⌈·⌉₊` is the paper's ceiling.
Defined for every agent, read only on deficient ones. -/
noncomputable def kDef {n m : ℕ} (α : ℝ) (v : Fin n → Fin m → ℝ) (i : Fin n) : ℕ :=
  max 2 ⌈2 * qDef α v i⌉₊

/-- The mass `Σ_{g' before g in π_i} x_ig'` that agent `i`'s value order puts before `g`
(Definition 3.8, p.15 of arXiv:2609.35670, version of 2026-11-03, sha256 4e68de70…). -/
noncomputable def xBefore {n m : ℕ} (v : Fin n → Fin m → ℝ) (i : Fin n) (g : Fin m) : ℝ :=
  ∑ g' with rankV v i g' < rankV v i g, xRule v i g'

open Classical in
/-- **The retained high-good suballocation** `h` (Definition 3.8, p.15). A deficient agent keeps
`h_ig = x_ig` on `H_i` and `0` elsewhere. A non-deficient agent's row is `x_i` truncated at total mass
`1` in descending order of `v_i`.

arXiv:2609.35670 (version of 2026-11-03, sha256 4e68de70…), Definition 3.8, p.15.

**Formalization Note.** The truncation is written in closed form,
`h_ig = min{x_ig, max{0, 1 − Σ_{g' before g in π_i} x_ig'}}`. This agrees with the steps 1–3 of
Definition 3.8: before the first block ends the second argument exceeds `x_ig`, at `π_i(t_i)` it is
what brings the total to `1`, and afterwards it is `0`. A first block exists because
`Σ_g x_ig = m/n ≥ 1` under the standing `m ≥ n`. -/
noncomputable def hRet {n m : ℕ} (α : ℝ) (v : Fin n → Fin m → ℝ) (i : Fin n) (g : Fin m) : ℝ :=
  if IsDeficient α v i then
    (if g ∈ high α v i then xRule v i g else 0)
  else
    min (xRule v i g) (max 0 (1 - xBefore v i g))

end TIEMaximin


