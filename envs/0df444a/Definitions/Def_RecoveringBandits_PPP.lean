-- Prove2me | Definitions.Def_RecoveringBandits_PPP
-- name    : RecoveringBandits_PPP
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T07:54:21.257024+00:00
-- url     : https://prove2.me/theorems/b7757f4f-a4d3-4d52-83e0-3a2beb56eda3
-- title:
--   Purely periodic policies, $K$-PPPs and their rewards (Definitions 1–2)
-- statement:
--   A **purely periodic policy** assigns to every arm $i$ a period $d_i\in\mathbb Z_+\cup\{+\infty\}$ and an offset $t_i\in\mathbb Z$ with $t_i\in(-d_i,0]$; arm $i$ is pulled at the times $t_i+k d_i$, $k=1,2,\dots$, i.e. at every $t\ge1$ with $t\equiv t_i\pmod{d_i}$, and never if $d_i=+\infty$ (Definition 1). It is a **$K$-PPP** when
--
--   $$\sup_{t\ge1}\#\{i\in[N]:\ d_i<+\infty,\ t\equiv t_i\ (\mathrm{mod}\ d_i)\}\le K$$
--
--   (Definition 2). Its **total reward** up to $T$ is the sum over arms of the reward of the induced schedule, with every arm last pulled at time $0$: the first pull of arm $i$, at $t_i+d_i$, earns $R_i(t_i+d_i)$ and every later pull earns $R_i(d_i)$. Its **long-run average reward** is $\sum_{i:\,d_i<+\infty}R_i(d_i)/d_i$.
--
--   **Formalization Note** $+\infty$ is `⊤ : WithTop ℕ`. Definition 1 (i) for $d_i=+\infty$ reads $t_i\le 0$. The expected reward is the sum of mean rewards of the gaps, as in the objective of (1).
-- source:
--   Simchi-Levi–Zheng–Zhu, Offline Planning and Online Learning under Recovering Rewards, arXiv:2106.14813v2, Definitions 1–2, p.9; §2, p.6; Algorithm 1 line 10, p.13

import Mathlib
import Definitions.Def_RecoveringBandits_schedReward

namespace RecoveringBandits

/-- **A purely periodic policy `{(d_i, t_i)}_{i ∈ [N]}`** (arXiv:2106.14813v2, Definition 1, p.9):
a period `d_i ∈ ℤ₊ ∪ {+∞}` and an offset `t_i ∈ ℤ` for every arm.

**Formalization Note.** `+∞` is `⊤ : WithTop ℕ`. The constraints of Definition 1 (i) are
`PPP.Valid`. -/
structure PPP (N : ℕ) where
  /-- The period `d_i` (`⊤` = never pulled). -/
  period : Fin N → WithTop ℕ
  /-- The offset `t_i`. -/
  offset : Fin N → ℤ

/-- Definition 1 (i) (arXiv:2106.14813v2, p.9): `t_i ∈ (−d_i, 0]` and `d_i ∈ ℤ₊ ∪ {+∞}`. For
`d_i = +∞` this reads `t_i ≤ 0`. -/
def PPP.Valid {N : ℕ} (π : PPP N) : Prop :=
  ∀ i, π.offset i ≤ 0 ∧ ∀ d : ℕ, π.period i = (d : WithTop ℕ) → 1 ≤ d ∧ -(d : ℤ) < π.offset i

/-- Definition 1 (ii) (arXiv:2106.14813v2, p.9): arm `i` is pulled at the times `t_i + k·d_i`,
`k ∈ ℤ₊`. With `t_i ∈ (−d_i, 0]` these are exactly the times `t ≥ 1` with `t ≡ t_i (mod d_i)`;
an arm with `d_i = +∞` is never pulled. -/
def PPP.Pulls {N : ℕ} (π : PPP N) (i : Fin N) (t : ℕ) : Prop :=
  1 ≤ t ∧ ∃ d : ℕ, π.period i = (d : WithTop ℕ) ∧ (t : ℤ) ≡ π.offset i [ZMOD (d : ℤ)]

open Classical in
/-- The pull times of arm `i` up to the horizon `T` ("until the time horizon `T` is exhausted",
Definition 1 (ii), p.9). -/
noncomputable def PPP.pullSet {N : ℕ} (π : PPP N) (i : Fin N) (T : ℕ) : Finset ℕ :=
  (Finset.Icc 1 T).filter (fun t => π.Pulls i t)

/-- **The total (mean) reward of a purely periodic policy up to `T`**: the objective of (1)
(arXiv:2106.14813v2, §3.1, pp.7–8) for the schedule the policy induces, with every arm last
pulled at time `0` (§2, p.6). The first pull of arm `i`, at `t_i + d_i ∈ [1, d_i]`, earns
`R_i(t_i + d_i)`; every later one earns `R_i(d_i)`.

**Formalization Note.** The offline problem is deterministic in the mean rewards (p.7), so the
expected total reward is the sum of the mean rewards of the gaps. -/
noncomputable def totalReward {N : ℕ} (R : Fin N → ℕ → ℝ) (π : PPP N) (T : ℕ) : ℝ :=
  ∑ i, schedReward (R i) (π.pullSet i T)

open Classical in
/-- **A `K`-PPP** (arXiv:2106.14813v2, Definition 2, p.9): a (valid) purely periodic policy with
`sup_{t ≥ 1} #{i ∈ [N] : d_i < +∞, t ≡ t_i (mod d_i)} ≤ K`. -/
def IsKPPP {N : ℕ} (K : ℕ) (π : PPP N) : Prop :=
  π.Valid ∧ ∀ t : ℕ, 1 ≤ t → (Finset.univ.filter (fun i => π.Pulls i t)).card ≤ K

/-- **The long-run average reward of a purely periodic policy**: `∑_{i : d_i < +∞} R_i(d_i)/d_i`
(arXiv:2106.14813v2, §4.2, Algorithm 1 line 10, p.13; §4.3, p.14). -/
noncomputable def longRunReward {N : ℕ} (R : Fin N → ℕ → ℝ) (π : PPP N) : ℝ :=
  ∑ i, (match π.period i with
    | ⊤ => 0
    | (d : ℕ) => R i d / (d : ℝ))

end RecoveringBandits


