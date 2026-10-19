-- Prove2me | Definitions.Def_RandomLeadGBS_Diffusion_Model
-- name    : RandomLeadGBS_Diffusion_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-19T04:21:30.716437+00:00
-- url     : https://prove2.me/theorems/5f975be3-1a54-455d-b404-8f35bd1d4d8c
-- title:
--   §3.1–§3.2, §4.1–§4.2, pp. 6–8, 10, 13, 16–17 — the GBS inventory chain under exponential lead times, the gaps D, D̃, the artificial birth–death chain and the walk Q_n
-- statement:
--   **Parameters.** A sequence of inventory systems is indexed by the demand rate $r>0$. Demand units (customers) arrive as a Poisson process of rate $r$; each ordered supply unit (item) arrives after an exponential lead time with mean $1/\beta$, independently. The generalized base-stock (GBS) policy has an integer gain $\gamma$, a truncation level $f = f(r)$ and a centering $x_* = x_*(r)$. The *standing assumptions* are
--   $$
--   \beta>0,\qquad \gamma\in\mathbb Z,\ \gamma\ge 1,\qquad f(r)>0,\qquad \frac{f(r)}{r}\to 0,\qquad \frac{f(r)}{\sqrt r}\to\infty \quad (r\to\infty), \tag{10}
--   $$
--   with $x_*(r)$ arbitrary.
--
--   **Policy.** Let $X_* = r/\beta$. With net inventory level $Y\in\mathbb Z$ and $Z\in\mathbb Z_+$ items in transit, the target and truncated target are
--   $$
--   X = X_* - \gamma (Y - x_*), \tag{4}
--   $$
--   $$
--   T = [X \wedge (X_* + f)] \vee 0. \tag{5}
--   $$
--   At a customer arrival $Y := Y-1$; at an item arrival $Y := Y+1$, $Z := Z-1$. Then $T$ is updated and $A = \lceil T - Z\rceil \vee 0$ new items are ordered: $Z := Z + A$.
--
--   **The GBS chain.** Under exponential lead times $(Y,Z)$ is a continuous-time Markov chain on $\mathbb Z\times\mathbb Z_+$: from $(y,z)$ a customer arrival occurs at rate $r$ and an item arrival at rate $\beta z$ (each of the $z$ in-transit items arrives at rate $\beta$). Its exit rate is $r+\beta z$, and its stationary distributions are those of the countable-chain definition (global balance with finite mean exit rate). The scaled level is $(Y - x_*)/\sqrt r$, and the gaps (15) are
--   $$
--   D = Z - \lceil T\rceil, \qquad \tilde D = Z - \lceil T\wedge X\rceil .
--   $$
--
--   **The artificial chain** (§4.2). It keeps $\hat Z = \lceil \hat T\rceil$ at all times, so it is a birth–death chain $\hat Y$ on $\mathbb Z$: from $j$ it moves to $j-1$ at rate $r$ and to $j+1$ at rate $\beta\lceil \hat T(j)\rceil$, where $\hat T(j)$ is (5) evaluated at $Y = j$.
--
--   **The reflected random walk $Q_n$** (proof of Lemma 4). On $\mathbb Z_+$, from $q$ it moves to $q+(\gamma-1)$ with probability $1/2+\epsilon$ and to $[q-\gamma]\vee 0$ with probability $1/2-\epsilon$; when both moves land on the same state their probabilities add.
--
--   **Formalization Note** The state is $(Y,Z)\in\mathbb Z\times\mathbb N$ and the demand rate $r$ is real. The order step is written literally as $Z + \mathrm{toNat}\lceil T - Z\rceil$ (`Int.ceil`, with `Int.toNat` the "$\vee 0$"). The item transition uses natural-number $Z-1$ only behind the guard $Z\ge 1$, which is also where its rate $\beta Z$ is positive. $\lceil\hat T\rceil$ uses `Nat.ceil`, applied to $\hat T\ge 0$. The gaps use `Int.ceil` cast to $\mathbb R$, since $T\wedge X$ can be negative.
-- source:
--   Stolyar and Wang, Exploiting random lead times for significant inventory cost savings, arXiv:1801.02646v6, pp. 6–8, 10, 13, 16–17, 22: §3.1, §3.2 (4)–(5) and steps 1–3, §3.4 (10), (15), the random walk Q_n (p. 16), §4.2 and the rates in the proof of Lemma 8 (p. 22)

import Mathlib
import Definitions.Def_RandomLeadGBS_Diffusion_Markov

namespace RandomLeadGBS.Diffusion

open Filter Topology

/-- Parameters of the sequence of systems indexed by the demand rate `r`:
`β` (lead times are exponential with mean `1/β`), the integer gain `γ`, the truncation
`f = f(r)` and the centering `xs = x∗(r)`. -/
structure Params where
  β : ℝ
  γ : ℕ
  f : ℝ → ℝ
  xs : ℝ → ℝ

/-- Standing assumptions (§3.1, §3.2, §3.4 and Theorem 1): `β > 0`, `γ ≥ 1` an integer,
`f(r) > 0`, and (10): `f(r)/r → 0`, `f(r)/√r → ∞`. The centering `x∗(r)` is arbitrary. -/
def Params.Standing (P : Params) : Prop :=
  0 < P.β ∧ 1 ≤ P.γ ∧ (∀ r, 0 < P.f r) ∧
  Tendsto (fun r => P.f r / r) atTop (𝓝 0) ∧
  Tendsto (fun r => P.f r / Real.sqrt r) atTop atTop

/-- States `(Y, Z)`: net inventory level `Y ∈ ℤ` and number of in-transit items `Z ∈ ℕ`. -/
abbrev State := ℤ × ℕ

/-- `X∗ = r/β`. -/
noncomputable def Xstar (P : Params) (r : ℝ) : ℝ := r / P.β

/-- The target (4): `X = X∗ − γ (Y − x∗)`. -/
noncomputable def target (P : Params) (r : ℝ) (y : ℤ) : ℝ :=
  Xstar P r - (P.γ : ℝ) * ((y : ℝ) - P.xs r)

/-- The truncated target (5): `T = [X ∧ (X∗ + f)] ∨ 0`. -/
noncomputable def truncTarget (P : Params) (r : ℝ) (y : ℤ) : ℝ :=
  max (min (target P r y) (Xstar P r + P.f r)) 0

/-- Step 3 of the GBS policy at inventory level `y` with `z` items in transit:
order `A = ⌈T − Z⌉ ∨ 0` new items, `Z := Z + A`. -/
noncomputable def orderStep (P : Params) (r : ℝ) (y : ℤ) (z : ℕ) : ℕ :=
  z + Int.toNat ⌈truncTarget P r y - (z : ℝ)⌉

/-- State after a customer arrival: `Y := Y − 1`, then update `T` and order (steps 1–3). -/
noncomputable def afterCustomer (P : Params) (r : ℝ) (s : State) : State :=
  (s.1 - 1, orderStep P r (s.1 - 1) s.2)

/-- State after an item arrival: `Y := Y + 1`, `Z := Z − 1`, then update `T` and order
(steps 1–3). It is used only from states with `Z ≥ 1` (see `rate`), where the natural-number
subtraction `s.2 - 1` is the true `Z − 1`. -/
noncomputable def afterItem (P : Params) (r : ℝ) (s : State) : State :=
  (s.1 + 1, orderStep P r (s.1 + 1) (s.2 - 1))

/-- Transition rates of the GBS chain `(Y, Z)` under exponential lead times: customers arrive
at rate `r`; each of the `Z` in-transit items arrives at rate `β`, so items arrive at rate `βZ`
(only when `Z ≥ 1`). -/
noncomputable def rate (P : Params) (r : ℝ) (s s' : State) : ℝ :=
  (if s' = afterCustomer P r s then r else 0) +
  (if 1 ≤ s.2 ∧ s' = afterItem P r s then P.β * (s.2 : ℝ) else 0)

/-- Total rate of leaving state `(Y, Z)`: `r + βZ`. -/
def exitRate (P : Params) (r : ℝ) (s : State) : ℝ := r + P.β * (s.2 : ℝ)

/-- One-step accessibility in the GBS chain: a jump `s → s'` has positive rate. -/
def Step (P : Params) (r : ℝ) (s s' : State) : Prop := 0 < rate P r s s'

/-- A stationary distribution of the GBS chain of system `r`. -/
def IsStationary (P : Params) (r : ℝ) (p : State → ℝ) : Prop :=
  IsCTMCStationary (rate P r) (exitRate P r) p

/-- The scaled centered inventory level `(Y − x∗)/√r`. -/
noncomputable def scaled (P : Params) (r : ℝ) (s : State) : ℝ :=
  ((s.1 : ℝ) - P.xs r) / Real.sqrt r

/-- The gap (15): `D = Z − ⌈T⌉`. -/
noncomputable def gapD (P : Params) (r : ℝ) (s : State) : ℝ :=
  (s.2 : ℝ) - ((⌈truncTarget P r s.1⌉ : ℤ) : ℝ)

/-- The gap (15): `D̃ = Z − ⌈T ∧ X⌉`. -/
noncomputable def gapDt (P : Params) (r : ℝ) (s : State) : ℝ :=
  (s.2 : ℝ) - ((⌈min (truncTarget P r s.1) (target P r s.1)⌉ : ℤ) : ℝ)

/-- The artificial process (§4.2): its in-transit level is `Ẑ = ⌈T̂⌉`, a function of `Ŷ = j`. -/
noncomputable def artZ (P : Params) (r : ℝ) (j : ℤ) : ℕ := ⌈truncTarget P r j⌉₊

/-- Rates of the artificial birth–death chain `Ŷ` on `ℤ`: down `j → j − 1` at rate `r`,
up `j → j + 1` at rate `β Ẑ = β ⌈T̂(j)⌉`. -/
noncomputable def artRate (P : Params) (r : ℝ) (j j' : ℤ) : ℝ :=
  (if j' = j - 1 then r else 0) + (if j' = j + 1 then P.β * (artZ P r j : ℝ) else 0)

/-- Total rate of leaving state `j` of the artificial chain: `r + β ⌈T̂(j)⌉`. -/
noncomputable def artExitRate (P : Params) (r : ℝ) (j : ℤ) : ℝ := r + P.β * (artZ P r j : ℝ)

/-- A stationary distribution of the artificial chain of system `r`. -/
def IsArtStationary (P : Params) (r : ℝ) (p : ℤ → ℝ) : Prop :=
  IsCTMCStationary (artRate P r) (artExitRate P r) p

/-- The reflected random walk `Q_n` of the proof of Lemma 4 (p. 16): from `q` it moves to
`q + (γ − 1)` with probability `1/2 + ϵ` and to `[q − γ] ∨ 0` with probability `1/2 − ϵ`
(natural-number subtraction is exactly `[q − γ] ∨ 0`). The two branches are added, so when
they land on the same state their probabilities add up. -/
noncomputable def qKernel (γ : ℕ) (ε : ℝ) (q q' : ℕ) : ℝ :=
  (if q' = q + (γ - 1) then 1 / 2 + ε else 0) + (if q' = q - γ then 1 / 2 - ε else 0)

end RandomLeadGBS.Diffusion


