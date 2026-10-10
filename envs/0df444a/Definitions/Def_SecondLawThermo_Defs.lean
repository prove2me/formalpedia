-- Prove2me | Definitions.Def_SecondLawThermo_Defs
-- name    : SecondLawThermo_Defs
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-09T21:24:52.207686+00:00
-- url     : https://prove2.me/theorems/0fe2bf94-c90b-4156-b974-8df0c4ef0d50
-- title:
--   Cyclic heat-engine model: cycles, realizable cones, the Clausius and Kelvin statements, Carnot engines
-- statement:
--   Throughout, $\Theta$ is a type of *empirical temperatures* carrying a linear order ($s<t$ means the reservoir at $s$ is colder than the one at $t$), and a **cycle** is a finitely supported function $c:\Theta\to\mathbb R$: for each reservoir temperature $t$, the number $c(t)$ is the net heat *absorbed by the device from* the reservoir at $t$ in one complete cycle (negative when heat is rejected to it), and only finitely many reservoirs are touched. The **work** delivered in the cycle is
--   $$W(c)=\sum_{t} c(t),$$
--   which is the first law for a device returning to its initial state. A set $\mathcal C$ of cycles stands for the physically realizable ones; it is assumed to be a convex cone: $0\in\mathcal C$, $c+d\in\mathcal C$ (run two devices side by side), and $r\cdot c\in\mathcal C$ for $r\ge 0$ (scale a device). A cycle is **reversible** when $c\in\mathcal C$ and $-c\in\mathcal C$. A cycle **operates between** $h$ and $k$ when $c(t)=0$ for every $t\notin\{h,k\}$. A **Carnot engine** between a hot reservoir $h$ and a cold reservoir $k$ is a reversible cycle operating between $h$ and $k$ with $c(h)>0$, $c(k)<0$ and $W(c)>0$. The **efficiency** relative to the hot reservoir is $\eta=W(c)/c(h)$.
--
--   Two impossibility statements are expressed in this language.
--
--   **Clausius statement** (*"Heat can never pass from a colder to a warmer body without some other change, connected therewith, occurring at the same time."*): for all temperatures $k<h$, every realizable cycle operating between $h$ and $k$ with $W(c)=0$ satisfies $c(k)\le 0$ — a device whose only effect is to run through a cycle, exchanging heat with just these two reservoirs and doing no net work, cannot take heat out of the colder one.
--
--   **Kelvin statement** (*"It is impossible for any system to operate in a thermodynamic cycle and deliver a net amount of energy by work to its surroundings while receiving energy by heat transfer from a single thermal reservoir."*): every realizable cycle that exchanges heat with a single reservoir satisfies $W(c)\le 0$.
--
--   Finally, $\mathcal C$ **admits Carnot engines** when for every pair $k<h$ there is a Carnot engine between $h$ and $k$.
--
--   **Formalization Note** Cycles are modelled as finitely supported real-valued functions on the temperature type, so that running devices side by side is addition and scaling a device is scalar multiplication; the heat sign convention is "positive into the device". "Adiabatic enclosure", working substance, and the internal mechanism of a device play no role: a device is recorded only by the heat it draws from each reservoir.
-- source:
--   Wikipedia, "Second law of thermodynamics", revision oldid=1378607758, https://en.wikipedia.org/w/index.php?title=Second_law_of_thermodynamics&oldid=1378607758; sections "Clausius statement", "Kelvin statements", "Carnot's principle", "Thermodynamic temperature" (eq. (1))

import Mathlib

namespace SecondLawThermo

/-- A cyclic process (one complete cycle of a cyclically operating device) exchanging heat with
finitely many thermal reservoirs. Reservoirs are labelled by their empirical temperature, an
element of the linearly ordered type `Θ` (`s < t` means that the reservoir at `s` is colder than
the one at `t`). The value `c t` is the net heat absorbed by the device from the reservoir at
temperature `t` during one cycle (heat entering the device is positive, heat leaving it is
negative); all but finitely many values vanish. -/
abbrev Cycle (Θ : Type*) := Θ →₀ ℝ

variable {Θ : Type*}

/-- The net work delivered by the device to its surroundings during one cycle. Since the device
returns to its initial state, the first law of thermodynamics makes it equal to the total net
heat absorbed from all reservoirs. -/
noncomputable def work (c : Cycle Θ) : ℝ := c.sum fun _ q => q

/-- The set `𝒞` of cycles that can actually be realized forms a convex cone: doing nothing is
realizable, two realizable devices may be run side by side (their heat exchanges add up), and a
realizable device may be scaled by any nonnegative factor. -/
structure IsCycleCone (𝒞 : Set (Cycle Θ)) : Prop where
  zero_mem : (0 : Cycle Θ) ∈ 𝒞
  add_mem : ∀ c d, c ∈ 𝒞 → d ∈ 𝒞 → c + d ∈ 𝒞
  smul_mem : ∀ (r : ℝ) (c : Cycle Θ), 0 ≤ r → c ∈ 𝒞 → r • c ∈ 𝒞

/-- A cycle is reversible (with respect to the realizable cycles `𝒞`) if both it and the exactly
reversed cycle, in which every heat exchange changes sign, are realizable. -/
def IsReversible (𝒞 : Set (Cycle Θ)) (c : Cycle Θ) : Prop := c ∈ 𝒞 ∧ -c ∈ 𝒞

/-- The cycle `c` exchanges heat only with the reservoirs at temperatures `h` and `k`. -/
def OperatesBetween (c : Cycle Θ) (h k : Θ) : Prop := ∀ t, t ≠ h → t ≠ k → c t = 0

/-- **Clausius statement.** Heat can never pass from a colder to a warmer body without some other
change: no realizable cycle that exchanges heat only with a hotter reservoir at `h` and a colder
reservoir at `k < h`, and produces no net work, absorbs a positive amount of heat from the colder
reservoir. -/
def ClausiusStatement [LinearOrder Θ] (𝒞 : Set (Cycle Θ)) : Prop :=
  ∀ h k : Θ, k < h → ∀ c ∈ 𝒞, OperatesBetween c h k → work c = 0 → c k ≤ 0

/-- **Kelvin statement.** No realizable cycle that exchanges heat with a single thermal reservoir
delivers a positive net amount of work. -/
def KelvinStatement (𝒞 : Set (Cycle Θ)) : Prop :=
  ∀ t : Θ, ∀ c ∈ 𝒞, (∀ s, s ≠ t → c s = 0) → work c ≤ 0

/-- A **Carnot engine** between the hot reservoir `h` and the cold reservoir `k`: a reversible
cycle exchanging heat only with these two reservoirs, absorbing a positive heat `q_H = c h` from
the hot reservoir, rejecting heat to the cold one (`q_C = c k < 0`) and delivering positive net
work. -/
def IsCarnotEngine (𝒞 : Set (Cycle Θ)) (c : Cycle Θ) (h k : Θ) : Prop :=
  IsReversible 𝒞 c ∧ OperatesBetween c h k ∧ 0 < c h ∧ c k < 0 ∧ 0 < work c

/-- Every pair of reservoirs at different temperatures admits a Carnot engine operating between
them. -/
def CarnotEnginesExist [LinearOrder Θ] (𝒞 : Set (Cycle Θ)) : Prop :=
  ∀ h k : Θ, k < h → ∃ c, IsCarnotEngine 𝒞 c h k

/-- The efficiency `η = W / q_H` of a cycle, relative to its hot reservoir `h`: net work per cycle
divided by the heat absorbed from `h` (meaningful when `c h > 0`). -/
noncomputable def efficiency (c : Cycle Θ) (h : Θ) : ℝ := work c / c h

end SecondLawThermo


