-- Prove2me | Definitions.Def_MondererShapley_Congestion_FacilityConstruction
-- name    : MondererShapley_Congestion_FacilityConstruction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T19:15:46.074266+00:00
-- url     : https://prove2.me/theorems/7d3166b9-703c-471c-8682-906a260fcc36
-- title:
--   The facility set, strategies and vectors $x^n$, $x^1$ of the proof of Theorem 3.2 (Monderer–Shapley, pp. 139–141)
-- statement:
--   These are the objects built in Appendix B of Monderer and Shapley to represent a finite potential game $\Gamma$ (players $N = \{1,\dots,n\}$, finite strategy sets $Y^i$, payoffs $u^i$, a potential $P$) by a congestion game.
--
--   1. **Facilities.** $M = \times_{i=1}^n \{0,1\}^{K(i)}$: a facility $\varepsilon = (\varepsilon^1, \dots, \varepsilon^n)$ is, for every player $i$, a $0$–$1$ vector $\varepsilon^i$ indexed by the strategies of player $i$.
--   2. **Sums over facilities.** For $x \in \mathbb{R}^M$ and $B \subseteq M$, $x(B) = \sum_{j \in B} x(j)$.
--   3. **Strategies.** For a strategy $a^i_l$ of player $i$, $A^i_l = \{\varepsilon \in M : \varepsilon^i_l = 1\}$.
--   4. **The facility $\varepsilon(m)$.** For a profile $m = (m_1,\dots,m_n)$, $\varepsilon^i_{m_i} = 1$ for every $i$ and $\varepsilon^i_k = 0$ for every $k \neq m_i$; and $M_1 = \{\varepsilon(m) : m \in K\}$ (B.3).
--   5. **The vector $x^n$.** $x^n(\varepsilon) = P(a^1_{m_1}, \dots, a^n_{m_n})$ if $\varepsilon = \varepsilon(m) \in M_1$, and $x^n(\varepsilon) = 0$ if $\varepsilon \notin M_1$.
--   6. **The facility $\varepsilon(m^i)$.** For a player $i$ and $m^i = (m_k)_{k \neq i}$: $\varepsilon^i_s = 1$ for every $s$, and for every $k \neq i$, $\varepsilon^k_s = 0$ iff $s = m_k$; and $M_2 = \{\varepsilon(m^i)\}$ (B.5).
--   7. **The vector $x^1$.** With $Q^i(a^{-i}) = u^i(a^{-i}, a^i) - P(a^{-i}, a^i)$ for an arbitrarily chosen $a^i \in Y^i$ (B.4),
--   $$x^1(\varepsilon) = \begin{cases} Q^i\big((a^k_{m_k})_{k\neq i}\big) & \text{if } \varepsilon \in M_2 \text{ and } \varepsilon = \varepsilon(m^i),\\ 0 & \text{if } \varepsilon \notin M_2.\end{cases}$$
--
--   These objects are the scaffolding of the milestones (B.2) and (B.6) of the proof of Theorem 3.2.
--
--   **Formalization Note.** The paper enumerates $Y^i = \{a^i_1, \dots, a^i_{k(i)}\}$ and indexes by $K(i) = \{1,\dots,k(i)\}$; here the index set of player $i$ is $Y^i$ itself, so a facility is a function assigning to every player $i$ a Boolean vector indexed by $Y^i$ (`true` = 1) and a profile $m \in K$ is a strategy profile. $m^i$ is passed as a full profile whose $i$-th coordinate is ignored. $x^n$ and $x^1$ pick, by choice, a profile (respectively a pair $(i, m)$) representing $\varepsilon$; the chosen $i$-th coordinate of $m$ plays the role of the arbitrary $a^i$ in (B.4). $x(B)$ is a finite sum (`finsum`) over the finite facility set.
-- source:
--   Monderer and Shapley, Potential Games, Games Econ. Behav. 14 (1996), pp. 139–141 (PDF pp. 16–18), Appendix B: notation x(B) (p. 139), M and A^i_l (p. 140), ε(m), (B.3), x^n (p. 140), (B.4), ε(m^i), (B.5), x^1 (p. 141)

import Mathlib

namespace MondererShapley.Congestion

/-- Monderer and Shapley (1996), p. 140: the facility set `M = ×_{i=1}^{n} {0, 1}^{K(i)}` of the
congestion game built in the proof of Theorem 3.2. A facility `ε = (ε¹, …, εⁿ)` assigns to every
player `i` a 0–1 vector `εⁱ` indexed by the strategies of player `i` (`true` = 1, `false` = 0).

**Formalization Note.** The paper enumerates `Yⁱ = {aⁱ_1, …, aⁱ_{k(i)}}` and indexes by
`K(i) = {1, …, k(i)}`; here the index set of player `i` is `Yⁱ` itself (`l ∈ K(i)` ↔ `aⁱ_l ∈ Yⁱ`). -/
abbrev Facility {ι : Type*} (Y : ι → Type*) : Type _ := ∀ i, Y i → Bool

/-- Monderer and Shapley (1996), p. 139: for `x ∈ R^M` and `B ⊆ M`, `x(B) = Σ_{j∈B} x(j)`
(the facility set is finite). -/
noncomputable def vecSum {F : Type*} (x : F → ℝ) (B : Set F) : ℝ := ∑ᶠ j ∈ B, x j

/-- Monderer and Shapley (1996), p. 140: the strategy `Aⁱ_l = {ε ∈ M : εⁱ_l = 1}` of player `i` that
corresponds to the strategy `aⁱ_l` (here `l`) of the potential game. -/
def stratFac {ι : Type*} {Y : ι → Type*} (i : ι) (l : Y i) : Set (Facility Y) :=
  {ε | ε i l = true}

/-- Monderer and Shapley (1996), p. 140: for a profile `m = (m₁, …, mₙ) ∈ K`, the facility `ε(m)`
with `εⁱ_{m_i} = 1` for every `i` and `εⁱ_k = 0` for every `i` and every `k ≠ m_i`. -/
def epsOf {ι : Type*} {Y : ι → Type*} [∀ i, DecidableEq (Y i)] (m : ∀ i, Y i) : Facility Y :=
  fun i y => decide (y = m i)

/-- Monderer and Shapley (1996), p. 140, (B.3): `M₁ = {ε(m) : m ∈ K}`. -/
def M1 {ι : Type*} (Y : ι → Type*) [∀ i, DecidableEq (Y i)] : Set (Facility Y) :=
  Set.range (epsOf (Y := Y))

open Classical in
/-- Monderer and Shapley (1996), p. 140: the vector `xⁿ ∈ R^M`, `xⁿ(ε) = P(a¹_{m₁}, …, aⁿ_{mₙ})` if
`ε = ε(m) ∈ M₁` and `xⁿ(ε) = 0` if `ε ∉ M₁` (well defined because `m ↦ ε(m)` is injective). -/
noncomputable def xn {ι : Type*} {Y : ι → Type*} [∀ i, DecidableEq (Y i)]
    (P : (∀ i, Y i) → ℝ) (ε : Facility Y) : ℝ :=
  if h : ∃ m : ∀ i, Y i, ε = epsOf m then P h.choose else 0

/-- Monderer and Shapley (1996), p. 141: for a player `i` and `mⁱ = (m_k)_{k≠i} ∈ K⁻ⁱ`, the facility
`ε(mⁱ)` with `εⁱ_s = 1` for every `s ∈ K(i)`, and, for every `k ≠ i`, `εᵏ_s = 0` iff `s = m_k`.

**Formalization Note.** `mⁱ` is passed as a full profile `m` whose `i`-th coordinate is ignored. -/
def epsMinus {ι : Type*} [DecidableEq ι] {Y : ι → Type*} [∀ i, DecidableEq (Y i)]
    (i : ι) (m : ∀ k, Y k) : Facility Y :=
  fun k y => if k = i then true else decide (y ≠ m k)

/-- Monderer and Shapley (1996), p. 141, (B.5): `M₂ = {ε(mⁱ) : i ∈ N, mⁱ ∈ K⁻ⁱ}`. -/
def M2 {ι : Type*} [DecidableEq ι] (Y : ι → Type*) [∀ i, DecidableEq (Y i)] :
    Set (Facility Y) :=
  {ε | ∃ (i : ι) (m : ∀ k, Y k), ε = epsMinus i m}

open Classical in
/-- Monderer and Shapley (1996), p. 141, (B.4) and the definition of `x¹`: with
`Qⁱ(a⁻ⁱ) = uⁱ(a⁻ⁱ, aⁱ) − P(a⁻ⁱ, aⁱ)` for an arbitrarily chosen `aⁱ ∈ Yⁱ`,
`x¹(ε) = Qⁱ((aᵏ_{mⁱ_k})_{k≠i})` if `ε ∈ M₂` and `ε = ε(mⁱ)`, and `x¹(ε) = 0` if `ε ∉ M₂`.

**Formalization Note.** For `ε ∈ M₂` a pair `(i, m)` with `ε = ε(mⁱ)` is chosen; the `i`-th
coordinate of the chosen profile `m` plays the role of the arbitrarily chosen `aⁱ`, so
`Qⁱ(m⁻ⁱ) = uⁱ(m) − P(m)`. -/
noncomputable def x1 {ι : Type*} [DecidableEq ι] {Y : ι → Type*} [∀ i, DecidableEq (Y i)]
    (u : ι → (∀ i, Y i) → ℝ) (P : (∀ i, Y i) → ℝ) (ε : Facility Y) : ℝ :=
  if h : ∃ (i : ι) (m : ∀ k, Y k), ε = epsMinus i m then
    u h.choose h.choose_spec.choose - P h.choose_spec.choose
  else 0

end MondererShapley.Congestion


