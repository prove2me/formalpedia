-- Prove2me | Definitions.Def_ReusableAssort_Hybrid_Process
-- name    : ReusableAssort_Hybrid_Process
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T17:28:23.116295+00:00
-- url     : https://prove2.me/theorems/415f74c4-f052-43eb-b197-ff298759b6db
-- title:
--   Four-step template, p. 11 — the online rental process and its expected revenues
-- statement:
--   This file defines the random process run by every simulation-based algorithm of the paper (the four-step template of p. 11), for a fixed LP solution $y$ and a choice of *inner discarding rule* for each product.
--
--   A rule for product $i$ is either *random discarding* with probability $\gamma$ (Algorithm 2), which keeps $i$ with probability $1 - \gamma$, or a *revenue threshold* $P$ (Algorithm 3), which keeps $i$ at time $t$ for type $z$ exactly when $r^z_i \ge P(t, z)$.
--
--   At each time $t$ the following happens, given the history:
--   1. the type $z_t \sim F_t$ is revealed;
--   2. *simulation*: $\hat S \sim \{y_{S,t,z_t}\}_{S \in \mathcal S}$;
--   3. *discarding*: each $i \in \hat S$ is removed if no unit of $i$ is on hand, and otherwise kept independently with the probability of its rule; $\bar S$ is the set of kept products;
--   4. *post-processing*: $\tilde S$ is drawn by Procedure 1 on $(\phi^{z_t}, \bar S, \{\phi^{z_t}(\hat S, i)\}_{i \in \bar S})$ and offered;
--   5. the consumer rents $i \in \tilde S$ with probability $\phi^{z_t}(\tilde S, i)$ (or nothing), and a rented unit is away for a fresh duration $d \sim g^{z_t}_i$: it is out at times $t, \dots, t+d-1$ and back at $t + d$.
--
--   The process may start at any time $t_0$ with units of each product already out and due back at given later times. The law of a whole sample path is the product of the conditional laws of its steps. From it the file defines the expected revenue (total, per product, and per product and time) and the probability that no unit of product $i$ is on hand at the beginning of time $t$.
--
--   These are the quantities in which the paper's competitive-ratio statements are written: the algorithms of the mission differ only in the rules they assign.
--
--   **Formalization Note** A step is a tuple (type, $\hat S$, $\bar S$, $\tilde S$, choice, duration), and probabilities and expectations are finite sums over paths; no measure theory is used. When the consumer rents nothing the duration is forced to $0$. Units on hand are counted in $\mathbb N$ from $c_i$; for a valid start state (all outstanding units due in $(t_0, t_0 + T]$, at most $c_i$ of them) the count never truncates on paths of positive probability. `Rule.Valid` says that a random-discard probability lies in $[0,1]$.
-- source:
--   Feng, Niazadeh & Saberi, arXiv:2512.06997v1, p. 8 (model), p. 11 (four-step template), p. 15 (Algorithm 2), p. 18 (Algorithm 3), ec10 (indicators I_{i,t}, I_{i,τ,t}), ec12 (state J)

import Mathlib
import Definitions.Def_ReusableAssort_Hybrid_SubAssort

namespace ReusableAssort.Hybrid

/-- One step of the online process (four-step template, p. 11): the realized type `z_t`, the
simulated assortment `Ŝ_t`, the undiscarded set `S̄_t`, the offered assortment `S̃_t`, the
consumer's choice (`none` = no rental) and the rental duration (irrelevant, and forced to `0`,
when there is no rental). -/
abbrev Step (n T : ℕ) (Z : Type) :=
  Z × Finset (Fin n) × Finset (Fin n) × Finset (Fin n) × Option (Fin n) × Fin (T + 1)

/-- A per-product inner discarding rule: random discarding with probability `γ`
(Algorithm 2), or discarding by a revenue threshold `P t z` (Algorithm 3). -/
inductive Rule (Z : Type) where
  | random (γ : ℝ)
  | threshold (P : ℕ → Z → ℝ)

/-- A rule is a genuine discarding rule: a random-discard probability lies in `[0, 1]`. -/
def Rule.Valid {Z : Type} : Rule Z → Prop
  | Rule.random γ => γ ∈ Set.Icc (0 : ℝ) 1
  | Rule.threshold _ => True

variable {n T : ℕ} {Z : Type} [Fintype Z] [DecidableEq Z]

/-- Probability that the inner rule of product `i` keeps `i` at time `t` with type `z`,
given that a unit of `i` is on hand. -/
noncomputable def keep (I : Instance n T Z) (i : Fin n) : Rule Z → ℕ → Z → ℝ
  | Rule.random γ, _, _ => 1 - γ
  | Rule.threshold P, t, z => if P t z ≤ I.r z i then 1 else 0

/-- Units of product `i` on hand at step `k` (time `t₀ + k`) along the path `v`, for a run
started at time `t₀` with `ret i s` units of `i` out and returning at time `s`. A unit rented at
step `j` with duration `d` is out at steps `j, …, j + d - 1`. -/
def onHand (I : Instance n T Z) (t₀ : ℕ) (ret : Fin n → ℕ → ℕ)
    (v : Fin (T + 1 - t₀) → Step n T Z) (i : Fin n) (k : ℕ) : ℕ :=
  I.c i - ∑ s ∈ Finset.Ioc (t₀ + k) (t₀ + T), ret i s
    - (Finset.univ.filter (fun j : Fin (T + 1 - t₀) =>
        j.1 < k ∧ (v j).2.2.2.2.1 = some i ∧ k < j.1 + ((v j).2.2.2.2.2 : ℕ))).card

/-- The conditional law of step `k` (at time `t = t₀ + k`) given the earlier steps of the
path: type `z ∼ F_t`; `Ŝ ∼ y_{·,t,z}` over `𝒮`; each `i ∈ Ŝ` kept independently with
probability `0` if no unit of `i` is on hand and `keep` otherwise; `S̃ ∼` Procedure 1 on
`(ϕ^z, S̄, {ϕ^z(Ŝ, i)})`; the consumer picks `i ∈ S̃` w.p. `ϕ^z(S̃, i)` (nothing otherwise);
the duration is drawn from `g^z_i`. -/
noncomputable def kernel (I : Instance n T Z) (y : ℕ → Z → Finset (Fin n) → ℝ)
    (rule : Fin n → Rule Z) (t₀ : ℕ) (ret : Fin n → ℕ → ℕ)
    (v : Fin (T + 1 - t₀) → Step n T Z) (k : Fin (T + 1 - t₀)) : ℝ :=
  let t := t₀ + k.1
  let z := (v k).1
  let Shat := (v k).2.1
  let Sbar := (v k).2.2.1
  let Stil := (v k).2.2.2.1
  let ch := (v k).2.2.2.2.1
  let d := (v k).2.2.2.2.2
  let a : Fin n → ℝ := fun i => if onHand I t₀ ret v i k.1 = 0 then 0 else keep I i (rule i) t z
  I.F t z * y t z Shat * (if Shat ∈ I.feas then 1 else 0)
    * ((if Sbar ⊆ Shat then 1 else 0) * (∏ i ∈ Sbar, a i) * ∏ i ∈ Shat \ Sbar, (1 - a i))
    * subAssort (I.phi z) Sbar (fun i => I.phi z Shat i) Stil
    * (match ch with
        | some i => if i ∈ Stil then I.phi z Stil i else 0
        | none => 1 - ∑ i ∈ Stil, I.phi z Stil i)
    * (match ch with
        | some i => I.g z i (d : ℕ)
        | none => if (d : ℕ) = 0 then 1 else 0)

/-- Probability of the whole path `v` (steps at times `t₀, …, T`). -/
noncomputable def pathProb (I : Instance n T Z) (y : ℕ → Z → Finset (Fin n) → ℝ)
    (rule : Fin n → Rule Z) (t₀ : ℕ) (ret : Fin n → ℕ → ℕ)
    (v : Fin (T + 1 - t₀) → Step n T Z) : ℝ :=
  ∏ k, kernel I y rule t₀ ret v k

/-- Revenue collected from product `i` at step `k` of the path `v` (`0` past the horizon). -/
noncomputable def revAt (I : Instance n T Z) (t₀ : ℕ) (i : Fin n)
    (k : ℕ) (v : Fin (T + 1 - t₀) → Step n T Z) : ℝ :=
  if h : k < T + 1 - t₀ then
    (if (v ⟨k, h⟩).2.2.2.2.1 = some i then I.r (v ⟨k, h⟩).1 i else 0)
  else 0

/-- Expected revenue from product `i` over times `t₀, …, T`. -/
noncomputable def expRevProd (I : Instance n T Z) (y : ℕ → Z → Finset (Fin n) → ℝ)
    (rule : Fin n → Rule Z) (t₀ : ℕ) (ret : Fin n → ℕ → ℕ) (i : Fin n) : ℝ :=
  ∑ v, pathProb I y rule t₀ ret v * ∑ k ∈ Finset.range (T + 1 - t₀), revAt I t₀ i k v

/-- Total expected revenue over times `t₀, …, T`. -/
noncomputable def expRev (I : Instance n T Z) (y : ℕ → Z → Finset (Fin n) → ℝ)
    (rule : Fin n → Rule Z) (t₀ : ℕ) (ret : Fin n → ℕ → ℕ) : ℝ :=
  ∑ i, expRevProd I y rule t₀ ret i

/-- Expected revenue from product `i` at time `t ≥ t₀`: the paper's `E[r^{z_t}_i I_{i,t}]`. -/
noncomputable def expRevAt (I : Instance n T Z) (y : ℕ → Z → Finset (Fin n) → ℝ)
    (rule : Fin n → Rule Z) (t₀ : ℕ) (ret : Fin n → ℕ → ℕ) (i : Fin n) (t : ℕ) : ℝ :=
  ∑ v, pathProb I y rule t₀ ret v * revAt I t₀ i (t - t₀) v

/-- Probability that no unit of product `i` is on hand at the beginning of time `t ≥ t₀`:
the paper's `Pr[Σ_{τ<t} I_{i,τ} I_{i,τ,t} ≥ c_i]`. -/
noncomputable def probNoUnit (I : Instance n T Z) (y : ℕ → Z → Finset (Fin n) → ℝ)
    (rule : Fin n → Rule Z) (t₀ : ℕ) (ret : Fin n → ℕ → ℕ) (i : Fin n) (t : ℕ) : ℝ :=
  ∑ v, pathProb I y rule t₀ ret v * (if onHand I t₀ ret v i (t - t₀) = 0 then 1 else 0)

/-- A valid start state at time `t₀`: every outstanding unit returns at a time in
`(t₀, t₀ + T]`, and at most `c_i` units of each product are out. -/
def ValidStart (I : Instance n T Z) (t₀ : ℕ) (ret : Fin n → ℕ → ℕ) : Prop :=
  (∀ i s, s ∉ Finset.Ioc t₀ (t₀ + T) → ret i s = 0) ∧
  (∀ i, ∑ s ∈ Finset.Ioc t₀ (t₀ + T), ret i s ≤ I.c i)

end ReusableAssort.Hybrid


