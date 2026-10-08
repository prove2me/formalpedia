-- Prove2me | Definitions.Def_QualityEncroach_Differ_Benchmark
-- name    : QualityEncroach_Differ_Benchmark
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T00:22:45.105206+00:00
-- url     : https://prove2.me/theorems/8845c7f7-c41c-40a3-9385-0ef8b359d97c
-- title:
--   §3.2, p. 9 — the benchmark game without a direct channel and its subgame-perfect equilibria
-- statement:
--   The benchmark of §3.2 has no direct channel. The manufacturer chooses a wholesale price $w$ and a quality $u>0$; after observing them the retailer orders $q_R\ge 0$ and sells it at the market-clearing price $u(1-q_R)$. A unit of quality $u$ costs the manufacturer $ku^2$. The profits are
--
--   $$
--   \Pi^N_R = \bigl(u(1-q_R)-w\bigr)q_R,
--   \qquad
--   \Pi^N_M = (w-ku^2)\,q_R .
--   $$
--
--   A strategy profile $\tau$ consists of the manufacturer's choice $(w,u)$ and the retailer's rule $(w,u)\mapsto q_R$. It is a **subgame-perfect equilibrium** when (1) for every $w\in\mathbb R$ and $u>0$ the retailer's rule picks some $q_R\ge 0$ maximizing $\Pi^N_R$ over $q_R\ge 0$, and (2) the manufacturer's choice has $u>0$ and maximizes $\Pi^N_M$, evaluated at the retailer's rule, over all $w\in\mathbb R$, $u>0$.
--
--   This game supplies the benchmark profits $\Pi^N_M$ and $\Pi^N_R$ against which the paper measures the effect of encroachment.
--
--   **Formalization Note.** The order is restricted to $q_R\ge 0$; the paper's formula $q^N_R(w,u)=\tfrac12-\tfrac{w}{2u}$ is the interior best reply.
-- source:
--   Ha, Long & Nasiry, Quality in Supply Chain Encroachment, authors' manuscript, SSRN 3970373, p. 9, §3.2

import Mathlib

namespace QualityEncroach.Differ

/-!
# The benchmark without a direct channel (§3.2, p. 9)

The manufacturer chooses a wholesale price `w` and a quality `u > 0`; the retailer then orders
`q_R ≥ 0` and sells it at the market-clearing price `u (1 − q_R)`.
-/

/-- An outcome of the benchmark game. -/
structure BenchOutcome where
  w : ℝ
  u : ℝ
  qR : ℝ

/-- The retailer's benchmark profit `Π^N_R = (u (1 − q_R) − w) q_R` (p. 9). -/
def benchRetailerPayoff (o : BenchOutcome) : ℝ :=
  (o.u * (1 - o.qR) - o.w) * o.qR

/-- The manufacturer's benchmark profit `(w − k u²) q_R` (p. 9). -/
def benchMfrPayoff (k : ℝ) (o : BenchOutcome) : ℝ :=
  (o.w - k * o.u ^ 2) * o.qR

/-- A strategy profile of the benchmark game: the manufacturer's `(w, u)` and the retailer's
rule `order w u = q_R`. -/
structure BenchProfile where
  w : ℝ
  u : ℝ
  order : ℝ → ℝ → ℝ

/-- The outcome after the manufacturer chose `(w, u)` and the retailer follows `τ`. -/
def BenchProfile.outcomeAt (τ : BenchProfile) (w u : ℝ) : BenchOutcome :=
  ⟨w, u, τ.order w u⟩

/-- The equilibrium path of `τ`. -/
def BenchProfile.path (τ : BenchProfile) : BenchOutcome :=
  τ.outcomeAt τ.w τ.u

/-- `τ` is a subgame-perfect equilibrium of the benchmark game (`w ∈ ℝ`, `u > 0`, `q_R ≥ 0`). -/
def IsBenchSPE (k : ℝ) (τ : BenchProfile) : Prop :=
  (∀ w u : ℝ, 0 < u →
      0 ≤ τ.order w u ∧
      ∀ qR : ℝ, 0 ≤ qR → benchRetailerPayoff ⟨w, u, qR⟩ ≤ benchRetailerPayoff (τ.outcomeAt w u)) ∧
  (0 < τ.u ∧
      ∀ w u : ℝ, 0 < u → benchMfrPayoff k (τ.outcomeAt w u) ≤ benchMfrPayoff k τ.path)

end QualityEncroach.Differ


