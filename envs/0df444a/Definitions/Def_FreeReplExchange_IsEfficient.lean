-- Prove2me | Definitions.Def_FreeReplExchange_IsEfficient
-- name    : FreeReplExchange_IsEfficient
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T23:18:29.876993+00:00
-- url     : https://prove2.me/theorems/f2fb0eb9-4011-4615-a35c-cdd815b3bcce
-- title:
--   Desiderata: MIC, NIC, IR, stability and efficiency of a protocol
-- statement:
--   Let $M$ be a protocol for the instance $(x^{(0)},U)$.
--
--   1. $M$ is **MIC** if for every participating set and every history arising under any strategy profile, its proposals $P_t$ are MIC with respect to the current allocation $x^{(t-1)}$.
--   2. $M$ is **Nash incentive compatible (NIC)** if $u_i(M,P,\sigma^\star)\ge u_i(M,P,(\sigma_i,\sigma^\star_{P\setminus\{i\}}))$ for every $P$, every $i\in P$ and every strategy $\sigma_i$.
--   3. $M$ is **individually rational (IR)** if for every $i\in A$ and every $P\subseteq A\setminus\{i\}$, $u_i(M,P\cup\{i\},\sigma^\star)\ge u_i(M,P,\sigma^\star)$.
--   4. $M$ is **stable** if for every $P$ and every strategy profile,
--   $$\{p=((i,r),(j,s))\in F(x^{(\infty)},P):\Delta_i(p)>0,\ \Delta_j(p)>0\}\subseteq D_\infty .$$
--   5. A MIC protocol $M$ is **efficient** if for every $P\subseteq A$
--   $$\sum_{i\in A}\sum_{r=1}^m x^\star_{i,r}(M,P)=\max_{x\in X(x^{(0)},P)}\sum_{i\in A}\sum_{r=1}^m x_{i,r},$$
--   where $x^\star(M,P)$ is the terminal allocation under the accepting profile.
--
--   These are the guarantees of the main theorem.
--
--   **Formalization Note** The histories arising under a profile are those of its run. $\Delta_i(p)$ in stability is $\Delta_i(p,x^{(\infty)})$, which equals the slot form (16) for feasible $p$. Terminal quantities are read at the horizon of the Protocol module.
-- source:
--   Yang–Kandasamy, Pairwise Exchanges of Freely Replicable Goods with Negative Externalities, arXiv:2603.12403 (held version, sha256 3ae07967…), Desiderata 2–6, pp.15–18 (PDF pp.17–20), eqs. (7), (12)

import Mathlib
import Definitions.Def_FreeReplExchange_feasible
import Definitions.Def_FreeReplExchange_Protocol
import Definitions.Def_FreeReplExchange_IsMICSet

namespace FreeReplExchange

/-- A protocol is MIC, Desideratum 3, Yang–Kandasamy, *Pairwise Exchanges of Freely Replicable
Goods with Negative Externalities*, arXiv:2603.12403 (held version, sha256 3ae07967…), p.15
(PDF p.17): "for every participating set and every history arising under any strategy profile,
its proposals `P_t` are MIC with respect to the current allocation `x^(t−1)`".

**Formalization Note.** The histories arising under a profile `σ` are the `hist M P σ t`. -/
def IsMIC {A : Type*} [Fintype A] [DecidableEq A] {m : ℕ} (x0 : A → Fin m → Bool)
    (U : A → A → Fin m → ℝ) (M : Protocol A m) : Prop :=
  ∀ (P : Finset A) (σ : A → Strategy A m) (t : ℕ),
    IsMICSet U P (alloc x0 (hist M P σ t)) (M P (hist M P σ t))

/-- Nash incentive compatibility, Desideratum 2, p.15:
`u_i(M, P, σ⋆_P) ≥ u_i(M, P, (σ_i, σ⋆_{P∖{i}}))` for every `P`, every `i ∈ P` and every `σ_i`. -/
def IsNIC {A : Type*} [Fintype A] [DecidableEq A] {m : ℕ} (x0 : A → Fin m → Bool)
    (U : A → A → Fin m → ℝ) (M : Protocol A m) : Prop :=
  ∀ (P : Finset A), ∀ i ∈ P, ∀ σi : Strategy A m,
    util U i (xInf x0 M P (Function.update acceptAll i σi)) ≤ util U i (xInf x0 M P acceptAll)

/-- Individual rationality, Desideratum 4, p.17: for every `i ∈ A` and every `P ⊆ A ∖ {i}`,
`u_i(M, P ∪ {i}, σ⋆_{P∪{i}}) ≥ u_i(M, P, σ⋆_P)`. Utilities are defined for nonparticipants too. -/
def IsIR {A : Type*} [Fintype A] [DecidableEq A] {m : ℕ} (x0 : A → Fin m → Bool)
    (U : A → A → Fin m → ℝ) (M : Protocol A m) : Prop :=
  ∀ (i : A) (P : Finset A), i ∉ P →
    util U i (xInf x0 M P acceptAll) ≤ util U i (xInf x0 M (insert i P) acceptAll)

/-- Stability, Desideratum 5, p.17: for every participating set `P` and every strategy profile,
`{p = ((i, r), (j, s)) ∈ F(x^(∞), P) : ∆_i(p) > 0, ∆_j(p) > 0} ⊆ D_∞`.

**Formalization Note.** `∆_i(p)` is `∆_i(p, x^(∞))` of (8); for `p ∈ F(x^(∞), P)` both receiving
slots are empty, where (8) and (16) agree (p.16). -/
def IsStable {A : Type*} [Fintype A] [LinearOrder A] {m : ℕ} (x0 : A → Fin m → Bool)
    (U : A → A → Fin m → ℝ) (M : Protocol A m) : Prop :=
  ∀ (P : Finset A) (σ : A → Strategy A m), ∀ p ∈ feasible x0 U P (xInf x0 M P σ),
    0 < delta U (xInf x0 M P σ) p.i p → 0 < delta U (xInf x0 M P σ) p.j p → p ∈ Dinf M P σ

/-- Efficiency, Desideratum 6, (12), p.18: a MIC protocol is efficient if for every `P ⊆ A` its
terminal allocation under the accepting profile maximizes the number of filled slots over
`X(x^(0), P)`: `Σ_{i,r} x⋆_{i,r}(M, P) = max_{x ∈ X(x^(0), P)} Σ_{i,r} x_{i,r}`. -/
def IsEfficient {A : Type*} [Fintype A] [LinearOrder A] {m : ℕ} (x0 : A → Fin m → Bool)
    (U : A → A → Fin m → ℝ) (M : Protocol A m) : Prop :=
  IsMIC x0 U M ∧ ∀ P : Finset A, filledCount (xInf x0 M P acceptAll) = maxFilled x0 U P

end FreeReplExchange


