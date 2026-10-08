-- Prove2me | Definitions.Def_FuzzyGames_TUCore_Basic
-- name    : FuzzyGames_TUCore_Basic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T17:05:52.054312+00:00
-- url     : https://prove2.me/theorems/9184ac91-4174-41f0-b086-f94777814b1e
-- title:
--   Fuzzy games with side payments, their cores and superdifferentials; games on a family of coalitions, balances, the fuzzy extension $\pi v$ and balancedness
-- statement:
--   Let $N=\{1,\dots,n\}$ be the set of players. This file fixes the objects of §1, §2 and §6 of Aubin's *Cooperative Fuzzy Games*.
--
--   1. **Fuzzy coalitions.** A coalition $A\subseteq N$ is identified with its characteristic vector $\tau^A\in\{0,1\}^n$, $\tau^A_i=1$ if $i\in A$ and $0$ otherwise; $\tau^N=(1,\dots,1)$. A *fuzzy coalition* is a vector $\tau\in[0,1]^n$ of participation rates.
--   2. **Fuzzy games with side payments.** A worth function $v$ on fuzzy coalitions with $v(0)=0$ that is positively homogeneous,
--   $$v(t\tau)=t\,v(\tau)\qquad (t>0,\ \tau\in\mathbb R^n_+),$$
--   so that it is defined on the whole orthant $\mathbb R^n_+$.
--   3. **Superdifferential.** For $\tau\in\mathbb R^n_+$,
--   $$\partial v(\tau)=\Big\{c\in\mathbb R^n:\ v(\tau)-v(\sigma)\ge\sum_{i\in N}c_i(\tau_i-\sigma_i)\ \text{ for all }\sigma\in\mathbb R^n_+\Big\}.$$
--   4. **Core of a fuzzy game.** The set of multiutilities $c\in\mathbb R^n$ with $\sum_{i\in N}c_i=v(\tau^N)$ and $\sum_{i\in N}\tau_ic_i\ge v(\tau)$ for every fuzzy coalition $\tau\in[0,1]^n$, i.e. allocations that no fuzzy coalition blocks.
--   5. **Gradient.** $Dv(\tau)$ is the vector of partial derivatives $\big(\partial v/\partial\tau_i\big)_{i\in N}$ at $\tau$.
--   6. **Admissible coalitions.** A family $\mathscr C$ of nonempty coalitions that contains $N$ and every singleton $\{i\}$.
--   7. **Balances.** For $\tau\in\mathbb R^n$, $\mathscr C(\tau)$ is the set of systems of weights $m(A)\ge0$, $A\in\mathscr C$, such that
--   $$\tau_i=\sum_{A\in\mathscr C,\ A\ni i}m(A)\qquad\text{for every } i\in N;$$
--   $\mathscr C(\tau^N)$ is the set of balances.
--   8. **Core of a game with side payments.** For $v:\mathscr C\to\mathbb R$, the set of $c\in\mathbb R^n$ with $\sum_{i\in N}c_i=v(N)$ and $\sum_{i\in A}c_i\ge v(A)$ for every $A\in\mathscr C$.
--   9. **Fuzzy extension.** For $\tau\in\mathbb R^n_+$,
--   $$\pi v(\tau)=\sup_{m\in\mathscr C(\tau)}\ \sum_{A\in\mathscr C}m(A)\,v(A).$$
--   10. **Balanced game.** $v$ is balanced if $\pi v(\tau^N)=v(N)$.
--
--   These objects carry the Bondareva–Shapley theorem in Aubin's form: a game on $\mathscr C$ has a nonempty core exactly when it is balanced, and then its core is the core of the fuzzy game $\pi v$.
--
--   **Formalization Note** Players are `Fin n`; multiutilities and fuzzy coalitions are functions `Fin n → ℝ` with the coordinatewise order. The paper defines $v$ on $[0,1]^n$ and extends it to $\mathbb R^n_+$ by homogeneity (§2 (2)); here a fuzzy game is a function on $\mathbb R^n$ whose values off $\mathbb R^n_+$ are never used, and homogeneity is required for every $\tau\ge0$. The paper leaves the range of $\sigma$ in (5) implicit; we take the domain $\mathbb R^n_+$ of the extended $v$. The empty coalition is excluded from $\mathscr C$ (the paper only uses $A\neq\emptyset$), so $v(\emptyset)=0$ plays no role; since $N\in\mathscr C$ and $\emptyset\notin\mathscr C$, the family exists only for $n\ge1$. Weights $m$ are functions on all coalitions that vanish off $\mathscr C$. $\pi v$ is a real supremum: for $\tau\in\mathbb R^n_+$ the set of values is nonempty (the singleton weights $m(\{i\})=\tau_i$) and bounded above ($0\le m(A)\le\tau_i$ for $i\in A$), so it is the paper's supremum; off $\mathbb R^n_+$ the set is empty and the value $0$ is never used. The misprints $v(\mathscr C)$ and $\tau^{\mathscr C}$ in §6 (2)–(3) are read as $v(A)$ and $\tau^A$, as §6 (4) settles.
-- source:
--   Aubin, Cooperative Fuzzy Games, Math. Oper. Res. 6(1) (1981), §1, §2 (1)–(5), §6 (1)–(4), (6), pp. 2–3, 7–8

import Mathlib
import Definitions.Def_FuzzyGames_NTUCore_Basic

namespace FuzzyGames.TUCore

open Finset

/-- A fuzzy game with side payments (§2): `v(0) = 0`, and `v` is positively homogeneous,
`v(t τ) = t v(τ)` for every `t > 0` and every `τ ∈ ℝ^n_+` (§2 (1); the paper extends `v` from
`[0,1]^n` to `ℝ^n_+` by (2)). Values of `v` off `ℝ^n_+` are never used. -/
def IsFuzzyTUGame {n : ℕ} (v : (Fin n → ℝ) → ℝ) : Prop :=
  v 0 = 0 ∧ ∀ t : ℝ, 0 < t → ∀ τ : Fin n → ℝ, 0 ≤ τ → v (t • τ) = t * v τ

/-- The superdifferential of `v` at `τ` (§2 (5)), where `σ` ranges over the domain `ℝ^n_+` of
the extended worth function. -/
def superdiff {n : ℕ} (v : (Fin n → ℝ) → ℝ) (τ : Fin n → ℝ) : Set (Fin n → ℝ) :=
  {c | ∀ σ : Fin n → ℝ, 0 ≤ σ → v τ - v σ ≥ ∑ i, c i * (τ i - σ i)}

/-- The core of the fuzzy game with side payments `v` (§2 (4)(a)): the multiutilities `c` with
`∑ c_i = v(τ^N)` that no fuzzy coalition `τ ∈ [0,1]^n` blocks, i.e. `∑ τ_i c_i ≥ v(τ)`. -/
def fuzzyCore {n : ℕ} (v : (Fin n → ℝ) → ℝ) : Set (Fin n → ℝ) :=
  {c | ∑ i, c i = v (FuzzyGames.NTUCore.coal Finset.univ) ∧ ∀ τ ∈ FuzzyGames.NTUCore.cube n, ∑ i, τ i * c i ≥ v τ}

/-- The gradient `Dv(τ)` of `v : ℝ^n → ℝ` at `τ`, as the vector of partial derivatives. -/
noncomputable def grad {n : ℕ} (v : (Fin n → ℝ) → ℝ) (τ : Fin n → ℝ) : Fin n → ℝ :=
  fun i => fderiv ℝ v τ (Pi.single i 1)

/-- The core of a (usual) game with side payments `v` on `𝒞` (§6 (1)):
`∑_{i ∈ N} c_i = v(N)` and `∑_{i ∈ A} c_i ≥ v(A)` for every `A ∈ 𝒞`. -/
def core {n : ℕ} (𝒞 : FuzzyGames.NTUCore.CoalFamily n) (v : Finset (Fin n) → ℝ) : Set (Fin n → ℝ) :=
  {c | ∑ i, c i = v Finset.univ ∧ ∀ A ∈ 𝒞.C, ∑ i ∈ A, c i ≥ v A}

/-- The fuzzy extension `πv(τ) = sup_{m ∈ 𝒞(τ)} ∑_{A ∈ 𝒞} m(A) v(A)` (§6 (2)). For `τ ∈ ℝ^n_+`
the set is nonempty and bounded, so the real supremum is the paper's; off `ℝ^n_+` it is empty
and the value (`0`) is never used. -/
noncomputable def piV {n : ℕ} (𝒞 : FuzzyGames.NTUCore.CoalFamily n) (v : Finset (Fin n) → ℝ) (τ : Fin n → ℝ) : ℝ :=
  sSup ((fun m => ∑ A ∈ 𝒞.C, m A * v A) '' FuzzyGames.NTUCore.balances 𝒞 τ)

/-- `v` is balanced (§6 (6)): `πv(τ^N) = v(N)`. -/
def IsBalanced {n : ℕ} (𝒞 : FuzzyGames.NTUCore.CoalFamily n) (v : Finset (Fin n) → ℝ) : Prop :=
  piV 𝒞 v (FuzzyGames.NTUCore.coal Finset.univ) = v Finset.univ

end FuzzyGames.TUCore


