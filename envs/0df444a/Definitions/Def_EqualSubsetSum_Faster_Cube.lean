-- Prove2me | Definitions.Def_EqualSubsetSum_Faster_Cube
-- name    : EqualSubsetSum_Faster_Cube
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T23:23:57.976296+00:00
-- url     : https://prove2.me/theorems/61b7dd75-c9f4-4637-b03d-8228a85243b8
-- title:
--   Translated cubes, free coordinates, doubled entries and the parity classes D_T (§2.2, Lemma 4.5)
-- statement:
--   A **translated cube** is a product $C=C_1\times\dots\times C_n$ of sets $C_i\subseteq\mathbb Z$, each with one or two elements, such that all two-element sets have the same difference $\sigma$, the **step**, with $\sigma\in\{1,2\}$. A coordinate is **free** when $|C_i|=2$; $v$ denotes the number of free coordinates, and the **members** of $C$ are the vectors $u$ with $u_i\in C_i$ for all $i$.
--
--   For $v\in\mathbb Z^n$, $c(v)$ is the number of **doubled** entries, i.e. entries equal to $\pm2$. For $z\in\mathbb Z^n$ and $T\subseteq\{1,\dots,n\}$,
--   $$D_T=\{v\in\{-2,\dots,2\}^n:\ v\cdot z=0,\ \text{the odd entries of } v \text{ are exactly those indexed by } T\}.$$
-- source:
--   Cheshm Jahan, Keshavarz Hedayati, Safari, Shahrezaei, Faster Equal-Subset-Sum via Truncated Inclusion–Exclusion, STOC 2027 submission (manuscript, sha256 7ad8c8b2…61dacd1), p. 14, §2.2; p. 28, Lemma 4.5

import Mathlib
import Definitions.Def_EqualSubsetSum_Faster_Problem

namespace EqualSubsetSum.Faster

/-! Translated cubes (§2.2, p. 14) and the parity classes `D_T` of Lemma 4.5 (§4.3, p. 28). -/

/-- `C = C₁ × ⋯ × Cₙ` is a *translated cube*: every `Cᵢ ⊆ ℤ` has one or two elements, and all
two-element sets have the same difference `σ`, the *step*, which is `1` or `2`. -/
def IsTranslatedCube {n : ℕ} (C : Fin n → Finset ℤ) : Prop :=
  ∃ σ : ℤ, (σ = 1 ∨ σ = 2) ∧ ∀ i, (C i).card = 1 ∨ ∃ c : ℤ, C i = {c, c + σ}

/-- The number `v` of *free* coordinates of `C`: those whose set has two elements. -/
def freeCoords {n : ℕ} (C : Fin n → Finset ℤ) : ℕ :=
  (Finset.univ.filter fun i => (C i).card = 2).card

/-- The members of `C`: the vectors `u` with `uᵢ ∈ Cᵢ` for every `i`. -/
def cubeMembers {n : ℕ} (C : Fin n → Finset ℤ) : Finset (Fin n → ℤ) := Fintype.piFinset C

/-- `c(v)`: the number of *doubled* entries (`±2`) of `v`. -/
def doubledCount {n : ℕ} (v : Fin n → ℤ) : ℕ :=
  (Finset.univ.filter fun i => v i = 2 ∨ v i = -2).card

/-- `D_T` (Lemma 4.5): the vectors `v ∈ {-2, …, 2}ⁿ` with `v · z = 0` whose odd entries are
exactly those indexed by `T`. -/
noncomputable def parityClass {n : ℕ} (z : Fin n → ℤ) (T : Finset (Fin n)) : Finset (Fin n → ℤ) :=
  (Fintype.piFinset fun _ => Finset.Icc (-2 : ℤ) 2).filter fun v =>
    weightedSum v z = 0 ∧ ∀ i, (Odd (v i) ↔ i ∈ T)

end EqualSubsetSum.Faster


