-- Prove2me | Definitions.Def_UniversalNonstochastic_Main_Effective
-- name    : UniversalNonstochastic_Main_Effective
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T07:55:46.17445+00:00
-- url     : https://prove2.me/theorems/b27d2b00-8a6c-462d-823b-149a48856f90
-- title:
--   Effectivity notions: lower/upper semicomputable and computable real functions
-- statement:
--   A **rational name** is a pair $(a,b)\in\mathbb Z\times\mathbb N_0$, read as the rational number $a/(b+1)$; every rational number has such a name. All effectivity notions below use Mathlib's standard computability theory (partial recursive functions on `Primcodable` types).
--
--   1. A real function $f:\mathcal A\to\mathbb R$ on a type with a computable coding is **lower semicomputable** if the set of pairs $(x,r)$ of an argument and a rational name with $r<f(x)$ is recursively enumerable. Equivalently, $f$ is the pointwise limit of a computable nondecreasing sequence of rational approximations from below.
--   2. A function $F:\mathcal A\to\mathbb N_0$ is **upper semicomputable** if $\{(x,k) : F(x)<k\}$ is recursively enumerable. Equivalently, there is a computable approximation $F_s(x)\in\mathbb N_0\cup\{\infty\}$ that decreases to $F(x)$ as $s\to\infty$.
--   3. A real function $f$ is **computable** if there is a computable map $(x,k)\mapsto q(x,k)$ to rational names with $|f(x)-q(x,k)|\le 2^{-k}$ for all $x$ and $k$. This is uniform in the argument.
--
--   The lower semicomputability of deficiencies, which may take the value $+\infty$, is stated in the same form in the elementary-models definition. These are the standard notions of algorithmic information theory (see Shen, Uspensky and Vereshchagin, *Kolmogorov Complexity and Algorithmic Randomness*, the source's reference [16]), used throughout the mission for the universal semimeasure, the functions $F$ of Lemma 18 and Theorem 10, and the computable kernels of Lemma 17.
--
--   An object-space encoding is a bijection from a computably coded space to the positive integers, with computable forward and inverse maps. Sets and finite models are transported by its image map, as the source prescribes on pp.4–5.
-- source:
--   Vladimir Vovk, The universal measure of nonstochastic objects, STOC 2027 submission #11 (October 2026), SHA-256 1ca25c4b7c38d8f49718c9fecbc2a434a7592886b44992c4fbef31ab3f480078, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/11.pdf, Sect. 1 p.4 (conventions), Sect. 4 p.10 (lower semicomputable deficiencies), Lemma 17 p.15 (computable kernel), Lemma 18 p.16 (upper semicomputable F and its approximations)

import Mathlib

namespace UniversalNonstochastic.Main

/-- S, pp.4–5: an object space is identified with the positive integers by a fixed
computable bijection, whose inverse is computable as well. -/
structure ObjectEncoding (X : Type*) [Primcodable X] where
  equiv : X ≃ ℕ+
  computable_forward : Computable equiv
  computable_inverse : Computable equiv.symm

/-- Transport an arbitrary set of objects along the source's fixed bijection. -/
def ObjectEncoding.transportSet {X : Type*} [Primcodable X] (e : ObjectEncoding X)
    (A : Set X) : Set ℕ+ := e.equiv '' A

/-- Transport a finite model along the same bijection. -/
def ObjectEncoding.transportFinset {X : Type*} [Primcodable X] (e : ObjectEncoding X)
    (Ω : Finset X) : Finset ℕ+ := Ω.map e.equiv.toEmbedding

/-- A rational number written as a pair `(a, b) : ℤ × ℕ`, read as `a / (b + 1)`.
Every rational number has such a name, and the names carry Mathlib's standard
`Primcodable` structure on `ℤ × ℕ`. -/
noncomputable def ratVal (p : ℤ × ℕ) : ℝ := (p.1 : ℝ) / ((p.2 : ℝ) + 1)

/-- `f : α → ℝ` is lower semicomputable: the set of pairs `(x, r)` with `r < f x`
(`r` a rational name) is recursively enumerable. -/
def IsLowerSemicomputable {α : Type*} [Primcodable α] (f : α → ℝ) : Prop :=
  REPred fun p : α × (ℤ × ℕ) => ratVal p.2 < f p.1

/-- `F : α → ℕ` is upper semicomputable: the set of pairs `(x, k)` with `F x < k` is
recursively enumerable; equivalently `F` is the limit of a computable, pointwise
nonincreasing sequence of approximations with values in `ℕ ∪ {∞}`. -/
def IsUpperSemicomputableNat {α : Type*} [Primcodable α] (F : α → ℕ) : Prop :=
  REPred fun p : α × ℕ => F p.1 < p.2

/-- `f : α → ℝ` is computable as a real-valued function: there is a computable map
`(x, k) ↦ q(x, k)` to rational names with `|f x - q(x, k)| ≤ 2^{-k}` for all `x` and `k`. -/
def IsComputableRealFun {α : Type*} [Primcodable α] (f : α → ℝ) : Prop :=
  ∃ q : α → ℕ → ℤ × ℕ, Computable₂ q ∧ ∀ x k, |f x - ratVal (q x k)| ≤ (1 / 2 : ℝ) ^ k

end UniversalNonstochastic.Main


