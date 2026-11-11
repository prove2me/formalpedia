-- Prove2me | Definitions.Def_OCEClocks_DisplayAds_OCEC
-- name    : OCEClocks_DisplayAds_OCEC
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T18:21:24.563202+00:00
-- url     : https://prove2.me/theorems/db2936d5-644d-42b6-be64-7e29c62fd62e
-- title:
--   OCEC generators and OCEC rounding (Definitions 2 and 3), and the fresh-competitor sets $S_i^{\mathrm{Ind}}$
-- statement:
--   Requests $j$ arrive in the order of $\{0,\dots,n-1\}$. Resources are $i\in\{0,\dots,m-1\}$.
--
--   **OCEC generator (Definition 2).** An OCEC generator is an online algorithm with internal randomness $\omega$ drawn from a probability space $(\Omega,P)$. On an input sequence $x\in[0,1]^n$, fixed independently of $\omega$, it returns clocks $Y_j(\omega)\in[0,\infty]$, where $Y_j$ depends on the input only through $x_1,\dots,x_j$. For every input sequence $x\in[0,1]^n$ it must satisfy:
--
--   1. **exponential marginals**: $Y_j\sim\mathrm{Exp}(x_j)$ for every $j$;
--   2. **negative association**: the clocks $(Y_j)_j$ are negatively associated.
--
--   **OCEC rounding (Definition 3).** Let $x\in[0,1]^{m\times n}$ with $\sum_i x_{ij}\le1$ for every $j$, fixed independently of the randomness. Run an independent copy $G_i$ of the generator for each resource $i$, feeding it $(x_{ij})_j$, and let $Y_{ij}$ be its clocks. Draw independent discard clocks $\bar Y_j\sim\mathrm{Exp}(1-\sum_i x_{ij})$. Request $j$ goes to the resource with the minimum clock $Y_{ij}$ if that clock is below $\bar Y_j$, and is discarded otherwise. $S_i$ is the set of requests allocated to $i$.
--
--   **Fresh competitors (Lemma 6).** For a resource $i$, $S_i^{\mathrm{Ind}}=\{j: Y_{ij}<Z_j\}$, where the fresh competing clocks $Z_j\sim\mathrm{Exp}(1-x_{ij})$ are independent of each other and of $i$'s generator.
--
--   These are the paper's central objects: the rounding scheme, and the comparison process that localises its analysis to one resource.
--
--   **Formalization Note** A generator is a pair `(P, Y)` with `Y : (Fin n → ℝ) → Ω → Fin n → ℝ≥0∞`. `IsOCECGenerator P Y` requires three things. `P` is a probability measure. `Y` is online: `Y x ω j` depends on `x` only through `x 0, …, x j`. For every `x ∈ [0,1]^n`, each `Y x · j` is measurable with law `expLaw (x j)`, and the family is `NegAssoc`. `roundingLaw P x` is the product of $m$ copies of `P` and the discard clocks. `allocated Y x ω i` is $S_i$; ties in the minimum (a null event) go to the smallest index. `freshLaw P x i` is the product of `P` with the fresh clocks, and `freshAllocated Y x i` is $S_i^{\mathrm{Ind}}$.
-- source:
--   Huang, Patton, Yang, Zhao, Online Correlated Exponential Clocks, STOC 2027 submission (manuscript of November 3, 2026, sha256 820333a3…), p. 6, Definitions 2 and 3; p. 7 (S_i; Lemma 6's S_i^Ind)

import Mathlib
import Definitions.Def_OCEClocks_DisplayAds_NegAssoc
import Definitions.Def_OCEClocks_DisplayAds_ExpClock

open MeasureTheory
open scoped ENNReal

namespace OCEClocks.DisplayAds

/-!
# OCEC generators and OCEC rounding (Definitions 2 and 3)

Huang, Patton, Yang, Zhao, *Online Correlated Exponential Clocks*, STOC 2027 submission
(manuscript of November 3, 2026), p. 6, Definitions 2 and 3; p. 7 (`S_i`), p. 7 Lemma 6
(`S_i^Ind`).

Requests are `Fin n`, in arrival order; resources are `Fin m`. A generator is a probability
space `(Ω, P)` of internal randomness together with the map `Y` sending an input sequence
`x ∈ ℝ^n` and an outcome `ω` to the clocks `(Y_j)_j ∈ [0, ∞]^n`.
-/

/-- The generator is online: the clock `Y_j` depends on the input only through `x_1, …, x_j`. -/
def IsOnline {n : ℕ} {Ω : Type*} (Y : (Fin n → ℝ) → Ω → Fin n → ℝ≥0∞) : Prop :=
  ∀ x x' : Fin n → ℝ, ∀ j : Fin n, (∀ j' : Fin n, j' ≤ j → x j' = x' j') →
    ∀ ω, Y x ω j = Y x' ω j

/-- Definition 2 (OCEC generator), p. 6. `P` is a probability measure (the generator's internal
randomness) and `Y` is online. For every input sequence `x ∈ [0, 1]^n` (fixed independently of
the internal randomness, i.e. deterministic): (1) every clock `Y_j` is a random variable with law
`Exp(x_j)` on `[0, ∞]`; (2) the clocks `(Y_j)_j` are negatively associated. -/
def IsOCECGenerator {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Y : (Fin n → ℝ) → Ω → Fin n → ℝ≥0∞) : Prop :=
  IsProbabilityMeasure P ∧ IsOnline Y ∧
  ∀ x : Fin n → ℝ, (∀ j, x j ∈ Set.Icc (0 : ℝ) 1) →
    (∀ j, Measurable (fun ω => Y x ω j) ∧
      P.map (fun ω => Y x ω j) = expLaw (ENNReal.ofReal (x j))) ∧
    NegAssoc P (fun j ω => Y x ω j)

/-- The probability space of OCEC rounding (Definition 3, p. 6): one independent copy of the
generator's randomness per resource `i` and, independently, one discard clock
`Ȳ_j ∼ Exp(1 - Σ_i x_ij)` per request `j`. -/
noncomputable def roundingLaw {m n : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (x : Fin m → Fin n → ℝ) : Measure ((Fin m → Ω) × (Fin n → ℝ≥0∞)) :=
  (Measure.pi fun _ : Fin m => P).prod
    (Measure.pi fun j : Fin n => expLaw (ENNReal.ofReal (1 - ∑ i, x i j)))

/-- Resource `i` wins request `j` in OCEC rounding (Definition 3, step 2(c)): copy `G_i` receives
the sequence `x_i = (x_ij)_j` and returns `Y_ij`; `i` has the minimum clock `Y_ij` among all
resources and it is strictly below the discard clock `Ȳ_j`. Ties in the minimum (a null event)
go to the smallest index. -/
def WinsRequest {m n : ℕ} {Ω : Type*} (Y : (Fin n → ℝ) → Ω → Fin n → ℝ≥0∞)
    (x : Fin m → Fin n → ℝ) (ω : (Fin m → Ω) × (Fin n → ℝ≥0∞)) (i : Fin m) (j : Fin n) :
    Prop :=
  Y (x i) (ω.1 i) j < ω.2 j ∧
  (∀ i' : Fin m, i' < i → Y (x i) (ω.1 i) j < Y (x i') (ω.1 i') j) ∧
  (∀ i' : Fin m, i < i' → Y (x i) (ω.1 i) j ≤ Y (x i') (ω.1 i') j)

open Classical in
/-- `S_i`, the set of requests allocated to resource `i` by OCEC rounding (p. 7). -/
noncomputable def allocated {m n : ℕ} {Ω : Type*} (Y : (Fin n → ℝ) → Ω → Fin n → ℝ≥0∞)
    (x : Fin m → Fin n → ℝ) (ω : (Fin m → Ω) × (Fin n → ℝ≥0∞)) (i : Fin m) : Finset (Fin n) :=
  Finset.univ.filter (fun j => WinsRequest Y x ω i j)

/-- The probability space of the fresh-competitor comparison of Lemma 6 (p. 7) for resource `i`:
the randomness of `i`'s generator and, independently, fresh clocks `Z_j ∼ Exp(1 - x_ij)`. -/
noncomputable def freshLaw {m n : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (x : Fin m → Fin n → ℝ) (i : Fin m) : Measure (Ω × (Fin n → ℝ≥0∞)) :=
  P.prod (Measure.pi fun j : Fin n => expLaw (ENNReal.ofReal (1 - x i j)))

open Classical in
/-- `S_i^Ind = {j : Y_ij < Z_j}` against the fresh competing clocks `Z_j` (Lemma 6, p. 7). -/
noncomputable def freshAllocated {m n : ℕ} {Ω : Type*} (Y : (Fin n → ℝ) → Ω → Fin n → ℝ≥0∞)
    (x : Fin m → Fin n → ℝ) (i : Fin m) (ω : Ω × (Fin n → ℝ≥0∞)) : Finset (Fin n) :=
  Finset.univ.filter (fun j => Y (x i) ω.1 j < ω.2 j)

end OCEClocks.DisplayAds


