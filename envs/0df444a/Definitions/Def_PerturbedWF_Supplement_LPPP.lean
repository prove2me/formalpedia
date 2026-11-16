-- Prove2me | Definitions.Def_PerturbedWF_Supplement_LPPP
-- name    : PerturbedWF_Supplement_LPPP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T03:07:41.092673+00:00
-- url     : https://prove2.me/theorems/f0fb668c-28f6-4e78-825d-44a861c9fec7
-- title:
--   Randomized online algorithms for weighted paging and the laminar parking permit problem; $L_k$
-- statement:
--   **Weighted paging** with cache size $k$: pages with weights $w\ge0$, an initial cache $X_0$; on request $r_t$ the algorithm holds a cache $X_t$ with $r_t\in X_t$ and pays $\|X_t-X_{t-1}\|$.
--
--   **Laminar parking permit problem (LPPP)** with $k$ permit types: costs $C_1,\ldots,C_k\ge0$ and durations $D_1,\ldots,D_k\in\mathbb N$. Type $i$ partitions the days into the intervals $\{1,\ldots,D_i\},\{D_i+1,\ldots,2D_i\},\ldots$; the intervals of all types are **laminar** (any two are disjoint or nested). On day $t$ an algorithm may buy permits; a type-$i$ permit costs $C_i$ and is active from that day until the end of the current type-$i$ interval. The request on day $t$ is $r_t\in\{0,1\}$, and on a day with $r_t=1$ at least one purchased permit must be active.
--
--   A **deterministic online algorithm** makes its day-$t$ decision from $r_1,\ldots,r_t$ (and the instance). A **randomized online algorithm** is a probability distribution over deterministic ones; it is **$\rho$-competitive** if, for every instance, there is a constant $C$ (independent of the requests) with
--   $$\mathbb E[\mathrm{cost}(r_1,\ldots,r_T)]\le\rho\cdot\mathrm{OPT}(r_1,\ldots,r_T)+C$$
--   for every request sequence. Finally $L_1=1$ and $L_{k+1}=L_k/(1-e^{-L_k})$.
--
--   These notions are what Theorem 8.4 compares.
--
--   **Formalization Note** Requests are sequences used on days $1,\ldots,N$. A deterministic paging algorithm is a map from request prefixes to caches; a deterministic LPPP algorithm is a map from request prefixes to the set of types bought that day, which must cover every requested day of every sequence. A type-$i$ permit bought on day $s$ is active on day $t$ iff $s\le t$ and $\lfloor (t-1)/D_i\rfloor=\lfloor (s-1)/D_i\rfloor$. Weighted paging's OPT is the minimum of the work function (8.1); LPPP's OPT is the cheapest covering purchase plan. Expectations are lower Lebesgue integrals of nonnegative costs.
-- source:
--   Coester, Kashaev, Online Metric Problems via Randomly Perturbed Work Functions (STOC 2027 submission, held version, sha256 e2e30a44…), §8.2.3 'Lower bound', p.23 (PDF p.24); weighted paging model of §8.1–§8.2, pp.20–22 (PDF pp.21–23)

import Mathlib
import Definitions.Def_PerturbedWF_Supplement_WeightedPaging

namespace PerturbedWF.Supplement

open MeasureTheory

/-!
# Online algorithms for weighted paging and for the laminar parking permit problem (§8.2.3)

C. Coester, D. Kashaev, *Online Metric Problems via Randomly Perturbed Work Functions*, STOC 2027
submission (held version, sha256 e2e30a44…), §8.2.3 "Lower bound", p.23 (PDF p.24); the weighted
paging model of §8.1–§8.2, pp.20–22 (PDF pp.21–23).

**Weighted paging** with cache size `k`: pages `ι`, weights `w ≥ 0`, initial cache
`X₀ ∈ kConfig ι k`; the request at time `t` is a page `r_t`, the algorithm keeps a configuration
`X_t ∈ kConfig ι k` with `r_t ∈ X_t` and pays the movement cost `‖X_t − X_{t−1}‖`.

**LPPP** with `k` permit types: costs `C_i ≥ 0` and durations `D_i ∈ ℕ`, `D_i ≥ 1`. Type `i`
partitions the days `1, 2, …` into the intervals `{a D_i + 1, …, (a + 1) D_i}`; the intervals of all
types are laminar (any two are disjoint or nested). On day `t` an algorithm may buy permits; a
type-`i` permit bought on day `s` costs `C_i` and is active from day `s` to the end of the current
type-`i` interval. On a day with `r_t = 1` at least one purchased permit must be active.

**Online and randomized.** A deterministic online algorithm is a function of the request prefix:
its configuration (paging) or purchases (LPPP) on day `t` depend only on `r_1, …, r_t` (and the
instance). A randomized online algorithm is a probability distribution over deterministic ones;
its cost on a fixed (oblivious) request sequence is the expectation. A randomized algorithm is
`ρ`-competitive if `E[cost] ≤ ρ · OPT + C` for every request sequence, with `C` independent of the
request sequence (it may depend on the instance).

**Formalization Note.**
* Requests are sequences `r : ℕ → α` used on days `1, …, N`; `reqPrefix r t = [r_1, …, r_t]`.
* A deterministic weighted-paging algorithm is `a : List ι → (ι → ℝ)` with `a [] = X₀`, every value
  in `kConfig ι k`, and `r ∈ a (l ++ [r])`; its configuration after day `t` is `a [r_1, …, r_t]`.
  Its cost is `∑_{t=1}^N ‖X_t − X_{t−1}‖` (transportation norm of `wpDist w`), and `OPT` is
  `ksOPT`, the minimum of the work function (8.1).
* A deterministic LPPP algorithm is `b : List Bool → (Fin k → Bool)`, the set of permit types
  bought on day `t` being `b [r_1, …, r_t]`; it must cover every requested day of every request
  sequence. A type-`i` permit bought on day `s` is active on day `t` iff `s ≤ t` and
  `⌊(t−1)/D_i⌋ = ⌊(s−1)/D_i⌋`. `lpppOPT` is the minimum offline cost of a covering purchase plan
  over the days `1, …, N` (a real infimum of a finite set, nonempty when `k ≥ 1`).
* Randomized algorithms are probability measures on the deterministic ones, valid almost surely;
  expectations are lower Lebesgue integrals of the nonnegative costs.
* `Lseq k` is `L_k` of [CT26]: `L_1 = 1`, `L_{k+1} = L_k / (1 − e^{−L_k})` (`Lseq 0` is unused).
-/

/-- `[r_1, …, r_t]`. -/
def reqPrefix {α : Type} (r : ℕ → α) (t : ℕ) : List α :=
  (List.range t).map (fun i => r (i + 1))

/-- A deterministic online weighted-paging algorithm with cache size `k` from `X₀`. -/
def IsWPAlg {ι : Type} [Fintype ι] (k : ℕ) (X₀ : ι → ℝ) (a : List ι → ι → ℝ) : Prop :=
  a [] = X₀ ∧ (∀ l, a l ∈ kConfig ι k) ∧ ∀ l r, 1 ≤ a (l ++ [r]) r

/-- The movement cost `∑_{t=1}^N ‖X_t − X_{t−1}‖` of `a` on `r_1, …, r_N`. -/
noncomputable def wpAlgCost {ι : Type} [Fintype ι] [DecidableEq ι] (w : ι → ℝ)
    (a : List ι → ι → ℝ) (r : ℕ → ι) (N : ℕ) : ℝ :=
  ∑ t ∈ Finset.Icc 1 N, transNorm (wpDist w) (a (reqPrefix r t) - a (reqPrefix r (t - 1)))

/-- There is a `ρ`-competitive randomized online algorithm for weighted paging with cache size
`k`: for every set of pages, weights `w ≥ 0` and initial cache `X₀`. -/
def IsCompetitiveWP (k : ℕ) (ρ : ℝ) : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (w : ι → ℝ), (∀ i, 0 ≤ w i) →
    ∀ X₀ ∈ kConfig ι k,
      ∃ P : Measure (List ι → ι → ℝ), IsProbabilityMeasure P ∧ (∀ᵐ a ∂P, IsWPAlg k X₀ a) ∧
        ∃ C : ℝ, ∀ (N : ℕ) (r : ℕ → ι),
          ∫⁻ a, ENNReal.ofReal (wpAlgCost w a r N) ∂P ≤
            ENNReal.ofReal (ρ * ksOPT (wpDist w) k X₀ r N + C)

/-- The type-`i` interval number `a`, `{a D + 1, …, (a + 1) D}`. -/
def permitInterval (D a : ℕ) : Set ℕ := Set.Icc (a * D + 1) ((a + 1) * D)

/-- Laminarity: any two intervals (of any types) are disjoint or one contains the other. -/
def IsLaminar {k : ℕ} (D : Fin k → ℕ) : Prop :=
  ∀ i j : Fin k, ∀ a b : ℕ, Disjoint (permitInterval (D i) a) (permitInterval (D j) b) ∨
    permitInterval (D i) a ⊆ permitInterval (D j) b ∨
    permitInterval (D j) b ⊆ permitInterval (D i) a

/-- The purchase plan `p` (types bought on each day) covers day `t` of the requests `r`: if
`r_t = 1`, some permit bought on a day `s ≤ t` is still active on day `t`. -/
def Covers {k : ℕ} (D : Fin k → ℕ) (p : ℕ → Fin k → Bool) (r : ℕ → Bool) (t : ℕ) : Prop :=
  r t = true → ∃ s ∈ Finset.Icc 1 t, ∃ i, p s i = true ∧ (t - 1) / D i = (s - 1) / D i

/-- The cost `∑_{t=1}^N ∑_{i bought on day t} C_i` of a purchase plan. -/
def planCost {k : ℕ} (Cst : Fin k → ℝ) (p : ℕ → Fin k → Bool) (N : ℕ) : ℝ :=
  ∑ t ∈ Finset.Icc 1 N, ∑ i, if p t i then Cst i else 0

/-- A deterministic online LPPP algorithm: on every request sequence, the plan
`t ↦ b [r_1, …, r_t]` covers every day `t ≥ 1`. -/
def IsLPPPAlg {k : ℕ} (D : Fin k → ℕ) (b : List Bool → Fin k → Bool) : Prop :=
  ∀ (r : ℕ → Bool) (t : ℕ), 1 ≤ t → Covers D (fun s => b (reqPrefix r s)) r t

/-- The offline optimum of LPPP on days `1, …, N`. -/
noncomputable def lpppOPT {k : ℕ} (Cst : Fin k → ℝ) (D : Fin k → ℕ) (r : ℕ → Bool) (N : ℕ) : ℝ :=
  sInf {c : ℝ | ∃ p : ℕ → Fin k → Bool, (∀ t ∈ Finset.Icc 1 N, Covers D p r t) ∧
    c = planCost Cst p N}

/-- There is a `ρ`-competitive randomized online algorithm for LPPP with `k` permit types: for
every choice of costs `C_i ≥ 0` and laminar durations `D_i ≥ 1`. -/
def IsCompetitiveLPPP (k : ℕ) (ρ : ℝ) : Prop :=
  ∀ (Cst : Fin k → ℝ) (D : Fin k → ℕ), (∀ i, 0 ≤ Cst i) → (∀ i, 1 ≤ D i) → IsLaminar D →
    ∃ P : Measure (List Bool → Fin k → Bool), IsProbabilityMeasure P ∧
      (∀ᵐ b ∂P, IsLPPPAlg D b) ∧
      ∃ C : ℝ, ∀ (N : ℕ) (r : ℕ → Bool),
        ∫⁻ b, ENNReal.ofReal (planCost Cst (fun s => b (reqPrefix r s)) N) ∂P ≤
          ENNReal.ofReal (ρ * lpppOPT Cst D r N + C)

/-- `L_1 = 1`, `L_{k+1} = L_k / (1 − exp(−L_k))` ([CT26]); `Lseq 0 = 0` is unused. -/
noncomputable def Lseq : ℕ → ℝ
  | 0 => 0
  | 1 => 1
  | k + 2 => Lseq (k + 1) / (1 - Real.exp (-Lseq (k + 1)))

end PerturbedWF.Supplement


