-- Prove2me | Definitions.Def_BCFGJPSSV26_Model
-- name    : BCFGJPSSV26_Model
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:35:26.535929+00:00
-- url     : https://prove2.me/theorems/3e3075eb-a264-4d12-ae91-016e623cf763
-- title:
--   BCFGJPSSV26.Model — k-median and randomized algorithms
-- statement:
--   This is module `BCFGJPSSV26.Model` of the Lean 4 formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)), from the repository [raresbuhai/formalization-of-my-research](https://github.com/raresbuhai/formalization-of-my-research) (formalized with Claude Code, Apache-2.0).
--
--   The definitions that the main theorems of [BCFGJPSSV26a] and [BCFGJPSSV26b]
--   (`BCFGJPSSV26/Challenge.lean`) are stated in. Together with what they import (Mathlib, CSLib's
--   multitape Turing machines, and complexitylib's polynomial time), they are what a reader has to
--   check to know what the theorems say.
--
--   * **Instances** (`BCFGJPSSV26.Instance`): `n` clients and `m` facilities, the points of a
--     pseudometric space with rational distances, and the number `k` of centers. Clients and
--     facilities may share a location: their distance is then `0`. An instance is encoded by `n`, `m`,
--     `k` and its table of distances (`BCFGJPSSV26.encInstance`).
--   * **Costs** (`BCFGJPSSV26.Instance.cost`, `BCFGJPSSV26.Instance.opt`): the cost of a set of
--     facilities is the sum over the clients of their distance to the nearest one, and `opt ℓ` is the
--     least cost of a nonempty set of at most `ℓ` facilities.
--   * **Facility location** (`BCFGJPSSV26.Instance.optFL`): with a uniform opening cost `f`, a
--     nonempty set `S` of facilities costs `cost S + f |S|`; `optFL f` is the least such cost. The
--     number `k` of the instance plays no role.
--   * **Stability** (`BCFGJPSSV26.Instance.IsStable`): `opt (k - 1) ≥ (1 + β) opt k`.
--   * **Outputs** (`BCFGJPSSV26.Instance.IsCenterList`): a nonempty list of distinct facilities.
--   * **Randomized algorithms** (`BCFGJPSSV26.RunsInTime`): a deterministic multitape Turing machine
--     that reads an input `x` and a string `r` of coin flips and halts within `O(T x + |(x, r)|)`
--     steps. Probabilities are over coin strings of exactly `T x` flips (`BCFGJPSSV26.coinProb`).
--
--   References:
--
--   * [BCFGJPSSV26a] R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte,
--     M. R. Pittu, M. Stouras, O. Svensson, L. Vogl, *A Better-than-2 Approximation for k-Median,
--     Part I: The Power of General Bids*, arXiv:2610.18144.
--   * [BCFGJPSSV26b] the same authors, *A Better-than-2 Approximation for k-Median, Part II: Stable
--     Instances*, arXiv:2610.17172.
--
--   **Contents.** The module is published as a whole: 17 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_BCFGJPSSV26_Model`.
-- source:
--   https://github.com/raresbuhai/formalization-of-my-research/blob/7abf511c7e99fd3fec3ff245a2b8d616ae17bc2c/BCFGJPSSV26/Model.lean

module

public import Definitions.Def_BuhaiPapers_Background_Encoding
public import Definitions.Def_Cslib_254e30e_Computability_Machines_Turing_MultiTape_Deterministic
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_PolyTime
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Logic.Equiv.Fin.Basic

set_option maxSynthPendingDepth 3

/- Prove2me definition bundle for `BCFGJPSSV26.Model` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# k-median and randomized algorithms

The definitions that the main theorems of [BCFGJPSSV26a] and [BCFGJPSSV26b]
(`BCFGJPSSV26/Challenge.lean`) are stated in. Together with what they import (Mathlib, CSLib's
multitape Turing machines, and complexitylib's polynomial time), they are what a reader has to
check to know what the theorems say.

* **Instances** (`BCFGJPSSV26.Instance`): `n` clients and `m` facilities, the points of a
  pseudometric space with rational distances, and the number `k` of centers. Clients and
  facilities may share a location: their distance is then `0`. An instance is encoded by `n`, `m`,
  `k` and its table of distances (`BCFGJPSSV26.encInstance`).
* **Costs** (`BCFGJPSSV26.Instance.cost`, `BCFGJPSSV26.Instance.opt`): the cost of a set of
  facilities is the sum over the clients of their distance to the nearest one, and `opt ℓ` is the
  least cost of a nonempty set of at most `ℓ` facilities.
* **Facility location** (`BCFGJPSSV26.Instance.optFL`): with a uniform opening cost `f`, a
  nonempty set `S` of facilities costs `cost S + f |S|`; `optFL f` is the least such cost. The
  number `k` of the instance plays no role.
* **Stability** (`BCFGJPSSV26.Instance.IsStable`): `opt (k - 1) ≥ (1 + β) opt k`.
* **Outputs** (`BCFGJPSSV26.Instance.IsCenterList`): a nonempty list of distinct facilities.
* **Randomized algorithms** (`BCFGJPSSV26.RunsInTime`): a deterministic multitape Turing machine
  that reads an input `x` and a string `r` of coin flips and halts within `O(T x + |(x, r)|)`
  steps. Probabilities are over coin strings of exactly `T x` flips (`BCFGJPSSV26.coinProb`).

References:

* [BCFGJPSSV26a] R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte,
  M. R. Pittu, M. Stouras, O. Svensson, L. Vogl, *A Better-than-2 Approximation for k-Median,
  Part I: The Power of General Bids*, arXiv:2610.18144.
* [BCFGJPSSV26b] the same authors, *A Better-than-2 Approximation for k-Median, Part II: Stable
  Instances*, arXiv:2610.17172.
-/

@[expose] public section

namespace BCFGJPSSV26

open Encoding

/-! ### Instances -/

/-- A **k-median instance**: `n` clients and `m` facilities, the points `Fin n ⊕ Fin m` (`.inl j`
is client `j`, `.inr i` is facility `i`), the distances `d` between them, and the number `k` of
centers. -/
structure Instance where
  /-- The number of clients. -/
  n : ℕ
  /-- The number of facilities. -/
  m : ℕ
  /-- The number of centers to open. -/
  k : ℕ
  /-- The distance between two points. -/
  d : Fin n ⊕ Fin m → Fin n ⊕ Fin m → ℚ

/-- A **valid** instance: at least one center may be opened and there is at least one facility,
and the distances form a pseudometric (nonnegative, zero on the diagonal, symmetric, with the
triangle inequality). Distinct points may be at distance `0`, so a client and a facility may share
a location. -/
structure Instance.Valid (I : Instance) : Prop where
  one_le_k : 1 ≤ I.k
  one_le_m : 1 ≤ I.m
  nonneg : ∀ a b, 0 ≤ I.d a b
  self : ∀ a, I.d a a = 0
  comm : ∀ a b, I.d a b = I.d b a
  triangle : ∀ a b c, I.d a c ≤ I.d a b + I.d b c

/-- The table of distances, row by row: the clients `0, …, n - 1` first, then the facilities
`0, …, m - 1`. -/
def distTable (I : Instance) : List (List ℚ) :=
  List.ofFn fun a : Fin (I.n + I.m) ↦ List.ofFn fun b : Fin (I.n + I.m) ↦
    I.d (finSumFinEquiv.symm a) (finSumFinEquiv.symm b)

theorem distTable_injective {n m k k' : ℕ} {d d' : Fin n ⊕ Fin m → Fin n ⊕ Fin m → ℚ}
    (h : distTable ⟨n, m, k, d⟩ = distTable ⟨n, m, k', d'⟩) : d = d' := by
  funext x y
  have h1 := congrFun (List.ofFn_injective h) (finSumFinEquiv x)
  have h2 := congrFun (List.ofFn_injective h1) (finSumFinEquiv y)
  simpa using h2

/-- An instance is encoded by `n`, `m` and `k` in binary and its table of distances. -/
def encInstance : Instance ↪ List Bool :=
  ⟨fun I ↦ encPair encNat (encPair encNat (encPair encNat (encList (encList encRat))))
      (I.n, I.m, I.k, distTable I), by
    rintro ⟨n, m, k, d⟩ ⟨n', m', k', d'⟩ h
    have h' :=
      (encPair encNat (encPair encNat (encPair encNat (encList (encList encRat))))).injective h
    simp only [Prod.mk.injEq] at h'
    obtain ⟨rfl, rfl, rfl, h⟩ := h'
    rw [distTable_injective h]⟩

/-! ### Costs -/

/-- The distance from client `j` to facility `i`. -/
def Instance.dist (I : Instance) (j : Fin I.n) (i : Fin I.m) : ℝ := I.d (.inl j) (.inr i)

/-- The **cost** of a set `S` of open facilities: every client pays its distance to the nearest
facility of `S`. It is only used for nonempty `S`. The paper's convention `d(j, ∅) = ∞` is not
represented: on `S = ∅` this is a real number (Lean's default value of an empty infimum, `0`),
which no statement depends on, since outputs are nonempty (`BCFGJPSSV26.Instance.IsCenterList`). -/
noncomputable def Instance.cost (I : Instance) (S : Finset (Fin I.m)) : ℝ :=
  ∑ j : Fin I.n, ⨅ i : S, I.dist j i

/-- The **optimum** `opt ℓ` of `ℓ`-median: the least cost of a nonempty set of at most `ℓ`
facilities. It is used only for `ℓ ≥ 1` on instances with a facility, where such sets exist and
the infimum is a minimum. (For `ℓ = 0` it is `0`, Lean's default value of an empty infimum, where
the paper has `opt 0 = ∞`; `BCFGJPSSV26.Instance.IsStable` never uses it.) -/
noncomputable def Instance.opt (I : Instance) (ℓ : ℕ) : ℝ :=
  ⨅ S : {S : Finset (Fin I.m) // S.Nonempty ∧ S.card ≤ ℓ}, I.cost S.1

/-- The **optimum of facility location** with uniform opening cost `f`: the least
`cost S + f |S|` over nonempty sets `S` of facilities, the paper's `OPT_f` [BCFGJPSSV26a,
Section 2]. The number `k` of the instance plays no role. -/
noncomputable def Instance.optFL (I : Instance) (f : ℝ) : ℝ :=
  ⨅ S : {S : Finset (Fin I.m) // S.Nonempty}, I.cost S.1 + f * S.1.card

/-- The instance is **`β`-stable** [BCFGJPSSV26b, Section 2]: removing one of the `k` centers
raises the optimum by a factor at least `1 + β`, that is, `opt (k - 1) ≥ (1 + β) opt k`. For
`k = 1` the paper's `opt 0` is `∞`, so every such instance is stable; here the condition is
asked only for `k ≥ 2`, which gives the same notion without `opt 0`. -/
def Instance.IsStable (I : Instance) (β : ℝ) : Prop :=
  2 ≤ I.k → (1 + β) * I.opt I.k ≤ I.opt (I.k - 1)

/-! ### Outputs -/

/-- An output is a list of facilities: nonempty, without repetitions, and each `i < m`. -/
def Instance.IsCenterList (I : Instance) (S : List ℕ) : Prop :=
  S ≠ [] ∧ S.Nodup ∧ ∀ i ∈ S, i < I.m

/-- The set of facilities in the list `S`. -/
def Instance.centers (I : Instance) (S : List ℕ) : Finset (Fin I.m) :=
  Finset.univ.filter fun i ↦ i.1 ∈ S

/-- Outputs are encoded as lists of numbers in binary. -/
def encCenters : List ℕ ↪ List Bool := encList encNat

/-! ### Randomized algorithms -/

/-- `A` runs in time `O(T)`: it is computed by a multitape Turing machine (binary alphabet,
finitely many states) that, on an input `x` and a coin string `r`, halts with output `A (x, r)`
within `c (T x + |(x, r)| + 1)` steps and cells, for a constant `c`. The machine reads its whole
input, so the bound includes the length of the input with the coins; `BCFGJPSSV26.coinProb` gives
it exactly `T x` coins. -/
def RunsInTime {α β : Type} (encIn : α ↪ List Bool) (encOut : β ↪ List Bool)
    (A : α × List Bool → β) (T : α → ℕ) : Prop :=
  ∃ c : ℕ, Turing.MultiTapeTM.ComputableInTimeAndSpace A (encPair encIn encBits) encOut
    (fun xr ↦ c * (T xr.1 + (encPair encIn encBits xr).length + 1))
    (fun xr ↦ c * (T xr.1 + (encPair encIn encBits xr).length + 1))

open Classical in
/-- The probability that a uniformly random string of `M` coin flips satisfies `P`. -/
noncomputable def coinProb (M : ℕ) (P : List Bool → Prop) : ℝ :=
  (Fintype.card {r : Fin M → Bool // P (List.ofFn r)} : ℝ) / 2 ^ M

/-- The running time `2^(e L) (|I| + 2)^e` of an algorithm for stable instances on an instance
`I` given with a number `L ≥ 1/β`, where `|I|` is the length of the encoded instance. With
`e = poly(1/ε)` it is the `exp(O(β⁻¹ poly(1/ε))) n^poly(1/ε)` of [BCFGJPSSV26b, Theorem 1.1]. -/
def stableTime (e : ℕ) (x : Instance × ℕ) : ℕ :=
  2 ^ (e * x.2) * ((encInstance x.1).length + 2) ^ e

/-- The running time of the algorithm for stable instances on an input `((I, L), ε)`: an instance,
a number `L ≥ 1/β` and the accuracy `ε`. It is `stableTime e (I, L) = 2^(e L) (|I| + 2)^e` with
`e = a (⌈1/ε⌉ + 1)^b`, so for `ε ∈ (0, 1/200)` it is the `exp(O(β⁻¹ poly(1/ε))) n^poly(1/ε)` of
[BCFGJPSSV26b, Theorem 1.1]. (The `+ 1` keeps the base `⌈1/ε⌉ + 1` positive on every input,
also for `ε ≤ 0`, where `⌈1/ε⌉ = 0`.) `BCFGJPSSV26.RunsInTime` adds the length of the whole input,
the encoding of `ε` included. -/
def stableTimeOf (a b : ℕ) (x : (Instance × ℕ) × ℚ) : ℕ :=
  stableTime (a * (⌈1 / x.2⌉₊ + 1) ^ b) x.1

end BCFGJPSSV26


