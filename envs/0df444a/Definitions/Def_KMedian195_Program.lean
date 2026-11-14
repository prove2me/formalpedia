-- Prove2me | Definitions.Def_KMedian195_Program
-- name    : KMedian195_Program
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:22:07.367893+00:00
-- url     : https://prove2.me/theorems/13f5e38c-a2ff-4431-832e-a7f14c600f53
-- title:
--   KMedian195.Program — The factor-revealing program
-- statement:
--   This is module `KMedian195.Program` of the library KMedian195: the proof that the factor-revealing program of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) (Part I, Definition 4.1, with the bid $[\alpha-\gamma d]^+$) has value at most $2-(\gamma-1)^2$ for $\gamma\in[1,1.224]$ (Part I, Theorem 4.4). The library was written by Codex in [epfl-thl2/project-k-median](https://github.com/epfl-thl2/project-k-median) (project `bound-195`, commit `d87e2a2`) and is taken from its copy in [raresbuhai/formalization-of-my-research](https://github.com/raresbuhai/formalization-of-my-research) (Apache-2.0).
--
--   The factor-revealing program of Definition 4.1 in *A Better-than-2 Approximation for
--   k-Median*, Part I (arXiv:2610.18144), for the bid `β_γ(α, d) = [α - γ d]^+`.
--
--   Indices are shifted by one: the paper's clients `1, …, n` are `Idx n = Fin n`, and its times
--   `1, …, n + 1` are `TimeIdx n = Fin (n + 1)`. For a client `i : Idx n`, the paper's times `i` and
--   `i + 1` are `TimeIdx.ofIdx i` and `TimeIdx.succ i`, and the paper's time `n + 1` is
--   `TimeIdx.last n`. The paper's variable `r_{j,k}` exists only for `k ≥ j`; here `x.r j ℓ` is
--   defined for every `ℓ`, and the entries with `ℓ < TimeIdx.ofIdx j` occur only in the nonnegativity
--   constraint.
--
--   **Contents.** The module is published as a whole: 11 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_KMedian195_Program`.
-- source:
--   https://github.com/raresbuhai/formalization-of-my-research/blob/7abf511c7e99fd3fec3ff245a2b8d616ae17bc2c/Imported/KMedian195/Program.lean

/-
Copied from `epfl-thl2/project-k-median` (written by Codex),
commit `d87e2a20376896ab72fe005a493b3af970a0f82d`, file `bound-195/Challenge.lean` (the statements
that the source checks with the comparator), without its two theorems, which are proved in
`Imported/KMedian195/Main.lean`.
Changes: module header (`module`, `public import`, `@[expose] public section`) and a module
docstring. The source defines these declarations twice, in `Challenge.lean` and in the development
(`Idx`, `suffixRange` in `Imported/KMedian195/Basic.lean`, the rest in
`Imported/KMedian195/FactorRevealingPrimal.lean`); here they are defined once, in this file, which
`Imported/KMedian195/Basic.lean` imports. The docstrings of `OriginalPrimalSolution` and
`OriginalPrimalUpperBound` are the development's.
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Real.Basic

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

/- Prove2me definition bundle for `KMedian195.Program` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# The factor-revealing program

The factor-revealing program of Definition 4.1 in *A Better-than-2 Approximation for
k-Median*, Part I (arXiv:2610.18144), for the bid `β_γ(α, d) = [α - γ d]^+`.

Indices are shifted by one: the paper's clients `1, …, n` are `Idx n = Fin n`, and its times
`1, …, n + 1` are `TimeIdx n = Fin (n + 1)`. For a client `i : Idx n`, the paper's times `i` and
`i + 1` are `TimeIdx.ofIdx i` and `TimeIdx.succ i`, and the paper's time `n + 1` is
`TimeIdx.last n`. The paper's variable `r_{j,k}` exists only for `k ≥ j`; here `x.r j ℓ` is
defined for every `ℓ`, and the entries with `ℓ < TimeIdx.ofIdx j` occur only in the nonnegativity
constraint.
-/

@[expose] public section

namespace KMedian195

noncomputable section

/-- Finite client/time indices for the size-`n` factor-revealing programs. -/
abbrev Idx (n : ℕ) := Fin n

/-- Suffix `{i | j ≤ i}` used for lower-triangular ranges. -/
def suffixRange (j : Idx n) : Finset (Idx n) :=
  Finset.univ.filter fun i => j ≤ i

abbrev TimeIdx (n : ℕ) := Fin (n + 1)

namespace TimeIdx

def last (n : ℕ) : TimeIdx n := Fin.last n

def ofIdx (i : Idx n) : TimeIdx n := Fin.castSucc i

def succ (i : Idx n) : TimeIdx n := Fin.succ i

end TimeIdx

/-- The original factor-revealing variables from Definition 4.1,
specialized to the one-piece bid `β_γ(α,d) = [α - γ d]^+`. -/
structure OriginalPrimalSolution (n : ℕ) where
  d : Idx n → ℝ
  f : ℝ
  r : Idx n → TimeIdx n → ℝ

namespace OriginalPrimalSolution

variable {n : ℕ}

def bidValue (gamma alpha dist : ℝ) : ℝ :=
  max (alpha - gamma * dist) 0

def objective (gamma : ℝ) (x : OriginalPrimalSolution n) : ℝ :=
  (Finset.sum Finset.univ fun j =>
    Finset.sum (suffixRange j) (fun i =>
      bidValue gamma (x.r j (TimeIdx.ofIdx i)) (x.r j (TimeIdx.succ i))) +
      x.r j (TimeIdx.last n)) - x.f

def Feasible (gamma : ℝ) (x : OriginalPrimalSolution n) : Prop :=
  (Finset.sum Finset.univ x.d = 1) ∧
    (∀ ⦃j i : Idx n⦄, j ≤ i → x.r j (TimeIdx.succ i) ≤ x.r j (TimeIdx.ofIdx i)) ∧
    (∀ ⦃j k : Idx n⦄, j < k →
      x.r k (TimeIdx.ofIdx k) ≤ x.r j (TimeIdx.ofIdx k) + x.d k + x.d j) ∧
    (∀ ⦃j k : Idx n⦄ ⦃ell : TimeIdx n⦄,
      j ≠ k →
      TimeIdx.ofIdx j < ell →
      TimeIdx.ofIdx k < ell →
      x.r j ell ≤ x.r k ell + x.d k + x.d j) ∧
    (∀ k : Idx n,
      Finset.sum Finset.univ (fun j =>
          if _h : j < k then
            bidValue gamma (x.r j (TimeIdx.ofIdx k)) (x.d j)
          else
            bidValue gamma (x.r k (TimeIdx.ofIdx k)) (x.d j)) ≤ x.f) ∧
    (0 ≤ x.f) ∧
    (∀ j, 0 ≤ x.d j) ∧
    (∀ j ell, 0 ≤ x.r j ell)

end OriginalPrimalSolution

/-- A direct upper-bound formulation for the specialized original FRP:
every feasible objective value is at most `bound`. -/
def OriginalPrimalUpperBound (gamma bound : ℝ) : Prop :=
  ∀ n, n ≠ 0 → ∀ x : OriginalPrimalSolution n,
    x.Feasible gamma → x.objective gamma ≤ bound

end

end KMedian195


