-- Prove2me | Definitions.Def_DSICHardRev_ValuationClasses
-- name    : DSICHardRev_ValuationClasses
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:33:52.836309+00:00
-- url     : https://prove2.me/theorems/f21021e1-9963-478c-a18b-a1149473d8cf
-- title:
--   Matroid rank, weighted matroid rank, convolution and XOS valuations
-- statement:
--   Let $\iota$ be a finite set of items and write $x(S)=\sum_{j\in S}x_j$.
--
--   1. **Matroid.** A family $\mathcal M\subseteq 2^{\iota}$ of independent sets that is nonempty, downward closed and satisfies augmentation; its **rank function** is $r(S)=\max_{T\in\mathcal M}|S\cap T|$.
--   2. **Weighted matroid rank.** $v$ is weighted matroid rank if there are a matroid $\mathcal M$ on $\iota$ and weights $w\in\mathbb R^{\iota}_{\ge0}$ with $v(S)=\max_{T\in\mathcal M}w(S\cap T)$.
--   3. **Convolution.** For $f,g:2^{\iota}\to\mathbb R$,
--   $$(f\star g)(S)=\max_{T\subseteq S}\{f(S\setminus T)+g(T)\}.$$
--   4. **XOS.** $v$ is XOS if there are weight vectors $w_1,\dots,w_\lambda\in\mathbb R^{\iota}_{\ge0}$, $\lambda\ge1$, with $v(S)=\max_{\ell\in[\lambda]}w_\ell(S)$.
--
--   The GS hard instances of the paper are convolutions of weighted matroid rank functions built on matroids of Balcan and Harvey; XOS is the second complement-free class to which the KSSHD framework applies.
--
--   **Formalization Note** A matroid is a Mathlib `Matroid ι` with ground set all of $\iota$; the rank and weighted rank are stated as maxima over its independent sets (with `IsGreatest` for the weighted rank). The XOS clauses form a nonempty finite set of non-negative weight vectors.
-- source:
--   Qiu, The Hardness of Dominant Strategy Mechanism Design, Revisited, arXiv:2610.06773 (version of 27 Oct 2026, sha256 a9f98f35…), §2.3, p.10: Definitions 2.13, 2.14, 2.15, 2.16, 2.19

import Mathlib

namespace DSICHardRev

/-!
# Matroid rank, weighted matroid rank, convolution and XOS valuations

F. V. Qiu, *The Hardness of Dominant Strategy Mechanism Design, Revisited*, arXiv:2610.06773
(version of 27 Oct 2026, sha256 a9f98f35…), §2.3, p.10: Definition 2.13 (Matroid),
Definition 2.14 (Matroid Rank Function), Definition 2.15 (Weighted Matroid Rank),
Definition 2.16 (Convolution), Definition 2.19 (XOS); notation `x(S) = ∑_{j ∈ S} x_j`.

**Formalization Note.**
* A matroid on the finite item set `ι` (Definition 2.13) is a Mathlib `Matroid ι` whose ground set
  is all of `ι` (`M.E = Set.univ`); its independent sets are the family the paper calls `M`.
* `matroidRank M S = max_{T independent} |S ∩ T|` (Definition 2.14), a maximum over a finite
  nonempty family (`∅` is independent). `IsMatroidRankFn r` says that the real-valued `r` is the
  rank function of some matroid on `ι` with ground set `ι`.
* `IsWeightedMatroidRank v` (Definition 2.15): there are a matroid and non-negative item weights
  `w` with `v S = max_{T independent} w(S ∩ T)`; the maximum is stated with `IsGreatest`.
* `conv f g S = max_{T ⊆ S} (f (S \ T) + g T)` (Definition 2.16), as a `Finset.sup'` over the
  powerset of `S`.
* `IsXOS v` (Definition 2.19): there is a nonempty finite family of non-negative weight vectors
  (the paper's `w_1, …, w_λ`, `λ ≥ 1`) with `v S = max_ℓ w_ℓ(S)`.
-/

variable {ι : Type} [Fintype ι] [DecidableEq ι]

open Classical in
/-- The rank function of a matroid (Definition 2.14): `r(S) = max_{T ∈ M} |S ∩ T|`. -/
noncomputable def matroidRank (M : Matroid ι) (S : Finset ι) : ℕ :=
  ((Finset.univ : Finset (Finset ι)).filter fun T : Finset ι => M.Indep (↑T : Set ι)).sup
    fun T : Finset ι => (S ∩ T).card

/-- `r` is a matroid rank function (Definition 2.14): the rank function of a matroid on `ι` whose
ground set is all of `ι`. -/
def IsMatroidRankFn (r : Finset ι → ℝ) : Prop :=
  ∃ M : Matroid ι, M.E = Set.univ ∧ ∀ S, r S = (matroidRank M S : ℝ)

/-- `v` is weighted matroid rank (Definition 2.15): for a matroid on `ι` (ground set `ι`) and
non-negative item weights `w`, `v(S) = max_{T ∈ M} w(S ∩ T)`. -/
def IsWeightedMatroidRank (v : Finset ι → ℝ) : Prop :=
  ∃ (M : Matroid ι) (w : ι → ℝ), M.E = Set.univ ∧ (∀ j, 0 ≤ w j) ∧
    ∀ S, IsGreatest {x | ∃ T : Finset ι, M.Indep (T : Set ι) ∧ x = ∑ j ∈ S ∩ T, w j} (v S)

/-- The convolution `(f ⋆ g)(S) = max_{T ⊆ S} {f(S \ T) + g(T)}` (Definition 2.16). -/
def conv (f g : Finset ι → ℝ) (S : Finset ι) : ℝ :=
  S.powerset.sup' (Finset.powerset_nonempty S) fun T => f (S \ T) + g T

/-- `v` is XOS (Definition 2.19): there are finitely many (at least one) non-negative weight vectors
`w_1, …, w_λ` with `v(S) = max_ℓ w_ℓ(S)`. -/
def IsXOS (v : Finset ι → ℝ) : Prop :=
  ∃ (W : Finset (ι → ℝ)) (hW : W.Nonempty), (∀ w ∈ W, ∀ j, 0 ≤ w j) ∧
    ∀ S, v S = W.sup' hW fun w => ∑ j ∈ S, w j

end DSICHardRev


