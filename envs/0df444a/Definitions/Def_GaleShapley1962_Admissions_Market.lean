-- Prove2me | Definitions.Def_GaleShapley1962_Admissions_Market
-- name    : GaleShapley1962_Admissions_Market
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T02:41:02.394085+00:00
-- url     : https://prove2.me/theorems/8f898bd1-f840-49c4-a3ec-c0879f48d36c
-- title:
--   Finite admissions markets with strict acceptable lists
-- statement:
--   An admissions market has $n$ applicants, $m$ colleges, and a natural-number quota for each college. Each applicant gives a best-first list of acceptable colleges; each college gives a best-first list of acceptable applicants. Every list is duplicate-free. Omitted partners are unacceptable, and no comparison between two omitted partners is required.
--
--   Strict preference between two listed partners means that the first occurs earlier in the list. Both membership conditions are checked before comparing indices. The permissible application list of an applicant is their list filtered by the receiving colleges' acceptability, preserving its order.
--
--   **Formalization Note** Populations are indexed by `Fin n` and `Fin m`. Empty populations and quota zero are included as boundary extensions; zero quota retains nobody. This general market data structure contains no stability or algorithm-correctness assumptions.
-- source:
--   Gale and Shapley (1962), College Admissions and the Stability of Marriage, Section 2, printed pp. 9–10 (PDF pp. 1–2), and Section 4, printed p. 13 (PDF p. 5), https://doi.org/10.1080/00029890.1962.11989827

import Mathlib.Data.List.Basic
import Mathlib.Data.List.FinRange
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace GaleShapley1962.Admissions

/-- Finite many-to-one admissions data: best-first acceptable lists and college quotas.
No correctness property of an algorithm is part of the data. -/
structure Market (n m : ℕ) where
  applicantList : Fin n → List (Fin m)
  collegeList : Fin m → List (Fin n)
  applicant_nodup : ∀ a, (applicantList a).Nodup
  college_nodup : ∀ c, (collegeList c).Nodup
  quota : Fin m → ℕ

/-- Strict preference on the listed acceptable partners; absent partners have no rank. -/
def listPrefers {α : Type*} [DecidableEq α] (l : List α) (x y : α) : Prop :=
  x ∈ l ∧ y ∈ l ∧ l.idxOf x < l.idxOf y

instance {α : Type*} [DecidableEq α] (l : List α) (x y : α) :
    Decidable (listPrefers l x y) := by
  unfold listPrefers
  infer_instance

/-- Section 4 excludes applications unacceptable to the receiving college. -/
def Market.permissible {n m : ℕ} (M : Market n m) (a : Fin n) : List (Fin m) :=
  (M.applicantList a).filter fun c => a ∈ M.collegeList c

end GaleShapley1962.Admissions


