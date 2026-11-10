-- Prove2me | Definitions.Def_RevRedSAT_IsHSCode
-- name    : RevRedSAT_IsHSCode
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T04:46:39.729455+00:00
-- url     : https://prove2.me/theorems/fa8e15d3-50f9-49ff-9d79-c0ac94ada9b9
-- title:
--   Hitting Set codes, feasible solutions and lists of families
-- statement:
--   **Hitting Set** (App. C.1, p.92): "Given a finite universe $U$, an explicitly listed family $\mathcal F$ of subsets of $U$, and a budget $k$, find $S\subseteq U$ with $|S|\le k$ such that $S\cap F\ne\emptyset$ for every $F\in\mathcal F$. The family has rank at most $d$ if every member has at most $d$ elements. In $d$-Hitting Set, $d$ is fixed and the parameter is $k$. An empty family is hit by the empty set; a family containing the empty set has no hitting set."
--
--   An instance $(U,\mathcal F,k)$ with $U=\{0,\dots,n-1\}$ is the platform's `HSElemKernel.HSInstance` (a family without repeated sets, p.27). This module defines:
--
--   1. a **listing** of a family: a duplicate-free list of its members, each a duplicate-free list of elements;
--   2. the **codes** of an instance: $n$, then a listing of $\mathcal F$, then $k$; the codes of a $d$-Hitting Set instance are the codes of instances whose members have at most $d$ elements;
--   3. the **feasible solutions**: hitting sets of size at most $k$;
--   4. the code of a **list of families** (the output of the sparsifier): their number, then each family by a listing.
--
--   **Formalization Note** Every listing order is a code.
-- source:
--   Kundu, Panolan, Saurabh, Xue, Zehavi, Reverse Reductions: From Faster SAT to Subexponential Algorithms, STOC 2027 submission (held manuscript, sha256 7bf9a5af…), App. C.1, p.92 (Hitting Set, d-Hitting Set); §3, p.27 (no repeated sets, explicit universes)

import Mathlib
import Definitions.Def_RSListDecodingCapacity_AllRates_Encoding
import Definitions.Def_HSElemKernel_HSInstance
import Definitions.Def_HSElemKernel_IsDHS
import Definitions.Def_AlgebraicFPT_HittingSet_HittingSets
import Definitions.Def_RevRedSAT_SearchWithin

set_option autoImplicit false

namespace RevRedSAT

open RSListDecodingCapacity.AllRates

/-- `L` lists the family `F`: each listed set has no repeated element, no set is listed twice, and
the listed sets are exactly the members of `F` (in any order). -/
def IsListing {n : ℕ} (F : Finset (Finset (Fin n))) (L : List (List (Fin n))) : Prop :=
  (∀ s ∈ L, s.Nodup) ∧ (L.map List.toFinset).Nodup ∧ (L.map List.toFinset).toFinset = F

/-- The code of a listed family: the list of its sets, each set the list of its elements. -/
def encFamily {n : ℕ} (L : List (List (Fin n))) : List Bool := encList encSet L

/-- **The codes of a Hitting Set instance.**
Kundu, Panolan, Saurabh, Xue, Zehavi, *Reverse Reductions: From Faster SAT to Subexponential
Algorithms*, STOC 2027 submission (held manuscript, sha256 7bf9a5af…), App. C.1, p.92: "Hitting Set.
Given a finite universe U, an explicitly listed family F of subsets of U, and a budget k, find S ⊆ U
with |S| ≤ k such that S ∩ F ≠ ∅ for every F ∈ F"; §3, p.27: "Set-system universes are explicitly
listed. … Families contain no repeated sets".

An instance `(U, F, k)` with `U = {0, …, n − 1}` (`HSElemKernel.HSInstance`) is written as `n`, then a
listing of `F`, then `k`, every number in self-delimiting binary. Every listing order is a code. -/
def IsHSCode (I : HSElemKernel.HSInstance) (w : List Bool) : Prop :=
  ∃ L : List (List (Fin I.n)), IsListing I.S L ∧ w = encNat I.n ++ encFamily L ++ encNat I.k

/-- The codes of a `d`-Hitting Set instance: codes of instances in which every member of the family
has at most `d` elements (App. C.1, p.92: "In d-Hitting Set, d is fixed and the parameter is k"). -/
def IsDHSCode (d : ℕ) (I : HSElemKernel.HSInstance) (w : List Bool) : Prop :=
  HSElemKernel.IsDHS d I ∧ IsHSCode I w

/-- The feasible solutions of a Hitting Set instance: sets of at most `k` elements meeting every
member of the family. An empty family is hit by the empty set; a family containing `∅` has no
feasible solution (App. C.1, p.92). -/
def HSValid (I : HSElemKernel.HSInstance) (S : Finset (Fin I.n)) : Prop :=
  AlgebraicFPT.HittingSet.IsHitting I.S S ∧ S.card ≤ I.k

/-- `out` is the code of the list of families `Fs`: their number, then each family by some
listing (`IsListing`). -/
def IsFamListCode {n : ℕ} (Fs : List (Finset (Finset (Fin n)))) (out : List Bool) : Prop :=
  ∃ Ls : List (List (List (Fin n))), List.Forall₂ IsListing Fs Ls ∧ out = encList encFamily Ls

end RevRedSAT


