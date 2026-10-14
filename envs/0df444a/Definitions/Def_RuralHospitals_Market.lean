-- Prove2me | Definitions.Def_RuralHospitals_Market
-- name    : RuralHospitals_Market
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-11T15:15:47.275185+00:00
-- url     : https://prove2.me/theorems/c6cd3603-b024-4470-b1d6-42ec04f760ac
-- title:
--   Many-to-one doctor–hospital matching market with strict preferences
-- statement:
--   A **many-to-one matching market** consists of a finite set $D$ of doctors, a finite set $H$ of hospitals, and for each hospital $h$ a capacity $q_h\in\mathbb N$ (its number of positions).
--
--   1. Each doctor $d$ has a **strict** preference order over $H\cup\{\varnothing\}$, where $\varnothing$ means remaining unmatched; hospitals ranked below $\varnothing$ are unacceptable to $d$.
--   2. Each hospital $h$ has a **strict** preference order over $D\cup\{\varnothing\}$, where $\varnothing$ means leaving a position empty; doctors ranked below $\varnothing$ are unacceptable to $h$. Preferences over groups of doctors are responsive to this ranking.
--
--   An **assignment** $\mu$ sends each doctor to a hospital or to $\varnothing$; write $\mu(h)$ for the set of doctors assigned to $h$. The assignment is a **matching** if $|\mu(h)|\le q_h$ for all $h$. It is **individually rational** if every doctor weakly prefers $\mu(d)$ to $\varnothing$ and every hospital prefers each doctor in $\mu(h)$ to an empty position. A pair $(d,h)$ **blocks** $\mu$ if $d$ prefers $h$ to $\mu(d)$, $h$ finds $d$ acceptable, and either $|\mu(h)|<q_h$ or $h$ prefers $d$ to some doctor in $\mu(h)$. A matching is **stable** if it is individually rational and has no blocking pair.
--
--   This is the setting of the rural hospitals theorem (Roth 1984, 1986), and covers the one-to-one case $q_h\equiv 1$ (McVitie–Wilson 1970).
--
--   **Formalization Note** Preferences are encoded by rank functions `docRank d : Option H → ℕ` and `hospRank h : Option D → ℕ` (smaller rank = more preferred, `none` = unmatched / empty position), required to be injective so that preferences are strict. An assignment is `μ : D → Option H`; `assigned μ h` is the finset of doctors with `μ d = some h`. The predicates are `Market.IsMatching`, `Market.IsIndividuallyRational`, `Market.IsBlockingPair` and `Market.IsStable`.
-- source:
--   Wikipedia, "Rural hospitals theorem", revision oldid=1064508418 (https://en.wikipedia.org/w/index.php?title=Rural_hospitals_theorem&oldid=1064508418), introduction and section "Proof of a special case" (stable matching with strict preferences, hospital capacities, acceptability). Model as in A. E. Roth, Econometrica 54 (1986) 425–427, doi:10.2307/1913160.

import Mathlib

/-!
# Many-to-one matching markets (doctors and hospitals) with strict preferences

Model for the rural hospitals theorem (Roth 1984, 1986; McVitie–Wilson 1970).
Preferences are encoded by injective rank functions (smaller rank = more preferred),
which makes them strict total orders.  The option `none` stands for "remaining
unmatched" (for a doctor) or "leaving the position empty" (for a hospital), so each
side may find some partners unacceptable.  Hospital preferences over groups of
doctors are responsive to the ranking of individual doctors.
-/

namespace RuralHospitals

open Finset

/-- A many-to-one matching market between a finite set `D` of doctors and a finite set
`H` of hospitals, with strict preferences and hospital capacities. -/
structure Market (D H : Type*) [Fintype D] [Fintype H] where
  /-- `docRank d o` is the rank doctor `d` gives to outcome `o`
  (`some h` = working at `h`, `none` = unmatched); smaller is better. -/
  docRank : D → Option H → ℕ
  /-- Doctors' preferences are strict. -/
  docRank_injective : ∀ d, Function.Injective (docRank d)
  /-- `hospRank h o` is the rank hospital `h` gives to `o`
  (`some d` = doctor `d`, `none` = an empty position); smaller is better. -/
  hospRank : H → Option D → ℕ
  /-- Hospitals' preferences are strict. -/
  hospRank_injective : ∀ h, Function.Injective (hospRank h)
  /-- The number of positions of each hospital. -/
  capacity : H → ℕ

variable {D H : Type*} [Fintype D] [Fintype H] [DecidableEq H]

/-- An assignment of doctors: `μ d = some h` means `d` works at `h`,
`μ d = none` means `d` is unmatched. -/
abbrev Assignment (D H : Type*) := D → Option H

/-- The set of doctors assigned to hospital `h` under `μ`. -/
def assigned (μ : Assignment D H) (h : H) : Finset D :=
  univ.filter (fun d => μ d = some h)

namespace Market

variable (M : Market D H)

/-- `μ` is a matching: no hospital receives more doctors than it has positions. -/
def IsMatching (μ : Assignment D H) : Prop :=
  ∀ h, (assigned μ h).card ≤ M.capacity h

/-- Individual rationality: every doctor weakly prefers her assignment to being
unmatched, and every hospital strictly prefers each of its doctors to an empty position. -/
def IsIndividuallyRational (μ : Assignment D H) : Prop :=
  (∀ d, M.docRank d (μ d) ≤ M.docRank d none) ∧
  (∀ d h, μ d = some h → M.hospRank h (some d) < M.hospRank h none)

/-- `(d, h)` blocks `μ`: doctor `d` strictly prefers `h` to her assignment, `h` finds
`d` acceptable, and `h` either has an empty position or strictly prefers `d` to one of
its assigned doctors. -/
def IsBlockingPair (μ : Assignment D H) (d : D) (h : H) : Prop :=
  M.docRank d (some h) < M.docRank d (μ d) ∧
  M.hospRank h (some d) < M.hospRank h none ∧
  ((assigned μ h).card < M.capacity h ∨
    ∃ d' ∈ assigned μ h, M.hospRank h (some d) < M.hospRank h (some d'))

/-- A stable matching: a matching that is individually rational and has no blocking pair. -/
def IsStable (μ : Assignment D H) : Prop :=
  M.IsMatching μ ∧ M.IsIndividuallyRational μ ∧ ∀ d h, ¬ M.IsBlockingPair μ d h

end Market

end RuralHospitals


