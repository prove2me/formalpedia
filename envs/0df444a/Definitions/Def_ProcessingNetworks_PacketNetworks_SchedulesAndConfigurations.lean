-- Prove2me | Definitions.Def_ProcessingNetworks_PacketNetworks_SchedulesAndConfigurations
-- name    : ProcessingNetworks_PacketNetworks_SchedulesAndConfigurations
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T19:45:15.672711+00:00
-- url     : https://prove2.me/theorems/cce2e6e3-abe5-40c7-b84a-801af448b5ee
-- title:
--   Link configurations, schedule sets, and Assumption 12.4 (Section 12.2, Eqs. 12.3-12.4, 12.9-12.10)
-- statement:
--   **Section 12.2.** Links $k\in K$ and a $K\times J$ link usage matrix $A$ (single $1$ per
--   column) give, for a configuration $c\in\mathbb Z^K_+$, the schedule set $S_c := \{s\in
--   \mathbb Z^J_+ : As\le c\}$ (Eq. 12.9), and $S := \bigcup_{c\in C} S_c$ (Eq. 12.10) for a
--   feasible-configuration set $C$. $S$ is monotone (Eq. 12.4): every schedule dominated by a
--   feasible one is feasible.
--
--   **Assumption 12.4.** Every link has positive capacity under some feasible configuration.
--
--   **Formalization note.** `IsScheduleSetAt`/`IsScheduleSet` characterize $S_c$/$S$ via an `↔`
--   rather than constructing them, since enumerating a `Finset` from `A`/`c`/`C` needs no explicit
--   construction for this mission's own downstream statements — matching how set-valued model data
--   (e.g. `TildeAllocSet` in missions IX/X) is taken as given elsewhere in this series. `C`/`S` are
--   `Finset`s throughout, a standing convention (see `LinkConfigData`'s own doc comment).
-- source:
--   Dai & Harrison, Processing Networks: Fluid Models and Stability, pre-publication draft 2020-4-2, p. 228, Section 12.2, Assumption 12.4, Eqs. (12.3),(12.4),(12.9),(12.10)

import Mathlib

namespace ProcessingNetworks.PacketNetworks

/-- Link configuration data (Section 12.2): `K` links, a `K × J` link usage matrix `A` with a
single `1` in each column (`hA`: activity `j` uses exactly one link), and a finite set `C` of
feasible link configurations. `C`/`S` are taken as `Finset`s throughout this mission — every
worked example in the book has finitely many configurations and (since each column of `A` has a
single `1`, so `As ≤ c` bounds each `s j` by the capacity of `j`'s own link) finitely many
schedules per configuration; this is a standing convention, not a per-item hypothesis, documented
in `MODERATION_NOTES.md`. -/
structure LinkConfigData (J K : ℕ) where
  A : Matrix (Fin K) (Fin J) ℝ
  hA : ∀ j : Fin J, ∃! k : Fin K, A k j = 1
  hA0 : ∀ j : Fin J, ∀ k : Fin K, A k j ≠ 1 → A k j = 0
  C : Finset (Fin K → ℕ)

/-- Assumption 12.4, Dai & Harrison p. 228 (PDF p. 244): for each link `k` there exists a
feasible configuration giving it positive capacity. -/
def SatisfiesAssumption124 {J K : ℕ} (cfg : LinkConfigData J K) : Prop :=
  ∀ k : Fin K, ∃ c ∈ cfg.C, 0 < c k

/-- The packet availability / capacity constraint `As ≤ c` (Eq. 12.3 specialized with a fixed
configuration `c` in place of a general capacity vector): schedule `s` is available under
configuration `c`. -/
def scheduleAvailable {J K : ℕ} (cfg : LinkConfigData J K) (c : Fin K → ℕ) (s : Fin J → ℕ) : Prop :=
  ∀ k : Fin K, (cfg.A.mulVec (fun j => (s j : ℝ))) k ≤ (c k : ℝ)

/-- `Sc` (Eq. 12.9), characterized rather than constructed: `Sc` is *the* schedule set for
configuration `c` iff it contains exactly the schedules available under `c`. -/
def IsScheduleSetAt {J K : ℕ} (cfg : LinkConfigData J K) (c : Fin K → ℕ)
    (Sc : Finset (Fin J → ℕ)) : Prop :=
  ∀ s : Fin J → ℕ, s ∈ Sc ↔ scheduleAvailable cfg c s

/-- `S := ⋃_{c∈C} Sc` (Eq. 12.10), characterized rather than constructed, matching
`IsScheduleSetAt`'s convention. -/
def IsScheduleSet {J K : ℕ} (cfg : LinkConfigData J K) (S : Finset (Fin J → ℕ)) : Prop :=
  ∀ s : Fin J → ℕ, s ∈ S ↔ ∃ c ∈ cfg.C, scheduleAvailable cfg c s

/-- `S` is monotone (Eq. 12.4): every schedule dominated (componentwise) by a feasible schedule
is itself feasible. -/
def IsMonotoneScheduleSet {J : ℕ} (S : Finset (Fin J → ℕ)) : Prop :=
  ∀ s ∈ S, ∀ s' : Fin J → ℕ, (∀ j, s' j ≤ s j) → s' ∈ S

end ProcessingNetworks.PacketNetworks


