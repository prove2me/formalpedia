-- Prove2me | Definitions.Def_RobustMarkovAssort_Duality_Extrema
-- name    : RobustMarkovAssort_Duality_Extrema
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T23:15:38.85308+00:00
-- url     : https://prove2.me/theorems/a1c5d060-6b2c-4684-b6e1-13327bb5286f
-- title:
--   Attained optimization values and nested min–max values
-- statement:
--   MinValue and MaxValue mean a least or greatest member of the objective image, hence include attainment. MaxMin requires an inner minimum for every assortment and a greatest such value. MinMax requires an inner maximum for every admissible scenario and a least such value. These predicates assign no default value to an empty image or to an unattained extremum.
-- source:
--   Désir, Goyal, Jiang, Xie and Zhang, Robust Assortment Optimization Under the Markov Chain Choice Model, Operations Research (2023), DOI 10.1287/opre.2022.2420; canonical artifact pp. 8–12, the displayed robust programs

import Mathlib

namespace RobustMarkovAssort.Duality

def MinValue {α : Type*} (U : Set α) (g : α → ℝ) (z : ℝ) : Prop :=
  IsLeast (g '' U) z

def MaxValue {α : Type*} (U : Set α) (g : α → ℝ) (z : ℝ) : Prop :=
  IsGreatest (g '' U) z

def MaxMin {α β : Type*} (U : Set β) (R : α → β → ℝ) (z : ℝ) : Prop :=
  (∀ S, ∃ t, MinValue U (R S) t) ∧
  IsGreatest {t | ∃ S, MinValue U (R S) t} z

def MinMax {α β : Type*} (U : Set β) (R : α → β → ℝ) (z : ℝ) : Prop :=
  (∀ u ∈ U, ∃ t, MaxValue Set.univ (fun S => R S u) t) ∧
  IsLeast {t | ∃ u ∈ U, MaxValue Set.univ (fun S => R S u) t} z

end RobustMarkovAssort.Duality


