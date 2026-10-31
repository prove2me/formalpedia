-- Prove2me | Definitions.Def_FairVaccineReserves_DA_Model
-- name    : FairVaccineReserves_DA_Model
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T14:53:11.861081+00:00
-- url     : https://prove2.me/theorems/b62a2187-fc0b-4e49-a72c-a3e947b030fb
-- title:
--   Reserve systems with independent full priority orders
-- statement:
--   There are finitely many patients and categories. Each category $c$ has a natural-number quota $r_c$ and its own strict linear priority order $\pi_c$ on all patients together with the outside option $\varnothing$. The total supply is $q=\sum_c r_c$. Higher priority means strict precedence; weakly higher means equality or higher priority. Patient $i$ is eligible at $c$ exactly when $i\pi_c\varnothing$.
--
--   There is no relationship required between different categories' orders, no universal eligibility condition, no scarcity assumption, and no positive-quota restriction. Full orders retain the relative positions of ineligible patients.
--
--   **Formalization Note** Patients and categories are indexed by arbitrary `Fin n` and `Fin m`. A strict full order is a bijection from the corresponding `Option` type to all consecutive ranks, with smaller rank better. `none` represents the outside option. This uses the general Mathlib equivalence object. Total supply is derived from quotas instead of storing a redundant equality. Empty populations are also allowed as a boundary generalization.
-- source:
--   Pathak, Sönmez, Ünver and Yenmez, arXiv:2008.00374v3 (1 July 2023; draft May 2023), https://arxiv.org/abs/2008.00374v3, §3.1, printed/PDF p. 13

import Definitions.Def_GaleShapley1962_Admissions_Assignments
import Mathlib.Logic.Equiv.Defs

namespace FairVaccineReserves.DA

/-- Section 3.1: independent full category priorities, with smaller ranks better.
The rank bijection includes the outside option and all ineligible patients. -/
structure ReserveSystem (n m : ℕ) where
  quota : Fin m → ℕ
  priority : Fin m → (Option (Fin n) ≃ Fin (n + 1))

def ReserveSystem.totalUnits {n m : ℕ} (R : ReserveSystem n m) : ℕ :=
  ∑ c : Fin m, R.quota c

def ReserveSystem.Higher {n m : ℕ} (R : ReserveSystem n m)
    (c : Fin m) (x y : Option (Fin n)) : Prop :=
  R.priority c x < R.priority c y

def ReserveSystem.WeaklyHigher {n m : ℕ} (R : ReserveSystem n m)
    (c : Fin m) (x y : Option (Fin n)) : Prop :=
  x = y ∨ R.Higher c x y

def ReserveSystem.Eligible {n m : ℕ} (R : ReserveSystem n m)
    (i : Fin n) (c : Fin m) : Prop :=
  R.Higher c (some i) none

instance {n m : ℕ} (R : ReserveSystem n m) (i : Fin n) (c : Fin m) :
    Decidable (R.Eligible i c) := by
  unfold ReserveSystem.Eligible ReserveSystem.Higher
  infer_instance

end FairVaccineReserves.DA


