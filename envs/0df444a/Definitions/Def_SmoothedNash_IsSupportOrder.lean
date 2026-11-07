-- Prove2me | Definitions.Def_SmoothedNash_IsSupportOrder
-- name    : SmoothedNash_IsSupportOrder
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:47:44.892421+00:00
-- url     : https://prove2.me/theorems/c4310184-e4f6-408c-b3ef-b845fabaf794
-- title:
--   Processing order of the support profiles
-- statement:
--   A **support order** is a list of support profiles in which every support profile occurs exactly once. Line 2 of Algorithm 2 ("for all support profiles $A$") fixes no order; the theorems hold for every order.
-- source:
--   Attias–Dagan–Daskalakis–Yao–Zampetakis, Nash Equilibria, Variational Inequalities, and Fixed Points: Beating Brute Force via Smoothed Analysis, STOC 2027 submission (manuscript sha256 3f9ea37d…77a1ea53), Algorithm 2 line 2, p.15

import Mathlib
import Definitions.Def_SmoothedNash_SupportProfile

namespace SmoothedNash

/-- A processing order of the support profiles for line 2 of Algorithm 2 (Attias–Dagan–Daskalakis–Yao–Zampetakis, *Nash Equilibria, Variational Inequalities, and Fixed Points: Beating Brute Force via Smoothed Analysis*, STOC 2027 submission manuscript (sha256 3f9ea37d…77a1ea53), p.15): a list in which
every support profile occurs exactly once. -/
def IsSupportOrder {m n : ℕ} (σ : List (SupportProfile m n)) : Prop :=
  σ.Nodup ∧ ∀ A, A ∈ σ

end SmoothedNash


