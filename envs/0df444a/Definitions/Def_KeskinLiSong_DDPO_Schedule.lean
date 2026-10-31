-- Prove2me | Definitions.Def_KeskinLiSong_DDPO_Schedule
-- name    : KeskinLiSong_DDPO_Schedule
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T14:45:16.303176+00:00
-- url     : https://prove2.me/theorems/c5ef3db4-fb5c-46cc-9f73-0179c5c33012
-- title:
--   Both DDPO schedules and history-based detections
-- statement:
--   For DDPO-N, m=ceil(kappa T^(1/3)) and n=ceil(kappa T^(2/3)); for DDPO-E, m=ceil(kappa log T) and n=ceil(kappa sqrt T). The experimental sets are the literal unions in equation (8), retaining overlaps. Internally prices i=0,1 represent source prices i=1,2. The cycle of t is ceil(t/n)-1. The last reset is computed recursively from comparisons of the two experimental demand means against all earlier means since the last reset. Empty comparison sets yield no detection. The sample set and M_t retain the source reset convention.
-- source:
--   Keskin, Li and Song (2022), Data-Driven Dynamic Pricing and Ordering with Perishable Inventory in a Changing Environment, Management Science, doi:10.1287/mnsc.2021.4011, supplied source.pdf (internally dated January 3, 2021; SSRN 3401188 footers), pp. 10–11, equations (8)–(11)

import Definitions.Def_KeskinLiSong_DDPO_Control

open MeasureTheory ProbabilityTheory
noncomputable section

namespace KeskinLiSong.DDPO

inductive Version | N | E deriving DecidableEq

structure Tuning (A : Model) where
  eta : ℝ
  kappa : ℝ
  rho : ℝ
  omega1 : ℝ
  omega2 : ℝ
  upsilon : ℝ
  positive : 0 < eta ∧ 0 < kappa ∧ 0 < rho
  test_prices : omega1 ∈ A.P ∧ omega2 ∈ A.P ∧ omega1 ≠ omega2
  test_stock : upsilon ∈ A.Y

def m {A : Model} (u : Tuning A) (v : Version) (T : ℕ) : ℕ :=
  Nat.ceil (u.kappa * if v = .N then (T : ℝ) ^ (1 / 3 : ℝ) else Real.log T)

def n {A : Model} (u : Tuning A) (v : Version) (T : ℕ) : ℕ :=
  Nat.ceil (u.kappa * if v = .N then (T : ℝ) ^ (2 / 3 : ℝ) else Real.sqrt T)

def block {A : Model} (u : Tuning A) (v : Version) (T i cycle : ℕ) : Finset ℕ :=
  (Finset.Icc 1 (m u v T)).image (fun s => cycle * n u v T + i * m u v T + s)

def experimentalAt {A : Model} (u : Tuning A) (v : Version) (T i : ℕ) : Finset ℕ :=
  (Finset.range (T / n u v T + 1)).biUnion (block u v T i)

def experimental {A : Model} (u : Tuning A) (v : Version) (T : ℕ) : Finset ℕ :=
  experimentalAt u v T 0 ∪ experimentalAt u v T 1

def cycleAt {A : Model} (u : Tuning A) (v : Version) (T t : ℕ) : ℕ :=
  Nat.ceil ((t : ℝ) / (n u v T : ℝ)) - 1

def demandMean {A : Model} (u : Tuning A) (v : Version) (T : ℕ)
    (D : ℕ → ℝ) (i cycle : ℕ) : ℝ :=
  (∑ t ∈ block u v T i cycle, D t) / m u v T

/-- Equation (9) recursively stores the last claimed detection. An empty
comparison set produces no detection. -/
def lastReset {A : Model} (u : Tuning A) (v : Version) (T : ℕ)
    (D : ℕ → ℝ) : ℕ → ℕ
  | 0 => 0
  | τ + 1 =>
    let L := lastReset u v T D τ
    if ∃ i ∈ Finset.range 2, ∃ s ∈ Finset.Ico L τ,
      u.eta < |demandMean u v T D i τ - demandMean u v T D i s|
    then τ + 1 else L

def samples {A : Model} (u : Tuning A) (v : Version) (T : ℕ)
    (D : ℕ → ℝ) (t : ℕ) : Finset ℕ :=
  (Finset.Icc (n u v T * lastReset u v T D (cycleAt u v T t) + 1) t) ∩
    experimental u v T

def sampleSize {A : Model} (u : Tuning A) (v : Version) (T : ℕ)
    (D : ℕ → ℝ) (t : ℕ) : ℕ :=
  m u v T * (Nat.ceil ((t : ℝ) / (n u v T : ℝ)) -
    lastReset u v T D (cycleAt u v T t))

end KeskinLiSong.DDPO


