-- Prove2me | Definitions.Def_SmoothedNash_run
-- name    : SmoothedNash_run
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:54:34.771739+00:00
-- url     : https://prove2.me/theorems/347b6d43-1ec1-4d4c-95d1-ccef25feb1b1
-- title:
--   A run of Algorithm 2
-- statement:
--   A **run of Algorithm 2** on a game $u$ with accuracy $\varepsilon$, a support order $\sigma$ and a frontier enumeration processes the support profiles in the order $\sigma$, one by one, as in the outer loop of the algorithm. It stops at the first support profile that returns a point and returns that point (line 15); after the last support profile it returns **Fail** (line 25). The numbers of payoff-vector computations and of work units add up over the support profiles processed, the returning one included.
--
--   This is the deterministic algorithm whose output and cost Theorem 2.2 describes.
-- source:
--   Attias–Dagan–Daskalakis–Yao–Zampetakis, Nash Equilibria, Variational Inequalities, and Fixed Points: Beating Brute Force via Smoothed Analysis, STOC 2027 submission (manuscript sha256 3f9ea37d…77a1ea53), Algorithm 2, p.15

import Mathlib
import Definitions.Def_SmoothedNash_Game
import Definitions.Def_SmoothedNash_SupportProfile
import Definitions.Def_SmoothedNash_RunResult
import Definitions.Def_SmoothedNash_supportRun

namespace SmoothedNash

/-- A run of Algorithm 2 (Attias–Dagan–Daskalakis–Yao–Zampetakis, *Nash Equilibria, Variational Inequalities, and Fixed Points: Beating Brute Force via Smoothed Analysis*, STOC 2027 submission manuscript (sha256 3f9ea37d…77a1ea53), p.15) on the game `u` with accuracy `ε`: the support profiles are
processed in the order of the list `σ` (line 2) by `supportRun`, the run stops at the first support
that returns a point (line 15), and `Fail` (`out = none`, line 25) is returned after the last one.
`evals` and `work` add up over the supports processed, the returning one included. -/
noncomputable def run {m n : ℕ} (u : Game m n) (ε : ℝ)
    (enum : SupportProfile m n → Finset (Fin m → Fin n → ℕ) → List (Fin m → Fin n → ℕ)) :
    List (SupportProfile m n) → RunResult m n
  | [] => ⟨none, 0, 0⟩
  | A :: σ =>
    match (supportRun u ε enum A).out with
    | some _ => supportRun u ε enum A
    | none =>
      ⟨(run u ε enum σ).out, (supportRun u ε enum A).evals + (run u ε enum σ).evals,
        (supportRun u ε enum A).work + (run u ε enum σ).work⟩

end SmoothedNash


