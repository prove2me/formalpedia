-- Prove2me | Definitions.Def_KServer_discrete_martingale
-- name    : KServer_discrete_martingale
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-01T09:33:05.438261+00:00
-- url     : https://prove2.me/theorems/5b05b80e-ea1a-4ede-a7da-9c57533d090f
-- title:
--   Finite discrete martingales with atom-encoded filtrations
-- statement:
--   A **finite discrete martingale difference structure**: a finite sample space $\Omega$ with nonnegative weights $P$, a refining filtration encoded by functions $\mathrm{hist}_j \colon \Omega \to \mathbb{N}$ (two outcomes lie in the same time-$j$ atom iff their values agree), and increments $X_j$ that are measurable at time $j+1$, have conditional mean zero on every time-$j$ atom, and conditional second moment $v_j$ (measurable at time $j$):
--
--   $$\sum_{\omega \in A} P(\omega) X_j(\omega) = 0, \qquad \sum_{\omega \in A} P(\omega) X_j(\omega)^2 = v_j(A) \sum_{\omega \in A} P(\omega)$$
--
--   for every time-$j$ atom $A$. `mgSum X j` is the partial-sum process $S_j = X_0 + \dots + X_{j-1}$.
--
--   ## Role
--
--   This is the probabilistic scaffolding for the stage-2a analysis in the Bubeck–Coester–Rabani lower bound (STOC 2023, Section 4.2): the left-right imbalance process of their subchunk construction is a martingale with bounded increments, and the lower bound needs an anti-concentration estimate for it at a variance-based stopping time. Encoding conditional structure by atom functions keeps everything at the level of finite sums — no measure theory. Stopping times are handled by zeroing increments after the stopping time, which preserves the structure, so no optional-stopping machinery is needed.
--
--   ## Formalization note
--
--   Conditional expectations are stated multiplicatively (no division by atom masses), so atoms of mass zero cause no trouble.
-- source:
--   Standard discrete martingale theory, packaged for S. Bubeck, C. Coester, Y. Rabani, 'The randomized k-server conjecture is false!', STOC 2023, Section 4.2.

import Mathlib

namespace KServer

open Finset

/-- The partial-sum process of a discrete-time process `X`. -/
def mgSum {Ω : Type*} (X : ℕ → Ω → ℝ) (j : ℕ) (ω : Ω) : ℝ :=
  ∑ i ∈ Finset.range j, X i ω

/-- A **finite discrete martingale difference structure**: `hist` is a refining
filtration of the finite weighted sample space `(Ω, P)` (encoded by functions to
`ℕ`, two outcomes being in the same time-`j` atom iff their values agree), the
increment `X j` is measurable at time `j + 1`, has conditional mean zero on every
time-`j` atom, and conditional second moment `v j` (itself measurable at time `j`). -/
structure IsDiscreteMartingale {Ω : Type*} [Fintype Ω] (P : Ω → ℝ) (N : ℕ)
    (hist : ℕ → Ω → ℕ) (X v : ℕ → Ω → ℝ) : Prop where
  hP : ∀ ω, 0 ≤ P ω
  href : ∀ i j : ℕ, i ≤ j → ∀ ω ω', hist j ω = hist j ω' → hist i ω = hist i ω'
  hadapt : ∀ j, j < N → ∀ ω ω', hist (j + 1) ω = hist (j + 1) ω' → X j ω = X j ω'
  hvmeas : ∀ j, j < N → ∀ ω ω', hist j ω = hist j ω' → v j ω = v j ω'
  hmart : ∀ j, j < N → ∀ ω₀ : Ω,
    ∑ ω ∈ univ.filter (fun ω => hist j ω = hist j ω₀), P ω * X j ω = 0
  hvar : ∀ j, j < N → ∀ ω₀ : Ω,
    ∑ ω ∈ univ.filter (fun ω => hist j ω = hist j ω₀), P ω * (X j ω) ^ 2
      = v j ω₀ * ∑ ω ∈ univ.filter (fun ω => hist j ω = hist j ω₀), P ω

end KServer


