-- Prove2me | Definitions.Def_PaceSSSP517_Certified_Supplement_TraceStatistics
-- name    : PaceSSSP517_Certified_Supplement_TraceStatistics
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T19:32:42.267042+00:00
-- url     : https://prove2.me/theorems/0ab814f5-2bbf-445a-9429-dbb3bd441ed9
-- title:
--   Executed windows, density, bulk intervals and trajectory climb length
-- statement:
--   For a published PACE round list $t_1,\ldots,t_R$, retain its one-based indices, profiles $d_j$, bulk flags, relative jumps $J(e;d_j)$, total weights $Q^{(j)}$ and violating fractions $\rho_j$. Write $s=(20/\varepsilon)kn^{1+1/k}\ln n$. For $S_L=\{r_0,\ldots,r_0+L-1\}$, let $J_L^\star=\max_{j\in S_L,e\in E}J(e;d_j)$ and let $L^\star$ be the least positive $L$ with $J_L^\star/\varepsilon\le L$. The execution-wide maximum is $J^\star=\max_{1\le j\le R,e\in E}J(e;d_j)$. Define
--
--   $$
--   \gamma=m/s,\qquad
--   T=\left\lfloor\min\{5k/\varepsilon,\;kn^{2/k}/(3\varepsilon\gamma)\}\right\rfloor.
--   $$
--
--   Count non-bulk and bulk executed rounds through a specified horizon. Count maximal bulk intervals by their starts: a bulk round that is round 1 or follows a non-bulk round. Failure counts filter a round set using the published violation predicate.
--
--   Over non-bulk rounds $j\le R$, let $\rho_R^\star=\max_j\rho_j$. When this set is nonempty, define
--   $$
--   f_R^\star(\rho_R^\star)=
--   \left\lceil\frac{\ln(2Q^{(R+1)}/s)}
--   {\ln(1+\varepsilon/(10k\rho_R^\star))}\right\rceil\in\mathbb Z.
--   $$
--   When there is no such round, the evaluated climb length is zero. The general formula climbAt keeps $\rho$ as an argument; climbLength handles the empty maximum without dividing by zero.
--
--   These are statistics of the actual trace, not success assumptions. Theorems must establish the existence, minimality and bounds for the qualifying window and all failure and stopping estimates.
--
--   **Formalization Note** Finite real maxima include zero, changing no nonempty maximum of these nonnegative quantities. Only to totalize the least-window search after a finite execution ends, nonexistent rounds contribute no jump. Every claimed window inequality and stopping window is wholly executed. Empty infima for the least qualifying length default to zero, with nonemptiness and a positive least length asserted by Theorem 3.7. The climb formula uses an integer ceiling, including on negative numerators, and actual Qat at $R+1$. No potential upper bound is substituted.
-- source:
--   Sarwan Ali, STOC 2027 submission #517 (October 2026), pp. 7–9, Theorems 3.7(iv), 3.10, display (2), and Theorem 3.11; pp. 19–20, A.6/A.8/A.9

import Definitions.Def_PaceSSSP517_Certified_Resources

set_option autoImplicit false
open Classical

namespace PaceSSSP517.Certified.Supplement

/-- The source's one-based half-open window S_L. -/
def window (r₀ L : ℕ) : Finset ℕ := Finset.Ico r₀ (r₀ + L)

/-- Maximum jump in a finite execution window. Nonexecuted indices contribute
zero; this only totalizes L⋆ when its proposed window outlasts the execution.
Every asserted window inequality uses a completely executed window. -/
noncomputable def windowJump {n : ℕ} (G : WeightedGraph n) (ts : List (Round n))
    (r₀ L : ℕ) : ℝ :=
  let S := (window r₀ L).filter (fun j => 1 ≤ j ∧ j ≤ ts.length)
  let values := S.biUnion (fun j => G.edges.image (jump G (profile ts j)))
  (insert 0 values).max' (Finset.insert_nonempty _ _)

/-- Least positive L satisfying the observed-window stopping inequality.
Existence and the source's ceiling bound are theorem conclusions, not fields. -/
noncomputable def firstWindow {n : ℕ} (G : WeightedGraph n) (ts : List (Round n))
    (ε : ℝ) (r₀ : ℕ) : ℕ :=
  sInf {L : ℕ | 1 ≤ L ∧ windowJump G ts r₀ L / ε ≤ (L : ℝ)}

noncomputable def executionJump {n : ℕ} (G : WeightedGraph n)
    (ts : List (Round n)) : ℝ := windowJump G ts 1 ts.length

noncomputable def density {n : ℕ} (G : WeightedGraph n) (k : ℕ) (ε : ℝ) : ℝ :=
  G.edges.card / budget n k ε

/-- Natural floor of the nonnegative horizon in Theorem 3.10, p.8. -/
noncomputable def earlyHorizon {n : ℕ} (G : WeightedGraph n) (k : ℕ) (ε : ℝ) : ℕ :=
  ⌊min (5 * (k : ℝ) / ε)
    ((k : ℝ) * (n : ℝ) ^ (2 / (k : ℝ)) / (3 * ε * density G k ε))⌋₊

noncomputable def nonBulkRounds {n : ℕ} (ts : List (Round n)) (R : ℕ) : Finset ℕ :=
  (past (min R ts.length)).filter (fun j => (roundAt ts j).bulk = false)

noncomputable def bulkRounds {n : ℕ} (ts : List (Round n)) (R : ℕ) : Finset ℕ :=
  (past (min R ts.length)).filter (fun j => (roundAt ts j).bulk = true)

/-- Each maximal interval of executed bulk rounds has exactly one start. -/
noncomputable def bulkRunCount {n : ℕ} (ts : List (Round n)) : ℕ :=
  ((bulkRounds ts ts.length).filter (fun j =>
    j = 1 ∨ (roundAt ts (j - 1)).bulk = false)).card

noncomputable def failureRounds {n : ℕ} (G : WeightedGraph n)
    (ts : List (Round n)) (S : Finset ℕ) (e : Edge n) : Finset ℕ :=
  S.filter (fun j => fails G (profile ts j) e)

/-- Maximum violating fraction over the executed non-bulk rounds up to R.
Zero is an empty-maximum convention; climbLength handles that case separately. -/
noncomputable def rhoStar {n : ℕ} (G : WeightedGraph n)
    (ts : List (Round n)) (R : ℕ) : ℝ :=
  let values := (nonBulkRounds ts R).image (rhoAt G ts)
  (insert 0 values).max' (Finset.insert_nonempty _ _)

/-- The exact integer ceiling in display (2), p.9, with the actual Q^(R+1).
The real formula is used at positive rho, never at the empty maximum. -/
noncomputable def climbAt {n : ℕ} (G : WeightedGraph n) (ts : List (Round n))
    (k : ℕ) (ε : ℝ) (R : ℕ) (ρ : ℝ) : ℤ :=
  ⌈Real.log (2 * Qat G ts (R + 1) / budget n k ε) /
    Real.log (1 + ε / (10 * (k : ℝ) * ρ))⌉

/-- f⋆_R(rho⋆_R), with value zero when no non-bulk round has occurred. -/
noncomputable def climbLength {n : ℕ} (G : WeightedGraph n) (ts : List (Round n))
    (k : ℕ) (ε : ℝ) (R : ℕ) : ℤ :=
  if (nonBulkRounds ts R).Nonempty then climbAt G ts k ε R (rhoStar G ts R) else 0

end PaceSSSP517.Certified.Supplement


