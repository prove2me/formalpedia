-- Prove2me | Definitions.Def_CFLOutliers_LocalRun
-- name    : CFLOutliers_LocalRun
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:39:28.20451+00:00
-- url     : https://prove2.me/theorems/d63ac9fd-5afd-4712-809d-5af4f2619256
-- title:
--   Terminal solutions and runs of $\mathrm{Local}(\lambda,\tau;S_0)$
-- statement:
--   Fix $\lambda\ge 0$ and $\tau>0$. The **exact add change** of a closed facility $t$ is $\Phi^*_\lambda(F_S\cup\{t\})-\Phi_\lambda(S)$.
--
--   A solution $S$ is **terminal** if
--
--   1. its assignment is an optimal penalty assignment on $F_S$;
--   2. every exact add change of a closed facility is at least $-\tau$;
--   3. every admissible open certificate (9) is at least $-\tau$;
--   4. every admissible close certificate (10) is at least $-\tau$.
--
--   An **accepted change** goes from $S$ to $S'$: some exact add change, open certificate or close certificate of $S$ is below $-\tau$, $S'$ has the corresponding open set ($F_S\cup\{t\}$, $(F_S\cup\{t\})\setminus K$ or $(F_S\setminus\{s\})\cup T$), and $S'$ carries an optimal penalty assignment on it.
--
--   A **run** of $\mathrm{Local}(\lambda,\tau;S_0)$ with $N$ accepted changes first computes an optimal penalty assignment on the open set of $S_0$, then makes $N$ accepted changes, and ends at a terminal solution, its output.
--
--   **Formalization Note** The paper leaves open which optimal assignment is computed and which improving change is applied; every choice is a run, so statements about runs hold for every run.
-- source:
--   R. Dabas, A Constant-Factor Approximation for Capacitated Facility Location with Outliers, arXiv:2611.04094 (preprint; held version, sha256 613f7405…9798), §3.2, p.9

import Mathlib
import Definitions.Def_CFLOutliers_assignChange

namespace CFLOutliers

open Finset

/-- **Exact add change** of `add(t)` (§3.2, p.9): `Φ*_λ(F_S ∪ {t}) − Φ_λ(S)`, computed with the
original capacities and including the opening cost `f_t`. -/
noncomputable def addChange {I : Inst} (lam : ℝ) (S : Sol I) (t : Fin I.m) : ℝ :=
  PhiStar I lam (insert t S.openSet) - Phi lam S

/-- **Terminal solution** of `Local(λ, τ; ·)` (§3.2, p.9): the assignment is an optimal penalty
assignment on `F_S`, every exact add change of a closed facility, every admissible open
certificate (9) and every admissible close certificate (10) is at least `−τ`. -/
def IsTerminal {I : Inst} (lam τ : ℝ) (S : Sol I) : Prop :=
  PenaltyOptimal lam S ∧
  (∀ t, t ∉ S.openSet → -τ ≤ addChange lam S t) ∧
  (∀ t K, OpenAdm S t K → -τ ≤ DeltaOpen lam S t K) ∧
  (∀ s T a, CloseAdm S s T a → -τ ≤ DeltaClose lam S s T a)

/-- **One accepted change** of `Local(λ, τ; ·)` (§3.2, p.9): some exact add change, open
certificate (9) or close certificate (10) of `S` is below `−τ`; `S'` has the open set of that
change (`F_S ∪ {t}`, `(F_S ∪ {t}) \ K` or `(F_S \ {s}) ∪ T`) and any optimal penalty assignment on
it ("applies a change with value below −τ and recomputes the optimal assignment"). -/
def LocalStep {I : Inst} (lam τ : ℝ) (S S' : Sol I) : Prop :=
  ((∃ t, t ∉ S.openSet ∧ addChange lam S t < -τ ∧ S'.openSet = insert t S.openSet) ∨
   (∃ t K, OpenAdm S t K ∧ DeltaOpen lam S t K < -τ ∧ S'.openSet = insert t S.openSet \ K) ∨
   (∃ s T a, CloseAdm S s T a ∧ DeltaClose lam S s T a < -τ ∧
      S'.openSet = S.openSet.erase s ∪ T)) ∧
  PenaltyOptimal lam S'

/-- **A run of `Local(λ, τ; S₀)`** (§3.2, p.9) with `N` accepted changes ending at `S`: first an
optimal penalty assignment on the open set of `S₀`, then `N` accepted changes, ending at a
terminal solution `S`.

**Formalization Note.** The paper leaves open which optimal assignment is computed ("need not be
unique", p.7) and which improving change is applied; the relation admits every such choice, so
statements about runs hold for every run. -/
def LocalRun {I : Inst} (lam τ : ℝ) (S0 S : Sol I) (N : ℕ) : Prop :=
  ∃ seq : ℕ → Sol I, (seq 0).openSet = S0.openSet ∧ PenaltyOptimal lam (seq 0) ∧
    (∀ k < N, LocalStep lam τ (seq k) (seq (k + 1))) ∧ seq N = S ∧ IsTerminal lam τ S

end CFLOutliers


