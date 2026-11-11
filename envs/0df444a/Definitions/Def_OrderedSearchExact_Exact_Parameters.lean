-- Prove2me | Definitions.Def_OrderedSearchExact_Exact_Parameters
-- name    : OrderedSearchExact_Exact_Parameters
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T07:06:58.540198+00:00
-- url     : https://prove2.me/theorems/7f853f72-8c19-454c-89b4-223af805618a
-- title:
--   Slowly varying quartic parameters and the constructed family
-- statement:
--   A parameter record contains sequences $W_m,d_m,\rho_m,M_m$ and natural thresholds $N_m$. Its admissibility requirements are precisely the near-$\pi$ compact certificate, $M_m\ge1$, $\tanh(M_m/2)>\rho_m^2$, strict growth of the thresholds to infinity, $2N_m\ge M_m$, and $(W_m+\ln M_m+1)/\ln n\le1/m$ for $m\ge1$ and $n\ge N_m$. Positive widths, $0<d_m<\pi$, monotone convergence $d_m\uparrow\pi$, and $0<\rho_m<1$ are explicit. An unused zero index is allowed, and thresholds start at least at two.
--
--   For each $n$, choose the largest eligible $m\ge1$ with $N_m\le n$; before the first threshold use index zero. Fix $h_{W_m}$ for the whole greedy run. Set $k(n)$ to (43) with $D=2$, run $k(n)-2$ greedy steps, and append the concrete two-step exactifier. The little-o predicate means
--
--   $$\forall\varepsilon>0\;\exists N\;\forall n\ge N:\quad |k(n)-\ln n/\pi|\le\varepsilon\ln n.$$
--
--   No existence, feasibility, or algorithm-correctness assertion is a field of the parameter record: these remain conclusions of the main theorem.
-- source:
--   Joseph Carolan, Andrew Childs, STOC 2027 submission #1443 (October 2026), Proposition 4.9; §4.6, (47)–(49), p.21, 23–24 (PDF p.21, 23–24); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1443.pdf; sha256 8bb6cbb4037a439039875fd77a9f212e2c0f90a6e87f0c4c690230223813da44

import Definitions.Def_OrderedSearchExact_Exact_Greedy

open Filter

namespace OrderedSearchExact.Exact

/-- Only parameter data. Existence and the resulting path's correctness are conclusions
of Theorem 4.14, never fields of this structure. Indices m≥1 are used. -/
structure Parameters where
  W : ℕ → ℝ
  d : ℕ → ℝ
  ρ : ℕ → ℝ
  M : ℕ → ℝ
  N : ℕ → ℕ

def NearPi (W d ρ : ℕ → ℝ) : Prop :=
  Tendsto W atTop atTop ∧ Monotone d ∧ Tendsto d atTop (nhds Real.pi) ∧
    ∀ m, 0 < W m ∧ 0 < d m ∧ d m < Real.pi ∧ 0 < ρ m ∧ ρ m < 1 ∧
      IsDensity (quarticDensity (W m)) ∧
      ∀ x, |convB (quarticDensity (W m)) x - convB (quarticDensity (W m)) (x - d m)| ≤
        2 * ρ m * Real.sqrt (convA (quarticDensity (W m)) x *
          convA (quarticDensity (W m)) (x - d m))

def Admissible (P : Parameters) : Prop :=
  NearPi P.W P.d P.ρ ∧ StrictMono P.N ∧ Tendsto P.N atTop atTop ∧ 2 ≤ P.N 0 ∧
    ∀ m, 1 ≤ m → 1 ≤ P.M m ∧ Real.tanh (P.M m / 2) > P.ρ m ^ 2 ∧
      P.M m ≤ 2 * P.N m ∧
      ∀ n, P.N m ≤ n → (P.W m + Real.log (P.M m) + 1) / Real.log n ≤ 1 / (m : ℝ)

/-- Largest eligible m; strict threshold growth implies it lies at most n.
The value 0 before the first threshold has no asymptotic significance. -/
noncomputable def parameterIndex (P : Parameters) (n : ℕ) : ℕ :=
  Nat.findGreatest (fun m => 1 ≤ m ∧ P.N m ≤ n) n

noncomputable def familyBudget (P : Parameters) (n : ℕ) : ℕ :=
  queryBudget n (P.W (parameterIndex P n)) (P.d (parameterIndex P n))
    (P.M (parameterIndex P n)) 2

noncomputable def familyDensity (P : Parameters) (n : ℕ) : ℝ → ℝ :=
  quarticDensity (P.W (parameterIndex P n))

/-- Run the greedy prefix for budget−2 steps and apply the explicit exactifier.
Completed constant paths continue by zero increments. -/
noncomputable def constructedPath (P : Parameters) (n : ℕ) : ℕ → Coeff n :=
  exactify (greedyPath n (familyDensity P n)) (familyBudget P n - 2)

def AdversaryAsymptotic (k : ℕ → ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    |(k n : ℝ) - Real.log n / Real.pi| ≤ ε * Real.log n

end OrderedSearchExact.Exact


