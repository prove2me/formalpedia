-- Prove2me | Definitions.Def_CFLOutliers_QuotaOut
-- name    : CFLOutliers_QuotaOut
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:40:45.494939+00:00
-- url     : https://prove2.me/theorems/a9d52c14-6568-4438-81c7-172f9c120c30
-- title:
--   The complete quota algorithm of Appendix B as a relation
-- statement:
--   Let $0<\varepsilon\le 1$. The **outputs** of the complete quota algorithm are defined as follows. If $q=0$ the output is the empty solution. Otherwise, for every facility $i_0$ whose modified instance $J$ is feasible:
--
--   1. if $J$ has a capacity-feasible solution of cost $0$ serving at least $q$ clients, one such solution is recorded;
--   2. otherwise let $\ell$ be the smallest positive opening or connection cost of $J$ and $U$ the cost of opening all facilities of $J$ and assigning $q$ clients at minimum service cost. For $B=\ell 2^j$, $j=0,1,\dots$ up to the first scale with $B\ge U$, put
--   $$\tau=\frac{\varepsilon B}{100m},\qquad \eta=\frac{\varepsilon B}{100n},\qquad K=\Bigl\lceil\frac{400n}{\varepsilon}\Bigr\rceil,\tag{21}$$
--   with $m$ the original number of facilities. Starting from the empty solution $S_0$, $S_k$ is the output of a run of $\mathrm{Local}(k\eta,\tau;S_{k-1})$, $k=1,\dots,K$. At the first $k$ with $|C_{S_k}|\ge q$, a solution meeting the merge bound (3) for $S^-=S_{k-1}$, $S^+=S_k$ and $M=f_{i_0}$ is recorded; scales with no crossing are discarded.
--
--   An output is a recorded candidate of minimum cost under the original opening costs.
--
--   **Formalization Note** The procedure leaves choices open (optimal assignments, improving changes, the merged solution). The relation admits every execution, and the merge is any solution meeting Lemma 2.2's bound; the construction of Appendix A is one of them. $\ell$ and $U$ carry junk value $0$ in cases the procedure never reaches.
-- source:
--   R. Dabas, A Constant-Factor Approximation for Capacitated Facility Location with Outliers, arXiv:2611.04094 (preprint; held version, sha256 613f7405…9798), Appendix B, "Scales and parameters", p.14, displays (20)–(21)

import Mathlib
import Definitions.Def_CFLOutliers_LocalRun
import Definitions.Def_CFLOutliers_MergeSpec
import Definitions.Def_CFLOutliers_branchInst
import Definitions.Def_CFLOutliers_OPT

namespace CFLOutliers

open Finset

open Classical in
/-- The positive opening costs and positive connection costs of an instance. -/
noncomputable def posCosts (J : Inst) : Finset ℝ :=
  ((univ.image J.f) ∪ (univ.image (fun p : Fin J.m × Fin J.n => J.cFC p.1 p.2))).filter
    (fun x => 0 < x)

/-- `ℓ`, the smallest positive opening cost or connection cost (Appendix B, p.14); `0` when
there is none (a junk value, only reached for zero-cost branches, which are handled
separately). -/
noncomputable def ell (J : Inst) : ℝ :=
  if h : (posCosts J).Nonempty then (posCosts J).min' h else 0

open Classical in
/-- Capacity-feasible assignments into all facilities serving exactly `q` clients. -/
noncomputable def quotaAssign (J : Inst) : Finset (Fin J.n → Option (Fin J.m)) :=
  univ.filter (fun σ => AssignInto univ σ ∧ CapOK J σ ∧ (aserved σ).card = J.q)

/-- `U`, "the cost of opening all retained facilities and assigning q clients by minimum-cost
flow" (Appendix B, p.14); the assignment part is `0` (a junk value) if no such assignment exists,
which never happens on a feasible branch. -/
noncomputable def Ubound (J : Inst) : ℝ :=
  ∑ i, J.f i + if h : (quotaAssign J).Nonempty then (quotaAssign J).inf' h (acs J) else 0

/-- The instance has a zero-cost capacity-feasible solution serving at least `q` clients. -/
def ZeroCost (J : Inst) : Prop :=
  ∃ S : Sol J, S.CapFeasible ∧ J.q ≤ (served S).card ∧ cost S = 0

/-- The scale `B = ℓ 2^j` (Appendix B, p.14). -/
noncomputable def scaleB (J : Inst) (j : ℕ) : ℝ := ell J * 2 ^ j

/-- The scale index `j` is tried: "from j = 0 through the first scale at least U". -/
def ScaleOK (J : Inst) (j : ℕ) : Prop := ∀ j' < j, ell J * 2 ^ j' < Ubound J

/-- `τ = εB/(100 m)`, (21), with `m` the original number of facilities. -/
noncomputable def tauOf (I : Inst) (ε B : ℝ) : ℝ := ε * B / (100 * I.m)

/-- `η = εB/(100 n)`, (21). -/
noncomputable def etaOf (I : Inst) (ε B : ℝ) : ℝ := ε * B / (100 * I.n)

/-- `K = ⌈4B/η⌉ = ⌈400 n/ε⌉`, (21). -/
noncomputable def gridK (I : Inst) (ε : ℝ) : ℕ := ⌈(400 * (I.n : ℝ)) / ε⌉₊

/-- `k` is the first grid point `1 ≤ k ≤ K` whose solution serves at least `q` clients. -/
def FirstCross {J : Inst} (seq : ℕ → Sol J) (K k : ℕ) : Prop :=
  1 ≤ k ∧ k ≤ K ∧ J.q ≤ (served (seq k)).card ∧
    ∀ k', 1 ≤ k' → k' < k → (served (seq k')).card < J.q

/-- **The choices of one execution** of the Appendix B procedure: for every branch `i₀`, scale
index `j` and grid point `k` a solution `run i₀ j k` and its number of accepted changes
`steps i₀ j k`; the merged solution `merged i₀ j` of each scale; the zero-cost solution
`zero i₀` of each branch. -/
structure Exec (I : Inst) where
  /-- the grid solutions `S_k` -/
  run : (i0 : Fin I.m) → ℕ → ℕ → Sol (branchInst I i0)
  /-- the number of accepted changes of each run -/
  steps : Fin I.m → ℕ → ℕ → ℕ
  /-- the merged solution of each scale -/
  merged : (i0 : Fin I.m) → ℕ → Sol (branchInst I i0)
  /-- the zero-cost solution of each branch -/
  zero : (i0 : Fin I.m) → Sol (branchInst I i0)

namespace Exec

variable {I : Inst}

/-- **The execution follows Appendix B** (p.14). In every feasible branch `i₀` (instance
`J = branchInst I i₀`, `M = f_{i₀}`): if `J` has a zero-cost solution, `zero i₀` is one; otherwise,
for every tried scale `B = ℓ 2^j`, with `τ, η, K` of (21), `S₀` is the empty solution, each
`S_k` (`1 ≤ k ≤ K`) is the output of a run of `Local(kη, τ; S_{k−1})`, and at the first crossing
`k` the merged solution satisfies Lemma 2.2's conclusion for `S⁻ = S_{k−1}`, `S⁺ = S_k`, `M`. -/
def Valid (X : Exec I) (ε : ℝ) : Prop :=
  ∀ i0 : Fin I.m, (branchInst I i0).Feasible →
    (ZeroCost (branchInst I i0) →
      (X.zero i0).CapFeasible ∧ I.q ≤ (served (X.zero i0)).card ∧ cost (X.zero i0) = 0) ∧
    (¬ ZeroCost (branchInst I i0) → ∀ j, ScaleOK (branchInst I i0) j →
      X.run i0 j 0 = Sol.empty _ ∧
      (∀ k, 1 ≤ k → k ≤ gridK I ε →
        LocalRun ((k : ℝ) * etaOf I ε (scaleB (branchInst I i0) j))
          (tauOf I ε (scaleB (branchInst I i0) j))
          (X.run i0 j (k - 1)) (X.run i0 j k) (X.steps i0 j k)) ∧
      (∀ k, FirstCross (X.run i0 j) (gridK I ε) k →
        MergeSpec (X.run i0 j (k - 1)) (X.run i0 j k) (I.f i0) (X.merged i0 j)))

/-- **The recorded candidates** of the execution, as solutions of the original instance (original
opening costs restored): the zero-cost solution of each feasible zero-cost branch, and the merged
solution of each tried scale with a crossing of each other feasible branch ("Discard scales with
no crossing"). -/
def Candidate (X : Exec I) (ε : ℝ) (S : Sol I) : Prop :=
  ∃ i0 : Fin I.m, (branchInst I i0).Feasible ∧
    ((ZeroCost (branchInst I i0) ∧ S = liftSol (X.zero i0)) ∨
     (¬ ZeroCost (branchInst I i0) ∧ ∃ j, ScaleOK (branchInst I i0) j ∧
        (∃ k, FirstCross (X.run i0 j) (gridK I ε) k) ∧ S = liftSol (X.merged i0 j)))

end Exec

/-- **The outputs of the complete quota algorithm** of Appendix B (pp.14–15) with parameter `ε`:
the empty solution if `q = 0`; otherwise a cheapest recorded candidate, under the original costs,
of some execution that follows Appendix B.

**Formalization Note.** The procedure leaves choices open (which optimal assignment, which
improving change, which merged solution); the relation admits every execution, and the merge is
any solution meeting Lemma 2.2's bound (3). Statements about `QuotaOut` hold for every
execution. -/
def QuotaOut (I : Inst) (ε : ℝ) (S : Sol I) : Prop :=
  (I.q = 0 ∧ S = Sol.empty I) ∨
  (0 < I.q ∧ ∃ X : Exec I, X.Valid ε ∧ X.Candidate ε S ∧ ∀ S', X.Candidate ε S' → cost S ≤ cost S')

end CFLOutliers


