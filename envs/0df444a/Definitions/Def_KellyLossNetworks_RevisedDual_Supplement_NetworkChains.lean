-- Prove2me | Definitions.Def_KellyLossNetworks_RevisedDual_Supplement_NetworkChains
-- name    : KellyLossNetworks_RevisedDual_Supplement_NetworkChains
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T02:56:48.065358+00:00
-- url     : https://prove2.me/theorems/dda94de9-5a6c-4f78-9577-bc5bd50c131c
-- title:
--   Genuine route-count Markov chains and empirical occupancy path laws
-- statement:
--   The star network has $J$ links of capacity $C$ and all $w$-subsets as routes. Each route has offered rate $\lambda/\binom{J-1}{w-1}$. The exchangeable alternative network uses singleton and two-link routes. Each link receives independent rate-$\nu$ traffic; an arrival blocked on its first-choice link examines $v$ uniformly sampled disjoint pairs of other links and uses the first pair whose occupancies are both below $C-s$.
--   $$X_{Jn}(t)=J^{-1}\#\{j:\text{link }j\text{ has }n\text{ occupied circuits at }t\}.$$
--   The state records the number of calls on each whole route. Arrivals increment one route count; a departure decrements one whole route count at a rate equal to that count. Thus circuits of a two-link call are released together. The generator, the published Markov-chain law and the published càdlàg space specify the actual empirical path laws. Initial route-count distributions are arbitrary feasible distributions. The case $s=0,v=1$ is the exchangeable network of Theorem 4.22.
-- source:
--   Kelly, Loss networks, Ann. Appl. Probab. 1(3):319–378 (1991), DOI 10.1214/aoap/1177005872, pp.343–344,349–350,352–353, §§4.1,4.3–4.4

import Definitions.Def_KellyLossNetworks_RevisedDual_Supplement_PathLimits

open scoped NNReal ENNReal

open MeasureTheory
open scoped Classical

namespace KellyLossNetworks.RevisedDual.Supplement

/-- Allowed routes for the star (all w-subsets), or the exchangeable model (singletons and
pairs). Kelly (1991), §§4.1,4.3, pp.343,349–350. All routes use one circuit per link. -/
def starRoutes (J w : ℕ) : Finset (Finset (Fin J)) :=
  Finset.univ.filter (fun r => r.card = w ∧ r.Nonempty)

def alternativeRoutes (J : ℕ) : Finset (Finset (Fin J)) :=
  Finset.univ.filter (fun r => r.card = 1 ∨ r.card = 2)

/-- Full route-count state, retaining the pairing information needed for simultaneous
release. Kelly (1991), p.343 and pp.349–350. Invalid routes have count zero; every link
has at most C occupied circuits. Counts are bounded by C because routes are nonempty. -/
def NetworkState (J C : ℕ) (routes : Finset (Finset (Fin J))) :=
  {n : Finset (Fin J) → Fin (C+1) //
    (∀ r, r ∉ routes → (n r).val = 0) ∧
    ∀ j, (∑ r, if j ∈ r then (n r).val else 0) ≤ C}

noncomputable instance (J C : ℕ) (rs : Finset (Finset (Fin J))) :
    Fintype (NetworkState J C rs) := by
  classical
  unfold NetworkState
  infer_instance
noncomputable instance (J C : ℕ) (rs : Finset (Finset (Fin J))) :
    DecidableEq (NetworkState J C rs) := Classical.decEq _
instance (J C : ℕ) (rs : Finset (Finset (Fin J))) :
    TopologicalSpace (NetworkState J C rs) := ⊥
instance (J C : ℕ) (rs : Finset (Finset (Fin J))) :
    MeasurableSpace (NetworkState J C rs) := ⊤

/-- The number of circuits occupied on link j. -/
def linkOccupancy {J C : ℕ} {rs : Finset (Finset (Fin J))}
    (a : NetworkState J C rs) (j : Fin J) : ℕ :=
  ∑ r, if j ∈ r then (a.1 r).val else 0

/-- Empirical occupancy fractions Q_Jn/J. At J=0 set them to zero; the limits use only
J large enough to contain the fixed route/trial sizes. Kelly (1991), p.343. -/
noncomputable def empirical {J C : ℕ} {rs : Finset (Finset (Fin J))}
    (a : NetworkState J C rs) : Fin (C+1) → ℝ :=
  fun n => ((Finset.univ.filter (fun j => linkOccupancy a j = n.val)).card : ℝ) / J

/-- A generator from route birth rates and exponential unit-mean holding periods. One
death removes one entire call, simultaneously releasing every link on its route.
Kelly (1991), §4 standing assumptions, pp.343–344,350,352. -/
noncomputable def networkGenerator {J C : ℕ} {rs : Finset (Finset (Fin J))}
    (birth : NetworkState J C rs → Finset (Fin J) → ℝ) :
    Matrix (NetworkState J C rs) (NetworkState J C rs) ℝ :=
  let q := fun a b : NetworkState J C rs =>
    ∑ r ∈ rs, (
      (if (∀ u, (b.1 u).val = (a.1 u).val + if u = r then 1 else 0)
        then birth a r else 0) +
      (if 0 < (a.1 r).val ∧ (∀ u, (b.1 u).val =
        (a.1 u).val - if u = r then 1 else 0) then ((a.1 r).val : ℝ) else 0))
  fun a b => if a = b then -(∑ c, if c = a then 0 else q a c) else q a b

/-- Offered rate per w-subset, with fixed per-link load lam. Kelly (1991), p.343. -/
noncomputable def starArrival (J C w : ℕ) (lam : ℝ) :
    NetworkState J C (starRoutes J w) → Finset (Fin J) → ℝ :=
  fun _ _ => lam / (Nat.choose (J-1) (w-1) : ℝ)

/-- Ordered v disjoint pairs from the other J−1 links, sampled uniformly without
replacement, as specified in §4.4, p.352. -/
def Trials (J v : ℕ) (j : Fin J) :=
  {f : Fin v × Fin 2 → Fin J // Function.Injective f ∧ ∀ i, f i ≠ j}
noncomputable instance (J v : ℕ) (j : Fin J) : Fintype (Trials J v j) := by
  classical
  unfold Trials
  infer_instance

/-- The route of trial i. -/
def trialPair {J v : ℕ} {j : Fin J} (f : Trials J v j) (i : Fin v) : Finset (Fin J) :=
  {f.1 (i, 0), f.1 (i, 1)}

/-- A trial succeeds when both links have fewer than C−s busy circuits. -/
def TrialSucceeds {J C v : ℕ} {j : Fin J} {rs : Finset (Finset (Fin J))}
    (s : ℕ) (a : NetworkState J C rs) (f : Trials J v j) (i : Fin v) : Prop :=
  ∀ k ∈ trialPair f i, linkOccupancy a k < C-s

/-- Actual overflow birth rate, not a mean-field approximation. Direct arrivals have
priority. A blocked arrival examines its v disjoint trial pairs and is carried by the first
successful pair. For 4.22 use s=0,v=1. Kelly (1991), pp.349–350,352.
**Formalization Note.** The denominator is positive once J≥2v+1, the source's domain for
sampling all pairs. Definitions at smaller J have no effect on the limit. -/
noncomputable def alternativeArrival (J C s v : ℕ) (nu : ℝ)
    (a : NetworkState J C (alternativeRoutes J)) (r : Finset (Fin J)) : ℝ :=
  (if r.card = 1 then nu else 0) +
  ∑ j : Fin J, if linkOccupancy a j = C then
    nu * ((Finset.univ.filter (fun f : Trials J v j =>
      ∃ i : Fin v, trialPair f i = r ∧ TrialSucceeds s a f i ∧
        ∀ h : Fin v, h < i → ¬ TrialSucceeds s a f h)).card : ℝ) /
      (Fintype.card (Trials J v j) : ℝ) else 0

/-- The full empirical path law, as a push-forward of the càdlàg route-count chain.
Kelly (1991), Theorems 4.1,4.22,4.30. -/
noncomputable def empiricalLaw {J C : ℕ} {rs : Finset (Finset (Fin J))}
    (P : Measure (RBMSensitivity.Cadlag (NetworkState J C rs))) :
    Measure (ℝ≥0 → (Fin (C+1) → ℝ)) :=
  P.map (fun x t => empirical (x.1 t))

end KellyLossNetworks.RevisedDual.Supplement


