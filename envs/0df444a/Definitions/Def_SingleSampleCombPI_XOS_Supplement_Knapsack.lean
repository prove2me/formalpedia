-- Prove2me | Definitions.Def_SingleSampleCombPI_XOS_Supplement_Knapsack
-- name    : SingleSampleCombPI_XOS_Supplement_Knapsack
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T17:37:52.172207+00:00
-- url     : https://prove2.me/theorems/f43a6a9a-b0ee-4f32-a45f-0e254dec34b3
-- title:
--   Fractional knapsack quantiles, conditional GoG experiment and Algorithm 8
-- statement:
--   An item is a density–demand pair $(q,x)$ with $q\ge0$ and $x\in[0,1]$. The density quantile scans the density-sorted profile using a uniform $u\in[0,1]$, and the capacity-one tail is
--   $$K_r(t)=\min\{1,\sum_i x(r_i)\mathbf1[q(r_i)>t]\}.$$
--   The analysis experiment averages fair buyer-by-buyer sample/real swaps and two independent uniform quantiles conditional on those swaps. FilledDistinct records exactly the filled-profile and pairwise distinct-density assumptions of §5.2. The medium mass is $\sum_i x(r_i)\mathbf1[\tau_s<q(r_i)\le t]$.
--
--   Algorithm 8 sorts the samples plus a unit-weight zero-density dummy, draws its random quantile, and scans real arrivals. It accepts the smaller of the remaining capacity and the arriving demand if its key exceeds the sampled key. Keys are density followed by symmetric random distinct ranks of all sample/real slots, including the dummy slots. Rewards use the original densities. The real dummy need not be executed because it has zero reward. Remaining capacity is computed from the revealed qualifying demands only. The explicit quadratic sorting/scan budget bounds the operations of this implementation; it is independent of rewards, weights and the quantile. The null endpoint of the uniform interval and exhausted quantile scans use total sentinels.
-- source:
--   Shuchi Chawla, Trung Dang, STOC 2027 submission #30 (October 2026), Algorithm 8 and §5.2, printed pp. 27–30 / PDF pp. 29–32.

import Mathlib
import Definitions.Def_SingleSampleCombPI_XOS_Algorithms

open scoped ENNReal

namespace SingleSampleCombPI.XOS.Supplement

/-- The uniform quantile, independent of the fair GoG orientations. -/
noncomputable def uniformUnit : RandomSource ℝ where
  space := inferInstance
  law := MeasureTheory.volume.restrict (Set.Icc 0 1)
  isProbability := ⟨by simp⟩

/-- Integrating a bounded step function of the uniform quantile. -/
noncomputable def uavg (f : ℝ → ℝ) : ℝ :=
  ∫ u in Set.Icc (0 : ℝ) 1, f u

/-- Find the record occupying quantile u in a density-sorted list. Zero weights
are skipped. The value at the null endpoint u=1 is immaterial. -/
noncomputable def quantileScan : List Item → ℝ → ℝ
  | [], _ => 0
  | a :: L, u => if u < a.2 then a.1 else quantileScan L (u - a.2)

noncomputable def densityQuantile {n : ℕ} (r : Fin n → Item) (u : ℝ) : ℝ := by
  classical
  exact quantileScan (((List.finRange n).map r).mergeSort (fun a b => decide (b.1 ≤ a.1))) u

/-- The prophet's density tail, including the capacity truncation. -/
noncomputable def knapTail {n : ℕ} (r : Fin n → Item) (t : ℝ) : ℝ :=
  min 1 (∑ i, if t < (r i).1 then (r i).2 else 0)

/-- The distinct-density, filled experiment in the standing assumptions of §5.2.
No independent-draw substitute: every buyer's two records are swapped fairly. -/
def FilledDistinct {n : ℕ} (V : Fin n → Fin 2 → Item) : Prop :=
  (∀ i t, ItemValid .divisible (V i t)) ∧
  Function.Injective (fun p : Fin n × Fin 2 => (V p.1 p.2).1) ∧
  ∀ c : Fin n → Bool, 1 ≤ ∑ i, (gogPair (V i) (c i)).1.2

/-- Conditional on orientations, sample and real quantiles are independent.
Their unconditional laws are generally dependent. -/
noncomputable def quantileExp {n : ℕ} (V : Fin n → Fin 2 → Item)
    (f : (Fin n → Item) → (Fin n → Item) → ℝ → ℝ → ℝ) : ℝ :=
  avgR (fun c : Fin n → Bool =>
    let s := fun i => (gogPair (V i) (c i)).1
    let r := fun i => (gogPair (V i) (c i)).2
    uavg (fun us => uavg (fun ur => f s r (densityQuantile s us) (densityQuantile r ur))))

noncomputable def mediumMass {n : ℕ} (r : Fin n → Item) (τ t : ℝ) : ℝ :=
  ∑ i, if τ < (r i).1 ∧ (r i).1 ≤ t then (r i).2 else 0

/-- Keys include symmetric random ranks, including the dummy slots. -/
abbrev KKey := WithBot (Lex (ℝ × ℕ))

noncomputable def keyQuantileScan : List (KKey × ℝ) → ℝ → KKey
  | [], _ => ⊥
  | a :: L, u => if u < a.2 then a.1 else keyQuantileScan L (u - a.2)

/-- Sort the samples and a zero-density unit-weight dummy, then take a uniform
quantile. Dummies fill unused capacity; rewards use the original densities. -/
noncomputable def alg8Threshold {n : ℕ} (rank : Ranks (n+1)) (s : Fin n → Item)
    (u : ℝ) : KKey := by
  classical
  let L := ((List.finRange n).map fun i =>
    (key (s i) (rank (Sum.inl i.castSucc)), (s i).2)) ++
    [(key (0,1) (rank (Sum.inl (Fin.last n))), 1)]
  exact keyQuantileScan (L.mergeSort (fun a b => decide (b.1 ≤ a.1))) u

/-- Algorithm 8. The residual before the current buyer depends only on the
qualifying earlier demands. The strict comparison is on (density, rank). -/
noncomputable def alg8 (n : ℕ) : KSPI .divisible n 1 where
  Ω := Ranks (n+1) × ℝ
  seed := (RandomSource.ofPMF (PMF.uniformOfFintype (Ranks (n+1)))).prod uniformUnit
  act := fun ω s hist i it => by
    classical
    let τ := alg8Threshold ω.1 (s 0) ω.2
    let mass := (hist.map fun e =>
      if τ < key e.2 (ω.1 (Sum.inr e.1.castSucc)) then e.2.2 else 0).sum
    exact if τ < key it (ω.1 (Sum.inr i.castSucc)) then
      min (max 0 (1 - mass)) it.2 else 0
  seedCost := 2*(n+1)+1
  actCost := fun _ _ hist _ _ => 20*(n+1)^2 + 10*(hist.length+1)

end SingleSampleCombPI.XOS.Supplement


