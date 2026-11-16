-- Prove2me | Definitions.Def_SingleSampleCombPI_XOS_Supplement_Multi
-- name    : SingleSampleCombPI_XOS_Supplement_Multi
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T17:40:25.410862+00:00
-- url     : https://prove2.me/theorems/17db4f50-6ac6-407a-8573-97503fcdbbc5
-- title:
--   Compressed multi-unit XOS extension and vertex Algorithms 3/5/8
-- statement:
--   There are $\ell\ge1$ units per item type, and each buyer may receive at most one unit of a type. MultiFeasible imposes binary buyer allocations and per-type supply $\ell$. Its benchmark optimizes welfare over every such allocation.
--
--   The divisible extension is a maximum of capped-additive clauses $\sum_{j\in S}q_{v,j}(1_S)\min\{\ell x_j,1\}$, using all original supporting vectors, zeroed outside their bundles. This is a finite XOS representation of the original valuation on vertices. At $1_S/\ell$, the map uses $\ell q_v(S)$ on $S$; off vertices it uses a tight clause and the source ratio convention, which is zero at a zero coordinate.
--
--   The vertex implementation of Algorithm 5 sorts the earlier nonzero-demand records per type and reads the $\ell$-th retained density, defaulting to zero for unused supply. It stores no expanded list of $\ell$ dummy blocks. One original demand query at these densities divided by $\ell$ selects a bundle, and one supporting-price query freezes the prices at its scaled indicator. Algorithm 3 with this Algorithm 5 and Algorithm 8 returns a divisible allocation, multiplied by $\ell$ to obtain the multi-unit output. Operation and query counters account for sorting only the recorded history, so the polynomial bound is uniform in $\ell$ in the source unit-cost model.
-- source:
--   Shuchi Chawla, Trung Dang, STOC 2027 submission #30 (October 2026), Theorem 6.3, printed p. 33 / PDF p. 35; Appendix F, printed pp. 43–44 / PDF pp. 45–46.

import Mathlib
import Definitions.Def_SingleSampleCombPI_XOS_Supplement_Oracle

open scoped ENNReal

namespace SingleSampleCombPI.XOS.Supplement

/-- The canonical finite XOS representation by all given supporting vectors,
zeroed outside their bundles. It agrees with v on every bundle. -/
noncomputable def extendedClause {m : ℕ} (b : Buyer m) (ℓ : ℕ)
    (S : Finset (Fin m)) (x : Vec m) : ℝ :=
  ∑ j ∈ S, b.q (ind S) j * min ((ℓ:ℝ)*x j) 1

noncomputable def extensionValue {m : ℕ} (b : Buyer m) (ℓ : ℕ) (x : Vec m) : ℝ :=
  maxOrZero Finset.univ (fun S : Finset (Fin m) => extendedClause b ℓ S x)

noncomputable def tightBundle {m : ℕ} (b : Buyer m) (ℓ : ℕ) (x : Vec m) : Finset (Fin m) := by
  classical
  exact if h : ∃ S : Finset (Fin m), ∀ T, extendedClause b ℓ T x ≤ extendedClause b ℓ S x then
    Classical.choose h else ∅

/-- At source vertices use exactly the given support; elsewhere use a tight
capped clause with the source ratio min(ell*x,1)/x, zero when x=0. -/
noncomputable def extensionPrice {m : ℕ} (b : Buyer m) (ℓ : ℕ) (x : Vec m) : Vec m := by
  classical
  let U := Finset.univ.filter (fun j => x j = 1/(ℓ:ℝ))
  exact if ∀ j, x j = 0 ∨ x j = 1/(ℓ:ℝ) then
    fun j => if j ∈ U then (ℓ:ℝ)*b.q (ind U) j else 0
  else
    let S := tightBundle b ℓ x
    fun j => if j ∈ S then b.q (ind S) j * min ((ℓ:ℝ)*x j) 1 / x j else 0

/-- The extension is a proof construction. Demand queries in its vertex
implementation are passed to the original buyer with prices divided by ell. -/
noncomputable def extendBuyer {m : ℕ} (ℓ : ℕ) (b : Buyer m) : Buyer m :=
  ⟨extensionValue b ℓ, extensionPrice b ℓ, fun p => b.d (fun j => p j / (ℓ:ℝ))⟩

/-- Minimum among the ell retained unit blocks, with zero padding compressed.
Only the nonzero records are sorted; no list of length ell is constructed. -/
noncomputable def leastRetained {m : ℕ} (ℓ : ℕ) (H : FrozenHistory m) (j : Fin m) : ℝ := by
  classical
  let L := (H.filter (fun e => 0 < e.amount.1 j)).map (fun e => e.price j)
  exact ((L.mergeSort (fun a b => decide (b ≤ a)))[ℓ-1]?).getD 0

/-- Vertex implementation of Algorithm 5, Appendix F. A single original demand
query chooses the maximizing vertex, and a supporting query freezes its prices. -/
noncomputable def multiGreedy (ℓ n m : ℕ) : FDAlg .divisible n m where
  State := FrozenHistory m
  Ω := Unit
  seed := RandomSource.ofPMF (PMF.pure ())
  init := fun _ => []
  step := fun H _ b =>
    let S := b.d (fun j => leastRetained ℓ H j)
    let x : Cube m := ⟨fun j => if j ∈ S then min 1 (1/(ℓ:ℝ)) else 0, by
      intro j
      change 0 ≤ (if j ∈ S then min 1 (1/(ℓ:ℝ)) else 0) ∧
        (if j ∈ S then min 1 (1/(ℓ:ℝ)) else 0) ≤ 1
      split_ifs <;> constructor
      · positivity
      · exact min_le_left _ _
      · exact le_rfl
      · exact zero_le_one⟩
    (x, H ++ [freeze b x])
  seedCost := 0
  stepCost := fun H _ _ => (20*(m+1)*(H.length+1)^2,1,1)

/-- Multi-unit feasibility is binary buyer demand and ell units per type. -/
def MultiFeasible {n m : ℕ} (ℓ : ℕ) (x : Fin n → Vec m) : Prop :=
  (∀ i, InDom .indivisible (x i)) ∧ ∀ j, ∑ i, x i j ≤ (ℓ:ℝ)

noncomputable def multiOpt {n m : ℕ} (ℓ : ℕ) (b : Fin n → Buyer m) : ℝ :=
  sSup {z | ∃ x, MultiFeasible ℓ x ∧ z = ∑ i, (b i).v (x i)}

/-- Algorithms 3/5/8, followed by multiplication by ell. -/
noncomputable def multiOut (ℓ n m : ℕ) (H : Fin n → Bool) (π : Equiv.Perm (Fin n))
    (ωs : Fin m → (alg8 n).Ω) (ρ : Equiv.Perm (Fin n)) (s r : Fin n → Buyer m) :
    Fin n → Vec m :=
  fun i j => (ℓ:ℝ) * alg3 (multiGreedy ℓ n m) (alg8 n) H π () ωs ρ
    (fun k => extendBuyer ℓ (s k)) (fun k => extendBuyer ℓ (r k)) i j

noncomputable def multiExp {n m : ℕ} (ℓ : ℕ) (V : Fin n → Fin 2 → Buyer m)
    (ρ : Equiv.Perm (Fin n)) : ℝ≥0∞ :=
  pexpPi (alg8 n).seed (fun ωs => avg (fun c : Fin n → Bool =>
    bernExp qStar (fun H => avg (fun π : Equiv.Perm (Fin n) =>
      let s := fun i => (gogPair (V i) (c i)).1
      let r := fun i => (gogPair (V i) (c i)).2
      ENNReal.ofReal (∑ i, (r i).v (multiOut ℓ n m H π ωs ρ s r i))))))

end SingleSampleCombPI.XOS.Supplement


