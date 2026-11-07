-- Prove2me | Definitions.Def_LipStableCA_weightedVCG
-- name    : LipStableCA_weightedVCG
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T20:48:47.353194+00:00
-- url     : https://prove2.me/theorems/75284f8e-9cca-46d3-b839-8fe759ab140c
-- title:
--   Mechanism 1: the randomly weighted VCG auction
-- statement:
--   Fix public desired bundles $Q_1,\dots,Q_n$ and $0<\epsilon<1$. Let $\mathcal F_Q$ be the family of sets of bidders with pairwise disjoint desired bundles, $\tau=-\frac12\log(1-\epsilon)$, and $\rho(z)=\frac{15}{16}(1-z^2)^2$ on $[-1,1]$. Draw $Z\in[-1,1]^n$ with independent entries of density $\rho$, and let $I^*$ be the first set in a fixed order maximizing $\sum_{i\in I}e^{\tau Z_i}v_i$ over $\mathcal F_Q$. A bidder $i\in I^*$ gets $Q_i$ and pays
--   $$p_i=e^{-\tau Z_i}\Bigl(\max_{I\in\mathcal F_Q:\,i\notin I}\sum_{h\in I}e^{\tau Z_h}v_h-\sum_{h\in I^*\setminus\{i\}}e^{\tau Z_h}v_h\Bigr),$$
--   and the others get $\emptyset$ and pay $0$. Reports are scalars, with $d(v,w)=\sum_i\mathrm{ld}(v_i,w_i)$.
--
--   **Formalization Note.** Mechanism 3 runs this auction on a subset of the bidders, so a participant set $J$ restricts $\mathcal F_Q$; $J=N$ is the printed mechanism. The order is a linear order on all sets of bidders, whose restriction to $\mathcal F_Q$ is the fixed order.
-- source:
--   Afshinmehr, Koutsoupias, Lipschitz Stable Combinatorial Auctions, STOC 2027 submission (manuscript sha256 c5e4c53f…), Mechanism 1, p.10; §3.1, p.9

import Definitions.Def_LipStableCA_emd
import Definitions.Def_LipStableCA_profileDist

open MeasureTheory
open scoped ENNReal

namespace LipStableCA

variable {n m : ℕ}

/-- The density `ρ(z) = (15/16)(1 − z²)²` on `[−1, 1]`, Mechanism 1, line 2, p.10, and `0` elsewhere. -/
noncomputable def weightDensity (z : ℝ) : ℝ :=
  if z ∈ Set.Icc (-1 : ℝ) 1 then 15 / 16 * (1 - z ^ 2) ^ 2 else 0

/-- The law with density `ρ`. -/
noncomputable def weightLaw : Measure ℝ :=
  volume.withDensity fun z => ENNReal.ofReal (weightDensity z)

instance : SigmaFinite weightLaw := SigmaFinite.withDensity_ofReal _

/-- The law of `Z ∈ [−1, 1]ⁿ` with independent entries of density `ρ`, Mechanism 1, line 3, p.10. -/
noncomputable def weightMeasure (n : ℕ) : Measure (Fin n → ℝ) :=
  Measure.pi fun _ => weightLaw

/-- `τ = −(1/2) log(1 − ϵ)`, Mechanism 1, line 2, p.10. -/
noncomputable def tauOf (ϵ : ℝ) : ℝ := -(1 / 2) * Real.log (1 - ϵ)

open Classical in
/-- `F_Q`, Mechanism 1, line 1, p.10, on the participant set `J`. **Formalization Note.** Mechanism 3
runs Mechanism 1 on a subset of the bidders, so the family is restricted to subsets of `J`; `J = univ` is
the printed family `{I ⊆ N | Qᵢ ∩ Qᵢ′ = ∅ for all distinct i, i′ ∈ I}`. -/
noncomputable def feasibleFamily (Q : Fin n → Finset (Fin m)) (J : Finset (Fin n)) :
    Finset (Finset (Fin n)) :=
  J.powerset.filter fun I => ∀ i ∈ I, ∀ i' ∈ I, i ≠ i' → Disjoint (Q i) (Q i')

theorem empty_mem_feasibleFamily (Q : Fin n → Finset (Fin m)) (J : Finset (Fin n)) :
    ∅ ∈ feasibleFamily Q J := by
  simp [feasibleFamily]

/-- The weighted value `Σ_{h∈I} e^{τ z_h} v_h` of a set of bidders, Mechanism 1, line 4, p.10. -/
noncomputable def weightedValue (τ : ℝ) (z v : Fin n → ℝ) (I : Finset (Fin n)) : ℝ :=
  ∑ h ∈ I, Real.exp (τ * z h) * v h

/-- `I*`, Mechanism 1, line 4, p.10: the first set of `F_Q` in the fixed order that maximizes the weighted
value. **Formalization Note.** `ord` is a linear order on all sets of bidders. Its restriction to `F_Q` is
the fixed order, and every order on `F_Q` arises this way. -/
noncomputable def winnerSet (ord : LinearOrder (Finset (Fin n))) (Q : Fin n → Finset (Fin m))
    (J : Finset (Fin n)) (τ : ℝ) (z v : Fin n → ℝ) : Finset (Fin n) :=
  firstMaximizerOn ord (feasibleFamily Q J) ⟨∅, empty_mem_feasibleFamily Q J⟩ (weightedValue τ z v)

open Classical in
/-- The critical bid, Mechanism 1, line 8, p.10:
`pᵢ = e^{−τZᵢ}(max_{I∈F_Q: i∉I} Σ_{h∈I} e^{τZₕ}vₕ − Σ_{h∈I*∖{i}} e^{τZₕ}vₕ)` for `i ∈ I*`, and `pᵢ = 0`
otherwise. -/
noncomputable def scalarPay (ord : LinearOrder (Finset (Fin n))) (Q : Fin n → Finset (Fin m))
    (J : Finset (Fin n)) (τ : ℝ) (z v : Fin n → ℝ) (i : Fin n) : ℝ :=
  if i ∈ winnerSet ord Q J τ z v then
    (Real.exp (τ * z i))⁻¹ *
      (((feasibleFamily Q J).filter fun I => i ∉ I).sup'
          ⟨∅, Finset.mem_filter.mpr ⟨empty_mem_feasibleFamily Q J, by simp⟩⟩
          (weightedValue τ z v) -
        weightedValue τ z v ((winnerSet ord Q J τ z v).erase i))
  else 0

open Classical in
/-- **Mechanism 1 (Randomly weighted VCG auction)**, p.10: `Sᵢ = Qᵢ` for `i ∈ I*` and `Sᵢ = ∅` otherwise.
**Formalization Note.** Reports are the scalars `v`; bidders outside `J` are not in the run and get `∅`. The
tuple is pairwise disjoint because `I* ∈ F_Q`. -/
noncomputable def scalarAlloc (ord : LinearOrder (Finset (Fin n))) (Q : Fin n → Finset (Fin m))
    (J : Finset (Fin n)) (τ : ℝ) (z v : Fin n → ℝ) : Alloc n m :=
  toAlloc fun i => if i ∈ winnerSet ord Q J τ z v then Q i else ∅

/-- The allocation law `P_v` of Mechanism 1 at the scalar report `v`. -/
noncomputable def scalarLaw (ord : LinearOrder (Finset (Fin n))) (Q : Fin n → Finset (Fin m))
    (J : Finset (Fin n)) (ϵ : ℝ) (v : Fin n → ℝ) (T : Alloc n m) : ℝ :=
  (weightMeasure n).real {z | scalarAlloc ord Q J (tauOf ϵ) z v = T}

/-- The distance `d(v, w) = Σᵢ ld(vᵢ, wᵢ)` on scalar reports, §3.1, p.9, summed over the participants
`J`. -/
noncomputable def scalarDist (J : Finset (Fin n)) (v w : Fin n → ℝ) : ℝ≥0∞ :=
  ∑ i ∈ J, ld (v i) (w i)

open Classical in
/-- The truthfulness inequality of Definition 2.1, p.7, for known single-minded bidders at fixed weights
`z`: a bidder's true value is a scalar, and her utility is that value if she is a winner, minus her payment.
Reports are nonnegative scalars. -/
def ScalarTruthful (W : (Fin n → ℝ) → Finset (Fin n)) (p : (Fin n → ℝ) → Fin n → ℝ) : Prop :=
  ∀ (i : Fin n) (v : Fin n → ℝ) (x : ℝ), (∀ h, 0 ≤ v h) → 0 ≤ x →
    (if i ∈ W (Function.update v i x) then v i else 0) - p (Function.update v i x) i ≤
      (if i ∈ W v then v i else 0) - p v i

end LipStableCA


