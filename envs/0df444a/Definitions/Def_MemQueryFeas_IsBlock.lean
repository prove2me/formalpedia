-- Prove2me | Definitions.Def_MemQueryFeas_IsBlock
-- name    : MemQueryFeas_IsBlock
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:35:25.6491+00:00
-- url     : https://prove2.me/theorems/487a4c2a-04aa-4fd5-9be6-dd1e8e4b6d2f
-- title:
--   The property $\Delta$-$\mathrm{Block}_k(q\mid C)$ (Definition 2)
-- statement:
--   Let $R$ be a random region of $\mathbb R^d$ and $C$ a random variable. $R$ has the **blocking property $\Delta$-$\mathrm{Block}_k(q\mid C)$** if for every $C$-measurable $k$-dimensional subspace $W$,
--   $$
--   \Pr\big(R\cap(W+\Delta B)=\emptyset\big)\ge q ,
--   $$
--   where $W+\Delta B=\{x:\exists w\in W,\ \|x-w\|\le\Delta\}$.
--
--   **Formalization Note** $C$-measurable subspaces are $W=f(C)$ for measurable maps $f$ into $\mathrm{Gr}(k,d)$. The printed "$\mathrm{Gr}(d,k)$" is read as $\mathrm{Gr}(k,d)$.
-- source:
--   Yu–Blanchard, Exponential memory/query-complexity tradeoffs in high-accuracy feasibility problems, preprint (Nov. 3, 2026), Definition 2, p.10 (PDF p.11)

import Mathlib
import Definitions.Def_MemQueryFeas_IsOrthProj

open MeasureTheory

namespace MemQueryFeas

/-- **The property `∆-Block_k(q | C)` (Definition 2).** Yu–Blanchard, *Exponential memory/query-complexity tradeoffs in high-accuracy feasibility problems*, preprint (Nov. 3, 2026), Definition 2, p.10 (PDF p.11).

`IsBlock μ k Δ q R C`: for every measurable `f` from the range space of `C` to rank-`k` orthogonal
projections (so `W = range f(C)` is a `C`-measurable `k`-dimensional subspace), the event that `R`
misses the closed `Δ`-neighbourhood `W + ΔB = {x | ∃ w ∈ W, ‖x − w‖ ≤ Δ}` has probability at least `q`.

The page reads:
"Fix `∆ > 0` and `q ∈ [0, 1]`. Let `R ⊂ ℝ^d` be a random region and let `C` be any potentially
correlated random variable. We say that `R` has the blocking property `∆-Block_k(q|C)` if for any
`C`-measurable subspace `W ∈ Gr(d, k)`, `P(R ∩ (W + ∆B) = ∅) ≥ q`."

**Formalization Note.** "`Gr(d, k)`" is read as `Gr(k, d)` (`k`-dimensional subspaces; the index
`k` of `Block_k`). `C`-measurable random subspaces are exactly `f ∘ C` with `f` measurable
(Doob–Dynkin; the projections form a standard Borel space). The probability is the measure of the
event (outer measure if it were not measurable). -/
def IsBlock {Ω γ : Type*} [MeasurableSpace Ω] [MeasurableSpace γ] {d : ℕ} (μ : Measure Ω)
    (k : ℕ) (Δ q : ℝ) (R : Ω → Set (Vec d)) (C : Ω → γ) : Prop :=
  ∀ f : γ → Op d, Measurable f → (∀ z, IsOrthProj k (f z)) →
    ENNReal.ofReal q ≤ μ {ω | R ω ∩
      {x | ∃ w ∈ LinearMap.range (f (C ω) : Vec d →ₗ[ℝ] Vec d), ‖x - w‖ ≤ Δ} = ∅}

end MemQueryFeas


