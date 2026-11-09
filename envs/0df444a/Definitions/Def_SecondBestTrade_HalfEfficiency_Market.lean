-- Prove2me | Definitions.Def_SecondBestTrade_HalfEfficiency_Market
-- name    : SecondBestTrade_HalfEfficiency_Market
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:03:13.927528+00:00
-- url     : https://prove2.me/theorems/80f7dd47-cfab-4675-aa2f-5d72e22cff9e
-- title:
--   §§1.1 and 3 — Finite multidimensional market
-- statement:
--   A market has finite disjoint buyer and seller sets, a finite set $E$ of possible trades, and one endpoint of each kind for every trade. An agent's type is a nonnegative real vector indexed by its incident trades. Each prior has finite nonempty support, strictly positive support masses summing to one, and may correlate all coordinates of a single type. Types are independent across agents. A nonempty downward-closed family $\mathcal F\subseteq 2^E$ describes feasibility.
--
--   Write $\pi$ for the product mass function, $x$ for a report-dependent vector in the convex hull of feasible incidence vectors, and $v_{i(e),e}-c_{j(e),e}$ for the gain on trade $e$. The benchmarks are
--   $$H(v,c)=\max_{X\in\mathcal F}\sum_{e\in X}(v_{i(e),e}-c_{j(e),e}),\qquad \mathrm{FB}=\mathbb E_\pi H,$$
--   and $\mathrm{GFT}(x)=\mathbb E_\pi\sum_e x_e(v,c)(v_{i(e),e}-c_{j(e),e})$.
--
--   These definitions provide the common model for all results. **Formalization Note** Finite sets are labelled by `Fin`; support labels embed injectively into incident-coordinate vectors. Coordinates outside an agent's incident set are extended by zero solely for summation. Empty buyer, seller and trade sets are allowed. `maxSurplus` is a genuine maximum over the nonempty finite family.
-- source:
--   Dirk Bergemann, Yang Cai, Kangning Wang, Jinzhao Wu, Renzhe Xu, STOC 2027 submission #529 (October 2026), §§1.1 and 3, printed pp. 1–4 (PDF pp. 2–5)

import Mathlib

open scoped BigOperators NNReal
open MeasureTheory
set_option autoImplicit false
noncomputable section

namespace SecondBestTrade.HalfEfficiency

/-- The finite market of §§1.1 and 3, printed pp. 1–4 (PDF pp. 2–5).
Supports are injectively labelled nonnegative incident-trade vectors. -/
structure Market where
  nb : ℕ
  ns : ℕ
  ne : ℕ
  buyer : Fin ne → Fin nb
  seller : Fin ne → Fin ns
  nt : Fin nb ⊕ Fin ns → ℕ
  nt_pos : ∀ a, 0 < nt a
  value : ∀ a, Fin (nt a) →
    ({e : Fin ne // Sum.elim (fun i => buyer e = i) (fun j => seller e = j) a} → ℝ≥0)
  value_injective : ∀ a, Function.Injective (value a)
  mass : ∀ a, Fin (nt a) → ℝ
  mass_pos : ∀ a t, 0 < mass a t
  mass_sum : ∀ a, ∑ t, mass a t = 1
  family : Finset (Finset (Fin ne))
  family_nonempty : family.Nonempty
  downward : ∀ X ∈ family, ∀ Y, Y ⊆ X → Y ∈ family

abbrev Agent (N : Market) := Fin N.nb ⊕ Fin N.ns
abbrev Trade (N : Market) := Fin N.ne
abbrev Ty (N : Market) (a : Agent N) := Fin (N.nt a)
abbrev Profile (N : Market) := ∀ a : Agent N, Ty N a
abbrev Allocation (N : Market) := Profile N → Trade N → ℝ

def incident (N : Market) (a : Agent N) (e : Trade N) : Prop :=
  Sum.elim (fun i => N.buyer e = i) (fun j => N.seller e = j) a

noncomputable def coord (N : Market) (a : Agent N) (t : Ty N a) (e : Trade N) : ℝ := by
  classical
  exact if h : incident N a e then (N.value a t ⟨e, h⟩ : ℝ) else 0

def prior (N : Market) (v : Profile N) : ℝ := ∏ a, N.mass a (v a)
def expect (N : Market) (h : Profile N → ℝ) : ℝ := ∑ v, prior N v * h v

noncomputable def overwrite (N : Market) (v : Profile N) (a : Agent N) (t : Ty N a) :
    Profile N := by
  classical
  exact Function.update v a t

noncomputable def indicator (N : Market) (X : Finset (Trade N)) : Trade N → ℝ := by
  classical
  exact fun e => if e ∈ X then 1 else 0

noncomputable def allocationPolytope (N : Market) : Set (Trade N → ℝ) :=
  convexHull ℝ {x | ∃ X ∈ N.family, x = indicator N X}

def feasible (N : Market) (x : Allocation N) : Prop :=
  ∀ v, x v ∈ allocationPolytope N

def gains (N : Market) (v : Profile N) (e : Trade N) : ℝ :=
  coord N (.inl (N.buyer e)) (v (.inl (N.buyer e))) e -
    coord N (.inr (N.seller e)) (v (.inr (N.seller e))) e

noncomputable def maxSurplus (N : Market) (w : Trade N → ℝ) : ℝ := by
  classical
  exact N.family.sup' N.family_nonempty (fun X => ∑ e ∈ X, w e)

def GFT (N : Market) (x : Allocation N) : ℝ :=
  expect N (fun v => ∑ e, x v e * gains N v e)
def H (N : Market) (v : Profile N) : ℝ := maxSurplus N (gains N v)
def FB (N : Market) : ℝ := expect N (H N)

end SecondBestTrade.HalfEfficiency


