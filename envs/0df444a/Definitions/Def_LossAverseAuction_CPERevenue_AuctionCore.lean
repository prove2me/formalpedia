-- Prove2me | Definitions.Def_LossAverseAuction_CPERevenue_AuctionCore
-- name    : LossAverseAuction_CPERevenue_AuctionCore
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T12:34:07.885608+00:00
-- url     : https://prove2.me/theorems/34fab30a-1d3f-4160-9e47-69f8529b67a3
-- title:
--   §2.1 and §3.1 — independent-signal auction with interdependent values
-- statement:
--   There are $N=m+2\ge2$ bidders with independent signals in $[\underline t,\overline t]$, positive density $f$, and cumulative distribution $F$. A bidder with own signal $t$ and opponents’ signals $s$ has value $v(t,s)$. The highest opposing signal has distribution and density
--
--   $$F_1(t)=F(t)^{m+1},\qquad f_1(t)=(m+1)F(t)^mf(t).$$
--
--   The data and standing conditions express the paper’s signal support, density, value monotonicity, smoothness, and opponent symmetry assumptions.
--
--   **Formalization Note** Measurability of the value map is explicit so its outcome lotteries are valid.
-- source:
--   Balzer & Rosato, Expectations-Based Loss Aversion in Auctions with Interdependent Values, Management Science (Articles in Advance, 2020; doi:10.1287/mnsc.2019.3563), §2.1, p. 4 (PDF 5); §3.1, p. 7 (PDF 8)

import Mathlib

namespace LossAverseAuction.CPERevenue

open MeasureTheory

/-- An independent-signal, symmetric interdependent-value auction with m+2 bidders. -/
structure AuctionCore (m : ℕ) where
  tl : ℝ
  th : ℝ
  f : ℝ → ℝ
  v : ℝ → (Fin (m + 1) → ℝ) → ℝ

noncomputable def AuctionCore.F {m : ℕ} (A : AuctionCore m) (t : ℝ) : ℝ :=
  ∫ x in A.tl..t, A.f x

noncomputable def AuctionCore.F1 {m : ℕ} (A : AuctionCore m) (t : ℝ) : ℝ :=
  A.F t ^ (m + 1)

noncomputable def AuctionCore.f1 {m : ℕ} (A : AuctionCore m) (t : ℝ) : ℝ :=
  (m + 1 : ℝ) * A.F t ^ m * A.f t

/-- Section 2.1's signal, regularity, monotonicity, and opponent-symmetry conditions. -/
def AuctionCore.Standing {m : ℕ} (A : AuctionCore m) : Prop :=
  0 ≤ A.tl ∧ A.tl < A.th ∧
  ContinuousOn A.f (Set.Icc A.tl A.th) ∧
  (∀ x ∈ Set.Icc A.tl A.th, 0 < A.f x) ∧
  (∫ x in A.tl..A.th, A.f x) = 1 ∧
  Measurable (fun p : ℝ × (Fin (m + 1) → ℝ) => A.v p.1 p.2) ∧
  (∀ t s, 0 ≤ t → (∀ j, 0 ≤ s j) → 0 ≤ A.v t s) ∧
  MonotoneOn (fun p : ℝ × (Fin (m + 1) → ℝ) => A.v p.1 p.2)
    (Set.Ici 0 ×ˢ {s | ∀ j, 0 ≤ s j}) ∧
  (∀ s, (∀ j, 0 ≤ s j) → StrictMonoOn (fun t => A.v t s) (Set.Ici 0)) ∧
  ContDiffOn ℝ 2 (fun p : ℝ × (Fin (m + 1) → ℝ) => A.v p.1 p.2)
    (Set.Ici 0 ×ˢ {s | ∀ j, 0 ≤ s j}) ∧
  (∀ (σ : Equiv.Perm (Fin (m + 1))) t s, A.v t (s ∘ σ) = A.v t s)

noncomputable def AuctionCore.signalLaw {m : ℕ} (A : AuctionCore m) : Measure ℝ :=
  (volume.restrict (Set.Icc A.tl A.th)).withDensity (fun x => ENNReal.ofReal (A.f x))

noncomputable def AuctionCore.oppLaw {m : ℕ} (A : AuctionCore m) :
    Measure (Fin (m + 1) → ℝ) :=
  Measure.pi fun _ => A.signalLaw

noncomputable def AuctionCore.allLaw {m : ℕ} (A : AuctionCore m) :
    Measure (Fin (m + 2) → ℝ) :=
  Measure.pi fun _ => A.signalLaw

end LossAverseAuction.CPERevenue


