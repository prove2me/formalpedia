-- Prove2me | Definitions.Def_MaoLowDegree_Counterexample_construction
-- name    : MaoLowDegree_Counterexample_construction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:02:09.1792+00:00
-- url     : https://prove2.me/theorems/330fd924-594b-4172-b015-76e057ca3bd6
-- title:
--   The alternating-form planted law and its finite initial segment
-- statement:
--   For $K$ binary coordinates, independent fair upper-triangular entries $c_{ab}$, $a<b$, specify the alternating bilinear form
--   $$B(u,v)=\sum_{a<b}c_{ab}(u_av_b+u_bv_a).$$
--
--   Given evaluation data, sample these entries and an independent uniform vertex permutation $\pi$, and set $X_{\pi(i),\pi(j)}=B(v_i,v_j)$. This pushforward is the planted law. A construction fixes a threshold $n_0$ and one set of evaluation data for every $n\ge n_0$; below it, $P_n=Q_n$.
--
--   Validity means exactly the standing setup: $n_0\ge2$, $L\ge2$ on the eventual range, $W\le\mathrm{RM}(m,r)$, the low-bias condition, and $L$-wise independent evaluation vectors. These are the choices made on pp.8–10, not conclusions about marginal uniformity, low-degree advantage, rank, or computation. The goal theorem assumes none of them; their existence is part of its proof obligations.
-- source:
--   Songtao Mao, STOC 2027 submission #509 (October 2026), §2.1–2.2, pp.8–10

import Definitions.Def_MaoLowDegree_Counterexample_reedMuller

open Classical
noncomputable section
set_option autoImplicit false

namespace MaoLowDegree.Counterexample

/-- The independent upper-triangular bits of an alternating binary form. -/
abbrev FormBits (K : ℕ) := Edge K → F₂

/-- The alternating bilinear form with these upper-triangular entries. -/
def alternatingForm {K : ℕ} (c : FormBits K) (u v : Vec K) : F₂ :=
  ∑ e : Edge K, c e * (u e.val.1 * v e.val.2 + u e.val.2 * v e.val.1)

def formGraph {m K n : ℕ} (d : CodeData m K n) (c : FormBits K) : Graph n :=
  fun e => decide (alternatingForm c (evaluations d e.val.1) (evaluations d e.val.2) = 1)

/-- Independent uniform alternating form and uniform vertex permutation. -/
def plantedLaw {m K n : ℕ} (d : CodeData m K n) : GraphLaw n :=
  (PMF.uniformOfFintype (FormBits K)).bind fun c =>
    (PMF.uniformOfFintype (Equiv.Perm (Fin n))).map fun π => relabel π (formGraph d c)

/-- One fixed choice of the data for each n past a finite threshold. -/
structure Construction (r : ℕ) (b κ : ℝ) where
  n₀ : ℕ
  data : ∀ n : ℕ, n₀ ≤ n → CodeData (ambientDimension b n) (codeDimension r b κ n) n

/-- This records precisely the choices fixed on pp.8–10, never the desired graph-law conclusions. -/
def ValidConstruction {r : ℕ} {b κ : ℝ} (β₁ : ℝ) (C : Construction r b κ) : Prop :=
  2 ≤ C.n₀ ∧ ∀ n (h : C.n₀ ≤ n),
    2 ≤ independenceLength r b κ n ∧
    (C.data n h).W ≤ RM (ambientDimension b n) r ∧
    LowBias (C.data n h).W (eta r β₁ b n) ∧
    WiseIndependent (evaluations (C.data n h)) (independenceLength r b κ n)

def constructedFamily {r : ℕ} {b κ : ℝ} (C : Construction r b κ) : GraphFamily :=
  fun n => if h : C.n₀ ≤ n then plantedLaw (C.data n h) else nullLaw n

end MaoLowDegree.Counterexample


