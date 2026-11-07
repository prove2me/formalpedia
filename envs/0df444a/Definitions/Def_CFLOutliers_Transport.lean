-- Prove2me | Definitions.Def_CFLOutliers_Transport
-- name    : CFLOutliers_Transport
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:35:17.310912+00:00
-- url     : https://prove2.me/theorems/7a22ef4b-dc33-47a5-b63c-3d85d4ea66ba
-- title:
--   Transport data, comparisons and weighted families of Lemma 4.1
-- statement:
--   **Transport data** consist of finite sets of sources $\mathcal S$ and real targets $\mathcal T$, a pseudometric $c$ on $\mathcal S\sqcup\mathcal T$, a penalty $\lambda\ge 0$, source loads $w_s$, an integral transport $y_{st}$, disposal quantities $z_s$ and analysis capacities $\hat u(t)$, subject to
--
--   $$\sum_t y_{st}+z_s=w_s,\qquad Q_t:=\sum_s y_{st}\le\hat u(t),\qquad \hat u(t)\ge 1 .$$
--
--   The transfer and rejection charge is $\alpha=\sum_{s,t}y_{st}c_{st}+\lambda\sum_s z_s$ (13). Each source $s$ has a private disposal leaf $d_s$ with analysis capacity $z_s$; routing a unit to a disposal leaf means rejecting a client at charge $\lambda$.
--
--   A **comparison** is either
--
--   1. an open comparison $\mathrm{open}(t,K)$ with $K$ a nonempty set of sources, $W_K=\sum_{s\in K}w_s\le\hat u(t)$: it closes $K$, $t$ appears in it, $t$ receives $W_K$, and its charge is $\sum_{s\in K}w_sc_{st}$; or
--   2. an averaged close comparison of a source $s$ with a recipient set $R$ of real targets and disposal leaves of positive analysis capacity and integers $0\le x_o\le\hat u(o)$, $\sum_{o\in R}x_o=w_s$: it closes $s$, every real target of $R$ appears in it and receives $x_t$, and its charge is $\mathrm{route}(s,x)=\sum_{t\in R\cap\mathcal T}x_tc_{st}+\lambda\sum_{d\in R\text{ disposal}}x_d$.
--
--   For a weighted family of comparisons, the closing weight of a source and the number of comparisons in which a target appears are counted over the family.
--
--   **Formalization Note** Recipients are `Tgt ⊕ Src`, with `Sum.inr s'` the disposal leaf of $s'$. A family is a finite list of (weight, comparison) pairs.
-- source:
--   R. Dabas, A Constant-Factor Approximation for Capacitated Facility Location with Outliers, arXiv:2611.04094 (preprint; held version, sha256 613f7405…9798), §4.1, pp.9–10; §4.2 display (17), p.11; §4.3, p.11

import Mathlib
import Definitions.Def_MetricMinTest_IsPseudometric

namespace CFLOutliers

open Finset

/-- **Transport data of §4.1 and §4.3** (Dabas, arXiv:2611.04094, pp.10–11).

* `Src`, the sources `S = F_S \ F_O`; `Tgt`, the real targets `T`;
* `d`, the distances between sources and targets (all facilities of one metric space);
* `lam`, the common penalty `λ`;
* `w s`, the load of source `s`; `y s t`, the number of its paths to target `t`; `z s`, the
  number of its paths to rejection;
* `uhat t`, the analysis capacity `û(t) = |in(t)|` of target `t`.

The conditions of the paper are the predicate `Transport.Valid`. -/
structure Transport (Src Tgt : Type) where
  /-- distances on sources and targets -/
  d : Src ⊕ Tgt → Src ⊕ Tgt → ℝ
  /-- the penalty `λ` -/
  lam : ℝ
  /-- source loads `w_s` -/
  w : Src → ℕ
  /-- real transport `y_{st}` -/
  y : Src → Tgt → ℕ
  /-- disposal quantities `z_s` -/
  z : Src → ℕ
  /-- analysis capacities `û(t)` -/
  uhat : Tgt → ℕ

namespace Transport

variable {Src Tgt : Type} [Fintype Src] [Fintype Tgt]

/-- Column sum `Q_t = Σ_{s} y_{st}` (p.10). -/
def Q (D : Transport Src Tgt) (t : Tgt) : ℕ := ∑ s, D.y s t

/-- Transfer and rejection charge `α = Σ_{s,t} y_{st} c_{st} + λ Σ_s z_s`, display (13), p.10. -/
def alpha (D : Transport Src Tgt) : ℝ :=
  ∑ s, ∑ t, (D.y s t : ℝ) * D.d (Sum.inl s) (Sum.inr t) + D.lam * ∑ s, (D.z s : ℝ)

/-- **The conditions of §4.1, p.10**: `d` is a pseudometric, `λ ≥ 0`, `Σ_t y_{st} + z_s = w_s`,
`Q_t ≤ û(t)`, and `û(t) ≥ 1` (every target has a nonempty set `in(t)`, p.9). -/
def Valid (D : Transport Src Tgt) : Prop :=
  MetricMinTest.IsPseudometric D.d ∧ 0 ≤ D.lam ∧ (∀ s, ∑ t, D.y s t + D.z s = D.w s) ∧
    (∀ t, D.Q t ≤ D.uhat t) ∧ (∀ t, 1 ≤ D.uhat t)

/-- Analysis capacity of a recipient: a real target `Sum.inl t` has `û(t)`; the private disposal
leaf `Sum.inr s'` of source `s'` has `z_{s'}` (§4.3, p.11). -/
def rcap (D : Transport Src Tgt) : Tgt ⊕ Src → ℕ
  | Sum.inl t => D.uhat t
  | Sum.inr s' => D.z s'

end Transport

/-- **A comparison of Lemma 4.1** (§4.2–4.3, pp.10–11).

* `opn t K`: an open comparison sending the whole load of the group `K` of sources to `t`;
* `cls s R x`: an averaged close comparison (17) of source `s` with recipient set `R` of real
  targets (`Sum.inl t`) and disposal leaves (`Sum.inr s'`) and allocation `x`. -/
inductive Comparison (Src Tgt : Type) where
  | opn (t : Tgt) (K : Finset Src)
  | cls (s : Src) (R : Finset (Tgt ⊕ Src)) (x : Tgt ⊕ Src → ℕ)

namespace Comparison

variable {Src Tgt : Type} [Fintype Src] [Fintype Tgt]

/-- **Admissibility.** An open comparison has `K` nonempty with `W_K = Σ_{s∈K} w_s ≤ û(t)`
((16), p.11). A close comparison has positive analysis capacities on `R`, integers
`0 ≤ x_o ≤ û(o)` and `Σ_{o∈R} x_o = w_s` ((17), p.11). -/
def Admissible (D : Transport Src Tgt) : Comparison Src Tgt → Prop
  | opn t K => K.Nonempty ∧ ∑ s ∈ K, D.w s ≤ D.uhat t
  | cls s R x => (∀ o ∈ R, 0 < D.rcap o ∧ x o ≤ D.rcap o) ∧ ∑ o ∈ R, x o = D.w s

/-- The sources a comparison closes. -/
def Closes : Comparison Src Tgt → Src → Prop
  | opn _ K, s => s ∈ K
  | cls s' _ _, s => s' = s

/-- The real targets appearing in a comparison. -/
def Appears : Comparison Src Tgt → Tgt → Prop
  | opn t' _, t => t' = t
  | cls _ R _, t => Sum.inl t ∈ R

open Classical in
/-- The quantity a comparison sends to the real target `t`. -/
noncomputable def quantity (D : Transport Src Tgt) : Comparison Src Tgt → Tgt → ℕ
  | opn t' K, t => if t' = t then ∑ s ∈ K, D.w s else 0
  | cls _ R x, t => if Sum.inl t ∈ R then x (Sum.inl t) else 0

/-- The transfer and rejection charge of a comparison: `Σ_{s∈K} w_s c_{st}` for `open(t, K)`;
`route(s, x) = Σ_{real t ∈ R} x_t c_{st} + λ Σ_{disposal o ∈ R} x_o` for a close. -/
def charge (D : Transport Src Tgt) : Comparison Src Tgt → ℝ
  | opn t K => ∑ s ∈ K, (D.w s : ℝ) * D.d (Sum.inl s) (Sum.inr t)
  | cls s R x => ∑ o ∈ R, (match o with
      | Sum.inl t => (x o : ℝ) * D.d (Sum.inl s) (Sum.inr t)
      | Sum.inr _ => D.lam * (x o : ℝ))

end Comparison

section Family

variable {Src Tgt : Type}

open Classical in
/-- Total weight of the comparisons of a weighted family that close the source `s`. -/
noncomputable def closedWeight (fam : List (ℝ × Comparison Src Tgt)) (s : Src) : ℝ :=
  (fam.map (fun p => if p.2.Closes s then p.1 else 0)).sum

open Classical in
/-- Number of comparisons of a weighted family in which the real target `t` appears. -/
noncomputable def appearCount (fam : List (ℝ × Comparison Src Tgt)) (t : Tgt) : ℕ :=
  fam.countP (fun p => decide (p.2.Appears t))

end Family

end CFLOutliers


