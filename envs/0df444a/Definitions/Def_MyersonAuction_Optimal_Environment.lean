-- Prove2me | Definitions.Def_MyersonAuction_Optimal_Environment
-- name    : MyersonAuction_Optimal_Environment
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T05:17:43.749551+00:00
-- url     : https://prove2.me/theorems/e1d3f60e-a1a5-42f7-b365-dd58748ea2c0
-- title:
--   The independent-value auction environment and its virtual values
-- statement:
--   A finite, nonempty set of bidders has independent value estimates $t_i$ in bidder-specific finite intervals $[a_i,b_i]$. Each estimate has a continuous, strictly positive density $f_i$ of total mass one. A continuous revision effect $e_i(t_i)$ changes other agents’ valuations, and the seller has a known value $t_0$. The support and distribution are the product support and product density. The bidder and seller valuations, CDF and virtual value are
--
--   $$
--   T=\prod_i[a_i,b_i],\quad F_i(s)=\int_{a_i}^s f_i(u)\,du,\quad
--   v_i(t)=t_i+\sum_{j\ne i}e_j(t_j),\quad v_0(t)=t_0+\sum_j e_j(t_j),\quad
--   c_i(s)=s-e_i(s)-\frac{1-F_i(s)}{f_i(s)}.
--   $$
--
--   These primitives underlie all direct mechanisms and the ironing construction.
--
--   **Formalization Note** The bidder type is finite; the mission's theorems additionally require it to be nonempty. Continuity of $e_i$ makes $c_i$ continuous as used in the paper. The optional mean-zero condition (2.9) is not imposed.
-- source:
--   Myerson, Optimal Auction Design, Math. Oper. Res. 6(1) (1981), pp. 59–60, §2, eqs. (2.1)–(2.8); p. 66, eq. (5.1)

import Mathlib

noncomputable section

namespace MyersonAuction.Optimal

open MeasureTheory

/-- The independent private-value environment of Myerson, §§2–4. -/
structure Environment (ι : Type) [Fintype ι] where
  a : ι → ℝ
  b : ι → ℝ
  a_lt_b : ∀ i, a i < b i
  f : ι → ℝ → ℝ
  f_cont : ∀ i, ContinuousOn (f i) (Set.Icc (a i) (b i))
  f_pos : ∀ i t, t ∈ Set.Icc (a i) (b i) → 0 < f i t
  f_int : ∀ i, ∫ t in a i..b i, f i t = 1
  e : ι → ℝ → ℝ
  e_cont : ∀ i, ContinuousOn (e i) (Set.Icc (a i) (b i))
  t0 : ℝ

def support {ι : Type} [Fintype ι] (E : Environment ι) : Set (ι → ℝ) :=
  Set.pi Set.univ (fun i => Set.Icc (E.a i) (E.b i))

def distribution {ι : Type} [Fintype ι] (E : Environment ι) : Measure (ι → ℝ) :=
  (volume.restrict (support E)).withDensity
    (fun t => ENNReal.ofReal (∏ i, E.f i (t i)))

def F {ι : Type} [Fintype ι] (E : Environment ι) (i : ι) (s : ℝ) : ℝ :=
  ∫ u in E.a i..s, E.f i u

def bidderValue {ι : Type} [Fintype ι] [DecidableEq ι]
    (E : Environment ι) (i : ι) (t : ι → ℝ) : ℝ :=
  t i + ∑ j ∈ Finset.univ.filter (fun j => j ≠ i), E.e j (t j)

def sellerValue {ι : Type} [Fintype ι] (E : Environment ι) (t : ι → ℝ) : ℝ :=
  E.t0 + ∑ j, E.e j (t j)

def virtualValue {ι : Type} [Fintype ι] (E : Environment ι) (i : ι) (s : ℝ) : ℝ :=
  s - E.e i s - (1 - F E i s) / E.f i s

end MyersonAuction.Optimal


