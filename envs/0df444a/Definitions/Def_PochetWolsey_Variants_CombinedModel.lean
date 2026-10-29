-- Prove2me | Definitions.Def_PochetWolsey_Variants_CombinedModel
-- name    : PochetWolsey_Variants_CombinedModel
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T02:28:33.823685+00:00
-- url     : https://prove2.me/theorems/9be00b20-f41c-4693-91dd-10142505bee8
-- title:
--   Original and printed extended model with markets and production types
-- statement:
--   Let $n,K,L\ge1$ count periods, production types, and markets. Fixed demands $d_t$ and market bounds $V_t^l$ are nonnegative. Production slopes and setup charges satisfy $p_t^1\ge\cdots\ge p_t^K\ge0$ and $0\le q_t^1\le\cdots\le q_t^K$; market prices satisfy $e_t^1\ge\cdots\ge e_t^L$. Holding costs $h_t$ and backlog costs $b_t$ are real. Take $M>0$ at least $\sum_t(d_t+\sum_lV_t^l)$. Production $x$, sales $v$, stock $s$, and backlog $r$ are nonnegative, setups $y$ are binary, and the standard endpoints are $s_0=s_n=r_0=r_n=0$.
--
--   The original constraints are
--   $$s_{t-1}-r_{t-1}+\sum_kx_t^k=d_t+\sum_lv_t^l+s_t-r_t,\quad v_t^l\le V_t^l,\quad x_t^k\le My_t^k.$$
--   Both models minimize
--   $$C(x,y,v,s,r)=\sum_{k,t}(p_t^kx_t^k+q_t^ky_t^k)+\sum_{t=0}^nh_ts_t+\sum_{t=1}^nb_tr_t-\sum_{l,t}e_t^lv_t^l.$$
--   Write $\bar V_t^l=\sum_{\lambda=1}^lV_t^\lambda$, with $\bar V_t^0=0$. The printed extended system has nonnegative $\alpha_{ut}^{kl},z_{ut}^k$ and
--   $$z_{ut}^k=\sum_{l=0}^L\alpha_{ut}^{kl},\quad \sum_{k,u}z_{ut}^k=1,\quad z_{tt}^k\le y_t^k,$$
--   $$z_{ut}^k\ge z_{u,t+1}^k\ (u\le t),\qquad z_{ut}^k\ge z_{u,t-1}^k\ (t\le u),$$
--   $$v_t^l=\sum_{k,u}\sum_{\lambda=l}^LV_t^\lambda\alpha_{ut}^{kl},\quad x_u^k=\sum_{l,t}(d_t+\bar V_t^l)\alpha_{ut}^{kl},$$
--   $$s_{t-1}=\sum_{k,l}\sum_{u<t\le\tau}(d_\tau+\bar V_\tau^l)\alpha_{u\tau}^{kl},\quad r_t=\sum_{k,l}\sum_{\tau\le t<u}(d_\tau+\bar V_\tau^l)\alpha_{u\tau}^{kl}.$$
--   Projection existentially eliminates $\alpha,z$. A minimum is a feasible point whose cost is no larger than that of every feasible point. The interval-production property says each positive $x_t^k$ is the sum of fixed demands and selected full-market bounds over some interval containing $t$.
--
--   These definitions keep the original set independent of the proposed extension and preserve the printed market formula.
--
--   **Formalization Note** The original market bounds and balance equations are not added to the extended system. Equation (11.63) retains its fixed $l$ on $\alpha$ while summing over $\lambda$, and (11.67) retains binary setups. Neighbor inequalities are imposed within the horizon; omitted neighbors have value zero. Standard endpoint normalization comes from printed pages 209 and 304–305. No sign restriction on $h,b$ is added; the resulting boundedness issue is recorded in F4.
-- source:
--   Pochet and Wolsey, Production Planning by Mixed Integer Programming, Springer 2006, p. 356–357 (PDF 369–370), Section 11.9, (11.52)–(11.67), Observation 11.3; DOI 10.1007/0-387-33477-7

import Mathlib

open scoped BigOperators

namespace PochetWolsey.Variants

structure CombinedData (n K L : ℕ) where
  d : Fin n → ℝ
  V : Fin L → Fin n → ℝ
  p : Fin K → Fin n → ℝ
  q : Fin K → Fin n → ℝ
  e : Fin L → Fin n → ℝ
  h : Fin (n + 1) → ℝ
  b : Fin n → ℝ
  M : ℝ

structure CombinedPoint (n K L : ℕ) where
  x : Fin K → Fin n → ℝ
  y : Fin K → Fin n → ℝ
  v : Fin L → Fin n → ℝ
  s : Fin (n + 1) → ℝ
  r : Fin (n + 1) → ℝ

def CombinedData.Standing {n K L : ℕ} (D : CombinedData n K L) : Prop :=
  0 < n ∧ 0 < K ∧ 0 < L ∧
  (∀ t, 0 ≤ D.d t) ∧ (∀ l t, 0 ≤ D.V l t) ∧
  (∀ k t, 0 ≤ D.p k t ∧ 0 ≤ D.q k t) ∧
  (∀ k j t, k ≤ j → D.q k t ≤ D.q j t ∧ D.p j t ≤ D.p k t) ∧
  (∀ l j t, l ≤ j → D.e j t ≤ D.e l t) ∧
  0 < D.M ∧ (∑ t, (D.d t + ∑ l, D.V l t)) ≤ D.M

noncomputable def CombinedData.Vbar {n K L : ℕ} (D : CombinedData n K L)
    (l : Fin (L + 1)) (t : Fin n) : ℝ :=
  ∑ j ∈ Finset.univ.filter (fun j : Fin L => j.val < l.val), D.V j t

def CombinedPoint.domains {n K L : ℕ} (w : CombinedPoint n K L) : Prop :=
  (∀ k t, 0 ≤ w.x k t ∧ (w.y k t = 0 ∨ w.y k t = 1)) ∧
  (∀ l t, 0 ≤ w.v l t) ∧ (∀ t, 0 ≤ w.s t ∧ 0 ≤ w.r t) ∧
  w.s 0 = 0 ∧ w.s (Fin.last n) = 0 ∧ w.r 0 = 0 ∧ w.r (Fin.last n) = 0

def CombinedData.original {n K L : ℕ} (D : CombinedData n K L)
    (w : CombinedPoint n K L) : Prop :=
  w.domains ∧
  (∀ t : Fin n, w.s t.castSucc - w.r t.castSucc + (∑ k, w.x k t) =
    D.d t + (∑ l, w.v l t) + w.s t.succ - w.r t.succ) ∧
  (∀ l t, w.v l t ≤ D.V l t) ∧ (∀ k t, w.x k t ≤ D.M * w.y k t)

noncomputable def CombinedData.cost {n K L : ℕ} (D : CombinedData n K L)
    (w : CombinedPoint n K L) : ℝ :=
  (∑ k, ∑ t, (D.p k t * w.x k t + D.q k t * w.y k t)) +
    (∑ t, D.h t * w.s t) + (∑ t, D.b t * w.r t.succ) -
    ∑ l, ∑ t, D.e l t * w.v l t

def IsMinimum {A : Type*} (P : A → Prop) (c : A → ℝ) (w : A) : Prop :=
  P w ∧ ∀ w', P w' → c w ≤ c w'

abbrev Allocation (n K L : ℕ) := Fin K → Fin (L + 1) → Fin n → Fin n → ℝ
abbrev Assignment (n K : ℕ) := Fin K → Fin n → Fin n → ℝ

noncomputable def CombinedData.printedExtended {n K L : ℕ} (D : CombinedData n K L)
    (w : CombinedPoint n K L) (α : Allocation n K L) (z : Assignment n K) : Prop :=
  w.domains ∧
  (∀ k l u t, 0 ≤ α k l u t) ∧ (∀ k u t, 0 ≤ z k u t) ∧
  (∀ k u t, z k u t = ∑ l, α k l u t) ∧
  (∀ t, (∑ k, ∑ u, z k u t) = 1) ∧
  (∀ k t, z k t t ≤ w.y k t) ∧
  (∀ (k : Fin K) (u t t' : Fin n), u ≤ t → t'.val = t.val + 1 → z k u t' ≤ z k u t) ∧
  (∀ (k : Fin K) (u t t' : Fin n), t ≤ u → t.val = t'.val + 1 → z k u t' ≤ z k u t) ∧
  (∀ l t, w.v l t = ∑ k, ∑ u,
    ∑ j ∈ Finset.univ.filter (fun j : Fin L => l ≤ j),
      D.V j t * α k l.succ u t) ∧
  (∀ k u, w.x k u = ∑ l, ∑ t, (D.d t + D.Vbar l t) * α k l u t) ∧
  (∀ t : Fin n, w.s t.castSucc = ∑ k, ∑ l,
    ∑ u ∈ Finset.univ.filter (fun u : Fin n => u < t),
      ∑ τ ∈ Finset.univ.filter (fun τ : Fin n => t ≤ τ),
        (D.d τ + D.Vbar l τ) * α k l u τ) ∧
  (∀ t : Fin n, w.r t.succ = ∑ k, ∑ l,
    ∑ u ∈ Finset.univ.filter (fun u : Fin n => t < u),
      ∑ τ ∈ Finset.univ.filter (fun τ : Fin n => τ ≤ t),
        (D.d τ + D.Vbar l τ) * α k l u τ)

noncomputable def CombinedData.extended {n K L : ℕ} (D : CombinedData n K L)
    (w : CombinedPoint n K L) : Prop :=
  ∃ α : Allocation n K L, ∃ z : Assignment n K, D.printedExtended w α z

noncomputable def CombinedData.intervalProduction {n K L : ℕ} (D : CombinedData n K L)
    (w : CombinedPoint n K L) : Prop :=
  ∀ k t, 0 < w.x k t → ∃ a b : Fin n, a ≤ t ∧ t ≤ b ∧
    ∃ S : Fin n → Finset (Fin L),
      w.x k t = ∑ u ∈ Finset.univ.filter (fun u => a ≤ u ∧ u ≤ b),
        (D.d u + ∑ l ∈ S u, D.V l u)

end PochetWolsey.Variants


