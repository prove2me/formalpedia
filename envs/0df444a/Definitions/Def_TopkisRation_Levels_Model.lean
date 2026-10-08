-- Prove2me | Definitions.Def_TopkisRation_Levels_Model
-- name    : TopkisRation_Levels_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T15:46:53.948677+00:00
-- url     : https://prove2.me/theorems/8c0a7dc5-39d2-4744-856d-8727689268e1
-- title:
--   §1, pp. 162–166 — the n-class rationing model, Assumptions (A)–(C), the recursion (1), the critical levels z̄_t^j and the rationing level policy (7)
-- statement:
--   This file sets up the single-procurement inventory model with $n$ demand classes of Topkis (1968, §1).
--
--   **Data.** A period is divided into $k$ intervals, indexed backwards: interval $t\in\{1,\dots,k\}$ has $t-1$ intervals after it, so interval $k$ is the first and interval $1$ the last. Demand comes in $n$ classes; class $n$ is the most important and class $1$ the least. The model consists of
--   1. constants $a_t\ge 0$: unsatisfied demand $u_t$ at the end of interval $t$ is carried into the next interval as the backlog $b_{t-1}=a_tu_t$ ($a_t=1$: complete backlogging, $a_t=0$: lost sales);
--   2. penalty vectors $p_t=(p_t^1,\dots,p_t^n)$, charged as $p_t\cdot u_t$ at the end of interval $t$;
--   3. holding costs $h_t(\cdot)$ on the stock at the end of interval $t$;
--   4. salvage costs $v_1(z)+v_2(z-a_1\sum_i u_1^i)$ at the end of interval $1$;
--   5. the ordering cost $c(w)$, $w\ge 0$, of the single order at the start of interval $k$;
--   6. the law $\mu_t$ of the demand vector $d_t=(d_t^1,\dots,d_t^n)$ of interval $t$; demands in different intervals are independent.
--
--   **Standing assumptions.** For $1\le t\le k$: $a_t\ge0$;
--   (A) $h_t$ is convex and continuous on $[0,\infty)$;
--   (B) $v_1$ is convex and continuous on $[0,\infty)$, $v_2$ is convex and continuous on $\mathbb R$, and $\lim_{w\to-\infty}D^+v_2(w)>-\infty$, where $D^+$ is the right derivative;
--   (C) $0\le p_t^1\le p_t^2\le\cdots\le p_t^n$;
--   and $\mu_t$ is a probability law on $[0,\infty)^n$ under which every class has a finite mean.
--
--   **The recursion (1).** With $\mathbf 1\cdot y=\sum_j y^j$, for $z\ge0$ and $B\ge0$ (stock and outstanding demand at the start of interval $t$), $u$ is feasible if $0\le u\le B$ and $w=z-\mathbf 1\cdot(B-u)\ge0$, and
--
--   $$
--   f_t(z,B)=\inf_{u \text{ feasible}}\big[p_t\cdot u+h_t(w)+g_{t-1}(w,a_tu)\big],\qquad g_t(z,b)=\mathbb E\,f_t(z,b+d_t),\qquad g_0(z,b)=v_1(z)+v_2(z-\mathbf 1\cdot b).
--   $$
--
--   **Critical levels and the rationing level policy.** Let $\delta_j$ be the $j$-th unit vector, $y^+=\max(y,0)$, $y_1\wedge y_2=\min(y_1,y_2)$ and $B^{(j)}=\sum_{i\ge j}B^i$. A critical level $\bar z_t^j\in[0,\infty]$ for class $j$ in interval $t$ is $+\infty$ if $\varphi_t^j(w)=p_t^jw+h_t(w)+g_{t-1}(w,a_tw\delta_j)$ is strictly decreasing on $[0,\infty)$, and the smallest minimizer of $\varphi_t^j$ on $[0,\infty)$ otherwise. Given levels $\bar z^j$, the rationing level policy (7) leaves unsatisfied
--
--   $$
--   u^j=\big(B^{(j)}-z+\bar z^j\big)^+\wedge B^j \qquad(u^j=B^j \text{ if } \bar z^j=+\infty).
--   $$
--
--   These are the objects of every statement of the mission.
--
--   **Formalization Note.** Classes are `Fin n` (the paper's class $j$ is index $j-1$, so class $n$ is the largest index); vectors are `Fin n → ℝ` with the pointwise order; $p_t\cdot u$ is a dot product and $\delta_j$ is `Pi.single j 1`. $f_t$ is *defined* by the dynamic-programming recursion (1), which the paper writes down as a consequence of the policy-space definition ("clearly we have"); the infimum is a real `sInf` and the expectation a Bochner integral, which are the paper's values on $z\ge0$, $B\ge0$ once the infimum is finite and attained and the integrand integrable (Lemma 2 of the mission). $f_0$ is junk and never used. $D^+$ is the extended-real right lower Dini derivative, and (B)'s limit condition is read as "$D^+v_2$ is bounded below", which is equivalent for convex $v_2$ (whose $D^+$ is nondecreasing). Interval-indexed assumptions are imposed for $1\le t\le k$ only. Demands are taken nonnegative almost surely, the paper's implicit convention for demand. The degenerate cases $n=0$ and $k=0$ are not excluded by the model; statements about them are vacuous or trivial. Critical levels are values in `WithTop ℝ` ($\top=+\infty$), characterized by the predicate `IsCriticalLevel`, never computed by a real `sInf`. Assumption (D) on the ordering cost is not part of the standing assumptions; no statement of this mission uses it.
-- source:
--   Topkis, Optimal ordering and rationing policies in a nonstationary dynamic inventory model with n demand classes, Management Science 15 (1968), pp. 162–166, §1, Assumptions (A)–(C), (1), definition of z̄_t^j, (7)

import Mathlib

namespace TopkisRation.Levels

open MeasureTheory Filter Topology

/-- Data of the single-procurement model of §1 (pp. 162–163). -/
structure Model (n : ℕ) where
  k : ℕ                          -- number of intervals in the period
  a : ℕ → ℝ                      -- a_t: b_{t-1} = a_t u_t
  p : ℕ → Fin n → ℝ              -- penalty p_t^j
  h : ℕ → ℝ → ℝ                  -- holding cost h_t
  v₁ : ℝ → ℝ                     -- salvage cost v₁(z)
  v₂ : ℝ → ℝ                     -- salvage cost v₂(z − a₁ Σ u₁ⁱ)
  c : ℝ → ℝ                      -- ordering cost c(w), w ≥ 0, at the start of interval k
  μ : ℕ → Measure (Fin n → ℝ)    -- law of the demand vector d_t

/-- `D⁺f(x)`: the right derivative, extended-real valued (it is `⊥` where the right difference
quotients tend to −∞, which a convex function on [0, ∞) may do at 0). -/
noncomputable def rightDeriv (f : ℝ → ℝ) (x : ℝ) : EReal :=
  Filter.liminf (fun ε : ℝ => (((f (x + ε) - f x) / ε : ℝ) : EReal)) (𝓝[>] 0)

variable {n : ℕ}

/-- The standing assumptions of §1: (A), (B), (C), a_t ≥ 0, and the demand distributions
(probability laws on [0, ∞)ⁿ with finite means). -/
structure Model.Standing (M : Model n) : Prop where
  a_nonneg : ∀ t ∈ Finset.Icc 1 M.k, 0 ≤ M.a t
  h_convex : ∀ t ∈ Finset.Icc 1 M.k, ConvexOn ℝ (Set.Ici 0) (M.h t)          -- (A)
  h_cont : ∀ t ∈ Finset.Icc 1 M.k, ContinuousOn (M.h t) (Set.Ici 0)          -- (A)
  v₁_convex : ConvexOn ℝ (Set.Ici 0) M.v₁                                     -- (B)
  v₁_cont : ContinuousOn M.v₁ (Set.Ici 0)                                     -- (B)
  v₂_convex : ConvexOn ℝ Set.univ M.v₂                                        -- (B)
  v₂_cont : Continuous M.v₂                                                   -- (B)
  v₂_slope : ∃ L : ℝ, ∀ w, (L : EReal) ≤ rightDeriv M.v₂ w                    -- (B)
  p_nonneg : ∀ t ∈ Finset.Icc 1 M.k, ∀ j, 0 ≤ M.p t j                         -- (C)
  p_mono : ∀ t ∈ Finset.Icc 1 M.k, Monotone (M.p t)                           -- (C)
  μ_prob : ∀ t ∈ Finset.Icc 1 M.k, IsProbabilityMeasure (M.μ t)
  μ_nonneg : ∀ t ∈ Finset.Icc 1 M.k, ∀ᵐ x ∂(M.μ t), 0 ≤ x
  μ_mean : ∀ t ∈ Finset.Icc 1 M.k, ∀ j, Integrable (fun x : Fin n → ℝ => x j) (M.μ t)

/-- Feasible unsatisfied-demand vectors in (1): 0 ≤ u ≤ B and w = z − 1·(B − u) ≥ 0. -/
def feasible (z : ℝ) (B : Fin n → ℝ) : Set (Fin n → ℝ) :=
  {u | 0 ≤ u ∧ u ≤ B ∧ ∑ j, (B j - u j) ≤ z}

/-- The bracket of (1): p_t·u + h_t(w) + G(w, a_t u) with w = z − 1·(B − u). -/
def Model.obj (M : Model n) (t : ℕ) (G : ℝ → (Fin n → ℝ) → ℝ) (z : ℝ) (B u : Fin n → ℝ) : ℝ :=
  M.p t ⬝ᵥ u + M.h t (z - ∑ j, (B j - u j)) + G (z - ∑ j, (B j - u j)) (M.a t • u)

/-- The right-hand side of (1) with g_{t−1} replaced by `G`. -/
noncomputable def Model.stage (M : Model n) (t : ℕ) (G : ℝ → (Fin n → ℝ) → ℝ)
    (z : ℝ) (B : Fin n → ℝ) : ℝ :=
  sInf (M.obj t G z B '' feasible z B)

/-- g_0(z, b) = v₁(z) + v₂(z − 1·b) and g_t(z, b) = E f_t(z, b + d_t). -/
noncomputable def Model.g (M : Model n) : ℕ → ℝ → (Fin n → ℝ) → ℝ
  | 0 => fun z b => M.v₁ z + M.v₂ (z - ∑ j, b j)
  | t + 1 => fun z b => ∫ x, M.stage (t + 1) (M.g t) z (b + x) ∂(M.μ (t + 1))

/-- f_t(z, B), for 1 ≤ t (at t = 0 it is junk and never used). -/
noncomputable def Model.f (M : Model n) (t : ℕ) (z : ℝ) (B : Fin n → ℝ) : ℝ :=
  M.stage t (M.g (t - 1)) z B

/-- B^{(j)} = Σ_{i ≥ j} B^i. -/
def tailSum (B : Fin n → ℝ) (j : Fin n) : ℝ := ∑ i ∈ Finset.Ici j, B i

/-- The rationing level policy (7): u^j = (B^{(j)} − z + z̄^j)⁺ ∧ B^j, and u^j = B^j when z̄^j = +∞. -/
def rationU (zbar : Fin n → WithTop ℝ) (z : ℝ) (B : Fin n → ℝ) : Fin n → ℝ :=
  fun j => WithTop.untopD (B j) ((zbar j).map fun x => min (max (tailSum B j - z + x) 0) (B j))

/-- The function whose smallest minimum is z̄_t^j: p_t^j w + h_t(w) + g_{t−1}(w, a_t w δ_j). -/
noncomputable def Model.levelObj (M : Model n) (t : ℕ) (j : Fin n) (w : ℝ) : ℝ :=
  M.p t j * w + M.h t w + M.g (t - 1) w (M.a t • w • Pi.single j 1)

/-- "z̄ = +∞ if φ is strictly decreasing on [0, ∞), and z̄ is the smallest minimum of φ on [0, ∞)
otherwise." -/
def IsCriticalLevel (φ : ℝ → ℝ) (zbar : WithTop ℝ) : Prop :=
  (zbar = ⊤ ∧ StrictAntiOn φ (Set.Ici 0)) ∨
  ∃ x : ℝ, zbar = x ∧ 0 ≤ x ∧ (∀ y, 0 ≤ y → φ x ≤ φ y) ∧
    ∀ y, 0 ≤ y → (∀ w, 0 ≤ w → φ y ≤ φ w) → x ≤ y

end TopkisRation.Levels


