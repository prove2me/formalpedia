-- Prove2me | Definitions.Def_LotteryInterm_IID_Menu
-- name    : LotteryInterm_IID_Menu
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T21:01:06.924438+00:00
-- url     : https://prove2.me/theorems/558b6d89-88d4-40ba-92af-dc82286979d1
-- title:
--   Finite menus and the lowest-payment selection rule
-- statement:
--   A seller menu is a finite collection of allocation-payment pairs $(x,p)$, with $0\le x\le1$ and $p\ge0$. The outside option $(0,0)$ is always available. A bidder of value $t$ obtains access utility $u_M(t)=\max_{(x,p)\in M\cup\{(0,0)\}}(xt-p)$ and, among maximizing options, chooses the one of lowest payment.
--
--   A lottery charging price $a$ with probability $\lambda$ and price $b$ otherwise is the menu
--   $$M(a,b,\lambda)=\{(\lambda,\lambda a),(1,\lambda a+(1-\lambda)b)\},\qquad 0\le a\le b,\quad0\le\lambda\le1.$$
--   The module separately defines a deterministic posted price. Equal prices or endpoint lottery weights are allowed, so the target uses at most two prices. The payment minimum ranges over a nonempty finite maximizing set; its defensive empty-set branch is unreachable.
--
--   These are the menu and bidder tie-breaking conventions used by every seller-revenue statement.
-- source:
--   Jingyi Liu, Aviad Rubinstein, Ertem Nusret Tas, Matt Weinberg, Qianfan Zhang, STOC 2027 submission #623 (October 2026), §2.1, pp.7–8 (PDF pp.8–9); Assumption 3.3, p.10 (PDF p.11); menu representation, p.23 (PDF p.24); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/623.pdf

import Mathlib

namespace LotteryInterm.IID

structure Menu where
  options : Finset (ℝ × ℝ)
  valid : ∀ o ∈ options, o.1 ∈ Set.Icc 0 1 ∧ 0 ≤ o.2

noncomputable def allOptions (M : Menu) : Finset (ℝ × ℝ) := by
  classical
  exact insert (0, 0) M.options

noncomputable def accessUtility (M : Menu) (t : ℝ) : ℝ := by
  classical
  exact (allOptions M).sup' (by simp [allOptions]) (fun o => o.1 * t - o.2)

/-- Minimum payment among all utility maximizers, with the outside option. -/
noncomputable def menuPayment (M : Menu) (t : ℝ) : ℝ := by
  classical
  let prices := ((allOptions M).filter (fun o => o.1 * t - o.2 = accessUtility M t)).image Prod.snd
  exact if h : prices.Nonempty then prices.min' h else 0

noncomputable def postedPrice (p : ℝ) (hp : 0 ≤ p) : Menu := by
  classical
  exact ⟨{(1, p)}, by intro o ho; simp only [Finset.mem_singleton] at ho; subst o; exact ⟨⟨by norm_num, le_rfl⟩, hp⟩⟩

/-- weight is the probability of the low price a. Equal prices and zero weights are allowed. -/
noncomputable def twoPrice (a b weight : ℝ) (ha : 0 ≤ a) (hab : a ≤ b)
    (hweight : weight ∈ Set.Icc 0 1) : Menu := by
  classical
  refine ⟨{(weight, weight * a), (1, weight * a + (1 - weight) * b)}, ?_⟩
  intro o ho
  simp only [Finset.mem_insert, Finset.mem_singleton] at ho
  rcases ho with rfl | rfl
  · exact ⟨hweight, mul_nonneg hweight.1 ha⟩
  · exact ⟨⟨by norm_num, le_rfl⟩,
      add_nonneg (mul_nonneg hweight.1 ha) (mul_nonneg (sub_nonneg.mpr hweight.2) (ha.trans hab))⟩

end LotteryInterm.IID


