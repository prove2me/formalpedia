-- Prove2me | Definitions.Def_LotteryInterm_IID_Supplement_GeneralMenu
-- name    : LotteryInterm_IID_Supplement_GeneralMenu
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T20:06:43.534654+00:00
-- url     : https://prove2.me/theorems/d093fc14-09f1-467a-a6b1-3c9fa79e560a
-- title:
--   General (possibly infinite) seller menus in the message-independent model
-- statement:
--   A **general seller menu** $\mathcal O$ is a set of options $(x,p)\in[0,1]\times\mathbb R_{\ge0}$ — allocation probability and expected payment — that contains the outside option $(0,0)$, may be infinite, and in which every type $t$ has a utility-maximizing option, so that
--   $$u_{\mathcal O}(t)=\max_{(x,p)\in\mathcal O}\,(xt-p)$$
--   is attained (the proviso of p.15). Every published finite menu, with its outside option, is a general menu.
--
--   A **utility-maximizing selection** $\sigma$ assigns to every type an option of $\mathcal O$ attaining $u_{\mathcal O}$. In the message-independent model the intermediary sells the right to choose from $\mathcal O$: its best responses are the admissible (BIC, interim IR, feasible, integrable) direct mechanisms for values $u_{\mathcal O}(v_i)$ that attain the optimal fee revenue, exactly as in the published definitions for finite menus. When a best response forwards bidder $i$ with probability $y_i(v)$ and the forwarded bidder takes $\sigma(v_i)$, the seller earns
--   $$\mathrm{SelRev}=\mathbb E\Big[\sum_i y_i(v)\,p_{\sigma}(v_i)\Big].$$
--
--   These objects let Theorem 6.6 bound the seller's revenue over arbitrary randomized truthful seller auctions.
-- source:
--   Jingyi Liu, Aviad Rubinstein, Ertem Nusret Tas, Matt Weinberg, Qianfan Zhang, STOC 2027 submission #623 (October 2026), §2.1, pp.7–8 (PDF pp.8–9); §5, p.15 (PDF p.16); proof of Theorem 6.6, p.27 (PDF p.28); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/623.pdf

import Definitions.Def_LotteryInterm_IID_Intermediary

open MeasureTheory

namespace LotteryInterm.IID.Supplement

/-- A general (possibly infinite) seller menu of (allocation probability, expected
payment) options. It contains the outside option `(0,0)` and every type has a
utility-maximizing option, so all maxima are well defined (p.15). -/
structure GenMenu where
  options : Set (ℝ × ℝ)
  valid : ∀ o ∈ options, o.1 ∈ Set.Icc (0 : ℝ) 1 ∧ 0 ≤ o.2
  outside : ((0 : ℝ), (0 : ℝ)) ∈ options
  maximizer : ∀ t : ℝ, ∃ o ∈ options, ∀ o' ∈ options, o'.1 * t - o'.2 ≤ o.1 * t - o.2

/-- Every published finite menu, with its outside option, is a general menu. -/
noncomputable def GenMenu.ofMenu (M : Menu) : GenMenu where
  options := ↑(allOptions M)
  valid := by
    classical
    intro o ho
    simp only [allOptions, Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at ho
    rcases ho with rfl | ho
    · exact ⟨⟨le_rfl, zero_le_one⟩, le_rfl⟩
    · exact M.valid o ho
  outside := by
    classical
    simp [allOptions]
  maximizer := by
    classical
    intro t
    obtain ⟨o, ho, hmax⟩ := (allOptions M).exists_max_image
      (fun o : ℝ × ℝ => o.1 * t - o.2) (by simp [allOptions])
    exact ⟨o, ho, fun o' ho' => hmax o' ho'⟩

/-- Utility of free access to the menu: the best option's utility (attained). -/
noncomputable def genAccessUtility (O : GenMenu) (t : ℝ) : ℝ :=
  sSup ((fun o : ℝ × ℝ => o.1 * t - o.2) '' O.options)

/-- A selection `σ` choosing, for every type, a utility-maximizing option of `O`. -/
def IsUtilityMaximizing (O : GenMenu) (σ : ℝ → ℝ × ℝ) : Prop :=
  ∀ t : ℝ, σ t ∈ O.options ∧ ∀ o' ∈ O.options, o'.1 * t - o'.2 ≤ (σ t).1 * t - (σ t).2

/-- Message-independent model: a best response of the intermediary to a general
menu is an admissible access mechanism (values `u_O(v_i)`) of maximal fee revenue. -/
def GenBestResponse {n : ℕ} (D : Fin n → ValueDist) (O : GenMenu) (I : Mechanism n) : Prop :=
  Admissible D (genAccessUtility O) I ∧
    (revenue (prior D) I : EReal) = OptRev D (genAccessUtility O)

/-- Seller revenue under the access mechanism `I` when each forwarded bidder of
type `t` takes the option `σ t`. -/
noncomputable def genSellerRevenue {n : ℕ} (D : Fin n → ValueDist) (σ : ℝ → ℝ × ℝ)
    (I : Mechanism n) : ℝ :=
  ∫ v, ∑ i, I.allocation v i * (σ (v i)).2 ∂prior D

end LotteryInterm.IID.Supplement


