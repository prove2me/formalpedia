-- Prove2me | Definitions.Def_HardcoreSlices_Ztilde
-- name    : HardcoreSlices_Ztilde
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:36:07.870192+00:00
-- url     : https://prove2.me/theorems/80ec9114-3215-4250-9bc7-25877d50eb2c
-- title:
--   The size classes and the truncated partition function $\tilde Z_G(\lambda)$
-- statement:
--   Fix $\alpha,\beta$. A side size $k$ is **low** if $k\le\alpha|X|$, **medium** if $\alpha|X|<k\le\beta|X|$, and **high** if $k>\max(\alpha,\beta)|X|$. These three classes partition the natural numbers. The truncated partition function is
--   $$\tilde Z_G(\lambda)=\sum_{\substack{I\in\mathcal I(G)\\|I\cap X|\le\alpha|X|\\|I\cap Y|\le\alpha|Y|}}\lambda^{|I|}+\sum_{\substack{I\in\mathcal I(G)\\\alpha|X|<|I\cap X|\le\beta|X|}}\lambda^{|I|}+\sum_{\substack{I\in\mathcal I(G)\\\alpha|Y|<|I\cap Y|\le\beta|Y|}}\lambda^{|I|}.$$
--   The sets medium on both sides are counted twice. The paper reduces counting for $Z_G(\lambda)$ to these three sums, each of which is a sum over slices.
--
--   **Formalization Note** The partition printed on p.26 writes $\lceil\beta\rceil|X|$ and ends that disagree with these sums. The classes above are the ones $\tilde Z$ uses, and for $\beta<\alpha$ the medium class is empty, as p.26 says.
-- source:
--   Kocurek, Oveis Gharan, Tjowasi, Sampling from the Hardcore Model on Random Regular Bipartite Graphs above the Uniqueness Threshold, arXiv:2604.21847 (version held, sha256 363c225d…), pp.26–27

import Mathlib
import Definitions.Def_ExpanderBIS_RandomHardCore_Setting

open Classical

namespace HardcoreSlices

open ExpanderBIS.RandomHardCore

/-- The class "low" of a side size: `k ≤ α|X|` (Kocurek, Oveis Gharan, Tjowasi, *Sampling from the Hardcore Model on Random Regular Bipartite Graphs above the Uniqueness Threshold*, arXiv:2604.21847 (version held, sha256 363c225d…), p.26). -/
def IsLow (α : ℝ) (m k : ℕ) : Prop := (k : ℝ) ≤ α * m

/-- The class "medium" of a side size: `α|X| < k ≤ β|X|` (p.26). -/
def IsMed (α β : ℝ) (m k : ℕ) : Prop := α * m < k ∧ (k : ℝ) ≤ β * m

/-- The class "high" of a side size: `k > max(α, β)|X|` (p.26).

**Formalization Note.** p.26 writes the partition with `⌈β⌉|X|` and with ends that disagree with the sums
of `Z̃`. These three classes are the ones `Z̃` uses, and they partition `ℕ` for all real `α, β`. For `β < α` the
medium class is empty, as p.26 says. -/
def IsHigh (α β : ℝ) (m k : ℕ) : Prop := α * m < k ∧ β * m < k

/-- **`Z̃_G(λ)`**, p.26: the sum of `λ^{|I|}` over the independent sets with `|I∩X| ≤ α|X|, |I∩Y| ≤ α|Y|`, plus the sum
over those with `α|X| < |I∩X| ≤ β|X|`, plus the sum over those with `α|Y| < |I∩Y| ≤ β|Y|`. An independent set in the
medium class on both sides is counted twice, as on the page. -/
noncomputable def Ztilde {m : ℕ} (G : SimpleGraph (Vertex m)) (lam α β : ℝ) : ℝ :=
  let I := (Finset.univ : Finset (Finset (Vertex m))).filter (IsIndependent G)
  ∑ J ∈ I.filter (fun J => IsLow α m (J ∩ oddSide m).card ∧ IsLow α m (J ∩ evenSide m).card),
      lam ^ J.card +
    ∑ J ∈ I.filter (fun J => IsMed α β m (J ∩ oddSide m).card), lam ^ J.card +
    ∑ J ∈ I.filter (fun J => IsMed α β m (J ∩ evenSide m).card), lam ^ J.card

end HardcoreSlices


