-- Prove2me | Definitions.Def_EndogMerger_SymLoyal_Regions
-- name    : EndogMerger_SymLoyal_Regions
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T03:11:22.15401+00:00
-- url     : https://prove2.me/theorems/88022e67-627d-47c8-b16e-a69d65555670
-- title:
--   Footnotes 12–14, PDF pp. 14–16, 46–47 — thresholds k^(0)_{1,2}, k^(BC)_{1,2}, k^(AB)_1, α^(BC)_1 and the regions of Lemmas 3–5
-- statement:
--   The regions of the parameter plane $(\alpha,k)$ on which Lemmas 3–5 of the paper give closed forms for the Table A1 quantities. With the cubic $c_0(\alpha)=-43\alpha^3+43\alpha^2-13\alpha+1$, define the thresholds
--   $$
--   k^{(0)}_{1,2}(\alpha)=\frac{(1-2\alpha)\bigl[(1-\alpha)(1-3\alpha)\mp\sqrt{(1-3\alpha)\,c_0(\alpha)}\bigr]}{2(1-3\alpha)(2-5\alpha)},
--   $$
--   $$
--   k^{(BC)}_{1,2}(\alpha)=\frac{(1-\alpha)(1-2\alpha)\mp\sqrt{(1-\alpha)(1-2\alpha)(26\alpha^2-11\alpha+1)}}{4(1-3\alpha)},\qquad
--   k^{(AB)}_{1}(\alpha)=\frac{(1-\alpha)(1-2\alpha)-\sqrt{(1-\alpha)(1-2\alpha)(14\alpha^2-7\alpha+1)}}{2(1-3\alpha)},
--   $$
--   and $\alpha^{(BC)}_1=(11-\sqrt{17})/52\approx 0.1322$. The regions are
--
--   1. $\Omega^{(0)}_1=\{0<\alpha<\alpha^{(0)}_1,\ k^{(0)}_1<k<k^{(0)}_2\}$ and $\Omega^{(0)}_2=\{(\alpha,k)\notin\Omega^{(0)}_1,\ 0<\alpha<1/3,\ \alpha<k<1-2\alpha\}$, where $\alpha^{(0)}_1$ is supplied as a parameter;
--   2. $\Omega^{(BC)}_1=\{0<\alpha<\alpha^{(BC)}_1,\ k^{(BC)}_1<k<k^{(BC)}_2\}$, $\Omega^{(BC)}_2=\{(\alpha,k)\notin\Omega^{(BC)}_1,\ 0<\alpha<1/3,\ \alpha<k<(1-\alpha)/2\}$, $\Omega^{(BC)}_3=\{0<\alpha<1/3,\ (1-\alpha)/2\le k<1-2\alpha\}$;
--   3. $\Omega^{(AB)}_1=\{0<\alpha<1/3,\ k^{(AB)}_1\le k<1-2\alpha\}$ and $\Omega^{(AB)}_2=\{0<\alpha<1/3,\ \alpha<k<k^{(AB)}_1\}$.
--
--   These regions decide which branch of each maximum in Table A1 is active, and they partition the comparisons in the proof of Proposition 3.
--
--   **Formalization Note** The paper defines $\alpha^{(0)}_1$ and $\alpha^{(BC)}_1$ by $k_1(\alpha_1)=k_2(\alpha_1)$; with Lean's `Real.sqrt` (which is $0$ on negative inputs) that equation holds for every $\alpha$ with a nonpositive radicand, so it is not used. $\alpha^{(BC)}_1$ is the closed form the paper gives in the proof of Lemma 4; $\alpha^{(0)}_1$, which has no closed form, is the parameter `α₁` of $\Omega^{(0)}_1$, and Lemma 3 pins it as the root in $(0,1/3)$ of $c_0$ (the cubic has one real root, $\approx 0.1167$).
-- source:
--   Wang, Wu, Tang & Dai, Endogenous merger decisions among competitors: impact of limited capacity and loyal segments, Management Science (2024), accepted manuscript, footnote 12 (PDF p. 14), footnote 13 (PDF p. 15), footnote 14 (PDF p. 16), proofs of Lemmas 3–4 (PDF pp. 46–47)

import Mathlib

namespace EndogMerger.SymLoyal

noncomputable section

/-! Thresholds and regions of Lemmas 3–5 (footnotes 12–14, PDF pp. 14–16; proofs PDF
pp. 46–47) of Wang, Wu, Tang & Dai (Management Science 2024), accepted manuscript. -/

/-- The cubic `-43α³ + 43α² - 13α + 1` under the square root of `k^(0)_{1,2}`; its root in
`(0, 1/3)` is `α^(0)_1` (proof of Lemma 3, PDF p. 46). -/
def cubic0 (α : ℝ) : ℝ := -43 * α ^ 3 + 43 * α ^ 2 - 13 * α + 1

/-- `k^(0)_1(α)` (footnote 12, PDF p. 14). -/
def k0₁ (α : ℝ) : ℝ :=
  (1 - 2 * α) * ((1 - α) * (1 - 3 * α) - Real.sqrt ((1 - 3 * α) * cubic0 α)) /
    (2 * (1 - 3 * α) * (2 - 5 * α))

/-- `k^(0)_2(α)` (footnote 12, PDF p. 14). -/
def k0₂ (α : ℝ) : ℝ :=
  (1 - 2 * α) * ((1 - α) * (1 - 3 * α) + Real.sqrt ((1 - 3 * α) * cubic0 α)) /
    (2 * (1 - 3 * α) * (2 - 5 * α))

/-- `k^(BC)_1(α)` (footnote 13, PDF p. 15). -/
def kBC₁ (α : ℝ) : ℝ :=
  ((1 - α) * (1 - 2 * α) - Real.sqrt ((1 - α) * (1 - 2 * α) * (26 * α ^ 2 - 11 * α + 1))) /
    (4 * (1 - 3 * α))

/-- `k^(BC)_2(α)` (footnote 13, PDF p. 15). -/
def kBC₂ (α : ℝ) : ℝ :=
  ((1 - α) * (1 - 2 * α) + Real.sqrt ((1 - α) * (1 - 2 * α) * (26 * α ^ 2 - 11 * α + 1))) /
    (4 * (1 - 3 * α))

/-- `α^(BC)_1 = (11 - √17)/52 ≈ 0.1322` (proof of Lemma 4, PDF p. 47). -/
def αBC₁ : ℝ := (11 - Real.sqrt 17) / 52

/-- `k^(AB)_1(α)` (footnote 14, PDF p. 16). -/
def kAB₁ (α : ℝ) : ℝ :=
  ((1 - α) * (1 - 2 * α) - Real.sqrt ((1 - α) * (1 - 2 * α) * (14 * α ^ 2 - 7 * α + 1))) /
    (2 * (1 - 3 * α))

/-- `Ω^(0)_1 = {(α,k) | 0 < α < α^(0)_1, k^(0)_1 < k < k^(0)_2}`, with `α^(0)_1` passed as the
parameter `α₁` (footnote 12, PDF p. 14). -/
def Omega0₁ (α₁ α k : ℝ) : Prop := 0 < α ∧ α < α₁ ∧ k0₁ α < k ∧ k < k0₂ α

/-- `Ω^(0)_2 = {(α,k) | (α,k) ∉ Ω^(0)_1, 0 < α < 1/3, α < k < 1 - 2α}` (footnote 12). -/
def Omega0₂ (α₁ α k : ℝ) : Prop :=
  ¬ Omega0₁ α₁ α k ∧ 0 < α ∧ α < 1 / 3 ∧ α < k ∧ k < 1 - 2 * α

/-- `Ω^(BC)_1 = {(α,k) | 0 < α < α^(BC)_1, k^(BC)_1 < k < k^(BC)_2}` (footnote 13, PDF p. 15). -/
def OmegaBC₁ (α k : ℝ) : Prop := 0 < α ∧ α < αBC₁ ∧ kBC₁ α < k ∧ k < kBC₂ α

/-- `Ω^(BC)_2 = {(α,k) | (α,k) ∉ Ω^(BC)_1, 0 < α < 1/3, α < k < (1-α)/2}` (footnote 13). -/
def OmegaBC₂ (α k : ℝ) : Prop :=
  ¬ OmegaBC₁ α k ∧ 0 < α ∧ α < 1 / 3 ∧ α < k ∧ k < (1 - α) / 2

/-- `Ω^(BC)_3 = {(α,k) | 0 < α < 1/3, (1-α)/2 ≤ k < 1 - 2α}` (footnote 13). -/
def OmegaBC₃ (α k : ℝ) : Prop := 0 < α ∧ α < 1 / 3 ∧ (1 - α) / 2 ≤ k ∧ k < 1 - 2 * α

/-- `Ω^(AB)_1 = {(α,k) | 0 < α < 1/3, k^(AB)_1 ≤ k < 1 - 2α}` (footnote 14, PDF p. 16). -/
def OmegaAB₁ (α k : ℝ) : Prop := 0 < α ∧ α < 1 / 3 ∧ kAB₁ α ≤ k ∧ k < 1 - 2 * α

/-- `Ω^(AB)_2 = {(α,k) | 0 < α < 1/3, α < k < k^(AB)_1}` (footnote 14). -/
def OmegaAB₂ (α k : ℝ) : Prop := 0 < α ∧ α < 1 / 3 ∧ α < k ∧ k < kAB₁ α

end

end EndogMerger.SymLoyal


