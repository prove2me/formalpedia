-- Prove2me | Definitions.Def_RobustDP_ChiSquare_L1Set
-- name    : RobustDP_ChiSquare_L1Set
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T06:36:23.313983+00:00
-- url     : https://prove2.me/theorems/d90850d8-c645-44ba-9e96-abeb8d654ed6
-- title:
--   The $L_1$ set $\{p\in\mathcal M(\mathcal S): \|p-q\|_1\le c\}$ of Section 4.3
-- statement:
--   Let $\mathcal S$ be a finite set, $\mathcal M(\mathcal S)$ the probability measures on $\mathcal S$, $q\in\mathcal M(\mathcal S)$ and $c\in\mathbb R$. The **$L_1$ set** around $q$ of radius $c$ is
--
--   $$
--   \mathcal P_1=\Big\{p\in\mathcal M(\mathcal S):\ \|p-q\|_1=\sum_{s\in\mathcal S}|p(s)-q(s)|\le c\Big\}.
--   $$
--
--   With $c=\sqrt{2\ln(2)\,t}$ this is the set (55)–(56) of Iyengar's Section 4.3, an outer approximation of the relative-entropy confidence region.
--
--   **Formalization Note** The page writes (55) as $\{p:\|p-q\|_1\le\sqrt{2\ln(2)t}\}$ without the condition $p\in\mathcal M(\mathcal S)$. The proof of Lemma 6 uses $\sum_s y(s)=0$ and $y\ge -q$ for $y=p-q$, i.e. it reads $p$ as a probability measure, and the sentence before (55) calls $p,q$ measures in $\mathcal M(\mathcal S)$; the definition follows that reading.
-- source:
--   Iyengar, Robust dynamic programming, CORC Tech Report TR-2002-07 (rev. May 4, 2004), pp. 19–20, eqs. (55)–(56)

import Mathlib

namespace RobustDP.ChiSquare

/-- The `L₁` set of conditional measures of §4.3 (Iyengar, TR-2002-07, pp. 19–20, (55)–(56)),
restricted to probability measures as its use in the proof of Lemma 6 requires:
`{p ∈ M(S) : ‖p − q‖₁ ≤ c}`, with `‖p − q‖₁ = ∑_{s ∈ S} |p(s) − q(s)|`. -/
def l1Set {S : Type*} [Fintype S] (q : S → ℝ) (c : ℝ) : Set (S → ℝ) :=
  {p | p ∈ stdSimplex ℝ S ∧ ∑ s, |p s - q s| ≤ c}

end RobustDP.ChiSquare


