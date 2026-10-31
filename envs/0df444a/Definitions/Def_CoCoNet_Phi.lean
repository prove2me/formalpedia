-- Prove2me | Definitions.Def_CoCoNet_Phi
-- name    : CoCoNet_Phi
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:26:42.419667+00:00
-- url     : https://prove2.me/theorems/f3602097-b12c-4a78-84e6-3f7b8c0997bf
-- title:
--   The map $\Phi$ from stock prices to asset values
-- statement:
--   Fix a network $(m,W)$, thresholds $l$ and credit amounts $c$. For $s\in\mathbb R^n$ let $(B,C,H)=(B(s),C(s),H(s))$ be the partition read off $s$ ($s_i<0$; $0\le s_i\le l_i$; $s_i>l_i$). Then
--   $$\Phi(s)=L_{B,C}\,s+(I-W)\,c_H=s+\mathrm{Diag}(m_B)s+(I-W)\mathrm{Diag}(m_C)s+(I-W)c_H. \tag{3}$$
--   By Lemma 1, $\Phi(s)$ is the unique asset vector that rationalises the prices $s$ in equilibrium; existence of an equilibrium for every asset vector is surjectivity of $\Phi$.
--
--   **Formalization Note** The credit vector is a parameter: the fair map of §3.2 is $\Phi$ with $l_i=c_i/m_i$, and the super-fair map $\hat\Phi$ of §3.3 is the same formula with smaller credit amounts $\hat c$.
-- source:
--   Balter, Schweizer & Vera, Contingent Capital with Stock Price Triggers in Interbank Networks, arXiv:2011.06474v1, §2, p.11, equation (3); §3.1, p.12, (4) and 'Φ is defined as Φ(s) = L_{B,C}s + b_H for s ∈ S_{B,C,H}'

import Mathlib
import Definitions.Def_CoCoNet_restrictTo
import Definitions.Def_CoCoNet_bankrupt
import Definitions.Def_CoCoNet_converting
import Definitions.Def_CoCoNet_healthy
import Definitions.Def_CoCoNet_Lmat
open Matrix

namespace CoCoNet

/-- **The map `Φ` from stock prices to asset values.**
Balter, Schweizer & Vera, arXiv:2011.06474v1, §2, p.11, (3): "For a given partition (B, C, H),
conditions (1) and (2) can be summarized as a = s + Diag(m_B)s + (I − W) Diag(m_C)s + (I − W)c_H";
§3.1, p.12: "Φ is defined as Φ(s) = L_{B,C}s + b_H for s ∈ S_{B,C,H}", where
S_{B,C,H} = {s | sᵢ < 0 for i ∈ B, 0 ≤ sᵢ ≤ lᵢ for i ∈ C and sᵢ > lᵢ for i ∈ H}.

`Phi m W l c s = L_{B,C} s + (I − W) c_H` with `(B, C, H)` read off `s` (`bankrupt s`,
`converting l s`, `healthy l s`).

**Formalization Note.** The credit vector `c` is a parameter: the fair map of §3.2 is
`Phi m W l c` with `lᵢ = cᵢ/mᵢ`; the super-fair map `Φ̂` of §3.3 is the same formula with the
smaller credit amounts `ĉ`. -/
noncomputable def Phi {n : ℕ} (m : Fin n → ℝ) (W : Matrix (Fin n) (Fin n) ℝ) (l c : Fin n → ℝ)
    (s : Fin n → ℝ) : Fin n → ℝ :=
  Lmat m W (bankrupt s) (converting l s) *ᵥ s + (1 - W) *ᵥ restrictTo (healthy l s) c

end CoCoNet


