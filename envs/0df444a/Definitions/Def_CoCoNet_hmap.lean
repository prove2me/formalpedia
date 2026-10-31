-- Prove2me | Definitions.Def_CoCoNet_hmap
-- name    : CoCoNet_hmap
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:28:27.701398+00:00
-- url     : https://prove2.me/theorems/29e1621a-4518-4f8e-8c3a-eefaceae22af
-- title:
--   The set map $h(X)=H(\hat a+(I-W)d_X)$
-- statement:
--   Fix an asset vector $\hat a\in\mathbb R^n$ and a vector of credit reductions $d\in\mathbb R^n_+$. For a set of banks $X\subseteq[n]$ let
--   $$h(X)=H\big(\hat a+(I-W)d_X\big),$$
--   the banks healthy in the fair case after shifting $\hat a$ by the vectors $(I-W)d_{\{j\}}$ of the banks $j\in X$. Iterates are $h^0(X)=X$, $h^{k+1}(X)=h(h^k(X))$. A fixed point $h(X)=X$ yields an equilibrium of the super-fair case (Lemma 2, Theorem 1).
--
--   **Formalization Note** Iterates are `Nat.iterate`, written `h^[k]`.
-- source:
--   Balter, Schweizer & Vera, Contingent Capital with Stock Price Triggers in Interbank Networks, arXiv:2011.06474v1, §3.3, p.22

import Mathlib
import Definitions.Def_CoCoNet_restrictTo
import Definitions.Def_CoCoNet_Hfair
open Matrix

namespace CoCoNet

/-- **The set map `h(X) = H(â + (I − W)d_X)`.**
Balter, Schweizer & Vera, arXiv:2011.06474v1, §3.3, p.22: "for the remainder of this section, we
fix some â ∈ ℝⁿ and define the mapping h(X) = H(â + (I − W)d_X), X ⊂ [n]. … given X ⊂ [n] we
define h⁰(X) = X and h^{m+1}(X) = h(h^m(X)) for all m ≥ 0."

Here `d ∈ ℝⁿ₊` is the credit reduction from the fair to the super-fair case (p.19) and `H` is
`Hfair`. The iterates `h^m` are `(hmap m W l d ahat)^[k]` (`Nat.iterate`). -/
noncomputable def hmap {n : ℕ} (m : Fin n → ℝ) (W : Matrix (Fin n) (Fin n) ℝ) (l d ahat : Fin n → ℝ)
    (X : Finset (Fin n)) : Finset (Fin n) :=
  Hfair m W l (ahat + (1 - W) *ᵥ restrictTo X d)

end CoCoNet


