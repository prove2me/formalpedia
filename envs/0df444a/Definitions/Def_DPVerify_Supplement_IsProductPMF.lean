-- Prove2me | Definitions.Def_DPVerify_Supplement_IsProductPMF
-- name    : DPVerify_Supplement_IsProductPMF
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T03:56:57.30939+00:00
-- url     : https://prove2.me/theorems/87e0c3bf-3632-4adc-8e28-992efce2500a
-- title:
--   Product distributions on $A_1\times\cdots\times A_d$ and their marginals
-- statement:
--   Let $\mathcal X=A_1\times\cdots\times A_d$ with finite nonempty coordinate sets $A_i$. A distribution $D$ on $\mathcal X$ is a **product distribution** if there are distributions $D_i$ on $A_i$ with
--   $$D(x_1,\dots,x_d)=\prod_{i=1}^d D_i(x_i)\qquad\text{for all }x\in\mathcal X .$$
--   The **$i$-th marginal** of $D$ is $D^{(i)}(a)=\Pr_{x\sim D}[x_i=a]$, $a\in A_i$. With the total variation distance $\mathrm{TV}(P,Q)=\tfrac12\sum_x|P(x)-Q(x)|$ (the published `TTTSampling.tvDist`, referenced by Theorem 5.1),
--   $D$ is **$\sigma$-far from any product distribution** if $\mathrm{TV}(D,Q)\ge\sigma$ for every product distribution $Q$ on $\mathcal X$.
--
--   These are the objects of §5 (independence testing): Theorem 5.1's honest prover sends the exact marginals, and its soundness hypothesis is $\sigma$-farness from every product distribution.
--
--   **Formalization Note** $A_i$ is `Fin (n i)` (any finite set is a relabelling of one) and distributions are `PMF`s; marginals are extended nonnegative reals.
-- source:
--   Du, Dwork, Tankala, Zhang, Differentially Private Verification of Distribution Properties, arXiv:2604.10819 (version of November 3, 2026, sha256 0146fa5f…), §5, p.19 (PDF p.22) and Theorem 5.1, p.20 (PDF p.23)

import Mathlib

set_option autoImplicit false

open scoped ENNReal

namespace DPVerify.Supplement

/-- A distribution `D` on the product domain `X = A₁ × ⋯ × A_d`, `A_i = Fin (n i)`, is a
**product distribution** (Du, Dwork, Tankala, Zhang, *Differentially Private Verification of
Distribution Properties*, arXiv:2604.10819 (version of November 3, 2026, sha256 0146fa5f…), §5,
p.19 = PDF p.22): `D = ⊗ᵢ D_i` for distributions `D_i` on `A_i`, i.e.
`D(x) = ∏ᵢ D_i(x_i)` for every `x`.

**Formalization Note** The finite coordinate sets `A_i` are `Fin (n i)` (any finite set is a
relabelling of one), distributions are `PMF`s. -/
def IsProductPMF {d : ℕ} {n : Fin d → ℕ} (D : PMF ((i : Fin d) → Fin (n i))) : Prop :=
  ∃ q : (i : Fin d) → PMF (Fin (n i)), ∀ x, D x = ∏ i, q i (x i)

/-- The `i`-th marginal of `D`: `D^{(i)}(a) = Pr_{x ∼ D}[x_i = a]`. -/
noncomputable def marginal {d : ℕ} {n : Fin d → ℕ} (D : PMF ((i : Fin d) → Fin (n i)))
    (i : Fin d) (a : Fin (n i)) : ℝ≥0∞ :=
  ∑ x ∈ Finset.univ.filter (fun x : (j : Fin d) → Fin (n j) => x i = a), D x

end DPVerify.Supplement


