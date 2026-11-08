-- Prove2me | Definitions.Def_MonoidProdQ_advPm
-- name    : MonoidProdQ_advPm
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T04:49:22.502034+00:00
-- url     : https://prove2.me/theorems/3bf60228-bac4-48da-b302-e7dd1403f7fb
-- title:
--   Negative-weight general adversary bound $\mathrm{ADV}^{\pm}(f)$
-- statement:
--   For a function $f$ on a finite promise domain $D\subseteq\Sigma^I$ with finite input alphabet $\Sigma$, the **negative-weight general adversary bound** is
--
--   $$\mathrm{ADV}^{\pm}(f)=\sup_{\Gamma}\ \frac{\|\Gamma\|}{\max_{i\in I}\|\Gamma\circ\Delta_i\|},$$
--
--   the supremum over nonzero adversary matrices $\Gamma$ of $f$, where $\|\cdot\|$ is the spectral norm. It lower-bounds the bounded-error quantum query complexity and, by the general adversary theorem, matches it up to universal constants.
--
--   **Formalization Note** The supremum is taken in $[0,\infty]$, and it is $0$ when $f$ is constant on $D$ (then every adversary matrix is zero). The zero matrix is excluded because its ratio is the undefined $0/0$; for a nonzero adversary matrix the denominator is positive. The construction is the platform's Boolean `QAlgorithms.advPm`, generalized to arbitrary finite input alphabets and output types.
-- source:
--   Lee–Santha, The quantum query complexity of the semigroup product problem, arXiv:2609.39974 (held version, sha256 9eec405d…ffb6), §3, Adversary bounds, p.24

import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_MonoidProdQ_IsAdvMatrix
import Definitions.Def_MonoidProdQ_maskMatrix
open scoped ENNReal

namespace MonoidProdQ

/-- Lee–Santha, *The quantum query complexity of the semigroup product problem*,
arXiv:2609.39974 (held version, sha256 9eec405d…ffb6), §3, "Adversary bounds", p.24: "The supremum of the displayed ratio over all such
matrices Γ is the negative-weight general adversary bound ADV±(f)", the ratio being
`‖Γ‖ / maxᵢ ‖Γ ∘ Δᵢ‖` with spectral norms (`QAlgorithms.specNorm`), over the adversary matrices
`Γ` of `f` on the promise domain `D` (`IsAdvMatrix`).

**Formalization Note.** The supremum is taken in `ℝ≥0∞`, so it is never a junk value. The zero
matrix is excluded (its ratio is the undefined `0/0`); `ADV± = 0` when `f` is constant on `D`
(then every adversary matrix is zero). For `Γ ≠ 0` the denominator is positive: a nonzero entry
`Γ_{xy}` has `f x ≠ f y`, so `x ≠ y` differ at some position `i` and the entry survives in
`Γ ∘ Δᵢ`. The maximum over the finite index set `I` is the real `⨆ i`. Same construction as the
platform's Boolean `QAlgorithms.advPm` (definition 77568192), for arbitrary finite input
alphabets `Sig` and output types. A total function is the case `D = Finset.univ`. -/
noncomputable def advPm {I Sig Out : Type*} [Fintype I] [DecidableEq I] [Fintype Sig]
    [DecidableEq Sig] (f : (I → Sig) → Out) (D : Finset (I → Sig)) : ℝ≥0∞ :=
  ⨆ (Γ : Matrix D D ℝ) (_ : IsAdvMatrix f D Γ ∧ Γ ≠ 0),
    ENNReal.ofReal (QAlgorithms.specNorm Γ / ⨆ i : I, QAlgorithms.specNorm (maskMatrix Γ i))

end MonoidProdQ


