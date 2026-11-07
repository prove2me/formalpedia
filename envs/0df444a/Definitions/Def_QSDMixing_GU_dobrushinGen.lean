-- Prove2me | Definitions.Def_QSDMixing_GU_dobrushinGen
-- name    : QSDMixing_GU_dobrushinGen
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:53:58.428058+00:00
-- url     : https://prove2.me/theorems/04b59e71-f511-4c49-98a8-4f973580e7fb
-- title:
--   The generalized quantum Dobrushin coefficient $\kappa_{\mathrm{gen}}(T)$
-- statement:
--   The generalized quantum Dobrushin coefficient is
--
--   $$
--   \kappa_{\mathrm{gen}}(T)=1-\sup_{s\ge1}\frac{1-\kappa(T^s)}{s}.
--   $$
--
--   The quantity $1-\kappa_{\mathrm{gen}}(T)$ is the best contraction per step over multistep blocks. It is the paper's quantum analogue of Wolfer's coefficient for Markov kernels, and it can be below $1$ when $\kappa(T)=1$.
--
--   **Formalization Note** The index $s$ runs over $s\ge1$, as eq. (15) writes it.
-- source:
--   Zhou, Leditzky, A mixing time method for estimating the sample complexity of quantum state discrimination, arXiv:2609.40182 (held version, sha256 62fb68dd…), eq. (52), p.15

import Mathlib
import Definitions.Def_QSDMixing_GU_dobrushin

set_option autoImplicit false

namespace QSDMixing.GU

/-- The generalized quantum Dobrushin coefficient `κ_gen(T) = 1 - sup_{s ∈ ℕ} (1 - κ(T^s)) / s`.

Zhou, Leditzky, *A mixing time method for estimating the sample complexity of quantum state discrimination*, arXiv:2609.40182 (held version, sha256 62fb68dd…), eq. (52), p.15.

**Formalization Note.** `s` ranges over `s ≥ 1`, the only reading under which the quotient makes sense.
`T^[s]` is the `s`-fold iterate. For a linear map sending `D(A)` into itself the quotients lie in `[0, 1]`,
so the supremum is genuine. -/
noncomputable def dobrushinGen {n : Type} [Fintype n] [DecidableEq n]
    (A : StarSubalgebra ℂ (Matrix n n ℂ)) (T : Matrix n n ℂ → Matrix n n ℂ) : ℝ :=
  1 - sSup {r | ∃ s : ℕ, 1 ≤ s ∧ r = (1 - dobrushin A T^[s]) / s}

end QSDMixing.GU


