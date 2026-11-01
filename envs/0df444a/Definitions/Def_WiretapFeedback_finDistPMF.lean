-- Prove2me | Definitions.Def_WiretapFeedback_finDistPMF
-- name    : WiretapFeedback_finDistPMF
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T15:23:53.303554+00:00
-- url     : https://prove2.me/theorems/9e7d49db-69f1-4b28-b5ea-135ecbde0f24
-- title:
--   A finite distribution as a probability mass function
-- statement:
--   A probability distribution $p$ on a finite alphabet, given by non-negative real masses $p(x)$ summing to one, is regarded as a probability mass function $x\mapsto p(x)$.
--
--   This is the bridge between the single-letter channel $W(y,z|x)$ (a family of finite distributions) and the joint law of an entire $n$-round protocol, which lives on alphabets that need not be finite (the feedback alphabet and the local randomness are arbitrary).
-- source:
--   Hayashi–Tyagi–Watanabe, Strong Converse for a Degraded Wiretap Channel via Active Hypothesis Testing, arXiv:1410.0443v1, §II, pp.1–2 (the channel W(y, z|x))

import Mathlib
import Definitions.Def_WildeQIT_FinDist

open scoped ENNReal

namespace WiretapFeedback

/-- A probability distribution `p` on a finite alphabet (`WildeQIT.FinDist`) viewed as a Mathlib
probability mass function, `x ↦ p(x)`. It is the bridge between the single-letter channel
`W(y, z|x)` of Hayashi–Tyagi–Watanabe, arXiv:1410.0443v1, §II, p. 1–2, and the `PMF`-valued law
of a whole transmission protocol.

**Formalization Note** The masses are `ENNReal.ofReal (p.prob x)`; they sum to one because the
`p.prob x` are non-negative reals summing to one. -/
noncomputable def finDistPMF {α : Type} [Fintype α] (p : WildeQIT.FinDist α) : PMF α :=
  PMF.ofFintype (fun x => ENNReal.ofReal (p.prob x)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun x _ => p.nonneg x), p.sum_eq_one, ENNReal.ofReal_one])

end WiretapFeedback


