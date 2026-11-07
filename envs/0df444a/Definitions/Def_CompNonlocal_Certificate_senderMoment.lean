-- Prove2me | Definitions.Def_CompNonlocal_Certificate_senderMoment
-- name    : CompNonlocal_Certificate_senderMoment
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:47:23.451096+00:00
-- url     : https://prove2.me/theorems/77742d38-7359-4df5-88ca-37b145ded267
-- title:
--   Conditional moments $\mathbb E[m_j^k\mid X=x]$
-- statement:
--   For the ideal outcome $m_j$ of measuring $M_j$ on the sender state conditioned on $X=x$,
--   $$\mathbb E[m_j^k\mid X=x]=\operatorname{Tr}(\omega_{S|x}M_j^k).$$
--
--   **Formalization Note** The value when $\Pr[X=x]=0$ is $0$ and is never used.
-- source:
--   Głuch, Morimae, From Computational Nonlocality to Public-Key Encryption and Commitments, manuscript (STOC 2027 submission, sha256 e245edd7…), Lemma 13 and its proof, pp.39–40

import Mathlib
import Definitions.Def_CompNonlocal_Certificate_senderObs
import Definitions.Def_CompNonlocal_Certificate_questionProb

set_option autoImplicit false

namespace CompNonlocal

open QAlgorithms.Complexity

/-- The conditional moments of the ideal outcome `m_j` of measuring the sender observable `M_j` on
the sender's state given `X = x`: `E[m_j^k | X = x] = Tr(ω_{S|x} M_j^k)`. Głuch, Morimae, *From
Computational Nonlocality to Public-Key Encryption and Commitments*, manuscript (STOC 2027
submission, sha256 e245edd7…), Lemma 13, p.39 ("let m_j be the ideal outcome of measuring M_j on the
sender state") and its proof, p.40 ("E[m_j | T = (x, a)] = Tr(ω_{S|x}M_j)", "E[m_j² | T = (x, a)] =
Tr(ω_{S|x}M_j²)").

**Formalization Note** `ω_{S|x}` is block diagonal in the question outcome `o`, so the trace is
`Σ_{o ↦ x} Re Tr(td_o · M_j(o, a)^k) / Pr[X = x]`. The value at `Pr[X = x] = 0` is `0` and is never
used: the statements condition on transcripts of positive probability. -/
noncomputable def Certificate.senderMoment (c : Certificate) (κ : ℕ) (x a : Str) (j : Fin 3)
    (k : ℕ) : ℝ :=
  (∑ o : Bits (c.Qg κ).outC.length,
      if (List.ofFn o).take (c.lx κ) = x then
        (c.td κ (List.ofFn o) * (c.senderObs κ (List.ofFn o) a j) ^ k).trace.re
      else 0) / c.questionProb κ x

end CompNonlocal


