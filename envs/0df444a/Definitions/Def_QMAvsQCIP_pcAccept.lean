-- Prove2me | Definitions.Def_QMAvsQCIP_pcAccept
-- name    : QMAvsQCIP_pcAccept
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T02:51:26.966982+00:00
-- url     : https://prove2.me/theorems/b75c5171-cb4e-442d-8676-b3837baca798
-- title:
--   Acceptance probability of a public-coin verifier
-- statement:
--   The acceptance probability of a public-coin verifier with oracle $O$ against a deterministic prover $P$: the average, over uniformly random messages $a\in(\{0,1\}^\ell)^R$, of the decision of the final query tree on $(a,b)$ with replies $b_j=P([a_0,\dots,a_j])$.
-- source:
--   Cakan, Separating QMA from QCIP with a Classical Oracle, arXiv:2610.03648 (held version, sha256 687668af…34ec), Section 5, p.23

import Definitions.Def_QMAvsQCIP_PCVerifier
import Definitions.Def_QMAvsQCIP_CTree_run

set_option autoImplicit false

namespace QMAvsQCIP

/-- The **acceptance probability** of the public-coin verifier `V` with oracle `O` against the
deterministic prover `P`: the average over uniformly random messages `a ∈ ({0,1}^ℓ)^R` of the
decision of `dec a b` with the replies `b_j = P([a₀, …, a_j])`.

Cakan, *Separating QMA from QCIP with a Classical Oracle*, arXiv:2610.03648 (held version,
sha256 687668af…34ec), Section 5, p.23 (PDF p.26): "its final computation is deterministic given
the transcript and oracle". -/
noncomputable def pcAccept {Z : Type} {ℓ : ℕ} (V : PCVerifier Z ℓ) (O : Z → Bool)
    (P : BBProver ℓ) : ℝ :=
  (∑ a : Fin V.R → Fin ℓ → Bool,
      if CTree.run O P []
          (V.dec a (fun j => P (((List.finRange V.R).filter (fun k => k.val ≤ j.val)).map a)))
      then (1 : ℝ) else 0) / (2 : ℝ) ^ (V.R * ℓ)

end QMAvsQCIP


