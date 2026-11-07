-- Prove2me | Definitions.Def_QMAPlusGap_IsSymSupported
-- name    : QMAPlusGap_IsSymSupported
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T04:07:51.729913+00:00
-- url     : https://prove2.me/theorems/5ac534b1-7abf-4ad5-8339-a266b0120e96
-- title:
--   Operators supported on $\mathrm{Sym}^m(\mathcal H)$
-- statement:
--   An operator $X$ on $\mathcal H^{\otimes m}$ is **supported on $\mathrm{Sym}^m(\mathcal H)$** if
--   $$
--   P^{(m)}_{\mathrm{sym}}X=X=XP^{(m)}_{\mathrm{sym}} .
--   $$
--   For a density operator this is $X\in\mathrm D(\mathrm{Sym}^m(\mathcal H))$, the hypothesis of the de Finetti statements and of Proposition 9.
-- source:
--   Miyamoto, Near-Optimal Gap Amplification for Nonnegative Unentangled Quantum Proofs, arXiv:2608.07986 (held version, sha256 4667925f…), Lemma 11, p.20; Theorem 12, p.25

import Mathlib
import Definitions.Def_QMAPlusGap_symProj

set_option autoImplicit false

namespace QMAPlusGap

/-- An operator `X` on `H^{⊗m}` is **supported on `Sym^m(H)`**, Miyamoto, *Near-Optimal Gap Amplification for Nonnegative Unentangled Quantum Proofs*, arXiv:2608.07986 (held version, sha256 4667925f…) (Lemma 11, p.20; Theorem 12, p.25;
Lemmas 13, 14, A.1, A.3): `P_sym^{(m)} X = X = X P_sym^{(m)}`, i.e. its range and the orthogonal complement of its
kernel lie in the symmetric subspace. For `X` positive semidefinite this is the paper's `X ∈ D(Sym^m(H))` /
"supported on Sym^m(H)". -/
def IsSymSupported {ι : Type} [Fintype ι] [DecidableEq ι] {m : ℕ}
    (X : Matrix (Fin m → ι) (Fin m → ι) ℂ) : Prop :=
  symProj m * X = X ∧ X * symProj m = X

end QMAPlusGap


