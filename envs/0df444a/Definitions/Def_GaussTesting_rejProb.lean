-- Prove2me | Definitions.Def_GaussTesting_rejProb
-- name    : GaussTesting_rejProb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:59:32.093759+00:00
-- url     : https://prove2.me/theorems/4df0ef97-7413-4f10-b8b7-a3e2a5e5a9b1
-- title:
--   Rejection probability $q(\psi)=1-\mathrm{tr}(\Pi_{\mathrm{test}}\psi^{\otimes k})$
-- statement:
--   For a projective test $\Pi_{\mathrm{test}}=\Pi_K$ on $\mathcal H^{\otimes k}$ and a pure state $\psi$, the rejection probability is
--
--   $$
--   q(\psi)=1-\mathrm{tr}\big(\Pi_{\mathrm{test}}\,\psi^{\otimes k}\big)=1-\langle\psi^{\otimes k}|\Pi_{\mathrm{test}}|\psi^{\otimes k}\rangle .
--   $$
--
--   Soundness statements bound $q(\psi)$ from below by a multiple of $\mathrm{dist}(\psi,\mathcal C)^2$.
-- source:
--   Iyer, O'Gorman, Parekh, Thompson, Zhao, Optimal testing of fermionic and bosonic Gaussian states, arXiv:2609.39113 (sha256 6683e57b…), §3, p.21

import Definitions.Def_GaussTesting_tpow
import Definitions.Def_GaussTesting_proj

namespace GaussTesting

/-- The rejection probability of the projective test `Π_test = Π_K` on `k` copies,
`q(ψ) = 1 − tr(Π_test ψ^{⊗k}) = 1 − ⟨ψ^{⊗k}| Π_test |ψ^{⊗k}⟩`.

Source: Iyer, O'Gorman, Parekh, Thompson, Zhao, *Optimal testing of fermionic and bosonic Gaussian states*, arXiv:2609.39113 (sha256 6683e57b…), §3, p.21 ("let `q(ψ) := 1 − tr(Π_test ψ^{⊗k})` be the rejection probability of
the test").

**Formalization Note.** `ψ` denotes the density operator `|ψ⟩⟨ψ|` in the paper, so the trace is the
expectation value in the vector `ψ^{⊗k}`. -/
noncomputable def rejProb {ι : Type*} {k : ℕ} (K : ClosedSubmodule ℂ (Ell2 (Fin k → ι)))
    (ψ : Ell2 ι) : ℝ :=
  1 - (inner ℂ (tpow k ψ) (proj K (tpow k ψ))).re

end GaussTesting


