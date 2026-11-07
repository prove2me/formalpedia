-- Prove2me | Definitions.Def_QMAPlusGap_symProj
-- name    : QMAPlusGap_symProj
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T04:05:56.620851+00:00
-- url     : https://prove2.me/theorems/c1dc4534-87d6-44fc-a349-b700220042a0
-- title:
--   Symmetric-subspace projector $P^{(m)}_{\mathrm{sym}}$
-- statement:
--   For a Hilbert space $\mathcal H=\mathbb C^{\iota}$, the symmetric subspace $\mathrm{Sym}^m(\mathcal H)\subseteq\mathcal H^{\otimes m}$ consists of the vectors invariant under every permutation of the $m$ registers. Its orthogonal projector is
--   $$
--   P^{(m)}_{\mathrm{sym}}=\frac1{m!}\sum_{\pi\in S_m}U_\pi ,
--   $$
--   where $U_\pi$ permutes the tensor factors.
--
--   **Formalization Note** $U_\pi$ is the published `OptimalSpectrum.Entangled.permOp`; the sum is over all of $S_m$, so its orientation convention ($\pi$ or $\pi^{-1}$) does not matter.
-- source:
--   Miyamoto, Near-Optimal Gap Amplification for Nonnegative Unentangled Quantum Proofs, arXiv:2608.07986 (held version, sha256 4667925f…), §2, p.10

import Mathlib
import Definitions.Def_OptimalSpectrum_Entangled_permOp

set_option autoImplicit false

namespace QMAPlusGap

/-- The **symmetric-subspace projector** `P_sym^{(m)} = (1/m!) Σ_{π ∈ S_m} U_π` on `H^{⊗m}`, Miyamoto, *Near-Optimal Gap Amplification for Nonnegative Unentangled Quantum Proofs*, arXiv:2608.07986 (held version, sha256 4667925f…), §2, p.10:
"The subspace of H^{⊗m} invariant under every permutation of the m registers is denoted by Sym^m(H), and its
orthogonal projector is P_sym^{(m)} = (1/m!) Σ_{π∈S_m} U_π".

**Formalization Note** `H = ℂ^ι` and `H^{⊗m}` has the basis `Fin m → ι` (register `r` holds `a r`). `U_π` is
the published `OptimalSpectrum.Entangled.permOp` (`|a⟩ ↦ |a ∘ π⁻¹⟩`); the sum runs over all of `S_m`, so the
orientation convention does not matter. -/
noncomputable def symProj {ι : Type} [DecidableEq ι] (m : ℕ) : Matrix (Fin m → ι) (Fin m → ι) ℂ :=
  ((m.factorial : ℂ)⁻¹) • ∑ π : Equiv.Perm (Fin m), OptimalSpectrum.Entangled.permOp (ι := ι) π

end QMAPlusGap


