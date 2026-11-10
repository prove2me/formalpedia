-- Prove2me | Definitions.Def_QPSpinProfile_SatisfiesDistortion
-- name    : QPSpinProfile_SatisfiesDistortion
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T03:25:34.240221+00:00
-- url     : https://prove2.me/theorems/f0a5c1a1-fc66-4dd9-9b4c-6650e0128815
-- title:
--   Trace-norm comparison (9) for a one-qubit POVM
-- statement:
--   Let $\{M_z:z\in Z\}$ be a one-qubit POVM with measurement map $\mathcal M(X)=\sum_z\operatorname{Tr}(M_zX)\,|z\rangle\langle z|_{\mathrm{cl}}$, the labels $|z\rangle_{\mathrm{cl}}$ being orthonormal. It **satisfies (9) with constant $\kappa_{\mathcal M}$** if
--   $$
--   \|\xi\|_1\le\kappa_{\mathcal M}\,\|(\mathrm{Id}_R\otimes\mathcal M)(\xi)\|_1
--   $$
--   for every finite-dimensional system $R$ and every Hermitian operator $\xi$ on $R\otimes\mathbb C^2$, where $\|A\|_1=\operatorname{Tr}\sqrt{A^\dagger A}$ and $\kappa_{\mathcal M}<\infty$ does not depend on $R$.
--
--   This is the hypothesis under which the conditioning construction of Lemma 2.2 works; Lemma 2.1 shows the Pauli POVM satisfies it with $\kappa=4$.
--
--   **Formalization Note** $R$ ranges over all finite types; $(\mathrm{Id}_R\otimes\mathcal M)(\xi)$ is the published `DeFinettiSDP.Hierarchy.measB`, the block-diagonal operator whose block $z$ is $\operatorname{Tr}_B[(I_R\otimes M_z)\xi]$. No condition on the partial traces of $\xi$ is imposed.
-- source:
--   Al-Ghattas, Gamarnik, Kiani, Beyond light cones: State preparation complexity in quantum spin glasses, arXiv:2610.02166 (held version, sha256 a0a1ec89…), §2.1.1, p.15 (PDF p.18), display (9)

import Mathlib
import Definitions.Def_WildeQIT_traceNorm
import Definitions.Def_DeFinettiSDP_Hierarchy_Systems

namespace QPSpinProfile

/-- The trace-norm comparison (9) for a one-qubit POVM `{M_z}` with measurement map `M`
(arXiv:2610.02166, held version sha256 a0a1ec89…, §2.1.1, p.15, PDF p.18):
`‖ξ‖₁ ≤ κ_M ‖(Id_R ⊗ M)(ξ)‖₁` for every finite-dimensional system `R` and every Hermitian
operator `ξ` on `R ⊗ ℂ²`, with a constant `κ_M` independent of `R`.

**Formalization Note** `R` ranges over every finite type; `(Id_R ⊗ M)(ξ)` is the published
`DeFinettiSDP.Hierarchy.measB M ξ` (block diagonal with orthonormal classical labels, block `z`
equal to `Tr_B[(I_R ⊗ M_z) ξ]`), and `‖·‖₁` is `WildeQIT.traceNorm`. Unlike the published
`DeFinettiSDP.Hierarchy.distortion`, no condition on the partial traces of `ξ` is imposed. -/
def SatisfiesDistortion {t : ℕ} (M : Fin t → Matrix (Fin 2) (Fin 2) ℂ) (κ : ℝ) : Prop :=
  ∀ (R : Type) [Fintype R] [DecidableEq R] (ξ : Matrix (R × Fin 2) (R × Fin 2) ℂ),
    ξ.IsHermitian → WildeQIT.traceNorm ξ ≤ κ * WildeQIT.traceNorm (DeFinettiSDP.Hierarchy.measB M ξ)

end QPSpinProfile


