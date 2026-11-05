-- Prove2me | Definitions.Def_RotationLadder_Protocol_accuracy
-- name    : RotationLadder_Protocol_accuracy
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:34:18.145106+00:00
-- url     : https://prove2.me/theorems/0737f798-d74a-47fd-91bf-74717e9c4620
-- title:
--   Accuracy $\max_\psi D(U\psi\psi^\dagger U^\dagger,V\psi\psi^\dagger V^\dagger)$ of an applied gate
-- statement:
--   The accuracy of an applied gate $V$ against a target $U$ is
--
--   $$\max_{|\psi\rangle}\;D\bigl(U|\psi\rangle\langle\psi|U^\dagger,\;V|\psi\rangle\langle\psi|V^\dagger\bigr),$$
--
--   where the maximum is over unit vectors and $D(\rho,\sigma)=\tfrac12\operatorname{tr}\sqrt{(\rho-\sigma)^\dagger(\rho-\sigma)}$ is the trace distance.
--
--   **Formalization Note** The maximum is a supremum over the subtype of unit vectors.
-- source:
--   Duclos-Cianci, Svore, A State Distillation Protocol to Implement Arbitrary Single-qubit Rotations, arXiv:1210.1980v1, Sec. III, unnumbered, p. 4

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_CommitOpen_Benign_Model

namespace RotationLadder.Protocol

/-- **The accuracy of an applied gate.**
Duclos-Cianci, Svore, *A State Distillation Protocol to Implement Arbitrary Single-qubit Rotations*,
arXiv:1210.1980v1, Sec. III, unnumbered, p. 4: "`max_|ψ⟩ D(U|ψ⟩⟨ψ|U†, V|ψ⟩⟨ψ|V†)`, where
`D(ρ, σ) = ½ tr √((ρ-σ)†(ρ-σ))` is the trace distance".

**Formalization Note.** The supremum ranges over unit vectors only, as a subtype, so it is the
supremum of a nonempty family. The trace distance is the platform's
`CommitOpen.Benign.traceDistance`, `½ tr √((ρ-σ)†(ρ-σ))`. -/
noncomputable def accuracy (U V : Matrix Bool Bool ℂ) : ℝ :=
  ⨆ ψ : {ψ : EuclideanSpace ℂ Bool // ‖ψ‖ = 1},
    CommitOpen.Benign.traceDistance
      (CommitOpen.Benign.pureState (QAlgorithms.act U ψ.1))
      (CommitOpen.Benign.pureState (QAlgorithms.act V ψ.1))

end RotationLadder.Protocol


