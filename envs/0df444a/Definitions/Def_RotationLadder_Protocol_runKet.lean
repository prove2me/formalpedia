-- Prove2me | Definitions.Def_RotationLadder_Protocol_runKet
-- name    : RotationLadder_Protocol_runKet
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:36:44.680577+00:00
-- url     : https://prove2.me/theorems/0d1a46b6-1705-4327-87d2-244555f4f29d
-- title:
--   The state of the data qubit during a run
-- statement:
--   Fix a rule, a target $\varphi$, an input $\psi$ and outcomes $\omega$. Set $\psi_0=\psi$. At step $t$, with $i=\mathrm{pick}(r_t)$, run Fig. 1 with resource $|Z(2\theta_i)\rangle$ on the first wire and $\psi_t$ on the second, and let the first wire read $\omega_t$. If $i=0$ and $(-1)^{\omega_t}\ne\operatorname{sign}(r_t)$, then follow with the Clifford correction $Z(\operatorname{sign}(r_t)\,\pi/2)$, which is $S$ or $S^\dagger$. The result is $\psi_{t+1}$.
--
--   **Formalization Note** The vector is unnormalized, so its squared norm is the probability of the outcomes seen so far.
-- source:
--   Duclos-Cianci, Svore, A State Distillation Protocol to Implement Arbitrary Single-qubit Rotations, arXiv:1210.1980v1, Sec. I, unnumbered, p. 2 and Sec. III, unnumbered, pp. 3-4

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_RotationLadder_Protocol_cnotSecond
import Definitions.Def_RotationLadder_Protocol_ketZ
import Definitions.Def_RotationLadder_Protocol_postOut
import Definitions.Def_RotationLadder_Protocol_residual
import Definitions.Def_RotationLadder_Protocol_zRot

namespace RotationLadder.Protocol

/-- **The circuit executed by a run.**
Duclos-Cianci, Svore, *A State Distillation Protocol to Implement Arbitrary Single-qubit Rotations*,
arXiv:1210.1980v1, Sec. III, p. 4, step 5: "Apply a rotation using the `|H_i⟩` state and the circuit of Fig. 1";
Sec. I, p. 2 and Sec. III, p. 3 for the correction at level `0`.

`runKet pick φ ψ ω t` is the unnormalized state of the data qubit after `t` steps on input `ψ` with
outcomes `ω`. At step `t`, with `r = r_t` and `i = pick r`, Fig. 1 is run with the resource
`|Z(2θ_i)⟩` on the first wire and the data on the second, and the first wire reads `ω t`. If `i = 0`
and the rotation that happened is the wrong one, `(-1)^(ω t) ≠ sign r`, the Clifford correction
`Z(sign(r) π/2)`, that is `S` or `S†`, follows.

**Formalization Note.** The state is the unnormalized post-measurement vector, so its squared norm
is the probability of the outcomes `ω 0, …, ω (t-1)`. -/
noncomputable def runKet (pick : ℝ → ℕ) (φ : ℝ) (ψ : EuclideanSpace ℂ Bool) (ω : Coins) :
    ℕ → EuclideanSpace ℂ Bool
  | 0 => ψ
  | t + 1 =>
    if pick (residual pick φ ω t) = 0 ∧
        (if ω t then (-1 : ℝ) else 1) ≠ Real.sign (residual pick φ ω t) then
      QAlgorithms.act (zRot (Real.sign (residual pick φ ω t) * (Real.pi / 2)))
        (postOut (ω t) (QAlgorithms.act cnotSecond
          (QAlgorithms.tensorVec (ketZ (angle (pick (residual pick φ ω t))))
            (runKet pick φ ψ ω t))))
    else
      postOut (ω t) (QAlgorithms.act cnotSecond
        (QAlgorithms.tensorVec (ketZ (angle (pick (residual pick φ ω t))))
          (runKet pick φ ψ ω t)))

end RotationLadder.Protocol


