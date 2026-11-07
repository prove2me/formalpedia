-- Prove2me | Definitions.Def_CompNonlocal_ASP
-- name    : CompNonlocal_ASP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:43:08.401876+00:00
-- url     : https://prove2.me/theorems/9fd036dd-7c31-4c00-86f8-e782dc5655fc
-- title:
--   QCCC asymmetric state preparation: syntax
-- statement:
--   An ASP protocol has three algorithms: the sender $\mathrm{Sen}(1^\kappa)\to(\mathrm{msg}_S,\mathrm{st}_S)$ (classical message, possibly quantum retained state), the receiver $\mathrm{Rec}(\mathrm{msg}_S)\to(\mathrm{msg}_R,\zeta)$ (classical reply, a designated retained qubit $Q$), and the decoder $\mathrm{Dec}(\mathrm{st}_S,\mathrm{msg}_S,\mathrm{msg}_R)\to\hat r_S$. Derived: the sender's unnormalized state per message, the receiver's unnormalized qubit per transcript, the decoder's output probabilities, and the Bloch vector $r(t)$ of the normalized prepared state $\zeta_t=\nu(r(t))$.
-- source:
--   Głuch, Morimae, From Computational Nonlocality to Public-Key Encryption and Commitments, manuscript (STOC 2027 submission, sha256 e245edd7…), Definition 14, p.33

import Mathlib
import Definitions.Def_CompNonlocal_Family
import Definitions.Def_CompNonlocal_ICirc_branchOn
import Definitions.Def_CompNonlocal_ICirc_effectOn
import Definitions.Def_CompNonlocal_toQubit
import Definitions.Def_CompNonlocal_blochVec

set_option autoImplicit false

namespace CompNonlocal

open QAlgorithms.Complexity

/-- QCCC asymmetric state preparation (ASP) protocols: the syntax. Głuch, Morimae, *From
Computational Nonlocality to Public-Key Encryption and Commitments*, manuscript (STOC 2027
submission, sha256 e245edd7…), Definition 14, p.33: "ASP.Sen(1^κ) → (msg_S, st_S): The QPT sender
outputs a classical message msg_S and retains a private state st_S on a register S …
ASP.Rec(msg_S) → (msg_R, ζ): The QPT receiver outputs a classical message msg_R and retains a
designated qubit register Q in the prepared state ζ … ASP.Dec(st_S, msg_S, msg_R) → r̂_S: The QPT
decoder uses the sender's retained state st_S and outputs a vector r̂_S ∈ B³."

The derived functions in this module, at security parameter `κ`: `senState κ mS`, the sender's
unnormalized retained state after sending `mS` (trace `Pr[msg_S = mS]`); `prepared κ mS mR`, the
receiver's unnormalized qubit after replying `mR` (trace `Pr[msg_R = mR | msg_S = mS]`); `decProb κ mS mR d`,
the probability that the sender sends `mS` and its decoder outputs `d` on transcript `(mS, mR)`;
`prepBloch κ mS mR`, the Bloch vector `r(t)` of the normalized prepared state `ζ_t` (Definition 14:
"ζ_t = ν(r(t))").

**Formalization Note** `qw κ` is the receiver's designated qubit wire `Q`; `IsASP` requires every
other wire of `Rec κ` to be measured into `msg_R`. The decoder reads `mS ++ mR` and `st_S`. -/
structure ASP where
  /-- The sender `ASP.Sen`. -/
  Sen : Family
  /-- The receiver `ASP.Rec`. -/
  Rec : Family
  /-- The decoder `ASP.Dec`. -/
  Dec : Family
  /-- The receiver's designated qubit wire `Q`. -/
  qw : (κ : ℕ) → Fin (Rec κ).width

namespace ASP

/-- The sender's unnormalized retained state after sending `mS`. -/
noncomputable def senState (P : ASP) (κ : ℕ) (mS : Str) :
    Matrix (Bits (P.Sen κ).outQ.length) (Bits (P.Sen κ).outQ.length) ℂ :=
  (P.Sen κ).branchOn 0 [] 1 (fun t => decide (t = mS))

/-- The receiver's unnormalized prepared qubit after replying `mR` to `mS`. -/
noncomputable def prepared (P : ASP) (κ : ℕ) (mS mR : Str) : Matrix Bool Bool ℂ :=
  toQubit ((P.Rec κ).branchWires (fun _ : Fin 1 => P.qw κ) 0 mS 1 (fun t => decide (t = mR)))

/-- The probability that the sender sends `mS` and the decoder outputs `d` on `(mS, mR)`. -/
noncomputable def decProb (P : ASP) (κ : ℕ) (mS mR d : Str) : ℝ :=
  ((P.Dec κ).effectOn (P.Sen κ).outQ.length (mS ++ mR) (fun t => decide (t = d)) *
    P.senState κ mS).trace.re

/-- The Bloch vector `r(t)` of the normalized prepared state at transcript `t = (mS, mR)`. -/
noncomputable def prepBloch (P : ASP) (κ : ℕ) (mS mR : Str) : EuclideanSpace ℝ (Fin 3) :=
  ((P.prepared κ mS mR).trace.re)⁻¹ • blochVec (P.prepared κ mS mR)

end ASP

end CompNonlocal


