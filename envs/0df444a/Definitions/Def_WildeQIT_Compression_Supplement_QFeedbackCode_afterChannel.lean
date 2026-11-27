-- Prove2me | Definitions.Def_WildeQIT_Compression_Supplement_QFeedbackCode_afterChannel
-- name    : WildeQIT_Compression_Supplement_QFeedbackCode_afterChannel
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T04:02:26.850793+00:00
-- url     : https://prove2.me/theorems/f1aaa42f-654c-4684-9774-5a1d9218e284
-- title:
--   State of a quantum-feedback protocol after each channel use
-- statement:
--   For a protocol for classical communication with quantum feedback (Figure 21.4) and a message $m$, this is the joint state $\omega^{(j+1)}$ of Alice's memory $A'_{j+1}$, the channel output $B_{j+1}$ and Bob's memory $B'_{j+1}$ right after the $(j+1)$-th channel use:
--
--   $$
--   \omega^{(1)}=\mathcal N_{A_1\to B_1}\big(\mathcal E^1(\rho^m_{A'_0}\otimes\tau_{X_0B'_1})\big),\qquad
--   \omega^{(j+1)}=\mathcal N_{A_{j+1}\to B_{j+1}}\big(\mathcal E^{j+1}(\mathcal D^{j}(\omega^{(j)}))\big),
--   $$
--
--   where Bob's decoder $\mathcal D^j$ acts on $B_jB'_j$ and produces the feedback system $X_j$, which is sent noiselessly to Alice, and his next memory $B'_{j+1}$. This is the state of (21.125) together with Alice's memory.
--
--   **Formalization Note** Registers are ordered (Alice's memory × channel system) × Bob's memory. The encoder and $I\otimes\mathcal N$ act on the left factor through the published `WildeQIT.EADamping.leftApply`, the decoder on $B\times B'$ through the published `WildeQIT.EADamping.idTensorApply`, after regrouping the registers.
-- source:
--   Wilde, From Classical to Quantum Shannon Theory, arXiv:1106.1445v8, pp. 605–606, eq. (21.125), Figure 21.4

import Mathlib
import Definitions.Def_WildeQIT_Compression_Supplement_QFeedbackCode
import Definitions.Def_WildeQIT_EADamping_leftApply
import Definitions.Def_WildeQIT_EADamping_idTensorApply

/-!
Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, pp. 605–606, (21.125) and
Figure 21.4 (the state of a quantum-feedback protocol after each channel use).
-/

open Matrix
open scoped Kronecker

namespace WildeQIT.Compression.Supplement

/-- **State after the `(j+1)`-th channel use** of a quantum-feedback protocol, given message `m`
(Wilde, *From Classical to Quantum Shannon Theory*, arXiv:1106.1445v8, pp. 605–606, Figure 21.4,
(21.125)): the joint state of Alice's memory `A′_{j+1}`, the channel output `B_{j+1}` and Bob's
memory `B′_{j+1}`. Round `j + 1` applies Alice's encoder `E^{j+1}` to `A′ⱼXⱼ`, then the channel
`N_{A_{j+1}→B_{j+1}}`; between rounds Bob applies his decoder `D^{j}` to `BⱼB′ⱼ`, producing the
feedback system `Xⱼ` (sent noiselessly to Alice) and his next memory `B′_{j+1}`. The first round
starts from `ρᵐ_{A′₀} ⊗ τ_{X₀B′₁}`.

**Formalization Note.** Registers are ordered `(Alice's memory × channel system) × Bob's memory`.
The encoder and the channel act on the left factor through the published
`WildeQIT.EADamping.leftApply` (the channel as `I_{A′} ⊗ N` on `A′ × A`); the decoder acts on
`B × B′` through the published `WildeQIT.EADamping.idTensorApply`, after regrouping the registers
with `Equiv.prodAssoc`. Noiseless transmission of `Xⱼ` to Alice is the regrouping that puts `Xⱼ`
next to Alice's memory. -/
noncomputable def QFeedbackCode.afterChannel {a b : Type} [Fintype a] [Fintype b]
    [DecidableEq a] [DecidableEq b] {n k : ℕ} (c : QFeedbackCode a b n k) (N : QChannel a b)
    (m : Fin k) : ℕ → Matrix ((Fin c.dA × b) × Fin c.dB) ((Fin c.dA × b) × Fin c.dB) ℂ
  | 0 =>
      WildeQIT.EADamping.leftApply (fun l => (1 : Matrix (Fin c.dA) (Fin c.dA) ℂ) ⊗ₖ N.K l)
        (WildeQIT.EADamping.leftApply (c.enc 0).K
          (Matrix.reindex (Equiv.prodAssoc _ _ _).symm (Equiv.prodAssoc _ _ _).symm
            (c.aliceInit m ⊗ₖ c.bobInit)))
  | j + 1 =>
      WildeQIT.EADamping.leftApply (fun l => (1 : Matrix (Fin c.dA) (Fin c.dA) ℂ) ⊗ₖ N.K l)
        (WildeQIT.EADamping.leftApply (c.enc (j + 1)).K
          (Matrix.reindex (Equiv.prodAssoc _ _ _).symm (Equiv.prodAssoc _ _ _).symm
            (WildeQIT.EADamping.idTensorApply (c.dec j)
              (Matrix.reindex (Equiv.prodAssoc _ _ _) (Equiv.prodAssoc _ _ _)
                (c.afterChannel N m j)))))

end WildeQIT.Compression.Supplement


