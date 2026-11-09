-- Prove2me | Definitions.Def_ChanTomoNB_choi
-- name    : ChanTomoNB_choi
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T11:28:02.71421+00:00
-- url     : https://prove2.me/theorems/a477982b-4e26-4eb1-bc7b-8576080fc203
-- title:
--   Choi operator $C_{\mathcal E}=(\mathcal E\otimes I)(|I\rangle\!\rangle\langle\!\langle I|)$
-- statement:
--   For a superoperator $\mathcal E:L(\mathbb C^{d_1})\to L(\mathbb C^{d_2})$, the Choi–Jamiołkowski operator is
--   $$
--   C_{\mathcal E}=(\mathcal E\otimes I)(|I\rangle\!\rangle\langle\!\langle I|)\in L(\mathbb C^{d_2}\otimes\mathbb C^{d_1}),\qquad |I\rangle\!\rangle=\sum_i|i\rangle|i\rangle ,
--   $$
--   with the unnormalized maximally entangled vector. Its entry at $((b,a),(b',a'))$ is $\langle b|\mathcal E(|a\rangle\langle a'|)|b'\rangle$.
--
--   The Choi operator determines the channel and gives the Choi trace norm distance and the tester probabilities.
--
--   **Formalization Note** The output factor comes first, as printed. The definition applies to every linear map.
-- source:
--   Chen, Oufkir, Quantum channel tomography: optimal bounds in the near-boundary regime, arXiv:2611.03639v1, §2.1, p.10

import Mathlib
import Definitions.Def_ChanTomoNB_QChan

open Matrix

namespace ChanTomoNB

/-- The Choi–Jamiołkowski operator `C_E = (E ⊗ I)(|I⟩⟩⟨⟨I|) ∈ L(ℂ^{d2} ⊗ ℂ^{d1})` with the
unnormalized `|I⟩⟩ = ∑ᵢ |i⟩|i⟩`. Chen, Oufkir, *Quantum channel tomography: optimal bounds in the
near-boundary regime*, arXiv:2611.03639v1, §2.1, p.10.

**Formalization Note.** The output factor comes first, as printed: the entry at
`((b, a), (b', a'))` is `⟨b| E(|a⟩⟨a'|) |b'⟩`. Defined for every linear map `E`. -/
noncomputable def choi {A B : Type} [DecidableEq A] (E : Superop A B) :
    Matrix (B × A) (B × A) ℂ :=
  Matrix.of fun p q => E (Matrix.single p.2 q.2 1) p.1 q.1

end ChanTomoNB


