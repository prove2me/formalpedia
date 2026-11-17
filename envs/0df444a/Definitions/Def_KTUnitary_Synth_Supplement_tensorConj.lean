-- Prove2me | Definitions.Def_KTUnitary_Synth_Supplement_tensorConj
-- name    : KTUnitary_Synth_Supplement_tensorConj
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:14:36.174773+00:00
-- url     : https://prove2.me/theorems/da676526-8d19-4f37-94d6-17b53e554975
-- title:
--   The unitary language $\mathcal U\otimes\mathcal U^*$
-- statement:
--   For a unitary language $\mathcal U=\{U_n\}_{n\in\mathbb N}$, $\mathcal U\otimes\mathcal U^*$ is the unitary language whose member on $2n$ qubits is
--   $$U_n\otimes U_n^*,$$
--   where $U_n^*$ is the **entrywise complex conjugate** of $U_n$ (not its adjoint $U_n^\dagger$ and not its transpose $U_n^{\mathrm T}$). The first $n$ qubits carry $U_n$ and the last $n$ qubits carry $U_n^*$: the entry in row $z=z_1z_2$, column $z'=z_1'z_2'$ is $\langle z_1|U_n|z_1'\rangle\,\overline{\langle z_2|U_n|z_2'\rangle}$.
--
--   It appears in Theorem 5.21, which characterizes the projective classes by the clean classes through $\mathcal U\otimes\mathcal U^*$ instead of $\mathcal U\otimes\mathcal U^\dagger$.
--
--   **Formalization Note** A unitary language has a member on every number of qubits; the members on an odd number of qubits, which the paper does not define, are the identity, as in the published $\mathcal U\otimes\mathcal U^\dagger$ (`PSPACEOracleSynth.Main.tensorAdj`), whose wire layout this definition follows.
-- source:
--   Kretschmer, Tang, Unitary Complexity in Polynomial Space, arXiv:2610.03705 (revision of 2026-10-31), Theorem 5.21, p. 22

import Mathlib
import Definitions.Def_KTUnitary_Synth_ULang
import Definitions.Def_PSPACEOracleSynth_Main_Dilation

open QAlgorithms.Complexity PSPACEOracleSynth.Main

namespace KTUnitary.Synth.Supplement

open Classical in
/-- **The unitary language `𝒰 ⊗ 𝒰*`** (Kretschmer, Tang, *Unitary Complexity in Polynomial Space*,
arXiv:2610.03705 (revision of 2026-10-31), Theorem 5.21, p. 22): the unitary language whose member
on `2n` qubits is `U_n ⊗ U_n^*`, where `U_n^*` is the **entrywise complex conjugate** of `U_n` (not
its adjoint `U_n^†` and not its transpose `U_n^T`). On `2n` qubits the first `n` wires (register `X`)
carry `U_n` and the last `n` wires (register `Y`) carry `U_n^*`: the entry in row `z`, column `z'`
is `U_n(z₁, z'₁) · conj(U_n(z₂, z'₂))` for the halves `z = z₁z₂`, `z' = z'₁z'₂`.

**Formalization Note** The paper indexes `𝒰 ⊗ 𝒰*` by `n` (member `U_n ⊗ U_n^*` on `2n` qubits); a
unitary language has one member on every number of qubits, so the members on an odd number of
qubits are the identity, as in the published `PSPACEOracleSynth.Main.tensorAdj` (`𝒰 ⊗ 𝒰†`), whose
wire layout and halves `firstHalf`/`secondHalf` are reused. Every member `U_n ⊗ U_n^*` is unitary,
so the identity branch of `ULang.ofMatrices` is never taken on even lengths. -/
noncomputable def tensorConj (U : ULang) : ULang :=
  ULang.ofMatrices fun k =>
    if k % 2 = 0 then
      Matrix.of fun z z' =>
        (U (k / 2) : Matrix (Bits (k / 2)) (Bits (k / 2)) ℂ) (firstHalf z) (firstHalf z') *
          star ((U (k / 2) : Matrix (Bits (k / 2)) (Bits (k / 2)) ℂ) (secondHalf z) (secondHalf z'))
    else 1

end KTUnitary.Synth.Supplement


