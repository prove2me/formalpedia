-- Prove2me | Definitions.Def_TwoFoldOPI_Supplement_qdpSuccessO
-- name    : TwoFoldOPI_Supplement_qdpSuccessO
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T14:03:08.969515+00:00
-- url     : https://prove2.me/theorems/b7e29733-74ee-4ca0-992c-617310af186b
-- title:
--   Success probability of a decoder with oracle access on $\mathrm{QDP}_{C^\perp,\mathrm{QFT}^\dagger|\psi\rangle}$
-- statement:
--   For a code $D=C^\perp$ and a state $\psi$, the quantum decoding problem gives the decoder $X^d\,\mathrm{QFT}^\dagger|\psi\rangle$ for a uniformly random $d\in D$ and asks for $d$. This is the success probability of a decoder program that queries given oracles:
--   $$\frac1{|D|}\sum_{d\in D}\Pr[\text{the output register decodes to } d].$$
--
--   **Formalization Note** The oracle version of the published `TwoFoldOPI.decoderSuccess`: input register, output register and work qubits, in the published word layout.
-- source:
--   Ragavan, Shutty, Quantum Algorithms for OPI Variants Beyond Locality and Classical Decodability, arXiv:2610.00502 (version held, sha256 ef050ec0…62605), §5.2, Definition 5.25, p. 26; Theorem 5.28, p. 27

import Mathlib
import Definitions.Def_QAlgorithms_Defs_OPIOraclePrograms
import Definitions.Def_QAlgorithms_Defs_GradientMethods
import Definitions.Def_TwoFoldOPI_qft
import Definitions.Def_TwoFoldOPI_shiftOp
import Definitions.Def_TwoFoldOPI_regEmbed
import Definitions.Def_TwoFoldOPI_decodeWord

namespace TwoFoldOPI

namespace Supplement

open QAlgorithms QAlgorithms.OPI

open scoped Matrix

open Classical in
/-- **Success probability of a decoder with oracle access on the quantum decoding problem.**
Ragavan, Shutty, *Quantum Algorithms for OPI Variants Beyond Locality and Classical
Decodability*, arXiv:2610.00502 (version held, sha256 ef050ec0…62605), §5.2, Definition 5.25, p.26: "Let C ⊆ F_q^M be a linear code, and |ψ_err⟩ = Σ_e α(e)|e⟩ be
some state. The quantum decoding problem QDP_{C⊥,|ψ_err⟩} is defined as follows: • Input: for a
uniformly random codeword c ← C⊥, the input is the state X^c|ψ_err⟩ = Σ_e α(e)|c + e⟩. • Output:
the algorithm succeeds if and only if it outputs c."; Theorem 5.28, p.27 ("solves
QDP_{C⊥,QFT†|A⟩} … using T_dec gates and Q_dec oracle queries").

The oracle version of the published `TwoFoldOPI.decoderSuccess`. The decoder `P` acts on
`M·b + (M·b + w)` qubits (`b = bitsPerSymbol F`): the input register, the output register, `w`
work qubits. For each `d ∈ D` it is run with oracles `O` on `X^d QFT† ψ` in the input register
(layout `wordBits`) and zeros elsewhere; the success is the probability that the output register
decodes (`decodeWord`) to `d`, averaged over `d ∈ D`:
`(1/|D|) Σ_{d ∈ D} Σ_{leaves} Σ_z [decode(out(z)) = d] ρ_leaf(z, z)`.

**Formalization Note.** With `D = C⊥` and `ψ = |A⟩` this is the success on
`QDP_{C⊥,QFT†|A⟩}`. For a coherent program (`coherentCounts P ≠ none`, as in every use) there is
one leaf, the final state, and the inner sum is the Born probability of the event. -/
noncomputable def qdpSuccessO (F : AvgCaseTI.FieldPres) (M w : ℕ) {r : ℕ} {a : Fin r → ℕ}
    {ctl : Fin r → Bool} {c out : ℕ} (O : (k : Fin r) → Matrix (Qubits (a k)) (Qubits (a k)) ℂ)
    (D : Submodule F.F (Fin M → F.F)) (ψ : EuclideanSpace ℂ (Fin M → F.F))
    (P : AdaptiveMembershipProgram htcxGateSet a ctl
      (M * bitsPerSymbol F + (M * bitsPerSymbol F + w)) c out) : ℝ :=
  (Nat.card D : ℝ)⁻¹ * ∑ d ∈ Finset.univ.filter (fun d : Fin M → F.F => d ∈ D),
    ((adaptiveExecution O P
        (pureDensity (regEmbed F M (M * bitsPerSymbol F + w)
          (act (shiftOp d * (qft F M)ᴴ) ψ))) (fun _ => false)).map fun leaf =>
      ∑ z : Qubits (M * bitsPerSymbol F + (M * bitsPerSymbol F + w)),
        if decodeWord F M (fun i => z (Fin.natAdd (M * bitsPerSymbol F) (Fin.castAdd w i))) = d
        then (leaf.1.2 z z).re else 0).sum

end Supplement

end TwoFoldOPI


