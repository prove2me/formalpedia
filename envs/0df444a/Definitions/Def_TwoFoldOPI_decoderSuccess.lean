-- Prove2me | Definitions.Def_TwoFoldOPI_decoderSuccess
-- name    : TwoFoldOPI_decoderSuccess
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:46:53.623483+00:00
-- url     : https://prove2.me/theorems/760168cf-8bc7-4c6b-b949-149a5acf6b40
-- title:
--   Success probability of a coherent decoder for $\mathrm{QDP}_{C^\perp,\mathrm{QFT}^\dagger|\psi\rangle}$
-- statement:
--   A coherent decoder is a unitary circuit $U$ over $\{H,T,\mathrm{CNOT}\}$ on an input register of $M$ symbols, an output register of $M$ symbols and $w$ work wires. For a code $D$ (in the mission $D=C^\perp$) and a state $|\psi\rangle$ on $\mathbb F_q^M$, its success probability is
--   $$\frac1{|D|}\sum_{d\in D}\Pr\Big[\text{measuring the output register of } U\big(X^d\,\mathrm{QFT}^\dagger|\psi\rangle\otimes|0\rangle\big)\text{ gives a word that reads as } d\Big],$$
--   the quantum decoding problem of Definition 5.25 with a uniformly random hidden codeword. Measurements and coins of a decoder are deferred to work registers, so the decoder is a unitary.
-- source:
--   Ragavan, Shutty, Quantum Algorithms for OPI Variants Beyond Locality and Classical Decodability, arXiv:2610.00502 (version held, sha256 ef050ec0…62605), §5.2, Definition 5.25 and Computational conventions, p. 26; Theorem 5.30, p. 29

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Circuit
import Definitions.Def_QAlgorithms_Defs_GradientMethods
import Definitions.Def_TwoFoldOPI_qft
import Definitions.Def_TwoFoldOPI_shiftOp
import Definitions.Def_TwoFoldOPI_regEmbed
import Definitions.Def_TwoFoldOPI_decodeWord

open scoped Matrix

namespace TwoFoldOPI

open QAlgorithms

/-- **Success probability of a coherent decoder for `QDP_{C⊥, QFT†|ψ⟩}`.**
Ragavan, Shutty, *Quantum Algorithms for OPI Variants Beyond Locality and Classical
Decodability*, arXiv:2610.00502 (version held, sha256 ef050ec0…62605), §5.2, Definition 5.25, p.26: "Input: for a uniformly random codeword c ← C⊥, the input is
the state X^c |ψ_err⟩ = Σ_e α(e) |c + e⟩. Output: the algorithm succeeds if and only if it outputs
c"; "Computational conventions", p.26: "A quantum decoder is given as a uniform circuit. Its
measurements and random choices are deferred to work registers, so it is a unitary"; Theorem 5.30,
p.29: "A coherent decoder solves QDP_{C⊥,QFT†|ψ_A⟩}".

The decoder is a circuit `U` over `{H, T, CNOT}` on `M·b + (M·b + w)` wires: an input register of
`M` symbols, an output register of `M` symbols, and `w` work wires. Its success is the average
over `d ∈ D` (uniform) of the probability that, on input `X^d QFT† |ψ⟩` (output and work wires
`|0⟩`), measuring the output register gives a word that decodes to `d`:
`(1/|D|) Σ_{d ∈ D} Pr[decodeWord(output register of U (X^d QFT†|ψ⟩ ⊗ |0⟩)) = d]`.

**Formalization Note.** `D` plays the role of `C⊥`. Symbols are laid out by `wordBits`; the
output register is read with the total decoding `decodeWord`. -/
noncomputable def decoderSuccess (F : AvgCaseTI.FieldPres) (M w : ℕ)
    (D : Submodule F.F (Fin M → F.F)) (ψ : EuclideanSpace ℂ (Fin M → F.F))
    (U : Circuit htcxGateSet (M * bitsPerSymbol F + (M * bitsPerSymbol F + w))) : ℝ :=
  open scoped Classical in
  (Nat.card D : ℝ)⁻¹ * ∑ d ∈ Finset.univ.filter (fun d : Fin M → F.F => d ∈ D),
    probEvent (act U.unitary
        (regEmbed F M (M * bitsPerSymbol F + w) (act (shiftOp d * (qft F M)ᴴ) ψ)))
      (fun z => decodeWord F M
        (fun i => z (Fin.natAdd (M * bitsPerSymbol F) (Fin.castAdd w i))) = d)

end TwoFoldOPI


