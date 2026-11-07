-- Prove2me | Definitions.Def_TwoFoldOPI_singleInputState
-- name    : TwoFoldOPI_singleInputState
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:46:19.985731+00:00
-- url     : https://prove2.me/theorems/1ad33ee0-b03b-4475-bc18-871965469651
-- title:
--   The single-symbol input $X^c\,\mathrm{QFT}^\dagger|A_i\rangle$
-- statement:
--   For a forbidden value $\beta\in\mathbb F_q$ and $c\in\mathbb F_q$, the one-qudit state
--   $$|\phi_c\rangle=X^c\,\mathrm{QFT}^\dagger|A_i\rangle,\qquad |A_i\rangle=(q-1)^{-1/2}\sum_{y\neq\beta}|y\rangle .$$
--   Each coordinate of the decoder input in Theorem 7.4 has this form.
--
--   **Formalization Note** One qudit is a register of one symbol.
-- source:
--   Ragavan, Shutty, Quantum Algorithms for OPI Variants Beyond Locality and Classical Decodability, arXiv:2610.00502 (version held, sha256 ef050ec0…62605), §7.1, p. 38; proof of Lemma 7.2, p. 38

import Mathlib
import Definitions.Def_TwoFoldOPI_qft
import Definitions.Def_TwoFoldOPI_shiftOp
import Definitions.Def_TwoFoldOPI_uniformState
import Definitions.Def_TwoFoldOPI_targetSet

open scoped Matrix

namespace TwoFoldOPI

open QAlgorithms

/-- **The single-symbol decoder input `X^c QFT† |A_i⟩`.**
Ragavan, Shutty, *Quantum Algorithms for OPI Variants Beyond Locality and Classical
Decodability*, arXiv:2610.00502 (version held, sha256 ef050ec0…62605), §7.1, p.38: "Each coordinate of the decoding input has the form X^c QFT†|A_i⟩"; Lemma 7.2
and its proof, p.38: "Let |ϕ_c⟩ = X^c QFT†|A_i⟩".

For a forbidden value `β` and `c ∈ K`: the one-symbol state `X^c QFT† |K ∖ {β}⟩`, where
`|K ∖ {β}⟩ = (q − 1)^{−1/2} Σ_{y ≠ β} |y⟩`.

**Formalization Note.** One qudit is a register of one symbol, `Fin 1 → K`; `A_i` is
`targetSet` of the constant `β`. -/
noncomputable def singleInputState (F : AvgCaseTI.FieldPres) (β c : F.F) :
    EuclideanSpace ℂ (Fin 1 → F.F) :=
  act (shiftOp (fun _ => c) * (qft F 1)ᴴ) (uniformState (targetSet fun _ : Fin 1 => β))

end TwoFoldOPI


