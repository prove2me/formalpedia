-- Prove2me | Definitions.Def_AgnosticTNS_CopyLearner_inputState
-- name    : AgnosticTNS_CopyLearner_inputState
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T16:38:35.300074+00:00
-- url     : https://prove2.me/theorems/3a5e9520-42c8-41bb-b856-3adfce022681
-- title:
--   Input of a learner
-- statement:
--   The input of a learner on the state $\rho$: the encoded copies $(\rho_{\mathrm{enc}})^{\otimes m_i}$ followed by the ancillas in $|0^{a_i}\rangle\langle0^{a_i}|$.
-- source:
--   Caro–McHugh–Strelchuk, Efficient Agnostic Learning of Tensor Network States, STOC 2027 submission (manuscript sha256 d69077bb…abec0), Theorem 3.6, p.23; Eq. (3.68), p.26

import Mathlib
import Definitions.Def_AgnosticTNS_CopyLearner
import Definitions.Def_AgnosticTNS_encOp
import Definitions.Def_AgnosticTNS_bitsSplit
import Definitions.Def_ShadowTomography_UpperBound_tensorPow

namespace AgnosticTNS

/-- **The input of a learner**, `(encoded ρ)^{⊗copies} ⊗ |0^anc⟩⟨0^anc|`, for the learner model of
pp.3, 26 (Caro–McHugh–Strelchuk, *Efficient Agnostic Learning of Tensor Network States*, STOC 2027 submission manuscript (sha256 d69077bb…abec0)): independent copies of the encoded `n`-qudit state, then ancillas in `|0⟩`.

**Formalization Note** `ρ^{⊗k}` is the published `ShadowTomography.UpperBound.tensorPow`. -/
noncomputable def CopyLearner.inputState {ι : Type} {nOf dOf : ι → ℕ} (Lr : CopyLearner ι nOf dOf)
    (i : ι) (ρ : Matrix (Fin (nOf i) → Fin (dOf i)) (Fin (nOf i) → Fin (dOf i)) ℂ) :
    Matrix (QAlgorithms.Complexity.Bits (Lr.copies i * (nOf i * Nat.clog 2 (dOf i)) + Lr.anc i))
      (QAlgorithms.Complexity.Bits (Lr.copies i * (nOf i * Nat.clog 2 (dOf i)) + Lr.anc i)) ℂ :=
  Matrix.of fun z z' =>
    ShadowTomography.UpperBound.tensorPow (encOp ρ) (Lr.copies i)
        (bitsBlocks _ _ (bitsSplit _ _ z).1) (bitsBlocks _ _ (bitsSplit _ _ z').1) *
      (if (∀ k, (bitsSplit _ _ z).2 k = false) ∧ (∀ k, (bitsSplit _ _ z').2 k = false) then 1 else 0)

end AgnosticTNS


