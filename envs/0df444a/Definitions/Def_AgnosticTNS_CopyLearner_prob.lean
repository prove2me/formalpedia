-- Prove2me | Definitions.Def_AgnosticTNS_CopyLearner_prob
-- name    : AgnosticTNS_CopyLearner_prob
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T16:39:19.034188+00:00
-- url     : https://prove2.me/theorems/62898c93-1df7-49bf-ab4a-bb53e77e5589
-- title:
--   Probability of a learner's output event
-- statement:
--   For a learner, an instance $i$, an input state $\rho$ and a property $E$ of output strings, the Born probability
--   $$
--   \Pr[E]=\sum_{z\,:\,E(\text{output bits of }z)}\langle z|U\,\mathrm P\,U^\dagger|z\rangle,
--   $$
--   where $U$ is the unitary of the circuit and $\mathrm P$ its input state; the sum runs over all computational-basis outcomes $z$ of all wires.
-- source:
--   Caro–McHugh–Strelchuk, Efficient Agnostic Learning of Tensor Network States, STOC 2027 submission (manuscript sha256 d69077bb…abec0), Theorem 3.6, p.23; Corollaries 5.1–5.2, pp.39–40

import Mathlib
import Definitions.Def_AgnosticTNS_CopyLearner_inputState
open Matrix

namespace AgnosticTNS

/-- **The probability that a learner's output has a property**, the success probabilities
"with probability at least `1 − δ`" of Theorem 3.6, Corollaries 3.7, 5.1, 5.2 and Lemma 3.9
(Caro–McHugh–Strelchuk, *Efficient Agnostic Learning of Tensor Network States*, STOC 2027 submission manuscript (sha256 d69077bb…abec0)): with `U` the unitary of the circuit (its columns are `runLayered` applied to basis states)
and `Ρ` the input state, the Born probability `Σ_z [E(out bits of z)] ⟨z|U Ρ U†|z⟩` over the
computational-basis outcomes `z` whose output string satisfies `E`. -/
noncomputable def CopyLearner.prob {ι : Type} {nOf dOf : ι → ℕ} (Lr : CopyLearner ι nOf dOf) (i : ι)
    (ρ : Matrix (Fin (nOf i) → Fin (dOf i)) (Fin (nOf i) → Fin (dOf i)) ℂ)
    (E : QAlgorithms.Complexity.Str → Prop) : ℝ := by
  classical
  exact
    let U : Matrix (QAlgorithms.Complexity.Bits (Lr.copies i * (nOf i * Nat.clog 2 (dOf i)) + Lr.anc i))
        (QAlgorithms.Complexity.Bits (Lr.copies i * (nOf i * Nat.clog 2 (dOf i)) + Lr.anc i)) ℂ :=
      Matrix.of fun z x => QAlgorithms.Complexity.runLayered (Lr.circ i) (fun y => if y = x then 1 else 0) z
    ∑ z, if E ((Lr.out i).map z) then ((U * Lr.inputState i ρ * Uᴴ) z z).re else 0

end AgnosticTNS


