-- Prove2me | Definitions.Def_QIndInf_Learner
-- name    : QIndInf_Learner
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T08:26:58.970632+00:00
-- url     : https://prove2.me/theorems/b7e62f93-8670-4cfd-b5b2-b45e07bf967c
-- title:
--   Learner: a family of quantum channels on the inputs of Definition 4.1
-- statement:
--   A **learner** for quantum inductive inference specifies, for every round $i$, a quantum channel (a completely positive trace-preserving map)
--
--   $$
--   \mathcal L(\mathsf{param},h_{<i},\mathcal I_i;\,\cdot\,):\ \mathcal D(R_1\cdots R_{i-1})\to\mathcal D(R_1\cdots R_i X_i),
--   $$
--
--   depending only on the parameters $\mathsf{param}=(1^s,1^t,1^n,1^{\epsilon^{-1}},1^{\delta^{-1}})$, the history $h_{<i}=(\mathcal I_1,x_1,\dots,\mathcal I_{i-1},x_{i-1})$ and the next instrument $\mathcal I_i$. It is applied to one copy of the post-measurement state $\rho_{<i|h<i}$. It is given neither the number of rounds $m$, nor the program, nor the source, nor later instruments.
--
--   This is the class of learners over which Definition 4.1 and Theorem 4.2 quantify.
--
--   **Formalization Note** The paper's "quantum algorithm" is read as a family of quantum channels (`QAlgorithms.IsChannel`: a finite normalized Kraus family), one per classical input; Theorem 4.2 is information theoretic and its learner is an integral of rotated Petz maps, so no efficiency is required. Requiring a channel excludes "learners" that read the whole input matrix from a single copy. Parameters are natural numbers with $\epsilon=1/a$, $\delta=1/b$. Instruments are passed as mathematical objects (finite Kraus families) rather than circuit descriptions; a description determines its instrument, so these learners are learners in the paper's sense. When the next instrument has no outcomes no such instrument exists, and the channel requirement is vacuous there.
-- source:
--   Hiroka, Hsieh, Shirakawa, arXiv:2609.36912 (PDF of 2026-11-02), Definition 4.1, p.19; §4.2, algorithm step 1, p.20; informal model §1, pp.4–5

import Mathlib
import Definitions.Def_QIndInf_QuantumProcess
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Defs_QuantumInstruments

set_option autoImplicit false

namespace QIndInf

open QAlgorithms QAlgorithms.CopyMeasurements

/-- **A learner for quantum inductive inference.** At round `i = j + 1` it receives exactly the
inputs of Definition 4.1: the parameters `param = (1^s, 1^t, 1^n, 1^{ε⁻¹}, 1^{δ⁻¹})`, the history
`h<i = (I₁, x₁, …, I_{i−1}, x_{i−1})`, the next instrument `I_i`, and one copy of the
post-measurement state `ρ_{<i|h<i}` of the past registers `R₁ … R_{i−1}`. It outputs a state on
`(R₁, …, R_i, X_i)`. For each classical input (parameters, instruments, outcomes) the map from the
quantum input to the output is a quantum channel.

arXiv:2609.36912 (PDF of 2026-11-02), Definition 4.1, p.19, and the input list of the algorithm
in §4.2, step 1, p.20; the informal model on pp.4–5 ("except for the parameters, the learner L is
given no description of the quantum source").

**Formalization Note.**
* `run s t n a b j k I x` is the channel used at round `j + 1` with parameters `s, t, n`,
  `ε = 1/a`, `δ = 1/b`; `k l` is the number of outcomes of instrument `I_{l+1}`; `I` lists the
  `j + 1` instruments `I₁, …, I_{j+1}` (the last, `I (Fin.last j)`, is the next instrument); `x`
  lists the past outcomes. The learner does **not** receive the number of rounds `m`, the program,
  the source, or any later instrument.
* Instruments are passed as mathematical objects (finite Kraus families) rather than circuit
  descriptions; a circuit description determines its instrument, so a learner of this type is in
  particular a learner in the paper's sense.
* "Quantum algorithm" is read as a family of quantum channels (`QAlgorithms.IsChannel`: a finite
  normalized Kraus family, i.e. a completely positive trace-preserving map), one per classical
  input. Theorem 4.2 is information theoretic (§4.2 is titled "An Information-Theoretic
  Algorithm"; the learner of the proof is an integral of rotated Petz maps), so no efficiency is
  required. Requiring a channel excludes "learners" that read the whole input matrix from one
  copy.
* When the next instrument has no outcomes (`k (Fin.last j) = 0`) there is no such instrument
  (its completeness relation `0 = 1` fails), so the channel requirement is vacuous there. -/
structure Learner where
  /-- The channel applied at round `j + 1`, as a function of the classical input. -/
  run : (s t n a b j : ℕ) → (k : Fin (j + 1) → ℕ) →
    ((l : Fin (j + 1)) → QuantumInstrument (Reg n) (Fin (k l))) →
    ((l : Fin j) → Fin (k l.castSucc)) →
    Superop (Regs n j) (Regs n j × (Reg n × Fin (k (Fin.last j))))
  /-- Every map `run …` is a quantum channel. -/
  isChannel : ∀ (s t n a b j : ℕ) (k : Fin (j + 1) → ℕ)
    (I : (l : Fin (j + 1)) → QuantumInstrument (Reg n) (Fin (k l)))
    (x : (l : Fin j) → Fin (k l.castSucc)), IsChannel (run s t n a b j k I x)

end QIndInf


