-- Prove2me | Definitions.Def_QAdvFew_PoQOracle_Supplement_DSample
-- name    : QAdvFew_PoQOracle_Supplement_DSample
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:16:20.31728+00:00
-- url     : https://prove2.me/theorems/e198db04-3880-41c6-a9f3-d71963266dbb
-- title:
--   The oracle distribution $\mathcal D$ of §5.1 (randomness)
-- statement:
--   Level $t$ of the oracle of §5.1 is determined by independent random choices: a uniformly random function $\mathrm{RO}_t:\{0,1\}^t\times\{0,1\}^{4t}\to\{0,1\}^{6t}\times\{0,1\}^{6t}$, a Haar-random unitary $W^{\mathrm{SG}}_t$ on $4t$ qubits, for each $x\in\{0,1\}^t$ a Haar-random state $|\phi_x\rangle$ on $4t$ qubits, and for each $x$ a Haar-random unitary $W^{\mathrm{Expand}}_{t,x}$ on $4t+1$ qubits. The distribution $\mathcal D$ is the independent product of these laws over all levels $t\in\mathbb N$.
--
--   **Formalization Note** $|\phi_x\rangle$ is sampled as $V_x|0\rangle$ with $V_x$ Haar-random; the oracle is a function of the sample (`oracleD`), so "with probability $1$ over $O\leftarrow\mathcal D$" is an almost-sure statement for this product measure.
-- source:
--   Goldin, Lombardi, Morimae, Quantum Advantage has Few Complexity Implications, arXiv:2611.05303v1, §5.1, p. 32 (PDF p. 34)

import Mathlib
import Definitions.Def_QAdvFew_PoQOracle_Supplement_haarU

open QAlgorithms.Complexity MeasureTheory

namespace QAdvFew.PoQOracle.Supplement

/-- The randomness of level `t` of the oracle distribution `D` (Goldin, Lombardi, Morimae, *Quantum Advantage has Few Complexity Implications*, arXiv:2611.05303v1, §5.1, p. 32 (PDF p. 34): "For
each `t`, let `RO_t : {0,1}^t × {0,1}^{4t} → {0,1}^{6t} × {0,1}^{6t}` be a random oracle. Let
`W^SG_t : H({0,1}^{4t}) → H({0,1}^{4t})` be random unitaries. For each `x ∈ {0,1}^t`, we will also
sample a random state `|ϕ_x⟩ ← HaarSt({0,1}^{4t})` and a random unitary
`W^Expand_{t,x} : H({0,1}^{4t+1}) → H({0,1}^{4t+1})`"): the tuple
`(RO_t, W^SG_t, (V_x)_x, (W^Expand_{t,x})_x)`, where `|ϕ_x⟩ = V_x|0⟩`.

**Formalization Note** `HaarSt(S)` is the law of `V|0⟩` for Haar-random `V` (`haarU`), so the
state `|ϕ_x⟩` is stored as the unitary `V_x` that prepares it. -/
abbrev DSample (t : ℕ) : Type :=
  (Bits t × Bits (4 * t) → Bits (6 * t) × Bits (6 * t)) ×
    Matrix.unitaryGroup (Bits (4 * t)) ℂ ×
    (Bits t → Matrix.unitaryGroup (Bits (4 * t)) ℂ) ×
    (Bits t → Matrix.unitaryGroup (Bits (4 * t + 1)) ℂ)

/-- The law of level `t` (§5.1, p. 32: "All random choices in our oracle constructions are
independent unless a dependence is specified", §3.2.2, p. 12): `RO_t` uniform over all functions,
and `W^SG_t`, every `V_x` and every `W^Expand_{t,x}` Haar-distributed, all independent. -/
noncomputable def levelMeasure (t : ℕ) : Measure (DSample t) :=
  (PMF.uniformOfFintype (Bits t × Bits (4 * t) → Bits (6 * t) × Bits (6 * t))).toMeasure.prod
    ((haarU (Bits (4 * t))).prod
      ((Measure.pi fun _ : Bits t => haarU (Bits (4 * t))).prod
        (Measure.pi fun _ : Bits t => haarU (Bits (4 * t + 1)))))

instance instProbLevelMeasure (t : ℕ) : IsProbabilityMeasure (levelMeasure t) := by
  unfold levelMeasure; infer_instance

/-- The oracle distribution `D` of §5.1 (pp. 32–33, PDF pp. 34–35) as a law on the randomness of
all levels: the independent product over `t ∈ ℕ` of `levelMeasure t`. The oracle itself is the
function `oracleD` of a sample. -/
noncomputable def Dmeasure : Measure ((t : ℕ) → DSample t) :=
  Measure.infinitePi levelMeasure

end QAdvFew.PoQOracle.Supplement


