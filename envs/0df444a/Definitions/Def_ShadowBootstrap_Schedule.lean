-- Prove2me | Definitions.Def_ShadowBootstrap_Schedule
-- name    : ShadowBootstrap_Schedule
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:23:28.961905+00:00
-- url     : https://prove2.me/theorems/c1734ffb-c8ed-465b-8a8b-367f84aacf27
-- title:
--   Measurement settings, schedules, histogram data, and the success probability
-- statement:
--   A **measurement setting** (p.3) is a circuit followed by computational-basis readout, applied to a number of fresh copies (its shots). A **schedule** is the list of all settings of a nonadaptive protocol, fixed before any outcome is observed; its number of settings is $N$ (counted with multiplicity) and its total number of shots, one copy each, is $T$ (Theorem 1.1, p.4).
--
--   Each shot of a setting with unitary $U$ on $|\psi\rangle$ gives $z$ with the Born probability $|\langle z|U|\psi\rangle|^2$, independently of all other shots. The data are one **histogram** per setting (§3.4). The post-processing input encodes $\epsilon$ (and $\delta$), the settings (tag, shots, gate list) and the histograms in a fixed order; its output is read as described for the real RAM.
--
--   For a law on schedules and a state $|\psi\rangle$, the success probability of an event is the probability, over the schedule and its outcomes, that the event holds of the schedule and its histograms.
--
--   **Formalization Note** Histograms are dense count arrays over $\{0,1\}^n$ in index order; the paper's dictionaries with absent keys read as $0$ are the same data. A setting carries a free integer tag (its stage or level).
-- source:
--   Cho, Kim, Shadow bootstrapping: Nearly minimal-setting pure-state tomography with shallow Clifford measurements, arXiv:2611.06073 (version of November 2, 2026, sha256 34fab758…), §1, p.3; Theorem 1.1, p.4; §3.4, p.10; Theorem 7.3, p.28

import Mathlib
import Definitions.Def_ShadowBootstrap_braket
import Definitions.Def_ShadowBootstrap_Circuit
import Definitions.Def_ShadowBootstrap_stateFrom

open ClassicalShadow.Linear MatMulTimeLP

namespace ShadowBootstrap

/-- A measurement setting (p.3: "Each setting specifies a unitary circuit followed by
computational-basis readout, and the same circuit can be applied repeatedly to fresh copies"): a
circuit, the number of shots (fresh copies) it is applied to, and a free label `tag` (the stage or
level the setting belongs to). -/
structure Setting (n : ℕ) where
  tag : ℕ
  circ : Circuit n
  shots : ℕ

/-- Cho, Kim, *Shadow bootstrapping: Nearly minimal-setting pure-state tomography with shallow
Clifford measurements*, arXiv:2611.06073 (version of November 2, 2026, sha256 34fab758…),
Theorem 1.1 (p.4) and Theorem 7.3 (p.28): a nonadaptive measurement schedule, the list of all
settings, fixed before any outcome is observed. `N` is its length (settings counted with
multiplicity) and `T` its total number of shots (`totalShots`).

**Formalization Note** The schedule law of an algorithm is a `PMF` on schedules that depends on
`(n, ϵ, δ)` only, never on the unknown state. Each shot measures one fresh copy (single-copy). The
data of a schedule `s` are one histogram per setting, a **count array** `h : Counts s`, the dense
form of the paper's dictionaries (absent keys read as `0`, §3.4, p.10). -/
abbrev Schedule (n : ℕ) := List (Setting n)

/-- `T`: the total number of copies of a schedule. -/
def totalShots {n : ℕ} (s : Schedule n) : ℕ := (s.map Setting.shots).sum

/-- One histogram per setting. -/
abbrev Counts {n : ℕ} (s : Schedule n) := Fin s.length → Bits n → ℕ

/-- The code of a gate: `[0, q, 0]` for `H` on `q`, `[1, q, 0]` for `S` on `q`, `[2, c, t]` for
`CX` with control `c` and target `t`. -/
def Gate.encode {n : ℕ} : Gate n → List ℕ
  | .h q => [0, q.1, 0]
  | .s q => [1, q.1, 0]
  | .cx c t _ => [2, c.1, t.1]

/-- The code of a circuit: its number of layers, then per layer its number of gates followed by
the gate codes. -/
def encodeCircuit {n : ℕ} (c : Circuit n) : List ℕ :=
  c.length :: c.flatMap fun L => L.length :: L.flatMap Gate.encode

/-- The code of a setting: tag, shots, circuit. -/
def encodeSetting {n : ℕ} (st : Setting n) : List ℕ :=
  st.tag :: st.shots :: encodeCircuit st.circ

/-- A histogram as reals in index order of `{0,1}ⁿ`. -/
noncomputable def countsList {n : ℕ} (h : Bits n → ℕ) : List ℝ :=
  (allBits n).map fun z => ((h z : ℕ) : ℝ)

/-- The input of the post-processing: the parameters `params` (e.g. `[ϵ, δ]`) followed by the
histograms in the real cells, and `n`, the number of settings and the setting codes in the index
cells. -/
noncomputable def encodeData {n : ℕ} (params : List ℝ) (data : List (Setting n × (Bits n → ℕ))) :
    State :=
  initState2 (params ++ data.flatMap fun p => countsList p.2)
    (n :: data.length :: data.flatMap fun p => encodeSetting p.1)

/-- The output of the program `P` on the data: the vector read after the real input. -/
noncomputable def dataOutput {n : ℕ} (P : Program) (params : List ℝ)
    (data : List (Setting n × (Bits n → ℕ))) : Bits n → ℂ :=
  outputVec P (encodeData params data) (params.length + data.length * 2 ^ n) n

/-- A schedule paired with its count array, in schedule order. -/
def dataOf {n : ℕ} (s : Schedule n) (h : Counts s) : List (Setting n × (Bits n → ℕ)) :=
  (List.finRange s.length).map fun i => (s.get i, h i)

/-- The Born probability `|⟨z|U|ψ⟩|²` of the outcome `z` of one shot of the setting. -/
noncomputable def bornProb {n : ℕ} (st : Setting n) (ψ : Bits n → ℂ) (z : Bits n) : ℝ :=
  ‖((circUnitary st.circ).mulVec ψ) z‖ ^ 2

/-- The raw outcomes of a schedule: for setting `i`, one bit string per shot. -/
abbrev Outcomes {n : ℕ} (s : Schedule n) := (i : Fin s.length) → Fin (s.get i).shots → Bits n

/-- The probability of the raw outcomes: all shots independent, each with its Born law. -/
noncomputable def outcomeWeight {n : ℕ} (s : Schedule n) (ψ : Bits n → ℂ) (ω : Outcomes s) : ℝ :=
  ∏ i, ∏ a, bornProb (s.get i) ψ (ω i a)

/-- The histograms of the raw outcomes. -/
def histArr {n : ℕ} (s : Schedule n) (ω : Outcomes s) : Counts s :=
  fun i => histOf (ω i)

open Classical in
/-- The probability that the histograms of schedule `s` on copies of `ψ` satisfy `A`. -/
noncomputable def dataProb {n : ℕ} (s : Schedule n) (ψ : Bits n → ℂ) (A : Counts s → Prop) : ℝ :=
  ∑ ω : Outcomes s, if A (histArr s ω) then outcomeWeight s ψ ω else 0

/-- The probability, over a schedule drawn from `law` and its outcomes on copies of `ψ`, that the
event `A` holds of the schedule and its histograms. -/
noncomputable def successProb {n : ℕ} (law : PMF (Schedule n)) (ψ : Bits n → ℂ)
    (A : (s : Schedule n) → Counts s → Prop) : ENNReal :=
  ∑' s, law s * ENNReal.ofReal (dataProb s ψ (A s))

end ShadowBootstrap


