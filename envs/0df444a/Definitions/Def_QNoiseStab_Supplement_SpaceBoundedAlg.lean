-- Prove2me | Definitions.Def_QNoiseStab_Supplement_SpaceBoundedAlg
-- name    : QNoiseStab_Supplement_SpaceBoundedAlg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:18:07.167051+00:00
-- url     : https://prove2.me/theorems/a5023ba5-8317-4635-8c20-79ec97474176
-- title:
--   Space-bounded quantum query algorithm with intermediate measurements and output commits
-- statement:
--   A **space-bounded quantum query algorithm** with $T$ queries has a memory consisting of a query register $Q=[n]$, a phase register $P=\mathbb Z_d$ and a finite workspace $W$; the whole state lives on $Q\otimes P\otimes W$. It is given by
--
--   1. an input-independent initial density matrix $\rho_{\mathrm{start}}$ on $Q\otimes P\otimes W$ (positive semidefinite, trace one), and
--   2. for each step $t=0,1,\dots,T$ a **quantum instrument** $\mathcal I_t$ on $Q\otimes P\otimes W$, in Kraus form $\{K_{t,o,r}\}$ with $\sum_{o,r}K_{t,o,r}^\dagger K_{t,o,r}=I$, whose classical outcome $o$ is either "no output" or a **commit** $(j,v)$: the algorithm declares the value $q(v)$ for output coordinate $j\in K$, where $q:V\to Y$ is a fixed post-processing map and $V$ is finite.
--
--   Between step $t$ and step $t+1$ the phase oracle $O_x\otimes I_W$, $O_x|i,p\rangle=\omega^{p x_i}|i,p\rangle$, is applied, so there are exactly $T$ queries.
--
--   This is the model of time-space tradeoffs with intermediate measurements: outputs are written during the computation to a write-only tape that does not count against the space, and measurements may reset qubits. The unitary steps, the flag measurement, the conditional output measurement and any reset measurements between two queries compose into a single instrument, so the class contains every fully general and every output-oblivious circuit.
--
--   **Formalization Note** The instrument is the published Kraus-form `KAQROM.Instrument`, with a finite Kraus index type shared by all steps (padding by zero operators). The start state is any input-independent density matrix; the paper's $|0\rangle$ is a special case.
-- source:
--   Beame–Holman–Kornerup, A Noise Operator Approach to Quantum Query Complexity and Time-Space Tradeoff Lower Bounds, arXiv:2609.40334 (version of 2026-11-02, sha256 814fe20e…), §2.2, p.7 (space bounded quantum circuits, fully general and output-oblivious models); §2.1, p.6 (registers Q, P, W and the T + 1 steps)

import Mathlib
import Definitions.Def_KAQROM_Instrument

set_option autoImplicit false

open scoped ComplexOrder

namespace QNoiseStab.Supplement

/-- A **space-bounded quantum query algorithm with intermediate measurements and output commits**
(Beame–Holman–Kornerup, *A Noise Operator Approach to Quantum Query Complexity and Time-Space Tradeoff Lower Bounds*, arXiv:2609.40334 (version of 2026-11-02, sha256 814fe20e…), §2.2, p.7: "we allow space bounded quantum algorithms to perform intermediate
measurements … A fully general quantum circuit … allows the algorithm to be adaptive with when it
chooses to produce each output … adding a 'flag' measurement gate … committing to q(w) as a
partial assignment to 1 output of f … additional measurement gates as a means to reset qubits";
§2.1, p.6, for the registers and the  + 1$ steps).

The whole memory is the register `M = (Fin n × ZMod d) × W`: the query register `Q = Fin n`, the
phase register `P = ZMod d` and a finite workspace `W` (p.7: "we assume that the state of C is
entirely stored in qubits"). The algorithm starts in an input-independent density matrix `start`
and runs `T + 1` steps `0, …, T`; between step `t` and step `t + 1` the phase oracle is applied
(so there are exactly `T` queries). Step `t` is a quantum instrument on `M` with outcomes in
`Option (K × V)`: outcome `none` means no output is produced at this step, and outcome
`some (j, v)` commits the value `q v` (for the algorithm's post-processing map `q : V → Y`) to
output coordinate `j ∈ K`.

**Formalization Note** One instrument per step contains every §2.2 circuit: the unitary `U_t`,
the flag measurement, the conditional output measurement and any reset measurements compose into
one instrument whose discarded outcomes are absorbed into the Kraus index `ι`; output-oblivious
circuits are the case where the outcome at step `t` is forced to commit a fixed index. The start
state is any input-independent density matrix (the paper's `|0⟩` is a special case, and step 0
can prepare any such state anyway). The instrument is the published `KAQROM.Instrument`
(Kraus form). -/
structure SpaceBoundedAlg (n d : ℕ) [NeZero d] (W K V ι : Type) [Fintype W] [DecidableEq W]
    [Fintype K] [Fintype V] [Fintype ι] (T : ℕ) where
  /-- The input-independent initial density matrix of the memory. -/
  start : Matrix ((Fin n × ZMod d) × W) ((Fin n × ZMod d) × W) ℂ
  /-- It is positive semidefinite. -/
  start_psd : start.PosSemidef
  /-- It has trace one. -/
  start_trace : start.trace = 1
  /-- The instruments of steps `0, …, T`, with outcome "no output" or "commit `(j, v)`". -/
  step : Fin (T + 1) →
    KAQROM.Instrument (Option (K × V)) ((Fin n × ZMod d) × W) ((Fin n × ZMod d) × W) ι

end QNoiseStab.Supplement


