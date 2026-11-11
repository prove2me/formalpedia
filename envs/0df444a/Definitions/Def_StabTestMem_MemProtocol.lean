-- Prove2me | Definitions.Def_StabTestMem_MemProtocol
-- name    : StabTestMem_MemProtocol
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T09:11:32.805507+00:00
-- url     : https://prove2.me/theorems/4cf49ff6-fb5e-40b5-9c15-becb8732f1a8
-- title:
--   Adaptive single-copy protocols with $k$ qubits of quantum memory (Definition 3.7)
-- statement:
--   A protocol with **$k$ qubits of memory** using **$t$ copies** of an unknown $n$-qubit state $\rho$ runs in $t$ rounds. The memory starts in a fixed $k$-qubit density matrix $\eta_0$. In round $i$ a fresh copy of $\rho$ is loaded; after the history of outcomes $x_{<i}=(x_1,\dots,x_{i-1})$ the protocol applies one branch of a quantum instrument
--
--   $$T^{x_i}_{x_{<i}}:\ \mathcal B(\mathcal H_{\mathrm{in}}\otimes\mathcal M)\to\mathcal B(\mathcal M),$$
--
--   each branch linear and completely positive, the branches summing to a trace-preserving map, records the outcome $x_i$, and keeps $T^{x_i}_{x_{<i}}(\rho\otimes\eta_{x_{<i}})$ as the (unnormalized) memory. The choice of instrument may depend on the history (adaptivity). After $t$ rounds the protocol accepts or rejects as a function of the transcript $x=(x_1,\dots,x_t)$.
--
--   The structure also provides:
--
--   1. the **transcript functional** $Y\mapsto\operatorname{Tr}[E_xY]$ on operators $Y$ on $t$ copies (Lemma 3.10): it applies the rounds in order to $Y\otimes\eta_0$, each round acting on its copy and the memory, and takes the trace; for $Y=\rho^{\otimes t}$ it is the probability of the transcript $x$;
--   2. the **acceptance probability** $\sum_{x\text{ accepted}}\operatorname{Tr}[E_xY]$, in particular on $\rho^{\otimes t}$;
--   3. the **tester property**: $P$ is an $\varepsilon$-tester if every pure state with $\mathcal F_{\mathsf{Stab}}=1$ is accepted with probability at least $2/3$ and every pure state with $\mathcal F_{\mathsf{Stab}}\le1-\varepsilon$ with probability at most $1/3$.
--
--   **Formalization Note** The final POVM of Definition 3.7 is an instrument in the last round whose output memory is discarded (a POVM $\{E^x\}$ is the instrument $Y\mapsto\operatorname{Tr}(E^xY)\eta_*$). Classical randomness and ancillas live inside the instruments, and the decision is a deterministic function of the transcript. The outcome alphabet is any finite type, the same in every round. Complete positivity is the shared `PeresTerno.IsCompletelyPositive`; the tensor power $\rho^{\otimes t}$ is the published `WildeQIT.Schumacher.tensorPow` (entries $\prod_i\rho(X_i,Y_i)$, copy $i$ in slot $i$).
-- source:
--   Arunachalam, Schatzki, Optimal stabilizer testing and learning with limited quantum memory, arXiv:2607.02444 (version of 2 Nov 2026), §3.3 and Definition 3.7, pp. 21–22; Lemma 3.10, Eq. (36), p. 23; Theorem 1.1, p. 4; Lemma 5.1, p. 36

import Definitions.Def_PeresTerno_kraus_basics
import Definitions.Def_StabTestMem_stabFidelity
import Definitions.Def_ObliviousRSP_pureState
import Definitions.Def_WildeQIT_Schumacher_tensorPow

namespace StabTestMem

open QAlgorithms
open scoped ComplexOrder

/-- **An adaptive protocol with `k` qubits of memory using `t` single copies of an `n`-qubit
state.** Arunachalam, Schatzki, *Optimal stabilizer testing and learning with limited quantum memory*, arXiv:2607.02444 (version of 2 Nov 2026), §3.3 and Definition 3.7, pp. 21–22 (Figure 1, p. 4): "At round i, the algorithm is
given a fresh copy of the unknown state ρ and the memory is in the state η_i … the algorithm may
perform an arbitrary channel N : B(H_in ⊗ M) → B(M)", formalized as a tree: "For every child node
x_{≤i} = x_{<i} x_i of x_{<i}, there is a linear, completely positive, and trace non-increasing map
T^{x_i}_{x<i} : B(H_in ⊗ H_m) → B(H_m) such that η_{x≤i} = T^{x_i}_{x<i}(ρ ⊗ η_{x<i}). • Fixing a
node x_{<i}, Σ_{x_i} T^{x_i}_{x<i} is a CPTP channel. • In the final round, the entire system is
measured with some POVM."

Fields:
* `η₀`: the initial state of the `k`-qubit memory (a density matrix);
* `inst i h x`: the map `T^{x}_{h}` of round `i` (rounds `0, …, t − 1`) after the history
  `h = (x_0, …, x_{i−1})`, from operators on (fresh copy ⊗ memory) = `Qubits n × Qubits k` to
  operators on the memory `Qubits k`; it is linear and completely positive (`inst_cp`), and the
  branches of one node sum to a trace-preserving map (`inst_tp`);
* `accept`: the decision (accept = `true`) as a function of the full transcript.

**Formalization Note.** (1) The final POVM of Definition 3.7 is encoded as an instrument in the last
round whose output memory is then discarded: a POVM `{E^x}` is the instrument
`T^x(Y) = Tr(E^x Y) η_*`, and conversely an instrument followed by discarding the memory is the
POVM `(T^x)†(I)`. (2) Classical randomness (e.g. random Cliffords) and ancillas live inside the
instruments; the decision is a deterministic function of the transcript, randomness being absorbed
into the outcomes. (3) Outcome alphabets are an arbitrary finite type `X`, the same in every round
(per-round alphabets embed into their disjoint union). (4) The memory is exactly `k` qubits and
each round consumes exactly one copy; adaptivity is the dependence of `inst i` on the history. -/
structure MemProtocol (n k t : ℕ) (X : Type) [Fintype X] where
  /-- Initial memory state. -/
  η₀ : Matrix (Qubits k) (Qubits k) ℂ
  η₀_psd : η₀.PosSemidef
  η₀_trace : η₀.trace = 1
  /-- The instrument branch `T^{x}_{h}` of round `i` after history `h`, outcome `x`. -/
  inst : (i : Fin t) → (Fin i → X) → X →
    (Matrix (Qubits n × Qubits k) (Qubits n × Qubits k) ℂ →ₗ[ℂ] Matrix (Qubits k) (Qubits k) ℂ)
  inst_cp : ∀ i h x, PeresTerno.IsCompletelyPositive (inst i h x)
  inst_tp : ∀ i h (ρ : Matrix (Qubits n × Qubits k) (Qubits n × Qubits k) ℂ),
    (∑ x, inst i h x ρ).trace = ρ.trace
  /-- Accept (`true`) or reject, as a function of the transcript. -/
  accept : (Fin t → X) → Bool

namespace MemProtocol

variable {n k t : ℕ} {X : Type} [Fintype X]

/-- **One round of the protocol on the register (t copies) ⊗ memory.** Arunachalam, Schatzki, *Optimal stabilizer testing and learning with limited quantum memory*, arXiv:2607.02444 (version of 2 Nov 2026), Definition 3.7,
pp. 21–22, and Definition 3.9, Eq. (34), p. 23 (forward operators).

Round `i` with transcript `x` applies `T^{x_i}_{x<i}` to copy `i` ⊗ memory and the identity to the
other copies, and leaves copy `i` in `|0⟩⟨0|` (the copy is consumed): the entry at
`((c, μ), (c', μ'))` is `T(Z_{c,c'})(μ, μ')` if `c_i = c'_i = 0` and `0` otherwise, where
`Z_{c,c'}` is the block of `Z` on copy `i` ⊗ memory with the other copies fixed at `c, c'`. -/
noncomputable def round (P : MemProtocol n k t X) (x : Fin t → X) (i : Fin t)
    (Z : Matrix ((Fin t → Qubits n) × Qubits k) ((Fin t → Qubits n) × Qubits k) ℂ) :
    Matrix ((Fin t → Qubits n) × Qubits k) ((Fin t → Qubits n) × Qubits k) ℂ :=
  Matrix.of fun p p' =>
    if p.1 i = (fun _ => false) ∧ p'.1 i = (fun _ => false) then
      P.inst i (fun j => x ⟨j, j.2.trans i.2⟩) (x i)
        (Matrix.of fun q q' =>
          Z (Function.update p.1 i q.1, q.2) (Function.update p'.1 i q'.1, q'.2)) p.2 p'.2
    else 0

/-- **The transcript functional `Y ↦ Tr[E_x Y]`.** Arunachalam, Schatzki, *Optimal stabilizer testing and learning with limited quantum memory*, arXiv:2607.02444 (version of 2 Nov 2026), Lemma 3.10, Eq. (36), p. 23: "the
probability of observing transcript x is given by Tr[E_x ρ^{⊗t}]", extended linearly to every
operator `Y` on the `t`-copy register (as used with `R(O)`, `σ_P`, `ρ_H`, `ρ_mm` in §5.4,
Eqs. (76), (103)–(105)).

`weight Y x = Tr[(Round_{t−1} ∘ ⋯ ∘ Round_0)(Y ⊗ η₀)]`, rounds applied in the order `0, 1, …, t − 1`.
For `Y = ρ^{⊗t}` it is the probability of the transcript `x`. -/
noncomputable def weight (P : MemProtocol n k t X)
    (Y : Matrix (Fin t → Qubits n) (Fin t → Qubits n) ℂ) (x : Fin t → X) : ℂ :=
  Matrix.trace ((List.finRange t).foldl (fun Z i => P.round x i Z)
    (Matrix.of fun p p' => Y p.1 p'.1 * P.η₀ p.2 p'.2))

/-- **Acceptance probability on a `t`-copy operator `Y`**: `Σ_{x accepted} Re Tr[E_x Y]`. For
`Y = ρ^{⊗t}` this is the probability that the protocol accepts (Lemma 3.10, p. 23); for
`Y = E_A[ψ_A^{⊗t}]`, `ρ_mm` or `ρ_H` it is the acceptance probability under the ensemble. -/
noncomputable def acceptProbOp (P : MemProtocol n k t X)
    (Y : Matrix (Fin t → Qubits n) (Fin t → Qubits n) ℂ) : ℝ :=
  ∑ x, if P.accept x then (P.weight Y x).re else 0

/-- **Acceptance probability when every copy is `ρ`**: `acceptProbOp P (ρ^{⊗t})`, with the tensor
power the published `WildeQIT.Schumacher.tensorPow` (entries `∏ᵢ ρ(Xᵢ, Yᵢ)`, copy `i` in slot `i`). -/
noncomputable def acceptProb (P : MemProtocol n k t X) (ρ : Matrix (Qubits n) (Qubits n) ℂ) : ℝ :=
  P.acceptProbOp (WildeQIT.Schumacher.tensorPow t ρ)

/-- **A stabilizer tester with accuracy `ε`.** Arunachalam, Schatzki, *Optimal stabilizer testing and learning with limited quantum memory*, arXiv:2607.02444 (version of 2 Nov 2026), Theorem 1.1, p. 4: a protocol "to distinguish
between F_Stab(|ψ⟩) = 1 vs. F_Stab(|ψ⟩) ≤ 1 − ε"; "distinguish" means success probability at least
`2/3` on every promised input (Lemma 5.1, p. 36; Lemma 5.3, p. 37; Fact 5.4, p. 38).

`IsStabTester P ε`: for every `n`-qubit pure state `ψ` (unit vector), if `F_Stab(ψ) = 1` the
protocol accepts with probability `≥ 2/3`, and if `F_Stab(ψ) ≤ 1 − ε` it accepts with probability
`≤ 1/3`. -/
def IsStabTester (P : MemProtocol n k t X) (ε : ℝ) : Prop :=
  ∀ ψ : EuclideanSpace ℂ (Qubits n), IsState ψ →
    (stabFidelity ψ = 1 → 2 / 3 ≤ P.acceptProb (ObliviousRSP.pureState ψ)) ∧
      (stabFidelity ψ ≤ 1 - ε → P.acceptProb (ObliviousRSP.pureState ψ) ≤ 1 / 3)

end MemProtocol

end StabTestMem


