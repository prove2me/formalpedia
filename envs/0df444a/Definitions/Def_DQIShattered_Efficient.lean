-- Prove2me | Definitions.Def_DQIShattered_Efficient
-- name    : DQIShattered_Efficient
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T20:29:38.877523+00:00
-- url     : https://prove2.me/theorems/f65981ab-e1c9-4289-a967-6d80fd2524ab
-- title:
--   Efficient decoder and sampler families for $\mathbb G_{\mathrm{ER}}(N,k,D)$
-- statement:
--   This file defines the two efficiency notions of Theorem 2.7.
--
--   1. **Efficient decoders solving w.h.p.** A family of decoder circuits $B\mapsto c_N(B)$ qualifies when there are a deterministic Turing machine $T$, constants $C,K$ and one sequence $o_N\to0$ such that for every $N\ge k$ the following hold.
--      - On input $B$ and a parameter word (the first $N$ binary digits of $\gamma$, or of $\beta$ when the decoder serves DQI at $\gamma=\frac12-\frac12\operatorname{sech}\beta$), $T$ writes $c_N(B)$ within $C(N+1)^K$ steps, for every instance in the support. The circuit $c_N(B)$ is over $\{H,T,\mathrm{CNOT}\}$, has at most $C(N+1)^K$ gates and wires, and has at least $2M$ wires.
--      - With probability at least $1-o_N$ over $B\sim\mathbb G_{\mathrm{ER}}(N,k,D)$, its unitary solves the $(B,\gamma,\delta)$-quantum decoding problem. The estimate register is wires $[0,M)$, the received register is wires $[M,2M)$, and the work wires start in $|0\rangle$.
--   2. **Efficient samplers.** A family $(B,J)\mapsto c_N(B,J)$ qualifies when a machine writes it in polynomial time, as above, on input $(B,J)$ and the first $N$ binary digits of $\beta$, and it has at least $N$ wires. Its output law is that of the first $N$ wires measured after running the circuit on $|0\cdots0\rangle$.
--
--   **Formalization Note** The real parameter's digits are on the input, because a machine cannot realize the rotations of an uncomputable $\gamma$ or $\beta$ that it does not read. The machine may depend on the fixed parameters. The machine, the constants and $o$ are chosen before $N$ and do not depend on the instance. This is the meaning of $1-o_N(1)$.
-- source:
--   Zhou, Shutty, Sellke, Jordan, Gibbs Sampling in the Shattered Phase by Decoded Quantum Interferometry, arXiv:2609.40345 (held version sha256 0c7f6fdf…), Theorem 2.7, p.7

import Mathlib
import Definitions.Def_DQIShattered_Machine
import Definitions.Def_DQIShattered_Ensemble
import Definitions.Def_DQIShattered_Decoding

namespace DQIShattered

open Filter Topology QAlgorithms

/-- The decoder wire layout on `n ≥ 2M` wires: wires `[0, M)` are the estimate register `E`, wires `[M, 2M)`
the received register `R`, the remaining `n − 2M` wires the work register `W` (bit `true` = `1 ∈ 𝔽₂`). -/
def decLayout (M n : ℕ) (t : Reg M × Reg M × Qubits (n - 2 * M)) : Qubits n := fun q =>
  if h1 : q.val < M then decide (t.1 ⟨q.val, h1⟩ = 1)
  else if h2 : q.val < 2 * M then decide (t.2.1 ⟨q.val - M, by omega⟩ = 1)
  else t.2.2 ⟨q.val - 2 * M, by have := q.isLt; omega⟩

/-- **The decoder unitary of a circuit**: `c.unitary` read on estimate ⊗ received ⊗ work registers through
`decLayout` (a bijection when `c.wires ≥ 2M`, which the efficiency clauses require). -/
noncomputable def decoderMatrix (M : ℕ) (c : Circ) :
    Matrix (Reg M × Reg M × Qubits (c.wires - 2 * M)) (Reg M × Reg M × Qubits (c.wires - 2 * M)) ℂ :=
  Matrix.of fun t t' => c.unitary (decLayout M c.wires t) (decLayout M c.wires t')

/-- The all-zero work register. -/
def zeroWork (n : ℕ) : Qubits n := fun _ => false

/-- The sampler wire layout on `n ≥ N` wires: wires `[0, N)` carry the output `x ∈ 𝔽₂^N`, the rest are work
wires. -/
def sampLayout (N n : ℕ) (x : Fin N → ZMod 2) (w : Qubits (n - N)) : Qubits n := fun q =>
  if h : q.val < N then decide (x ⟨q.val, h⟩ = 1) else w ⟨q.val - N, by have := q.isLt; omega⟩

/-- **The output law of a sampler circuit**: start all wires in `|0⟩`, apply the circuit, measure the first
`N` wires; `x` is output with probability `∑_w |⟨x, w| U |0…0⟩|²`, and `z = (−1)^x`. -/
noncomputable def samplerDist (N : ℕ) (c : Circ) (x : Fin N → ZMod 2) : ℝ :=
  ∑ w : Qubits (c.wires - N), ‖act c.unitary (zeroKet c.wires) (sampLayout N c.wires x w)‖ ^ 2

/-- **An efficient decoder family solving the quantum decoding problem with high probability over `B`**
(Zhou, Shutty, Sellke, Jordan, arXiv:2609.40345, held version sha256 0c7f6fdf…, Theorem 2.7, p.7: "can
efficiently solve the `(B, γ, δ)`-quantum decoding problem with high probability (`1 − o_N(1)`) over the choice
of `B`"). `circ N B` is the decoder circuit for the instance `B ∼ 𝔾_ER(N, k, D)`. There are a deterministic
multi-stack Turing machine `TM`, constants `C, K` and one sequence `o_N → 0` such that for every `N ≥ k`:

* for every hyperedge list `E`, `TM` writes, on input (the code of `B = incidence E`, then the parameter word
  `param N`: the first `N` binary places of `γ`, or of `β` when the decoder serves DQI at inverse temperature `β`
  with `γ = gammaOf β`), within `C (N+1)^K` steps, the code of `circ N B`, a circuit over `{H, T, CNOT}` with at most
  `C (N+1)^K` gates and wires and at least `2M` wires;
* with probability at least `1 − o_N` over `B`, its decoder unitary (estimate wires `[0, M)`, received wires
  `[M, 2M)`, work wires started in `|0⟩`) solves the `(B, γ, δ)`-quantum decoding problem.

**Formalization Note** The paper names no machine and no gate set. A fixed finite gate set is the strong
reading (gates with real parameters could carry `γ` for free). `γ` is an arbitrary real, so the binary digits
of the real parameter (`param N`, always `encReal N γ` or `encReal N β` in this mission) are on the input: a machine cannot realize the rotations of an uncomputable `γ` it does not read. The machine may
depend on the fixed parameters. The order (`TM, C, K, o` chosen before `N`, and independent of `B`) is the
meaning of `1 − o_N(1)`. -/
def EfficientDecoders (k : ℕ) (D γ δ : ℝ) (param : ℕ → List Bool)
    (circ : (N : ℕ) → Matrix (Fin (Mrows N k D)) (Fin N) (ZMod 2) → Circ) : Prop :=
  ∃ (TM : Turing.TM2ComputableAux Bool Bool) (C K : ℕ) (o : ℕ → ℝ), Tendsto o atTop (𝓝 0) ∧
    ∀ N : ℕ, k ≤ N →
      (∀ E : Fin (Mrows N k D) → KSet N k,
        OutputsWithin TM (encMatrix (incidence E) ++ param N) (encCirc (circ N (incidence E)))
            (C * (N + 1) ^ K) ∧
          (circ N (incidence E)).gates.length ≤ C * (N + 1) ^ K ∧
          (circ N (incidence E)).wires ≤ C * (N + 1) ^ K ∧
          2 * Mrows N k D ≤ (circ N (incidence E)).wires) ∧
      1 - o N ≤ erProbB N k D fun B =>
        SolvesDecoding B γ δ (decoderMatrix (Mrows N k D) (circ N B))
          (zeroWork ((circ N B).wires - 2 * Mrows N k D))

/-- **A polynomial-time sampler family for the ensemble**: a deterministic multi-stack Turing machine `TM` and
constants `C, K` such that for every `N ≥ k` and every instance `(B, J = (−1)^v)` of the support of
`𝔾_ER(N, k, D)`, `TM` writes, on input (the code of `B`, the code of `v`, the first `N` binary places of `β`),
within `C (N+1)^K` steps, the code of `circ N B v`, a circuit over `{H, T, CNOT}` with at most `C (N+1)^K` gates
and wires and at least `N` wires (Theorem 2.7, p.7, "DQI can efficiently solve the Gibbs sampling problem").

**Formalization Note** Same machine model and reading of the real parameter's digits as `EfficientDecoders`;
the sampler's output law is `samplerDist`. -/
def EfficientSamplers (k : ℕ) (D β : ℝ)
    (circ : (N : ℕ) → Matrix (Fin (Mrows N k D)) (Fin N) (ZMod 2) → (Fin (Mrows N k D) → ZMod 2) → Circ) :
    Prop :=
  ∃ (TM : Turing.TM2ComputableAux Bool Bool) (C K : ℕ),
    ∀ N : ℕ, k ≤ N → ∀ E : Fin (Mrows N k D) → KSet N k, ∀ v : Fin (Mrows N k D) → ZMod 2,
      OutputsWithin TM (encMatrix (incidence E) ++ encVec v ++ encReal N β)
          (encCirc (circ N (incidence E) v)) (C * (N + 1) ^ K) ∧
        (circ N (incidence E) v).gates.length ≤ C * (N + 1) ^ K ∧
        (circ N (incidence E) v).wires ≤ C * (N + 1) ^ K ∧
        N ≤ (circ N (incidence E) v).wires

end DQIShattered


