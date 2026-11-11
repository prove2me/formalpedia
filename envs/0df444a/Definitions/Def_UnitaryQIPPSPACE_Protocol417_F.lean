-- Prove2me | Definitions.Def_UnitaryQIPPSPACE_Protocol417_F
-- name    : UnitaryQIPPSPACE_Protocol417_F
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:34:25.465096+00:00
-- url     : https://prove2.me/theorems/63c3605e-0208-41bf-b684-a8c5c852696e
-- title:
--   The accepted map $F_\sigma$ of Protocol 4.17
-- statement:
--   Protocol 4.17 runs a unitary oracle circuit $C$ on the input register $Q$ and an ancillary register $E$ initialized to $|0\rangle$. Gates are applied directly. The $i$-th query, on $(Y_i,t_i)$ with $\ell_i+1$ qubits, is conjugated by $H$ on $t_i$; between the two Hadamards, for $j=1,\dots,\ell_i+1$, the verifier sends $z_j=(a_1,\dots,a_{j-1})$ to the prover, runs the subprotocol verifier of Lemma 4.16 with parameters $(z_j,1^{\ell_i+1},1^{R})$ on fresh registers, rejects if it rejects, otherwise keeps its output register $B_{i,j}$, applies CNOT from the $w$-th qubit of $(Y_i,t_i)$ to the $w$-th qubit of $B_{i,j}$, measures $B_{i,j}$ (outcome $a_j$) and discards it. Finally $E$ is discarded and $Q$ is output.
--
--   For a prover with private register $P$ in state $\sigma$, $F_\sigma:\mathcal L(\mathcal H_Q)\to\mathcal L(\mathcal H_Q)$ is the unnormalized accepted map: the output on $Q$ restricted to the accepting runs, summed over the measurement outcomes, with $P$ and $E$ discarded.
--
--   **Formalization Note** The protocol's ingredients are parameters: the oracle circuit, the subprotocol generator $G:(z,m,R)\mapsto$ verifier, the subprotocol parameter $R$ ($R_n$ in the protocol), the prover's private register size, and the prover's strategy, a unitary on (message register, $P$) for every stage, chosen from the classical history of all earlier outcomes. A prover of the paper is one such strategy. Steps 1–2 of the protocol (computing $q,r,\beta,C,K,R_n$) are the choice of these parameters.
-- source:
--   He, Ou, Zhao, unitaryQIP = unitaryPSPACE, arXiv:2611.02819 (held version, sha256 9e357a00…ead793), Protocol 4.17; §4.5.2, p.33 (PDF p.35)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Complexity
import Definitions.Def_QAdvFew_PoQOracle_tup
import Definitions.Def_UnitaryQIPPSPACE_run
import Definitions.Def_UnitaryQIPPSPACE_OCirc
import Definitions.Def_UnitaryQIPPSPACE_conjBy

open Matrix QAlgorithms.Complexity QAdvFew.PoQOracle

namespace UnitaryQIPPSPACE

namespace Protocol417

/-- Steps 4(ii)(b)–(c): the accepted branch of a state-synthesis subprotocol with verifier `V` (no
quantum input, output register `B = Z_out`, fresh verifier and message registers), run against the
prover operator `P` on `M ⊗ P` with the prover's current private register as input, tensored with
the identity on the verifier's other registers (`QE`). The result lives on `QE ⊗ B ⊗ P`; the
remaining verifier and message registers are discarded, a rejection contributes nothing. -/
noncomputable def stage (V : Verifier) {N y : ℕ}
    (P : Matrix (Bits V.m × Bits y) (Bits V.m × Bits y) ℂ)
    (X : Matrix (Bits N × Bits y) (Bits N × Bits y) ℂ) :
    Matrix (Bits N × (Bits V.o × Bits y)) (Bits N × (Bits V.o × Bits y)) ℂ :=
  fun x x' => acceptedMap V P 0 (fun _ => 1) (fun p p' => X (x.1, p) (x'.1, p')) x.2 x'.2

/-- Step 4(ii)(d) on outcome `a`: CNOT from the `w`-th qubit of `(Y_i, t_i)` (the qubits `qs`) to
the `w`-th qubit of `B`, measurement of `B` with outcome `a`, discard `B`; the Kraus operator
`(I ⊗ ⟨a|_B ⊗ I_P) · CNOT`, with entries `[r = r₀ ∧ p = p₀ ∧ b ⊕ r_{qs} = a]`. -/
def measKraus (V : Verifier) {N y : ℕ} (qs : List ℕ) (a : Bits V.o) :
    Matrix (Bits N × Bits y) (Bits N × (Bits V.o × Bits y)) ℂ :=
  fun x x' => if x'.1 = x.1 ∧ x'.2.2 = x.2 ∧
      Bits.xor x'.2.1 (fun w => bitAt x.1 (qs.getD w.val 0)) = a then 1 else 0

/-- The `ℓ_i + 1` injection rounds of the `i`-th query (steps 4(ii)(a)–(d) for
`j = 1, …, ℓ_i + 1`): in round `j`, the classical message `z_j = (a₁, …, a_{j−1})` (the outcomes of
this query so far, encoded `tup [a₁, …, a_{j−1}]`) selects the subprotocol verifier
`G(z_j, 1^{ℓ_i+1}, 1^R)`, the prover acts in it with the unitary `S h (·)` chosen from the whole
classical history `h`, and the outcome `a_j` is recorded. The continuation `k` receives the history
and the operator after the last round; the sum is over the outcomes. -/
noncomputable def injRounds (G : Str → ℕ → ℕ → Verifier) (R : ℕ) {n N y : ℕ}
    (S : List Str → (mm : ℕ) → Matrix (Bits mm × Bits y) (Bits mm × Bits y) ℂ) (qs : List ℕ)
    (k : List Str → Matrix (Bits N × Bits y) (Bits N × Bits y) ℂ → Matrix (Bits n) (Bits n) ℂ) :
    ℕ → List Str → List Str → Matrix (Bits N × Bits y) (Bits N × Bits y) ℂ →
      Matrix (Bits n) (Bits n) ℂ
  | 0, _, hist, X => k hist X
  | r + 1, zs, hist, X =>
      let V := G (tup zs) qs.length R
      let Y := stage V (S hist V.m) X
      ∑ a : Bits V.o,
        let K : Matrix (Bits N × Bits y) (Bits N × (Bits V.o × Bits y)) ℂ := measKraus V qs a
        injRounds G R S qs k r (zs ++ [a.toStr]) (hist ++ [a.toStr]) (K * Y * Kᴴ)

/-- Step 4 and step 5 on the remaining operations of the oracle circuit, in circuit order, on the
operator of `QE ⊗ P` (`e` ancillary qubits): (i) an elementary gate is applied; (ii) the `i`-th
query is conjugated by `H` on its target `t_i` around its injection rounds; at the end `E` and the
prover's register are discarded and `Q` is output. -/
noncomputable def procOps (G : Str → ℕ → ℕ → Verifier) (R : ℕ) (n e : ℕ) {y : ℕ}
    (S : List Str → (mm : ℕ) → Matrix (Bits mm × Bits y) (Bits mm × Bits y) ℂ) :
    List OOp → List Str → Matrix (Bits (n + e) × Bits y) (Bits (n + e) × Bits y) ℂ →
      Matrix (Bits n) (Bits n) ℂ
  | [], _, X => fun x x' => ∑ c : Bits e, ∑ p : Bits y, X (Fin.append x c, p) (Fin.append x' c, p)
  | OOp.query qs :: ops, hist, X =>
      injRounds G R S qs
        (fun hist' X' => procOps G R n e S ops hist'
          (liftLeft (conjBy (embed1 gateH (n + e) (qs.getLast?.getD 0))) X'))
        qs.length [] hist (liftLeft (conjBy (embed1 gateH (n + e) (qs.getLast?.getD 0))) X)
  | o :: ops, hist, X =>
      procOps G R n e S ops hist (liftLeft (conjBy (o.mat (fun _ => false) (n + e))) X)

end Protocol417

/-- **The accepted map `F_σ` of Protocol 4.17** (He, Ou, Zhao, *unitaryQIP = unitaryPSPACE*,
arXiv:2611.02819, held version sha256 9e357a00…, Protocol 4.17, p. 33 (PDF p. 35), and §4.5.2,
pp. 34–35): "Protocol 4.17 (An interactive protocol for `{U_n} ∈ unitaryPSPACE_{δ²/2¹⁴}` with
soundness `s`). Parameters. Fix polynomials `q, r` such that `q(n) ≥ 2`, `r(n) ≥ 4`,
`s(n) ≥ 1/q(n)` and `δ(n) ≥ 1/r(n)`. Input state. An `n`-qubit pure state `|ψ⟩`. Verifier `V_n`.
1. Compute `q(n)`, `r(n)` and `β(n) = ⌈log₂(8r(n))⌉`.
2. Obtain the description of the oracle circuit `C^{(·)}_{n,β(n)}`, which acts on an `n`-qubit
register `Q` and an ancillary register `E`, and has query access to the fixed oracle `A_W ∈ PSPACE`,
as in Corollary 4.8. Let `T` be its number of oracle queries, ordered by their occurrence in the
circuit, with the `i`-th query acting on `ℓ_i + 1` qubits. Set `K := ∑_{i=1}^T (ℓ_i + 1)`,
`R_n := ⌈8K · q(n)r(n)⌉`. (21)
3. Identify `Q` with the verifier's register holding the input `|ψ⟩`, and initialize `E` to the
all-zero state.
4. For each operation of `C^{(·)}_{n,β(n)}` in circuit order:
(i) If it is an elementary unitary gate, apply it and continue to the next operation.
(ii) Else, it is the `i`-th oracle query, acting on an `ℓ_i`-qubit register `Y_i` and a single-qubit
target register `t_i`. Apply `H` to `t_i`. For `j = 1, …, ℓ_i + 1`:
(a) Let `z_j ← (a₁, …, a_{j−1})`, with `z₁ := ∅`, be the sequence of measurement outcomes from the
preceding iterations. Send `(i, j, z_j)` to the prover.
(b) Run the verifier specified in Lemma 4.16 with parameters `(z_j, 1^{ℓ_i+1}, 1^{R_n})` and the
predicate `Γ_{A_W}` defined in Lemma 4.13, using fresh verifier and message registers.
(c) If the verifier in step (b) rejects, REJECT AND HALT. Otherwise, denote its output register by
`B_{i,j}`, retain it, and discard its remaining verifier and message registers.
(d) Apply CNOT from the `w`-th qubit of `(Y_i, t_i)` to the `w`-th qubit of `B_{i,j}` for each
`w ∈ [ℓ_i + 1]`. Measure `B_{i,j}` in the computational basis, record the outcome as
`a_j ∈ {0,1}^{ℓ_i+1}`, and discard `B_{i,j}`.
Apply `H` to `t_i`.
5. Discard the ancillary register `E`, output the register `Q` and ACCEPT."

"we fix an arbitrary prover `P_n` with private register `P` and let `F : L(H_Q ⊗ H_P) → L(H_Q)`
denote the unnormalized accepted map of the whole protocol" (p. 34); `F_σ(·) := F((·) ⊗ σ)`
(Lemma 4.18, p. 35).

Parameters of this definition (paper.md reading R15): the oracle circuit `C` (`Q` = its first `n`
qubits, `E` = its `C.anc` ancillary qubits; its queries `query [q₀, …, q_{ℓ−1}, t]` act on
`Y_i = (q₀, …, q_{ℓ−1})` and `t_i = t`), the subprotocol verifier generator
`G : (z, m, R) ↦ verifier` of Lemma 4.16 (with `m` the output size), the subprotocol parameter
`R` (`R_n` in the protocol), the prover's private register size `y`, the prover's strategy `S`, and
its initial private state `σ`. `F σ ρ` is the accepted output on `Q` for the input operator `ρ`.

**Formalization Note** The prover is modeled as follows: in the subprotocol of every stage it acts
with a unitary `S h m'` on the subprotocol's message register (`m'` qubits) and its private
register (`y` qubits), chosen from the full classical history `h` of earlier outcomes. A prover of
the paper (one unitary, its private register keeping track of the round and of the classical
messages `(i, j, z_j)` it received) is one such strategy, so a statement for every strategy covers
every prover; the paper's own proof (eq. (23)) allows the accepted maps `A_{k,h_k}` to depend on the
full history. The steps 1–2 that compute `q, r, β, C, K, R_n` are the choice of the parameters. -/
noncomputable def Protocol417.F (n : ℕ) (C : OCirc) (G : Str → ℕ → ℕ → Verifier) (R : ℕ)
    (y : ℕ) (S : List Str → (mm : ℕ) → Matrix (Bits mm × Bits y) (Bits mm × Bits y) ℂ)
    (σ : Matrix (Bits y) (Bits y) ℂ) (ρ : Matrix (Bits n) (Bits n) ℂ) :
    Matrix (Bits n) (Bits n) ℂ :=
  Protocol417.procOps G R n C.anc S C.ops []
    (fun x x' => conjBy (iota n C.anc) ρ x.1 x'.1 * σ x.2 x'.2)

end UnitaryQIPPSPACE


