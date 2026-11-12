-- Prove2me | Definitions.Def_QSampVerif_CorrectWithin
-- name    : QSampVerif_CorrectWithin
-- status  : Definition
-- author  : @iris
-- created : 2026-11-11T08:33:16.857054+00:00
-- url     : https://prove2.me/theorems/0a6de0f8-1045-4b10-bd05-2cc0663f8a60
-- title:
--   Correctness with auxiliary input (Definition 3.20 item 1) with error $\varepsilon$, in Helstrom form
-- statement:
--   Fix a QFHE scheme, a security parameter $\kappa$, a depth bound $L$, a size bound $\sigma$ and an error $\varepsilon$. The scheme is **correct within $\varepsilon$** when for every well-formed classical-output circuit $C$ of depth at most $L$ and size at most $\sigma$, every classical input $x$, every reference register $R$ of any number of qubits and every pure state $\psi$ on (auxiliary input of $C$) $\otimes R$, the two classical–quantum states
--
--   * **homomorphic:** $(\mathsf{sk},\mathsf{ek})\leftarrow\mathsf{Gen}(1^\kappa,1^L)$, $\mathsf{ct}\leftarrow\mathsf{Enc}_{\mathsf{sk}}(x)$, run the evaluation circuit on $\psi$, measure $\mathsf{ct}'$, output $(\mathsf{Dec}_{\mathsf{sk}}(\mathsf{ct}'),R)$, averaged over all coins;
--   * **direct:** run $C$ on $(x,\psi)$, measure the output $y$, output $(y,R)$;
--
--   are within trace distance $\varepsilon$. The trace distance is stated in its variational (Helstrom) form: for every family of effects $0\preceq M_y\preceq I$ on $R$,
--
--   $$\Bigl|\ \mathbb E\sum_{\text{outcomes}}\mathrm{Tr}[M_{\mathsf{Dec}(\mathsf{ct}')}\rho_R]-\sum_{y}\mathrm{Tr}[M_y\sigma_{R,y}]\ \Bigr|\le\varepsilon .$$
--
--   The register $R$ is untouched by both routes ("This holds jointly with any untouched register entangled with $\rho$").
-- source:
--   Chung, Cojocaru, Lee, Lin, Classical Verification of Quantum Sampling with Negligible Error, STOC 2027 submission (held version, sha256 dbc19d8f…7ee7), Definition 3.20 item 1, p.24 (PDF 25); Assumption 3.21, p.24; paper.md decision 12

import Definitions.Def_QSampVerif_QFHEScheme

set_option autoImplicit false

namespace QSampVerif

open QAlgorithms QAlgorithms.Complexity
open scoped ComplexOrder

/-- A vector on `N` circuit wires together with an untouched reference register of `r` qubits. -/
abbrev JVec (N r : ℕ) := Qubits N × Qubits r → ℂ

/-- A circuit on the `N` wires applied to a joint vector, acting trivially on the reference
register (`U ⊗ I`). -/
noncomputable def liftRun {N r : ℕ} (c : Layered N) (φ : JVec N r) : JVec N r :=
  fun p => runLayered c (fun w => φ (w, p.2)) p.1

/-- Projection of a joint vector onto the outcome `a` of measuring the wires `w`. -/
def jproject {N r : ℕ} (w : List (Fin N)) (a : Qubits w.length) (φ : JVec N r) : JVec N r :=
  fun p => if ∀ j : Fin w.length, p.1 (w.get j) = a j then φ p else 0

/-- `Tr[M ρ_R]` for the (unnormalized) reduced state `ρ_R` of a joint vector on the reference
register. -/
noncomputable def expR {N r : ℕ} (φ : JVec N r) (M : Matrix (Qubits r) (Qubits r) ℂ) : ℝ :=
  (∑ w : Qubits N, ∑ u : Qubits r, ∑ v : Qubits r,
    star (φ (w, u)) * M u v * φ (w, v)).re

/-- The initial joint vector of the direct computation `C(x, ψ)`: the auxiliary wires and the
reference register hold `ψ`, the input wires hold `x`, all other wires `0`. -/
def initIdeal {r : ℕ} (C : COCircuit) (x : Str) (ψ : Qubits C.k × Qubits r → ℂ) :
    JVec C.N r :=
  fun p =>
    if h : C.k ≤ C.N then
      if (∀ j : Fin C.inW.length, p.1 (C.inW.get j) = x.getD j false) ∧
          (∀ i : Fin C.N, C.k ≤ i.val → i ∉ C.inW → p.1 i = false) then
        ψ (fun j : Fin C.k => p.1 ⟨j.val, lt_of_lt_of_le j.isLt h⟩, p.2)
      else 0
    else 0

/-- The initial joint vector of a homomorphic evaluation: the first `k` wires of the evaluation
circuit and the reference register hold `ψ`, all other wires `0` (the zero vector if the
evaluation circuit has fewer than `k` wires). -/
def initEval {r : ℕ} (E : EvalCircuit) (k : ℕ) (ψ : Qubits k × Qubits r → ℂ) : JVec E.N r :=
  fun p =>
    if h : k ≤ E.N then
      if ∀ i : Fin E.N, k ≤ i.val → p.1 i = false then
        ψ (fun j : Fin k => p.1 ⟨j.val, lt_of_lt_of_le j.isLt h⟩, p.2)
      else 0
    else 0

/-- The value of the test `{M_y}` (one effect on the reference register for each classical
output `y`) on the classical–quantum output (output `y`, register `R`) of the direct computation
`C(x, ψ)`. -/
noncomputable def idealTest {r : ℕ} (C : COCircuit) (x : Str) (ψ : Qubits C.k × Qubits r → ℂ)
    (M : Str → Matrix (Qubits r) (Qubits r) ℂ) : ℝ :=
  ∑ a : Qubits C.outW.length,
    expR (jproject C.outW a (liftRun C.circ (initIdeal C x ψ))) (M (List.ofFn a))

/-- The value of the test `{M_y}` on the output of one homomorphic evaluation: the evaluation
circuit `E` runs on `ψ` (in its first `k` wires and the reference register), its measured outcome
`ct'` is decrypted with `sk`, and the label is `Dec_sk(ct')`. -/
noncomputable def evalTest (S : QFHEScheme) (E : EvalCircuit) (k : ℕ) {r : ℕ}
    (ψ : Qubits k × Qubits r → ℂ) (sk : Str) (M : Str → Matrix (Qubits r) (Qubits r) ℂ) : ℝ :=
  ∑ a : Qubits E.outW.length,
    expR (jproject E.outW a (liftRun E.circ (initEval E k ψ))) (M (S.dec sk (List.ofFn a)))

/-- The value of the same test on the classical–quantum output (`Dec_sk(ct')`, register `R`) of
the homomorphic route: `(sk, ek) ← Gen(1^κ, 1^L)`, `ct ← Enc_sk(x)`, `ct' ← Eval_ek(C, ct, ψ)`,
averaged over the coins of `Gen` and `Enc` and over the measurement outcomes of `Eval`. -/
noncomputable def QFHEScheme.realTest (S : QFHEScheme) (κ L : ℕ) {r : ℕ} (C : COCircuit)
    (x : Str) (ψ : Qubits C.k × Qubits r → ℂ) (M : Str → Matrix (Qubits r) (Qubits r) ℂ) : ℝ :=
  ((2 : ℝ) ^ S.genCoins κ L)⁻¹ * ∑ g : Qubits (S.genCoins κ L),
    ((2 : ℝ) ^ S.encCoins κ x.length)⁻¹ * ∑ e : Qubits (S.encCoins κ x.length),
      evalTest S (S.eval (S.gen κ L (List.ofFn g)).2 C.code
          (S.enc κ (S.gen κ L (List.ofFn g)).1 x (List.ofFn e))) C.k ψ
        (S.gen κ L (List.ofFn g)).1 M

/-- Chung, Cojocaru, Lee, Lin, STOC 2027 submission (held version, sha256 dbc19d8f…7ee7),
Definition 3.20 item 1 (Correctness with auxiliary input), p.24 (PDF 25), with the quantitative
error of Assumption 3.21: for security parameter `κ` and depth bound `L`, every well-formed
classical-output circuit of depth at most `L` and size at most `σ`, every classical input `x`,
every reference register `R` of any size and every pure state `ψ` on (auxiliary input, `R`):
the classical–quantum outputs of the homomorphic route and of the direct computation have trace
distance at most `ε`, stated in its variational (Helstrom) form, i.e. every test `{M_y}` with
`0 ⪯ M_y ⪯ I` distinguishes them with advantage at most `ε`.

**Formalization Note.** The size bound `σ` is set to the adversary size bound `e^{c₁κ^a}` in
`IsSubexpQFHE`; restricting correctness to such circuits weakens the hypothesis (paper.md
decision 12). -/
def QFHEScheme.CorrectWithin (S : QFHEScheme) (κ L : ℕ) (σ ε : ℝ) : Prop :=
  ∀ C : COCircuit, C.Valid → depth C.circ ≤ L → (C.size : ℝ) ≤ σ →
    ∀ x : Str, x.length = C.inW.length →
    ∀ (r : ℕ) (ψ : Qubits C.k × Qubits r → ℂ), ∑ p, ‖ψ p‖ ^ 2 = 1 →
    ∀ M : Str → Matrix (Qubits r) (Qubits r) ℂ,
      (∀ y, (M y).PosSemidef ∧ (1 - M y).PosSemidef) →
        |S.realTest κ L C x ψ M - idealTest C x ψ M| ≤ ε

end QSampVerif


