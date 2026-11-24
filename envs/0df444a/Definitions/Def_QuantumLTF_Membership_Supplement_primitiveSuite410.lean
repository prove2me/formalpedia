-- Prove2me | Definitions.Def_QuantumLTF_Membership_Supplement_primitiveSuite410
-- name    : QuantumLTF_Membership_Supplement_primitiveSuite410
-- status  : Definition
-- author  : @Robin Kothari
-- created : 2026-11-24T06:04:20.783579+00:00
-- url     : https://prove2.me/theorems/e6ee0716-70d5-4ad3-a51e-41e5a7006a94
-- title:
--   Gate- and Depth-Efficient Primitive Suite Interface for Theorem 4.10
-- statement:
--   This defines the abstract circuit-primitive interface `PrimitiveSuite410` for the gate- and depth-efficient quantum learning algorithm of Theorem 4.10 (Krivcenko, Nguyen, de Wolf 2026, Section 4.5.3 and Appendix C.5 / C.5.2), working strictly in the one- and two-qubit gate set `gates12` under all-to-all connectivity.
--
--   1. **Standard reversible and Hadamard blocks:** Toffoli on $3$ wires (`toffoliCirc`), controlled $H^{\otimes n}$ (`chCirc n`) using $O(n)$ gates and $O(\log n)$ non-oracle depth, multi-controlled single-qubit unitary on equality (`eqCirc L pat U`) using $O(L)$ gates and $O(\log L)$ depth, and the parallel carry-save Hamming-weight counter `hcCirc n` with its adjoint `hcAdjCirc n` using $O(n \log n)$ gates and $O(\log n)$ depth.
--   2. **Input-negation block for the parity lift:** `cnCirc n` implements controlled-$X^{\otimes n}$ on $1 + n$ main wires using $O(n)$ gates and $O(\log n)$ non-oracle depth, enabling coherent simulation of $g_A(x, y)$ from a single query to $\mathrm{majOracle}(A)$ via Equation (127).
--   3. **Multiplexed coupled transducer unitary $\tilde{U}$:** For $M \ge 1$ and $2M + 1 \le n'$, `uTilde410Circ M n'` implements the controlled map $\lvert \mathrm{fc}\rangle \lvert w\rangle \lvert \mathrm{mode}\rangle \mapsto \lvert \mathrm{fc}\rangle \lvert w\rangle U_{\mathrm{val}(w)}^{\mathrm{fc}}\lvert \mathrm{mode}\rangle$ (`U_op410 M (bitsToNatLSB w)`) using $O(n' \log n')$ gates and $O(\log n')$ non-oracle depth, matching the coherent routing construction of Appendix C.5 and C.5.2.
--
--   **Formalization Note.** Helper packers `packCH`, `packEq`, `packHC`, `packCN`, and `packUTilde410` embed the main and clean-ancilla registers into `Qubits (...)` without exposing internal ancilla layouts (`ancCH`, `ancEq`, `ancHC`, `ancCN`, `ancUTilde`).
-- source:
--   Krivcenko, Nguyen, de Wolf (2026), Fast Quantum Algorithms for Learning Linear Threshold Functions, arXiv:2609.40331, Section 4.3, Eq. (127) (p. 50), Section 4.5.3 (pp. 55-57), and Appendix C.5 / C.5.2 (pp. 95-99).

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QAlgorithms_Defs_Circuit
import Definitions.Def_QuantumLTF_Membership_gates12
import Definitions.Def_QuantumLTF_Membership_Supplement_nonOracleDepth
import Definitions.Def_QuantumLTF_Membership_Supplement_coupledOp410

set_option autoImplicit false

namespace QuantumLTF.Membership.Supplement.CoupledOp410

open QAlgorithms QuantumLTF.Membership QuantumLTF.Membership.Supplement

/-- Pack state for controlled-`H^{⊗ n}` primitive: control bit `c`, `n` target wires, `anc` clean ancillas. -/
def packCH (n anc : ℕ) (c : Bool) (x : Qubits n) (a : Qubits anc) : Qubits (1 + n + anc) :=
  fun i =>
    if h0 : i.1 = 0 then c
    else if h1 : i.1 < 1 + n then x ⟨i.1 - 1, by omega⟩
    else a ⟨i.1 - (1 + n), by omega⟩

/-- Pack state for equality-controlled single-qubit unitary `multiEqCtrl1`. -/
def packEq (L anc : ℕ) (addr : Qubits L) (tgt : Bool) (a : Qubits anc) : Qubits (L + 1 + anc) :=
  fun i =>
    if h0 : i.1 < L then addr ⟨i.1, h0⟩
    else if h1 : i.1 = L then tgt
    else a ⟨i.1 - (L + 1), by omega⟩

/-- Pack state for Hamming-weight counter `hammingCounter`. -/
def packHC (n ℓ anc : ℕ) (x : Qubits n) (w : Qubits ℓ) (a : Qubits anc) : Qubits (n + ℓ + anc) :=
  fun i =>
    if h0 : i.1 < n then x ⟨i.1, h0⟩
    else if h1 : i.1 < n + ℓ then w ⟨i.1 - n, by omega⟩
    else a ⟨i.1 - (n + ℓ), by omega⟩

/-- Pack state for controlled-`X^{⊗ n}` primitive (`ctrlNotN`). -/
def packCN (n anc : ℕ) (c : Bool) (x : Qubits n) (a : Qubits anc) : Qubits (1 + n + anc) :=
  fun i =>
    if h0 : i.1 = 0 then c
    else if h1 : i.1 < 1 + n then x ⟨i.1 - 1, by omega⟩
    else a ⟨i.1 - (1 + n), by omega⟩

/-- Pack state for the multiplexed step unitary `Ũ_410` (control `fc`, Hamming weight `w`, `qW M` mode wires, `anc` ancillas). -/
def packUTilde410 (M n' anc : ℕ) (fc : Bool) (w : Qubits (Nat.clog 2 (n' + 1)))
    (mode : Qubits (qW M)) (a : Qubits anc) :
    Qubits (1 + Nat.clog 2 (n' + 1) + qW M + anc) :=
  fun i =>
    if h0 : i.1 = 0 then fc
    else if h1 : i.1 < 1 + Nat.clog 2 (n' + 1) then w ⟨i.1 - 1, by omega⟩
    else if h2 : i.1 < 1 + Nat.clog 2 (n' + 1) + qW M then mode ⟨i.1 - (1 + Nat.clog 2 (n' + 1)), by omega⟩
    else a ⟨i.1 - (1 + Nat.clog 2 (n' + 1) + qW M), by omega⟩

/-- Gate-level primitive suite required to instantiate the Theorem 4.10 quantum walk in `gates12`
with `O(n log n log k)` gates and `O(log n log k)` non-oracle depth. -/
structure PrimitiveSuite410 where
  -- 1. Toffoli gate on 3 wires
  toffoliCirc : Circuit gates12 3
  toffoliDepth : ℕ
  toffoli_hdepth : ∀ (r : ℕ) (a : Fin r → ℕ),
    nonOracleDepth (toffoliCirc.map OracleStep.gate : OracleCircuit gates12 a 3) ≤ toffoliDepth
  toffoli_act : ∀ (b₀ b₁ b₂ : Bool),
    act toffoliCirc.unitary (ket fun i : Fin 3 =>
      if i.1 = 0 then b₀ else if i.1 = 1 then b₁ else b₂) =
      ket fun i : Fin 3 =>
        if i.1 = 0 then b₀ else if i.1 = 1 then b₁ else xor b₂ (b₀ && b₁)
  -- 2. Controlled H^{⊗ n}
  ancCH : ℕ → ℕ
  chCirc : (n : ℕ) → Circuit gates12 (1 + n + ancCH n)
  chDepth : ℕ → ℕ
  ch_hdepth : ∀ (n : ℕ) (r : ℕ) (a : Fin r → ℕ),
    nonOracleDepth ((chCirc n).map OracleStep.gate : OracleCircuit gates12 a (1 + n + ancCH n)) ≤ chDepth n
  C_ch : ℝ
  hC_ch_pos : 0 < C_ch
  ch_bound : ∀ n : ℕ, 2 ≤ n →
    ((chCirc n).length : ℝ) ≤ C_ch * n ∧ (chDepth n : ℝ) ≤ C_ch * Real.log n
  ch_act : ∀ (n : ℕ) (c : Bool) (x : Qubits n),
    act (chCirc n).unitary (ket (packCH n (ancCH n) c x (fun _ => false))) =
      if c then
        ∑ y : Qubits n, (hadamardN n y x) • ket (packCH n (ancCH n) true y (fun _ => false))
      else
        ket (packCH n (ancCH n) false x (fun _ => false))
  -- 3. Multi-controlled 1-qubit unitary on equality
  ancEq : ℕ → ℕ
  eqCirc : (L : ℕ) → Qubits L → (U : Matrix Bool Bool ℂ) → U ∈ Matrix.unitaryGroup Bool ℂ →
    Circuit gates12 (L + 1 + ancEq L)
  eqDepth : ℕ → ℕ
  eq_hdepth : ∀ (L : ℕ) (pat : Qubits L) (U : Matrix Bool Bool ℂ)
    (hU : U ∈ Matrix.unitaryGroup Bool ℂ) (r : ℕ) (a : Fin r → ℕ),
    nonOracleDepth ((eqCirc L pat U hU).map OracleStep.gate : OracleCircuit gates12 a (L + 1 + ancEq L)) ≤ eqDepth L
  C_eq : ℝ
  hC_eq_pos : 0 < C_eq
  eq_bound : ∀ (L : ℕ) (pat : Qubits L) (U : Matrix Bool Bool ℂ) (hU : U ∈ Matrix.unitaryGroup Bool ℂ),
    ((eqCirc L pat U hU).length : ℝ) ≤ C_eq * (L + 1) ∧
    (eqDepth L : ℝ) ≤ C_eq * (Nat.clog 2 (L + 1) + 1 : ℕ)
  eq_act : ∀ (L : ℕ) (pat : Qubits L) (U : Matrix Bool Bool ℂ) (hU : U ∈ Matrix.unitaryGroup Bool ℂ)
    (addr : Qubits L) (tgt : Bool),
    act (eqCirc L pat U hU).unitary (ket (packEq L (ancEq L) addr tgt (fun _ => false))) =
      if addr = pat then
        ∑ b' : Bool, (U b' tgt) • ket (packEq L (ancEq L) addr b' (fun _ => false))
      else
        ket (packEq L (ancEq L) addr tgt (fun _ => false))
  -- 4. Hamming counter + its adjoint
  ancHC : ℕ → ℕ
  hcCirc : (n : ℕ) → Circuit gates12 (n + Nat.clog 2 (n + 1) + ancHC n)
  hcAdjCirc : (n : ℕ) → Circuit gates12 (n + Nat.clog 2 (n + 1) + ancHC n)
  hcDepth : ℕ → ℕ
  hc_hdepth : ∀ (n : ℕ) (r : ℕ) (a : Fin r → ℕ),
    nonOracleDepth ((hcCirc n).map OracleStep.gate :
      OracleCircuit gates12 a (n + Nat.clog 2 (n + 1) + ancHC n)) ≤ hcDepth n ∧
    nonOracleDepth ((hcAdjCirc n).map OracleStep.gate :
      OracleCircuit gates12 a (n + Nat.clog 2 (n + 1) + ancHC n)) ≤ hcDepth n
  hcAdj_length : ∀ n, (hcAdjCirc n).length = (hcCirc n).length
  hcAdj_unitary : ∀ n, (hcAdjCirc n).unitary = star (hcCirc n).unitary
  C_hc : ℝ
  hC_hc_pos : 0 < C_hc
  hc_bound : ∀ n : ℕ, 2 ≤ n →
    ((hcCirc n).length : ℝ) ≤ C_hc * n * Real.log n ∧ (hcDepth n : ℝ) ≤ C_hc * Real.log n
  hc_act : ∀ (n : ℕ) (x : Qubits n),
    act (hcCirc n).unitary (ket (packHC n (Nat.clog 2 (n + 1)) (ancHC n) x (fun _ => false) (fun _ => false))) =
      ket (packHC n (Nat.clog 2 (n + 1)) (ancHC n) x
        (natToBitsLSB (Nat.clog 2 (n + 1)) (hammingWeight x)) (fun _ => false))
  -- 5. Controlled-NOT^n (Eq. 127 negation)
  ancCN : ℕ → ℕ
  cnCirc : (n : ℕ) → Circuit gates12 (1 + n + ancCN n)
  cnDepth : ℕ → ℕ
  cn_hdepth : ∀ (n : ℕ) (r : ℕ) (a : Fin r → ℕ),
    nonOracleDepth ((cnCirc n).map OracleStep.gate : OracleCircuit gates12 a (1 + n + ancCN n)) ≤ cnDepth n
  C_cn : ℝ
  hC_cn_pos : 0 < C_cn
  cn_bound : ∀ n : ℕ, 2 ≤ n →
    ((cnCirc n).length : ℝ) ≤ C_cn * n ∧ (cnDepth n : ℝ) ≤ C_cn * Real.log n
  cn_act : ∀ (n : ℕ) (c : Bool) (x : Qubits n),
    act (cnCirc n).unitary (ket (packCN n (ancCN n) c x (fun _ => false))) =
      ket (packCN n (ancCN n) c (if c then (fun i => !(x i)) else x) (fun _ => false))
  -- 6. Multiplexed `U_tilde410` (coherent router + two-level rotations + comparison sign)
  ancUTilde : ℕ → ℕ → ℕ
  uTilde410Circ : (M n' : ℕ) → 1 ≤ M → 2 * M + 1 ≤ n' →
    Circuit gates12 (1 + Nat.clog 2 (n' + 1) + qW M + ancUTilde M n')
  uTilde410Depth : ℕ → ℕ → ℕ
  uTilde410_hdepth : ∀ (M n' : ℕ) (hM : 1 ≤ M) (hle : 2 * M + 1 ≤ n') (r : ℕ) (a : Fin r → ℕ),
    nonOracleDepth ((uTilde410Circ M n' hM hle).map OracleStep.gate :
      OracleCircuit gates12 a (1 + Nat.clog 2 (n' + 1) + qW M + ancUTilde M n')) ≤ uTilde410Depth M n'
  C_ut : ℝ
  hC_ut_pos : 0 < C_ut
  uTilde410_bound : ∀ (M n' : ℕ) (hM : 1 ≤ M) (hle : 2 * M + 1 ≤ n'), 3 ≤ n' →
    ((uTilde410Circ M n' hM hle).length : ℝ) ≤ C_ut * n' * Real.log n' ∧
    (uTilde410Depth M n' : ℝ) ≤ C_ut * Real.log n'
  uTilde410_act : ∀ (M n' : ℕ) (hM : 1 ≤ M) (hle : 2 * M + 1 ≤ n')
    (fc : Bool) (w : Qubits (Nat.clog 2 (n' + 1))) (mode : Qubits (qW M)),
    act (uTilde410Circ M n' hM hle).unitary
        (ket (packUTilde410 M n' (ancUTilde M n') fc w mode (fun _ => false))) =
      if fc then
        ∑ mode' : Qubits (qW M), (U_op410 M (bitsToNatLSB w) mode' mode) •
          ket (packUTilde410 M n' (ancUTilde M n') true w mode' (fun _ => false))
      else
        ket (packUTilde410 M n' (ancUTilde M n') false w mode (fun _ => false))

end QuantumLTF.Membership.Supplement.CoupledOp410


