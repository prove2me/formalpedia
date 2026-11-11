-- Prove2me | Definitions.Def_UnitaryQIPPSPACE_OCirc
-- name    : UnitaryQIPPSPACE_OCirc
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:30:34.206228+00:00
-- url     : https://prove2.me/theorems/64afda2c-039b-4b63-bcc7-c2b1bd7facee
-- title:
--   Unitary oracle circuits, the isometry $\iota$, and $\Phi(\rho)=\operatorname{tr}_E[C\iota\rho\iota^\dagger C^\dagger]$
-- statement:
--   A **unitary oracle circuit** is a sequence of gates from $\{H,T,\mathrm{CNOT}\}$ and oracle queries, acting on data qubits followed by an ancillary register $E$. A query on qubits $(q_0,\dots,q_{\ell-1},t)$ with oracle $f$ applies $O_f:|x,b\rangle\mapsto|x,b\oplus f(x)\rangle$. Its unitary $C^f$ is the ordered product of its operations; its size is the number of operations; its description lists the ancilla count and the operations.
--
--   $\iota:|\psi\rangle_Q\mapsto|\psi\rangle_Q|0\rangle_E$ is the canonical isometry; for Theorem 4.6 the isometry $|\lambda\rangle_L|\psi\rangle_Q\mapsto|\lambda\rangle_L|\psi\rangle_Q|0\rangle_E$ on $\mathbb C^{2^t}\otimes\mathcal H_d$. The channel of the circuit with oracle $f$ is
--   $$\Phi(\rho)=\operatorname{tr}_E\big[C^f\iota\rho\iota^\dagger(C^f)^\dagger\big].$$
--   The module also defines the oracle of a language and the query weight $K=\sum_i(\ell_i+1)$.
--
--   **Formalization Note** $\mathcal H_d=\operatorname{span}\{|0\rangle,\dots,|d-1\rangle\}$ uses binary expansions with the most significant bit first.
-- source:
--   He, Ou, Zhao, unitaryQIP = unitaryPSPACE, arXiv:2611.02819 (held version, sha256 9e357a00…ead793), §2 (oracle circuits); Lemma 4.7; Theorem 4.6; Corollary 4.8, p.10 (PDF p.12)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Complexity
import Definitions.Def_QAdvFew_PoQOracle_tup
import Definitions.Def_UnitaryQIPPSPACE_Bits
import Definitions.Def_UnitaryQIPPSPACE_embed1
import Definitions.Def_UnitaryQIPPSPACE_conjBy

open Matrix QAlgorithms.Complexity QAdvFew.PoQOracle

namespace UnitaryQIPPSPACE

/-- An operation of a **unitary oracle circuit** (He, Ou, Zhao, *unitaryQIP = unitaryPSPACE*,
arXiv:2611.02819, held version sha256 9e357a00…, §2, p. 10 (PDF p. 12): "An oracle circuit `C^{(·)}`
is a quantum circuit that interleaves its own quantum operations with calls to an unspecified Boolean
oracle. When the circuit is unitary, we denote it by an operator `C^{(·)}`"; Lemma 4.7 and
Theorem 4.6, p. 25: "The circuit consists only of unitary gates and oracle queries").

* `hadamard i`, `tgate i`, `cnot i j`: a gate from `G = {H, T, CNOT}`;
* `query qs`: a call to the oracle on the `ℓ + 1` qubits `qs = [q₀, …, q_{ℓ−1}, t]`, acting as `O_f`
  ("we write `O_f` for the unitary on `ℓ + 1` qubits that maps `|x, b⟩` to `|x, b ⊕ f(x)⟩`", p. 9),
  with `x` read from `q₀, …, q_{ℓ−1}` and `b` the target qubit `t`. -/
inductive OOp where
  | hadamard (i : ℕ)
  | tgate (i : ℕ)
  | cnot (i j : ℕ)
  | query (qs : List ℕ)

/-- A **unitary oracle circuit**: an ancilla count `anc` and the operations, applied first to last.
On a register of `k` data qubits it acts on `k + anc` qubits, the data first (register `Q`, or
`L` then `Q`) and the `anc` ancillary qubits last (register `E`). -/
structure OCirc where
  /-- number of ancillary qubits (register `E`) -/
  anc : ℕ
  /-- the operations -/
  ops : List OOp

/-- The value of qubit `i` in a basis label (`false` out of range). -/
def bitAt {k : ℕ} (u : Bits k) (i : ℕ) : Bool := if h : i < k then u ⟨i, h⟩ else false

namespace OOp

/-- The operation is well formed on `k` qubits: every qubit exists; the qubits of a `CNOT` are
distinct; a query names at least one (target) qubit and no qubit twice. -/
def Valid : OOp → ℕ → Prop
  | hadamard i, k => i < k
  | tgate i, k => i < k
  | cnot i j, k => i < k ∧ j < k ∧ i ≠ j
  | query qs, k => qs ≠ [] ∧ qs.Nodup ∧ ∀ i ∈ qs, i < k

/-- The classical action `|x, b⟩ ↦ |x, b ⊕ f(x)⟩` of a query on the basis label `u`. -/
def queryMap {k : ℕ} (f : Str → Bool) (qs : List ℕ) (u : Bits k) : Bits k :=
  match qs.getLast? with
  | none => u
  | some t => fun j => if j.val = t then Bool.xor (u j) (f (qs.dropLast.map (bitAt u))) else u j

/-- The matrix of an operation on `k` qubits with oracle `f`. -/
noncomputable def mat (f : Str → Bool) : OOp → (k : ℕ) → Matrix (Bits k) (Bits k) ℂ
  | hadamard i, k => embed1 gateH k i
  | tgate i, k => embed1 gateT k i
  | cnot i j, k => embed2 gateCNOT k i j
  | query qs, _ => fun u' u => if u' = queryMap f qs u then 1 else 0

/-- The description of an operation: tag `1^r` (`r = 0, 1, 2, 3`), then the binary codes of its
qubits, joined by `tup`. -/
def code : OOp → Str
  | hadamard i => tup [List.replicate 0 true, natCode i]
  | tgate i => tup [List.replicate 1 true, natCode i]
  | cnot i j => tup [List.replicate 2 true, natCode i, natCode j]
  | query qs => tup (List.replicate 3 true :: qs.map natCode)

end OOp

namespace OCirc

/-- The circuit is well formed on `k` data qubits (every operation valid on `k + anc` qubits). -/
def Valid (C : OCirc) (k : ℕ) : Prop := ∀ o ∈ C.ops, o.Valid (k + C.anc)

/-- The size: the number of operations. -/
def size (C : OCirc) : ℕ := C.ops.length

/-- The unitary `C^f` on `k` qubits: the ordered product of the operations with oracle `f`. -/
noncomputable def mat (C : OCirc) (f : Str → Bool) (k : ℕ) : Matrix (Bits k) (Bits k) ℂ :=
  C.ops.foldl (fun M o => o.mat f k * M) 1

/-- The description: the ancilla count, then the operations, joined by `tup`. -/
def code (C : OCirc) : Str := tup (natCode C.anc :: C.ops.map OOp.code)

/-- The total number `K = ∑_i (ℓ_i + 1)` of qubits acted on by the queries (eq. (21), p. 33). -/
def queryWeight (C : OCirc) : ℕ :=
  (C.ops.map fun o => match o with
    | OOp.query qs => qs.length
    | _ => 0).sum

end OCirc

open Classical in
/-- A language `A ⊆ {0,1}*` as a Boolean oracle (its characteristic function). -/
noncomputable def langOracle (A : Set Str) : Str → Bool := fun s => decide (s ∈ A)

/-- The canonical isometry `ι : |ψ⟩_Q ↦ |ψ⟩_Q |0⟩_E` from `n` qubits into `n + e` qubits ("We use
`ι: |x⟩ ↦ |x⟩|0⟩` to denote the canonical isometry that appends the workspace qubits with ancillae
initialized to `|0⟩`", p. 9). -/
def iota (n e : ℕ) : Matrix (Bits (n + e)) (Bits n) ℂ :=
  fun u x => if u = Fin.append x (Bits.zero e) then 1 else 0

/-- The isometry `ι : |λ⟩_L |ψ⟩_Q ↦ |λ⟩_L |ψ⟩_Q |0⟩_E` for `|ψ⟩ ∈ H_d = span{|0⟩, …, |d−1⟩}`
(Theorem 4.6, p. 25), with domain `ℂ^{2^t} ⊗ ℂ^d`: the basis vector `|j⟩` of `H_d` is the
computational basis state of the `n`-qubit binary expansion of `j` (most significant bit first). -/
def iotaLd (t n d e : ℕ) : Matrix (Bits (t + n + e)) (Bits t × Fin d) ℂ :=
  fun u x => if u = Fin.append (Fin.append x.1 (Bits.ofNat n x.2.val)) (Bits.zero e) then 1 else 0

/-- The channel `Φ(ρ) := tr_E[C^f · ιρι† · (C^f)†]` on `n` qubits (Corollary 4.8, p. 26; Lemma 4.18,
p. 35): initialize the ancillary register `E` to `|0⟩`, apply the unitary oracle circuit with
oracle `f`, discard `E`. -/
noncomputable def oracleChannel (f : Str → Bool) (C : OCirc) (n : ℕ)
    (ρ : Matrix (Bits n) (Bits n) ℂ) : Matrix (Bits n) (Bits n) ℂ :=
  let X := conjBy (C.mat f (n + C.anc) * iota n C.anc) ρ
  fun x x' => ∑ e : Bits C.anc, X (Fin.append x e) (Fin.append x' e)

end UnitaryQIPPSPACE


