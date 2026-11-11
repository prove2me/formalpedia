-- Prove2me | Definitions.Def_QVolKLS_MemAlgorithm
-- name    : QVolKLS_MemAlgorithm
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:38:47.346734+00:00
-- url     : https://prove2.me/theorems/5964b2d8-2297-4473-a2bf-9f6fcaf82232
-- title:
--   Membership-query algorithms over $\{H,T,\mathrm{CNOT}\}$: query count, gate count, dyadic output
-- statement:
--   A **membership-query algorithm** for convex bodies in $\mathbb R^d$, for one fixed input, consists of:
--
--   1. a number $N$ of qubits, all initialized to $|0\rangle$;
--   2. finitely many coordinate formats $(b_k,p_k)$, one membership oracle $O_K^{(k)}$ per format;
--   3. one quantum circuit on the $N$ qubits built from the gates $H$, $T$, $\mathrm{CNOT}$ and from calls (plain, inverse, or controlled by one further qubit) to the oracles $O_K^{(k)}$;
--   4. designated output qubits holding a two's-complement mantissa $m$ and a two's-complement exponent $e$.
--
--   Run on a body $K$, the circuit is applied to $|0^N\rangle$, every qubit is measured in the computational basis, and the output is the dyadic number $\hat V=m\cdot 2^{e}$ read from the outcome. The **query count** is the total number of oracle calls of any kind, and the **gate count** is the number of $H,T,\mathrm{CNOT}$ gates. The circuit does not depend on $K$: the body enters only through the oracles.
--
--   The **bit length** of a rational number is the binary length of the absolute value of its numerator plus that of its denominator; the bit length of the input $(x_0,r,R,\psi,\varepsilon)$ of the main theorem is the sum over the $d$ coordinates of $x_0$ and over $r,R,\psi,\varepsilon$.
--
--   This is the computational model in which the main theorem counts membership queries ("on every execution") and the remaining computation ("gate complexity").
--
--   **Formalization Note** Built on the published `QAlgorithms.OracleCircuit`, `queryCount`, `gateCount` and `htcxGateSet`. A controlled call counts as one query, whereas §2.4 charges it two ordinary calls; this changes counts by a factor at most $2$. Intermediate measurements and discards of the paper's algorithm are deferred to the final measurement, which changes no count.
-- source:
--   R. Zhang, Improved Upper and Lower Bounds for Quantum Convex-Body Volume Estimation, arXiv:2610.04987 (preprint, held version, sha256 eee7a45e7117af08035a8d75fd6f145fa82ddade51ad87a6507911b6a0aa4f80), §2, p.21; §2.4, p.23; Theorem 6.1, p.44; p.5 (gate complexity)

import Definitions.Def_QAlgorithms_Defs_GradientMethods
import Definitions.Def_QVolKLS_memOracle

set_option autoImplicit false

namespace QVolKLS

open QAlgorithms

/-!
# Quantum membership-query algorithms over {H, T, CNOT}

R. Zhang, *Improved Upper and Lower Bounds for Quantum Convex-Body Volume Estimation*,
arXiv:2610.04987 (held version, sha256 eee7a45e…), §2, p.21 ("All quantum circuits act on finite
registers"), §2.4, p.23 (the strong coherent membership oracle; "rotations are synthesized over the
fixed gate set"), Theorem 6.1, p.44 ("a quantum algorithm on finitely many qubits that outputs V̂";
"coherent membership queries on every execution"; "the remaining computation is polynomial … in the
bit length of the input"), and p.5 ("The gate complexity is polynomial …").

**Formalization Note.**
* An algorithm for a fixed input is one oracle circuit (`QAlgorithms.OracleCircuit`) over the gate
  set `htcxGateSet = {H, T, CNOT}` on `N` wires, started in `|0^N⟩`, whose oracles are membership
  oracles `memOracle K b_k p_k`, one per coordinate format `(b_k, p_k)` it uses. The circuit does not
  depend on `K`: `K` enters only through the oracles.
* Queries are `∑_k queryCount k`: every plain, inverse or controlled call to any membership oracle
  counts one (§2.4 charges a controlled call two ordinary calls; counting it once changes the count
  by a factor at most `2`). The remaining computation is `gateCount`, the number of `H`, `T`, `CNOT`
  gates.
* The circuit is unitary and the whole register is measured once at the end in the computational
  basis. Intermediate measurements and discards of the paper's algorithm are deferred to the end
  (deferred-measurement principle), which changes no query count.
* The output is read from designated wires by the fixed dyadic decoding `decodeDyadic`: a
  two's-complement mantissa `m` and a two's-complement exponent `e` give `V̂ = m · 2^e`. A fixed
  decoding keeps classical post-processing inside the gate count.
* `inputBitLen` is the total binary length of the rational inputs: for each rational, the bit
  length of the absolute value of its numerator plus that of its denominator.
-/

/-- The dyadic number `m · 2^e` written on output wires: `m` is the two's-complement integer on the
mantissa wires and `e` the two's-complement integer on the exponent wires (both most significant
bit first). -/
noncomputable def decodeDyadic {N w u : ℕ} (mant : Fin w ↪ Fin N) (expo : Fin u ↪ Fin N)
    (z : Qubits N) : ℝ :=
  (twosComp (z ∘ mant) : ℝ) * (2 : ℝ) ^ (twosComp (z ∘ expo))

/-- The binary length of a rational number: bit length of `|numerator|` plus bit length of the
denominator. -/
def ratBitLen (q : ℚ) : ℕ :=
  Nat.size q.num.natAbs + Nat.size q.den

/-- The bit length of the input `(x₀, r, R, ψ, ε)` of Theorem 6.1: the sum of the binary lengths
of the `d` coordinates of `x₀` and of `r`, `R`, `ψ`, `ε`. -/
def inputBitLen {d : ℕ} (x0 : Fin d → ℚ) (r R ψ ε : ℚ) : ℕ :=
  (∑ j, ratBitLen (x0 j)) + ratBitLen r + ratBitLen R + ratBitLen ψ + ratBitLen ε

/-- A quantum membership-query algorithm for convex bodies in `ℝ^d` (for one fixed input): `N`
wires, `s` coordinate formats `fmt k = (b_k, p_k)`, one oracle circuit over `{H, T, CNOT}` whose
oracle `k` acts on `d·b_k + 1` wires, and the output wires (mantissa and exponent). -/
structure MemAlgorithm (d : ℕ) where
  /-- Number of wires (qubits). -/
  N : ℕ
  /-- Number of coordinate formats (one membership oracle per format). -/
  s : ℕ
  /-- The coordinate formats `(b, p)`: `b` bits per coordinate, scale `2^{-p}`. -/
  fmt : Fin s → ℕ × ℕ
  /-- The circuit over `{H, T, CNOT}` with membership-oracle calls. -/
  circuit : OracleCircuit htcxGateSet (fun k : Fin s => d * (fmt k).1 + 1) N
  /-- Number of mantissa wires. -/
  w : ℕ
  /-- Number of exponent wires. -/
  u : ℕ
  /-- The mantissa wires. -/
  mant : Fin w ↪ Fin N
  /-- The exponent wires. -/
  expo : Fin u ↪ Fin N

namespace MemAlgorithm

variable {d : ℕ}

/-- Total number of membership queries: calls (plain, inverse or controlled) to all oracles. -/
def queries (A : MemAlgorithm d) : ℕ :=
  ∑ k, A.circuit.queryCount k

/-- Number of elementary gates (`H`, `T`, `CNOT`). -/
def gates (A : MemAlgorithm d) : ℕ :=
  A.circuit.gateCount

/-- The final state `U_K |0^N⟩` when the oracles answer membership in `K`. -/
noncomputable def finalState (A : MemAlgorithm d) (K : Set (Euc d)) :
    EuclideanSpace ℂ (Qubits A.N) :=
  act (A.circuit.unitary (fun k => memOracle K (A.fmt k).1 (A.fmt k).2)) (zeroKet A.N)

/-- The output `V̂` read from a measured basis string. -/
noncomputable def outputValue (A : MemAlgorithm d) (z : Qubits A.N) : ℝ :=
  decodeDyadic A.mant A.expo z

/-- The probability, for the body `K`, that the measured output `V̂` lies in the set `S`. -/
noncomputable def outProb (A : MemAlgorithm d) (K : Set (Euc d)) (S : Set ℝ) : ℝ :=
  haveI := Classical.decPred (fun z : Qubits A.N => A.outputValue z ∈ S)
  probEvent (A.finalState K) (fun z => A.outputValue z ∈ S)

end MemAlgorithm

end QVolKLS


