-- Prove2me | Definitions.Def_QiOPoQ_Supplement_IsUniversal
-- name    : QiOPoQ_Supplement_IsUniversal
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:02:10.862182+00:00
-- url     : https://prove2.me/theorems/664a77a9-fbdc-4257-b3d2-7ee5c8900c2a
-- title:
--   A finite universal gate set
-- statement:
--   A gate set is universal if:
--
--   1. for every $n$, every unitary $U$ on $n$ qubits and every $\varepsilon>0$, some ancilla-free circuit over the gate set implements $U$ up to a global phase within $\varepsilon$ in operator norm; and
--   2. every entry of every gate matrix can be approximated to within $2^{-m}$ by a dyadic number computed from $1^m$ in polynomial time.
--
--   **Formalization Note** Clause 2 is the standing premise of the Solovay–Kitaev algorithm, which the proof of Theorem 6.7 cites for polynomial-time gate synthesis [DN06]; every concrete finite gate set such as Clifford+T has it. The published `QiOPoQ.GateSet` has no universality field, so Theorems 5.3 and 6.7 take this as a hypothesis.
-- source:
--   Gheorghiu, Gupte, Havlíček, Liu, Verifiable Quantum Advantage and Computation via Quantum Circuit Obfuscation, arXiv:2609.40289 (sha256 fe2f9210…), §3.1, p.13; Notation 6.1, p.30; proof of Theorem 6.7, p.34

import Mathlib
import Definitions.Def_QAlgorithms_ClassicalStringComputability
import Definitions.Def_QAlgorithms_ClassicalUnaryInput
import Definitions.Def_QAdvFew_PoQOracle_tup
import Definitions.Def_QiOPoQ_chan
import Definitions.Def_QiOPoQ_Supplement_opNorm
import Definitions.Def_QiOPoQ_Supplement_Placement

set_option autoImplicit false

namespace QiOPoQ.Supplement

open QAlgorithms.Complexity QAdvFew.PoQOracle

/-- An integer as a string: its sign bit and the binary digits of its absolute value (least
significant first), as a tuple. -/
def encZ (z : ℤ) : Str := tup [[decide (z < 0)], Nat.bits z.natAbs]

/-- The unitary `U_C` of the ancilla-free `n`-qubit circuit with gate list `gs`. -/
noncomputable def afUnitary {G : GateSet} (n : ℕ) (gs : List (Placement G n)) :
    Matrix (Fin (n + 0) → Bool) (Fin (n + 0) → Bool) ℂ :=
  circUnitary (afCirc n gs)

/-- **A finite universal gate set.** Gheorghiu, Gupte, Havlíček, Liu, *Verifiable Quantum
Advantage and Computation via Quantum Circuit Obfuscation*, arXiv:2609.40289 (sha256 fe2f9210…),
§3.1, p.13: "We fix a finite universal gate set, so that the gate count and description length are
polynomially related"; Notation 6.1, p.30: "Use the fixed finite universal gate set of Section
3.1"; proof of Theorem 6.7, p.34: "phase rotations can be synthesized to the required accuracy in
polynomial time [DN06]".

1. (density) for every `n`, every unitary `U` on `n` qubits and every `ε > 0` some ancilla-free
   circuit over `G` on `n` qubits implements `U` up to a global phase within `ε` in operator
   norm; and
2. (computable gates) every matrix entry of every gate is computable to `m` bits in time
   polynomial in `m`: a dyadic approximation `(a_m + i b_m)/2^m` within `2^{−m}` is computed from
   `1^m` in polynomial time.

**Formalization Note.** Clause 2 is the standing premise under which the Solovay–Kitaev algorithm
[DN06], which the paper cites, synthesizes circuits in polynomial time; every concrete finite gate
set (e.g. Clifford+T) has it. The published `QiOPoQ.GateSet` carries no universality, so the
theorems that use it (Theorems 5.3 and 6.7) take `IsUniversal G` as a hypothesis. -/
def IsUniversal (G : GateSet) : Prop :=
  (∀ (n : ℕ) (U : Matrix (Fin (n + 0) → Bool) (Fin (n + 0) → Bool) ℂ),
      U ∈ Matrix.unitaryGroup (Fin (n + 0) → Bool) ℂ → ∀ ε : ℝ, 0 < ε →
      ∃ (gs : List (Placement G n)) (θ : ℝ),
        opNorm (afUnitary n gs - Complex.exp (θ * Complex.I) • U) ≤ ε) ∧
    ∀ (i : Fin G.k) (y y' : Fin (G.arity i) → Bool), ∃ a b : ℕ → ℤ,
      (∀ m : ℕ, ‖G.mat i y y' - ((a m : ℂ) + (b m : ℂ) * Complex.I) / 2 ^ m‖ ≤ 1 / 2 ^ m) ∧
      ∃ g : Str → Str, PolyTimeComputable g ∧ ∀ m, g (unary m) = tup [encZ (a m), encZ (b m)]

end QiOPoQ.Supplement


