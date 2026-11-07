-- Prove2me | Definitions.Def_CutwidthCircuitLB_B2Circuit_prefixValues
-- name    : CutwidthCircuitLB_B2Circuit_prefixValues
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:25:43.82075+00:00
-- url     : https://prove2.me/theorems/797b2625-ef96-4f64-a287-bc5ea9019648
-- title:
--   Gate values of a $B_2$-circuit
-- statement:
--   For a $B_2$-circuit $C$ and an input $x \in \{0,1\}^n$, the value of a gate $g$ is obtained by applying the Boolean function of $g$ to the values of its two predecessors: the input bit $x_j$ for a variable $x_j$, and the (already computed) value of an earlier gate otherwise. This definition computes the values of the first $k$ gates, $k \le s$, by recursion along the topological order.
--
--   It is the evaluation step behind the circuit's output $C(x)$.
-- source:
--   McGuire–Schlesinger–Williams, Explicit functions requiring larger than 4.5n size circuits, STOC 2027 submission (manuscript sha256 ed87148f…cfa3), Definition 2.1, p.6

import Mathlib
import Definitions.Def_CutwidthCircuitLB_B2Circuit

namespace CutwidthCircuitLB

/-- The values of the first `k` gates of a B₂-circuit `C` on the input `x ∈ {0,1}ⁿ`
(McGuire–Schlesinger–Williams, *Explicit functions requiring larger than 4.5n size circuits*, STOC 2027 submission manuscript (sha256 ed87148f…cfa3), Definition 2.1, p.6): gate `g` applies its function `op g` to the values of its two
predecessors (an input bit `x j`, or the value of an earlier gate). Defined by recursion on `k`,
following the topological order of the gates. -/
def B2Circuit.prefixValues {n : ℕ} (C : B2Circuit n) (x : Fin n → Bool) :
    (k : ℕ) → k ≤ C.size → Fin k → Bool
  | 0, _ => Fin.elim0
  | k + 1, hk =>
    let prev := C.prefixValues x k (Nat.le_of_succ_le hk)
    let g : Fin C.size := ⟨k, hk⟩
    let sig : Fin n ⊕ Fin k → Bool := Sum.elim x prev
    Fin.snoc (α := fun _ => Bool) prev (C.op g (sig (C.pred₁ g)) (sig (C.pred₂ g)))

end CutwidthCircuitLB


