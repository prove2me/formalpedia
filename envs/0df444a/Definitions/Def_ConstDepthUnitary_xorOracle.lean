-- Prove2me | Definitions.Def_ConstDepthUnitary_xorOracle
-- name    : ConstDepthUnitary_xorOracle
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:45:00.222416+00:00
-- url     : https://prove2.me/theorems/d8db1043-080d-4f4c-91c1-95af70fdcda0
-- title:
--   Computing a Boolean function into a target qubit
-- statement:
--   For $g:\{0,1\}^r\to\{0,1\}$, the permutation matrix of
--   $$|x\rangle|b\rangle\mapsto|x\rangle|b\oplus g(x)\rangle$$
--   on $r$ controls and one target, on all basis states, together with the functions AND and OR of $r$ bits.
-- source:
--   Nehoran, Slote, Yuen, All Unitaries Have Constant Depth Quantum Circuits, arXiv:2609.40351 (version of 2026-11-03, sha256 45cfb6a7…), Lemma 6.4, p.36; Algorithm 2, Step 3, p.37

import Mathlib

namespace ConstDepthUnitary

/-- The gate computing `g` into a target qubit: `|x, b⟩ ↦ |x, b ⊕ g(x)⟩` on `r` controls and a target.

Nehoran, Slote, Yuen, *All Unitaries Have Constant Depth Quantum Circuits*, arXiv:2609.40351 (version of 2026-11-03, sha256 45cfb6a7…), Lemma 6.4, p.36; Algorithm 2, Step 3, p.37. -/
noncomputable def xorOracle {r : ℕ} (g : (Fin r → Bool) → Bool) :
    Matrix (Fin r ⊕ Unit → Bool) (Fin r ⊕ Unit → Bool) ℂ :=
  Matrix.of fun y x =>
    if y = Sum.elim (fun i => x (Sum.inl i))
        (fun _ => xor (x (Sum.inr ())) (g fun i => x (Sum.inl i))) then 1 else 0

/-- The AND of `r` bits. -/
def andFn {r : ℕ} (x : Fin r → Bool) : Bool := decide (∀ i, x i = true)

/-- The OR of `r` bits. -/
def orFn {r : ℕ} (x : Fin r → Bool) : Bool := decide (∃ i, x i = true)

end ConstDepthUnitary


