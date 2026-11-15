-- Prove2me | Definitions.Def_QuantumLTF_Example_qex
-- name    : QuantumLTF_Example_qex
-- status  : Definition
-- author  : @stockfish-soup
-- created : 2026-11-14T17:54:20.684196+00:00
-- url     : https://prove2.me/theorems/7374b08d-671b-4467-8952-1126d405add7
-- title:
--   Discretized Gaussian quantum-example oracle for homogeneous LTFs
-- statement:
--   For $M=2^q$, let the one-dimensional grid have spacing $\Delta=\sqrt{4\pi/M}$ and $M$ centered points, and give each $n$-dimensional grid point $x$ weight proportional to $e^{-\|x\|^2/2}$. For a unit vector $w$, the labeled quantum-example state is
--
--   $$
--   |\psi_{w,M}\rangle=\sum_x\sqrt{\gamma_{n,M}(x)}\,|x\rangle|\bar f_w(x)\rangle,\qquad f_w(x)=\operatorname{sign}\langle w,x\rangle.
--   $$
--
--   A valid oracle is any unitary that maps the all-zero state to this vector; its action on the orthogonal complement is unrestricted. This is the finite state-preparation access model used in Section 5.
--
--   **Formalization Note** Grid indices are encoded most-significant-bit first. The label bit is `true` exactly for the value $-1$, and the sign convention at zero is $+1$.
-- source:
--   Krivcenko, Nguyen, de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, arXiv:2609.40331v3, Section 1.5 pp. 10–11 and Section 5.1 pp. 57–58 (PDF pp. 11–12, 58–59), especially the definition of QEX_M and equations defining Δ and the discretized Gaussian normalization

import Mathlib
import Definitions.Def_QuantumLTF_Membership_ltf

namespace QuantumLTF.Example

open QuantumLTF.Membership

def bitsValue {q : ℕ} (z : Fin q → Bool) : ℕ :=
  ∑ j : Fin q, if z j then 2 ^ (q - 1 - j.1) else 0

noncomputable def gridPoint {n q : ℕ} (z : Fin (n * q) → Bool) :
    EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 fun i =>
    ((bitsValue fun j : Fin q => z ⟨i.1 * q + j.1, by
        have hi : i.1 < n := i.2
        have hj : j.1 < q := j.2
        calc
          i.1 * q + j.1 < i.1 * q + q := Nat.add_lt_add_left hj _
          _ = (i.1 + 1) * q := by simp [Nat.add_mul]
          _ ≤ n * q := Nat.mul_le_mul_right q (Nat.succ_le_iff.mpr hi)⟩ : ℝ) -
      (2 ^ (q - 1) : ℕ)) * Real.sqrt (4 * Real.pi / 2 ^ q)

noncomputable def gridWeight {n q : ℕ} (z : Fin (n * q) → Bool) : ℝ :=
  Real.exp (-‖gridPoint z‖ ^ 2 / 2)

noncomputable def qexKet {n q : ℕ} (w : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℂ (Fin (n * q + 1) → Bool) :=
  let Z := ∑ x : Fin (n * q) → Bool, gridWeight x
  WithLp.toLp 2 fun z =>
    let x : Fin (n * q) → Bool := fun i => z i.castSucc
    if z (Fin.last (n * q)) = decide (ltf w 0 (gridPoint x) = -1) then
      (Real.sqrt (gridWeight x / Z) : ℂ)
    else 0

def IsQEX {n q : ℕ} (w : EuclideanSpace ℝ (Fin n))
    (U : Matrix (Fin (n * q + 1) → Bool) (Fin (n * q + 1) → Bool) ℂ) : Prop :=
  U ∈ Matrix.unitaryGroup (Fin (n * q + 1) → Bool) ℂ ∧
    U.mulVec (Pi.single (fun _ => false) 1) = qexKet w

end QuantumLTF.Example


