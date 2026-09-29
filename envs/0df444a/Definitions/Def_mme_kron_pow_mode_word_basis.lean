-- Prove2me | Definitions.Def_mme_kron_pow_mode_word_basis
-- name    : mme_kron_pow_mode_word_basis
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-08-26T08:04:50.795395+00:00
-- url     : https://prove2.me/theorems/6000ddc0-c89e-4659-8982-0fe4130e701b
-- title:
--   Recursive word bases for a tensor-power mode
-- statement:
--   Let $T$ be an order-three tensor, fix one of its mode spaces, and choose a basis indexed by a finite type $I$. For every $n\geq0$, this definition constructs the tensor-product basis of the same mode of $T^{\otimes n}$, indexed by recursive words of length $n$ in $I$. The empty power has one empty word, and the successor power prepends one letter.
--
--   This gives a position-addressable basis for the small-block words occurring in tensor powers. In particular, it remains valid at exponent zero and therefore does not require a hidden positivity assumption.
--
--   **Formalization Note** Recursive words mirror the existing recursive definition $T^{\otimes(n+1)}=T\otimes T^{\otimes n}$ exactly; a `get` operation reads their letter at any position in $[n]$.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Definition 5.3, PDF p. 48 / printed p. 47 (small blocks indexed by words of length 2N); https://arxiv.org/abs/2210.10173

import Definitions.Def_mme_tensor
import Mathlib.LinearAlgebra.TensorProduct.Basis

open MME Module TensorProduct

universe u

namespace MME.DWZComponentRestriction

set_option autoImplicit false
set_option warningAsError true

variable {K : Type u} [Field K]

/-- Recursive word indices matching the recursive representation of
`TensorObj.kronPow`. -/
def PowIndex (ι : Type u) : ℕ → Type u
  | 0 => PUnit
  | n + 1 => ι × PowIndex ι n

instance powIndexFintype (ι : Type u) [Fintype ι] :
    (n : ℕ) → Fintype (PowIndex ι n)
  | 0 => by
      change Fintype PUnit
      infer_instance
  | n + 1 => by
      change Fintype (ι × PowIndex ι n)
      letI := powIndexFintype ι n
      infer_instance

instance powIndexDecidableEq (ι : Type u) [DecidableEq ι] :
    (n : ℕ) → DecidableEq (PowIndex ι n)
  | 0 => by
      change DecidableEq PUnit
      infer_instance
  | n + 1 => by
      change DecidableEq (ι × PowIndex ι n)
      letI := powIndexDecidableEq ι n
      infer_instance

/-- The empty recursive word has its canonical unique inhabitant. -/
instance powIndexUniqueZero (ι : Type u) : Unique (PowIndex ι 0) := by
  change Unique PUnit
  infer_instance

/-- Read a recursive word at a position in `Fin n`. -/
def PowIndex.get {ι : Type u} : (n : ℕ) → PowIndex ι n → Fin n → ι
  | 0, _, j => j.elim0
  | n + 1, w, j => Fin.cases w.1 (fun r => PowIndex.get n w.2 r) j

/-- The tensor-product basis of one mode of a recursively represented tensor
power. -/
noncomputable def kronPowModeBasis
    (T : TensorObj K 3) (i : Fin 3) {ι : Type u}
    (b : Basis ι K (T.V i)) :
    (n : ℕ) → Basis (PowIndex ι n) K ((T.kronPow n).V i)
  | 0 => Basis.singleton (PowIndex ι 0) K
  | n + 1 => by
      letI : IsScalarTower K K (T.V i) :=
        IsScalarTower.of_algebraMap_smul (by simp)
      exact Module.Basis.tensorProduct b (kronPowModeBasis T i b n)

end MME.DWZComponentRestriction


