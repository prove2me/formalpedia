-- Prove2me | Definitions.Def_QaryCVP_matAvg
-- name    : QaryCVP_matAvg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T09:58:19.892199+00:00
-- url     : https://prove2.me/theorems/e1300215-1b94-451a-babc-14a778922f92
-- title:
--   Uniform averages over matrices and vectors in $(\mathbb Z/q\mathbb Z)$
-- statement:
--   In the random input model the entries of $H\in(\mathbb Z/q\mathbb Z)^{m\times n}$ are independent and uniform. For a function $f$ of the matrix, its average is
--
--   $$\mathbb E_H[f(H)]=q^{-mn}\sum_{H\in(\mathbb Z/q\mathbb Z)^{m\times n}} f(H),$$
--
--   and the **fraction** of matrices with a property $P$ is the average of its indicator. The average over a uniform right-hand side $t\in(\mathbb Z/q\mathbb Z)^m$ is $q^{-m}\sum_t f(t)$.
--
--   "All but a $2^{-\Omega(n^{2/3})}$ fraction of matrices" in the paper is a statement about this fraction.
--
--   **Formalization Note** The value at $q=0$ (where $\mathbb Z/0\mathbb Z=\mathbb Z$ is infinite) is a junk $0$; every statement using these averages assumes $q\ge2$.
-- source:
--   Kim, Kwon, Lee, Lee, Fast Provable Algorithms for Approximate CVP and Exact SVP on Random q-ary Lattices, STOC 2027 submission manuscript (sha256 9aeb2ff4…ab4), §2.3 (random input model), p.14

import Mathlib

namespace QaryCVP

open Classical in
/-- The average of `f` over a uniform matrix `H ∈ (Z/qZ)^{m×n}` (random input model, §2.3,
p.14: "the entries of H are sampled independently and uniformly from Z/qZ").
Kim, Kwon, Lee, Lee, STOC 2027 submission manuscript (sha256 9aeb2ff4…ab4), §2.3, p.14.

**Formalization Note.** `(Σ_H f H) / q^{mn}`. At `q = 0` (where `ZMod 0 = ℤ` is infinite) the value
is the junk `0`; every statement using it assumes `q ≥ 2`. -/
noncomputable def matAvg (q m n : ℕ) (f : Matrix (Fin m) (Fin n) (ZMod q) → ℝ) : ℝ :=
  if h : q = 0 then 0 else
    haveI : NeZero q := ⟨h⟩
    (∑ H : Matrix (Fin m) (Fin n) (ZMod q), f H) / (q : ℝ) ^ (m * n)

open Classical in
/-- The fraction of matrices `H ∈ (Z/qZ)^{m×n}` with property `P` (R5: a count over the `q^{mn}`
matrices, as a real number). -/
noncomputable def matFrac (q m n : ℕ) (P : Matrix (Fin m) (Fin n) (ZMod q) → Prop) : ℝ :=
  matAvg q m n (fun H => if P H then 1 else 0)

open Classical in
/-- The average of `f` over a uniform vector `t ∈ (Z/qZ)^m` (junk `0` at `q = 0`). -/
noncomputable def vecAvg (q m : ℕ) (f : (Fin m → ZMod q) → ℝ) : ℝ :=
  if h : q = 0 then 0 else
    haveI : NeZero q := ⟨h⟩
    (∑ t : Fin m → ZMod q, f t) / (q : ℝ) ^ m

end QaryCVP


