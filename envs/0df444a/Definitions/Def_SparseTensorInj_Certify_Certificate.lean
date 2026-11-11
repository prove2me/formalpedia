-- Prove2me | Definitions.Def_SparseTensorInj_Certify_Certificate
-- name    : SparseTensorInj_Certify_Certificate
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T01:38:15.70786+00:00
-- url     : https://prove2.me/theorems/f2fc3ffa-2d4d-461b-82bd-8dbe9c633ad9
-- title:
--   The certificate $u_k$ of Theorem 5: Definition 37 for even $k$, eq. (9) for odd $k$
-- statement:
--   For an order-$k$ tensor $T$ over $\mathbb R^n$ the paper's certificate is
--   $$u_k(T)=\begin{cases}\|A(T)\|_{\mathrm{op}}&k=2q\ \text{(Definition 37)},\\ \|T-T^\circ\|_F+\frac{(2q+1)!}{2\cdot q!}\sqrt{\|M\|_{\mathrm{op}}+2d_{\max}}&k=2q+1\ \text{(eq. (9))}.\end{cases}$$
--   It is computed from $T$ alone (not from $\sigma$, $\gamma$ or the law of the entries), and the paper shows it is computable in polynomial time for fixed $k$ (pp. 24 and 54). Theorem 5 is stated for this certificate.
--
--   **Formalization Note.** With $q=\lfloor k/2\rfloor$, the tensor is re-indexed along $k=q+q$ (even) or $k=2q+1$ (odd) by `Fin.cast`; parity is tested by `k % 2 = 0`.
-- source:
--   Kothari, Louis, Paul, Raghavendra, Improved Bounds for Certifying Injective Norm of Sparse Random Tensors, STOC 2027 submission (manuscript of November 3, 2026, sha256 e46cf53d…), p. 4, Theorem 5; p. 22, Definition 37; p. 26, eq. (9)

import Mathlib
import Definitions.Def_SparseTensorInj_Certify_EvenCertificate
import Definitions.Def_SparseTensorInj_Certify_OddCertificate

namespace SparseTensorInj.Certify

/-- The paper's certificate `u_k` for order-`k` tensors (Theorem 5, Propositions 36 and 44):
for even `k = 2q` it is `‖A(T)‖_op` (Definition 37), for odd `k = 2q + 1` it is eq. (9). The
tensor is re-indexed along the identity `k = q + q`, resp. `k = 2q + 1`, with `q = ⌊k/2⌋`. -/
noncomputable def certificate (k n : ℕ) (T : Tensor k n) : ℝ :=
  if h : k % 2 = 0 then
    evenCert (q := k / 2) (fun i => T (i ∘ Fin.cast (by omega)))
  else
    oddCert (q := k / 2) (fun i => T (i ∘ Fin.cast (by omega)))

end SparseTensorInj.Certify


