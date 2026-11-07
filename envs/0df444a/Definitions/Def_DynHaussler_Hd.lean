-- Prove2me | Definitions.Def_DynHaussler_Hd
-- name    : DynHaussler_Hd
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:35:54.771996+00:00
-- url     : https://prove2.me/theorems/beadde3f-d5dd-4829-8f44-e2c4014d791e
-- title:
--   Fixed lower-bound class $H_d$ of zero-extended hyperplane indicators (Eq. (109))
-- statement:
--   For $m\ge1$, $a\in\mathbb F_{2^m}^d\setminus\{0\}$ and $b\in\mathbb F_{2^m}$, the **zero extension** of the hyperplane indicator $h_{a,b}$ to $X_d$ is
--   $$
--   \tilde h_{m,a,b}(n,x)=\begin{cases}h_{a,b}(x)=\mathbf 1\{a\cdot x=b\},& n=m,\\ 0,& n\neq m,\end{cases}
--   $$
--   and the **fixed class** is the union of all these extensions,
--   $$
--   H_d=\bigcup_{m\ge1}\{\tilde h_{m,a,b}: h_{a,b}\in H_{2^m}\}.
--   $$
--   It is a countable binary class depending only on $d$; Lemma 34 shows $\mathrm{Ldim}(H_d)=\mathrm{sfat}_\gamma(H_d)=d$, and Theorem 6 uses it for the matching lower bound.
--
--   **Formalization Note** $\tilde h_{m,a,b}$ is written as the real-valued indicator of the set $\{(m,x): a\cdot x=b\}\subseteq X_d$, which is $h_{a,b}$ on block $m$ and $0$ on every other block.
-- source:
--   Shao–Tao, A Sharp Dynamic Haussler Lemma, arXiv:2610.29898 (held version, sha256 b9ad736f…), Eqs. (106), (109), p.46 (PDF p.48)

import Mathlib
import Definitions.Def_DynHaussler_Xd

set_option autoImplicit false

namespace DynHaussler

/-- The **fixed lower-bound class** `H_d = ⋃_{m ≥ 1} {h̃_{m,a,b} : h_{a,b} ∈ H_{2^m}}` on `X_d`
(Eq. (109)): `h̃_{m,a,b}(n, x) = h_{a,b}(x) = 1{a · x = b}` if `n = m` and `0` if `n ≠ m`, for
`a ∈ F_{2^m}^d ∖ {0}`, `b ∈ F_{2^m}`.
Shao–Tao, *A Sharp Dynamic Haussler Lemma*, arXiv:2610.29898 (held version, sha256 b9ad736f…),
Eqs. (106), (109), p.46 (PDF p.48).

**Formalization Note** `h̃_{m,a,b}` is written as the indicator of
`{⟨m, x⟩ : a · x = b} ⊆ X_d`, which is `h_{a,b}` on block `m` and `0` on the other blocks;
values are the reals `0` and `1`. -/
noncomputable def Hd (d : ℕ) : Set (Xd d → ℝ) :=
  open Classical in
  {h | ∃ (m : ℕ+) (a : Fin d → GaloisField 2 (m : ℕ)) (b : GaloisField 2 (m : ℕ)), a ≠ 0 ∧
    h = fun p => if ∃ x : Fin d → GaloisField 2 (m : ℕ), p = ⟨m, x⟩ ∧ ∑ j, a j * x j = b
      then 1 else 0}

end DynHaussler


