-- Prove2me | Definitions.Def_SeqHolevo_idArr
-- name    : SeqHolevo_idArr
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T17:57:00.71991+00:00
-- url     : https://prove2.me/theorems/25680e52-626b-4761-90e5-8fe330c2970a
-- title:
--   Identity operator $I$ as a coefficient array
-- statement:
--   The identity operator $I$ on the Hilbert space $\ell^2(J)$, written in the orthonormal basis indexed by $J$:
--
--   $$I_{ab}=\begin{cases}1,&a=b,\\0,&a\neq b.\end{cases}$$
--
--   It appears in $0\le\Lambda\le I$ (Lemma 8, Lemma 9), in $\hat\Pi\equiv I-\Pi$ and in $\hat\Pi_i\equiv I^{\otimes n}-|\varphi_{x^n(i)}\rangle\langle\varphi_{x^n(i)}|$ (Appendix B).
--
--   **Formalization Note** The index set $J$ is arbitrary; equality of indices is decided classically.
-- source:
--   Wilde–Guha–Tan–Lloyd, Explicit capacity-achieving receivers for optical communication and quantum reading, arXiv:1202.0518v2, Appendix A, Lemma 8, p.6; Appendix B, p.6

import Mathlib

namespace SeqHolevo

/-- Wilde–Guha–Tan–Lloyd, *Explicit capacity-achieving receivers for optical communication and quantum reading*, arXiv:1202.0518v2, Appendix A, p.6 (PDF page; the paper prints no page numbers): the identity
operator `I` (and `I^{⊗n}` of Appendix B, p.6), written as its coefficient array
`I_{ab} = 1` if `a = b` and `0` otherwise, on the orthonormal basis indexed by `J`.

**Formalization Note.** Operators are coefficient arrays `Matrix J J ℂ` on ℓ²(J) for an arbitrary
index type `J` (no finiteness); equality of indices is decided classically, so no
`DecidableEq` instance is needed. -/
noncomputable def idArr (J : Type) : Matrix J J ℂ :=
  open Classical in fun a b => if a = b then 1 else 0

end SeqHolevo


