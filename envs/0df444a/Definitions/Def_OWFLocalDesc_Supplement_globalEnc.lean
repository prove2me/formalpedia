-- Prove2me | Definitions.Def_OWFLocalDesc_Supplement_globalEnc
-- name    : OWFLocalDesc_Supplement_globalEnc
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T12:40:05.669348+00:00
-- url     : https://prove2.me/theorems/31ab8f8a-9288-421a-89bf-4721171af304
-- title:
--   The self-delimiting code $\mathrm{enc}(e)$ and the conditioning input $E(x)$ (Appendix B)
-- statement:
--   For a positive integer $e$, $\mathrm{enc}(e)$ consists of the length of the binary expansion of $e$ written in unary (a run of ones), a zero separator, and that expansion, most significant bit first. For example $\mathrm{enc}(5)=111\,0\,101$. This code is self-delimiting.
--
--   An ordered vector $x=(x_1,\dots,x_m)$ of $n$-bit points is encoded as
--   $$E(x)=\mathrm{enc}(n)\,\mathrm{enc}(m)\,x_1\cdots x_m .$$
--
--   $E(x)$ is the conditioning input of the global decoder $V$: the global decoder reads the point length, the sample size and the points sequentially, with no length oracle.
--
--   **Formalization Note** The binary expansion is `(Nat.bits e).reverse`; the code is used only for $e\ge1$.
-- source:
--   Myrisiotis, One-Way Functions and Local Descriptions of Random Data, STOC 2027 submission (held manuscript, sha256 d818fa43…4c4e), Appendix B, p.37

import Mathlib
set_option autoImplicit false

namespace OWFLocalDesc.Supplement

/-- The binary expansion of `e`, most significant bit first (`true` is the bit `1`); for `e ≥ 1`
it starts with `1`. -/
def binExp (e : ℕ) : List Bool := (Nat.bits e).reverse

/-- **The self-delimiting code `enc(e)`.** Myrisiotis, *One-Way Functions and Local Descriptions
of Random Data*, STOC 2027 submission (held manuscript, sha256 d818fa43…4c4e), Appendix B, p.37:
"For a positive integer e, let enc(e) consist of the unary length of its binary expansion, a zero
separator, and that expansion."

**Formalization Note.** The unary length is a run of `1`s; the code is used only at `e ≥ 1`. -/
def enc (e : ℕ) : List Bool := List.replicate (binExp e).length true ++ false :: binExp e

/-- **The conditioning input `E(x)`.** Appendix B, p.37: "Encode an ordered vector
x = (x1,...,xm) of n-bit points by E(x) = enc(n)enc(m)x1 ···xm." -/
def globalEnc {m n : ℕ} (x : Fin m → Fin n → Bool) : List Bool :=
  enc n ++ enc m ++ (List.ofFn fun i => List.ofFn (x i)).flatten

end OWFLocalDesc.Supplement


