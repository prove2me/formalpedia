-- Prove2me | Definitions.Def_APSCounting893_Main_ImplicitCountingArithmetic
-- name    : APSCounting893_Main_ImplicitCountingArithmetic
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-18T21:01:42.791962+00:00
-- url     : https://prove2.me/theorems/183f99c1-9912-4d32-99db-563dfa220970
-- title:
--   Comparison language and exponentially indexed natural sums
-- statement:
--   For a natural-valued function $F$ on binary words, the comparison language tests whether the little-endian value written after a framed input is strictly below $F(x)$.
--
--   For fixed resource constants $a,b$, let $r=a(|x|+1)^b$. The implicit indexed sum is
--   $$S_{F,a,b}(x)=\sum_{i=0}^{2^r-1}F\bigl(\operatorname{frame}(x)\,\Vert\,\operatorname{bits}_r(i)\bigr),$$
--   where the index uses exactly $r$ little-endian bits and $\Vert$ denotes concatenation.
--
--   These objects support uniform counting arguments for short integer arithmetic. The sum is the actual finite natural-number sum; it does not assume a circuit, arithmetic oracle, or complexity bound.
-- source:
--   Hesse, Allender and Barrington, Uniform Constant-Depth Threshold Circuits for Division and Iterated Multiplication, JCSS 65(4), 2002, author manuscript Section 4, pp. 8–11, including the iterated-addition steps in Lemmas 4.1 and 4.3, https://www.cs.rutgers.edu/~allender/papers/division.pdf; used in the arithmetic simulation for Agarwal, Hari, Pandey and Shukla, STOC 2027 submission #893, Theorem 6.4, pp. 25–26, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/893.pdf.

import Definitions.Def_APSCounting893_Main_BinaryOracleArithmetic
set_option autoImplicit false
namespace APSCounting893.Main

def NaturalLessLanguage (F : Word → ℕ) : Language :=
  fun z => Turing.MultiTapeTM.ofBits (Turing.MultiTapeTM.dropFrame z)<F (Turing.MultiTapeTM.unframe z)

noncomputable def indexedNaturalSum (F : Word → ℕ) (a b : ℕ) (x : Word) : ℕ :=
  ∑ i : Fin (2^polyBound a b x.length),F (Turing.MultiTapeTM.frame x++
    Cslib.BitString.lowBits (polyBound a b x.length) i.val)

end APSCounting893.Main


