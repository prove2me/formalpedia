-- Prove2me | Definitions.Def_APSCounting893_Main_BinaryOracleArithmetic
-- name    : APSCounting893_Main_BinaryOracleArithmetic
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-18T20:44:50.563059+00:00
-- url     : https://prove2.me/theorems/b966d8b1-322a-4629-8ee2-80fc56b64358
-- title:
--   Bit-query and graph languages for implicit natural-number arithmetic
-- statement:
--   Let $F$ assign a natural number to each finite binary word. The bit language records queries $(x,q)$ whose answer is the $q$th binary digit of $F(x)$. The graph language accepts an input consisting of a framed word $x$ followed by little-endian candidate bits exactly when that candidate represents $F(x)$.
--
--   $$\operatorname{BIT}_F(x,q)=[\operatorname{bit}_q(F(x))=1],\qquad
--   \operatorname{GRAPH}_F(x,v)=[v=F(x)].$$
--
--   These interfaces permit implicit arithmetic values to be used in finite-oracle-machine constructions. Bit positions use the published length-delimited natural-number encoding. Graph candidates may contain trailing zero bits; the total decoder interprets them as the same natural number.
-- source:
--   Hesse, Allender and Barrington, Uniform Constant-Depth Threshold Circuits for Division and Iterated Multiplication, JCSS 65(4), 2002, Section 4, pp. 8–11 of the author manuscript, especially Lemmas 4.1–4.3, https://www.cs.rutgers.edu/~allender/papers/division.pdf; implicit short-value interfaces for the arithmetic-to-threshold step in Agarwal, Hari, Pandey and Shukla, STOC 2027 submission #893, Theorem 6.4, pp. 25–26, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/893.pdf.

import Definitions.Def_APSCounting893_Main_OracleProofPrimitives
import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Encodings_Nat_Words
set_option autoImplicit false
namespace APSCounting893.Main

def naturalBitQuery (x : Word) (q : ℕ) : Word := Turing.MultiTapeTM.frame x++encodeNat q

def NaturalBitLanguage (F : Word → ℕ) : Language :=
  fun w => ∃ x q,w=naturalBitQuery x q ∧ (F x).testBit q=true

def NaturalGraphLanguage (F : Word → ℕ) : Language :=
  fun w => F (Turing.MultiTapeTM.unframe w)=Turing.MultiTapeTM.ofBits (Turing.MultiTapeTM.dropFrame w)

end APSCounting893.Main


