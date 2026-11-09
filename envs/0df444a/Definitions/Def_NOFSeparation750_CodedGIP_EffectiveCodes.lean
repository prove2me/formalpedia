-- Prove2me | Definitions.Def_NOFSeparation750_CodedGIP_EffectiveCodes
-- name    : NOFSeparation750_CodedGIP_EffectiveCodes
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T02:42:57.592463+00:00
-- url     : https://prove2.me/theorems/af5a4986-d340-45c9-9b9c-eb022ebeff94
-- title:
--   Uniform effective generator construction and codeword encoding
-- statement:
--   For a pair of ordered-basis code families $(V_j,W_j)$, effective construction means that one finite binary program outputs both generator matrices from the level $j$, and one finite binary program encodes messages for either code. A selector bit distinguishes the two codes. Matrix rows are the basis vectors; the serialized output includes the row counts and then all field entries in the fixed binary representation.
--
--   For one polynomial $p$ independent of the level and messages, all these computations satisfy
--   $$T_{\mathrm{gen}}(j)\le p(r_j),\qquad T_{\mathrm{enc}}(j,u)\le p(r_j).$$
--   The encoding output is the actual basis linear combination of the supplied coefficients. The same finite field representation is used for input messages, generator matrices, and output codewords. Unary level and row-count headers only add polynomial overhead in $r_j$. This predicate specifies operational content and running-time conclusions for Theorem 3.2; it assumes no code existence or correctness theorem.
-- source:
--   Haoyu Wang, Yimeng Wang, Pei Wu, STOC 2027 submission #750 (October 2026), Theorem 3.2, p.7; Appendix A.2–A.3, pp.12–13; canonical PDF SHA-256 b28ac89d573094bcafec49dc3a1eeadc9e95b5c3074c478d242f60a2818a42ce

import Mathlib
import Definitions.Def_NOFSeparation750_CodedGIP_Programs
import Definitions.Def_NOFSeparation750_CodedGIP_Model

noncomputable section

namespace NOFSeparation750.CodedGIP

def fieldVectorBits {F : Type} {b m : ℕ} (codec : (Fin b → Bool) ≃ F)
    (x : Fin m → F) : List Bool :=
  (List.ofFn fun i => List.ofFn (codec.symm (x i))).flatten

def generatorBits {F : Type} [Field F] {b r : ℕ} (codec : (Fin b → Bool) ≃ F)
    (P : CodePresentation F r) : List Bool :=
  unary P.dimension ++ (List.ofFn fun i => fieldVectorBits codec (P.basis i).val).flatten

/-- One generator program and one encoding program, with fixed finite control and
polynomials, uniform over every level j and every message. Both generator matrices
have basis rows; encoding outputs their actual linear combinations. -/
def EffectivePairFamily {F : Type} [Field F] {a : ℕ} (D : PairFamily F a)
    (codec : (Fin (2 * a) → Bool) ≃ F) : Prop :=
  ∃ generator encoder : FiniteProgram, ∃ p : Polynomial ℕ, ∀ j,
    OutputsWithin generator (unary j)
      (generatorBits codec (D j).small ++ generatorBits codec (D j).large)
      (p.eval (codeLength a j)) ∧
    (∀ u : Fin (D j).small.dimension → F,
      OutputsWithin encoder (unary j ++ [false] ++ fieldVectorBits codec u)
        (fieldVectorBits codec ((D j).small.encode u).val) (p.eval (codeLength a j))) ∧
    (∀ u : Fin (D j).large.dimension → F,
      OutputsWithin encoder (unary j ++ [true] ++ fieldVectorBits codec u)
        (fieldVectorBits codec ((D j).large.encode u).val) (p.eval (codeLength a j)))

end NOFSeparation750.CodedGIP


