-- Prove2me | Definitions.Def_CommutativeRankNC_Approximation_RationalInput
-- name    : CommutativeRankNC_Approximation_RationalInput
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:49:25.218207+00:00
-- url     : https://prove2.me/theorems/1d3f297b-20a3-45f9-8847-8ee2f69a5f02
-- title:
--   Dense binary rational matrix input and output
-- statement:
--   A tuple of $m$ rational $n\times n$ matrices is written with unary dimensions (including zero), followed by its entries in matrix order and row-major order. Each entry uses the published self-delimiting signed binary numerator and positive reduced denominator encoding.
--
--   $$\operatorname{enc}(B)=1^n0\,1^m0\,\operatorname{entries}(B_1)\cdots\operatorname{entries}(B_m).$$
--
--   An output is the same unary-dimension matrix code followed by zero padding to the circuit's fixed output length. Every rational tuple is representable; dense positive-dimensional encodings are polynomially equivalent to the usual bit model. Unary dimensions ensure polynomial output length even for an empty generating list.
-- source:
--   Foram Lakhani, Partha Mukhopadhyay, STOC 2027 submission #458 (October 2026), p.24; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/458.pdf

import Definitions.Def_CommutativeRankNC_Approximation_MatrixSpace
import Definitions.Def_QAlgorithms_ClassicalRationalEncoding

namespace CommutativeRankNC.Approximation

open QAlgorithms.LocalHamiltonian

/-- Dense row-major rational entries. Numerators are signed binary, denominators
are positive reduced binary integers, with the published self-delimiting code. -/
def encodeEntries {n : ℕ} (A : QMatrix n) : List Bool :=
  (List.finRange n).flatMap fun i => (List.finRange n).flatMap fun j => encRat (A i j)

/-- Dimensions are unary, including zero. This also charges enough input for
an explicit zero output when the generating list is empty. -/
def encodeInput {n m : ℕ} (B : Fin m → QMatrix n) : List Bool :=
  List.replicate n true ++ [false] ++ List.replicate m true ++ [false] ++
    (List.finRange m).flatMap (fun i => encodeEntries (B i))

def encodeMatrix {n : ℕ} (A : QMatrix n) : List Bool :=
  List.replicate n true ++ [false] ++ encodeEntries A

/-- Fixed-length circuit outputs contain a self-delimiting matrix followed by
zero padding. The represented matrix has the input dimension. -/
def EncodesMatrix {n : ℕ} (bits : List Bool) (A : QMatrix n) : Prop :=
  ∃ padding : ℕ, bits = encodeMatrix A ++ List.replicate padding false

end CommutativeRankNC.Approximation


