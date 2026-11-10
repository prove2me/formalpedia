-- Prove2me | Definitions.Def_BMPV1173_Verification_Reductions
-- name    : BMPV1173_Verification_Reductions
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T23:04:08.933192+00:00
-- url     : https://prove2.me/theorems/c3c962ba-8184-4e18-b809-e3f370fa7f19
-- title:
--   Explicit bit maps for the verification, triangle and OV reductions
-- statement:
--   A target-bit instruction is either a constant or a possibly complemented source entry. The triangle map has three vertex blocks and complements the claimed product. Its converse uses (D,D,complement D). The verification-to-OV map has rows (A_i,e_i,1,0), (B^T_j,complement(C)^T_j,0,1), and two all-one filler rows. The converse uses (X,X^T,J). Each map therefore retains the source bit-oracle convention.
-- source:
--   Amin Shiraz Gilani, François Le Gall, Xingyu Zhou, STOC 2027 submission #1173 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1173.pdf, §3.1, equations (3.1)–(3.3), printed p.17 = PDF p.17.

import Definitions.Def_BMPV1173_Verification_QueryComplexity

/-! The explicit source maps (3.1), (3.3) and their converses, p.17.
Every target bit is constant or one (possibly complemented) source bit. -/
namespace BMPV1173.Verification

inductive BitInstruction (ι : Type) where
  | constant (b : Bool)
  | entry (i : ι) (complement : Bool)

def BitInstruction.eval {ι : Type} (b : BitInstruction ι) (x : ι → Bool) : Bool :=
  match b with
  | .constant v => v
  | .entry i flip => xor (x i) flip

def evalMap {ι κ : Type} (b : κ → BitInstruction ι) (x : ι → Bool) : κ → Bool :=
  fun i => (b i).eval x

def indexMod (n : ℕ) (hn : 0 < n) (i : ℕ) : Fin n := ⟨i % n, Nat.mod_lt i hn⟩

/-- Three graph blocks U,K,V in that order; C occurs complemented. -/
def verificationTriangleMap (n : ℕ) (hn : 0 < n) :
    MatrixIndex (3*n) → BitInstruction (VerificationIndex n) := fun q =>
  let i := indexMod n hn q.1.val
  let j := indexMod n hn q.2.val
  let a := q.1.val / n
  let b := q.2.val / n
  if a = b then .constant false
  else if a = 0 ∧ b = 1 then .entry (0,i,j) false
  else if a = 1 ∧ b = 0 then .entry (0,j,i) false
  else if a = 1 ∧ b = 2 then .entry (1,i,j) false
  else if a = 2 ∧ b = 1 then .entry (1,j,i) false
  else if a = 0 ∧ b = 2 then .entry (2,i,j) true
  else .entry (2,j,i) true

/-- (D,D,complement D); the diagonal of the third matrix is one. -/
def triangleVerificationMap (n : ℕ) :
    VerificationIndex n → BitInstruction (MatrixIndex n) := fun q =>
  .entry q.2 (q.1 = 2)

/-- (X,X transpose,J), the converse OV reduction. -/
def orthogonalVerificationMap (n : ℕ) :
    VerificationIndex n → BitInstruction (MatrixIndex n) := fun q =>
  if q.1 = 0 then .entry q.2 false
  else if q.1 = 1 then .entry (q.2.2,q.2.1) false
  else .constant true

/-- Rows (A_i,e_i,1,0), (B^T_j,complement(C)^T_j,0,1), then two all-one fillers. -/
def verificationOrthogonalMap (n : ℕ) (hn : 0 < n) :
    MatrixIndex (2*n+2) → BitInstruction (VerificationIndex n) := fun q =>
  let i := indexMod n hn q.1.val
  let j := indexMod n hn (q.1.val-n)
  let k := indexMod n hn q.2.val
  let l := indexMod n hn (q.2.val-n)
  if q.1.val < n then
    if q.2.val < n then .entry (0,i,k) false
    else if q.2.val < 2*n then .constant (i = l)
    else .constant (q.2.val = 2*n)
  else if q.1.val < 2*n then
    if q.2.val < n then .entry (1,k,j) false
    else if q.2.val < 2*n then .entry (2,l,j) true
    else .constant (q.2.val = 2*n+1)
  else .constant true

end BMPV1173.Verification


