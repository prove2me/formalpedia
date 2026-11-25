-- Prove2me | Definitions.Def_DetDLP_S8I_ECPairPredicate
-- name    : DetDLP_S8I_ECPairPredicate
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T04:56:33.214569+00:00
-- url     : https://prove2.me/theorems/4d488dae-84c1-4216-8e25-2a8ca937bc8b
-- title:
--   Predicate for elliptic-curve pair query witnesses
-- statement:
--   This predicate captures the witnesses counted by the elliptic-curve pair query: each pair of points lies in the corresponding factor blocks, the interleaved point encoding matches the supplied prefix, and the sum of all pairwise sums equals the specified target point.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.4 & Section 3.1–3.2, Lemma 2.4 & Theorem 3.1 (pp. 9–13)

import Definitions.Def_DetDLP_M89_S1_Queries

set_option autoImplicit false

namespace DetDLP.S8I.ECPairPredicate
open DetDLP.M89S1

/-- The pointwise predicate counted by the elliptic-curve pair query: both
entries at every coordinate lie in the corresponding factor block, the
interleaved point encoding has the requested prefix, and the coordinatewise
sum of the paired points is the target point. -/
def Accepts {p : ℕ} [Fact p.Prime] {E : WeierstrassCurve (ZMod p)} [E.IsElliptic]
    {m : ℕ} (T : ℕ) (S : ECSeed p m) (b : ℕ) (η : List Bool)
    (X : E.toAffine.Point) (ab : (Fin m → E.toAffine.Point) × (Fin m → E.toAffine.Point)) : Prop :=
  (∀ i, ab.1 i ∈ ecFactorBlock E T S i ∧ ab.2 i ∈ ecFactorBlock E T S i) ∧
  (tupleWord (ecWord b) ab).take η.length = η ∧
  (∑ i, (ab.1 i + ab.2 i)) = X

/-- The predicate is exactly the relation supplied to `pairCount` in Tag 6. -/
theorem accepts_relation {p : ℕ} [Fact p.Prime] {E : WeierstrassCurve (ZMod p)} [E.IsElliptic]
    {m : ℕ} (T : ℕ) (S : ECSeed p m) (b : ℕ) (η : List Bool)
    (X : E.toAffine.Point) (ab : (Fin m → E.toAffine.Point) × (Fin m → E.toAffine.Point)) :
    Accepts T S b η X ab ↔
      (∀ i, ab.1 i ∈ ecFactorBlock E T S i ∧ ab.2 i ∈ ecFactorBlock E T S i) ∧
      (tupleWord (ecWord b) ab).take η.length = η ∧
      (∑ i, (ab.1 i + ab.2 i)) = X := Iff.rfl

end DetDLP.S8I.ECPairPredicate


