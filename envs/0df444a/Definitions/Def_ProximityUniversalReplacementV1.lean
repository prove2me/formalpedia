-- Prove2me | Definitions.Def_ProximityUniversalReplacementV1
-- name    : ProximityUniversalReplacementV1
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-04T14:07:39.62379+00:00
-- url     : https://prove2.me/theorems/cd9978c6-5f04-441a-a14a-5c32305cf26b
-- title:
--   Weighted local contacts and constrained polynomial spaces
-- statement:
--   Use variables $(X,Y,R,Z)$ over a field $K$. For nonnegative weights $a=(a_0,a_1,a_2,a_3)$, the weighted polynomial replaces each variable $V_j$ by $V_jT^{a_j}$. At data $(x,b,c)$ define
--   $$\Phi_{x,b,c}(Q)=Q(x+XT,\;b+Zc+RXT+YT^2,\;R,\;Z).$$
--   The contact order is the least exponent of $T$ with a nonzero coefficient in $\Phi_{x,b,c}(Q)$, with value zero for the zero polynomial; contact at least $m$ means $T^m\mid\Phi_{x,b,c}(Q)$.
--
--   For arbitrary node data indexed by $I$ and multiplicities $m_i$, admissibility requires all local contacts and three source bounds:
--   $$\operatorname{wt}_{(1,w,w-1,0)}Q<D,\quad \operatorname{wt}_{(0,1,1,1)}Q\le L,\quad \deg_RQ\le s.$$
--   Weights and bounds are natural numbers, so $w-1$ is truncated natural subtraction. Weighted degree is the largest weighted monomial exponent, with value zero at the zero polynomial.
--
--   This proof-free module supplies the concrete polynomial and contact interface for universal-factor replacement theorems. Its associated proof establishes that contact at least $m$ is exactly a lower bound of $m$ on every support weight after localization, and proves multiplicative additivity of nonzero contact orders and weighted degrees.
-- source:
--   A standalone generalization of the actual-universal-factor replacement argument developed during research on the Yukon lower reduction-threshold benchmark a2e3eaa8-95c0-4a62-81d3-2cd7e78e8575. The polynomial/contact conventions come from https://github.com/proximity-prize/proximity-prize/blob/ed2b68c4a330d76dc4ab6693eec81b685b493270/ProximityPrize/SubmissionLower/LowerFoundation.lean and MergedInfra6815_7.lean in the same directory. The separate local ConstraintKernel-to-contact-space equivalence is not imported or claimed by this standalone theorem. No new numerical threshold or verified benchmark submission is asserted.
--
--   yukon-proof-operation:ae88ede2-8793-4d67-8d5d-3ff7e280087e; Yukon contributor: yudduy
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiZWVkZjQyYzI4YzY5ODM0MWI2ZjRhZWMyMzhlMmU3M2RhMTdlY2ZhYTNjNTBhNDU2N2FkZTk2MDE0YWQ3YzI4OCIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmFlODhlZGUyLTg3OTMtNGQ2Ny04ZDVkLTNmZjdlMjgwMDg3ZTsgWXVrb24gY29udHJpYnV0b3I6IHl1ZGR1eSIsInRhZyI6ImJldHRlci1jb2RlcyIsInRhcmdldCI6IlByb3hpbWl0eVVuaXZlcnNhbFJlcGxhY2VtZW50VjEiLCJ2IjoyfQ]

import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Algebra.Polynomial.Degree.TrailingDegree

namespace ProximityUniversalReplacementV1
noncomputable section

abbrev Poly4 (K : Type*) [CommSemiring K] := MvPolynomial (Fin 4) K

def weightedPolynomial (K : Type*) [Field K] (weights : Fin 4 → ℕ) :
    Poly4 K →+* Polynomial (Poly4 K) :=
  MvPolynomial.eval₂Hom (Polynomial.C.comp MvPolynomial.C)
    (fun i => Polynomial.C (MvPolynomial.X i) * Polynomial.X ^ weights i)

def localize (K : Type*) [Field K] (x u0 u1 : K) : Poly4 K →ₐ[K] Poly4 K :=
  MvPolynomial.aeval
    ![MvPolynomial.X 0 + MvPolynomial.C x,
      MvPolynomial.C u0 + MvPolynomial.X 3 * MvPolynomial.C u1 +
        MvPolynomial.X 2 * MvPolynomial.X 0 + MvPolynomial.X 1,
      MvPolynomial.X 2, MvPolynomial.X 3]

def contactPolynomial (K : Type*) [Field K] (x u0 u1 : K) :
    Poly4 K →+* Polynomial (Poly4 K) :=
  (weightedPolynomial K ![1, 2, 0, 0]).comp (localize K x u0 u1).toRingHom

def contactOrder (K : Type*) [Field K] (x u0 u1 : K) (P : Poly4 K) : ℕ :=
  (contactPolynomial K x u0 u1 P).natTrailingDegree

def contactAtLeast (K : Type*) [Field K] (x u0 u1 : K) (m : ℕ)
    (P : Poly4 K) : Prop :=
  Polynomial.X ^ m ∣ contactPolynomial K x u0 u1 P

def admissible (K : Type*) [Field K] {I : Type*} (D w L s : ℕ)
    (m : I → ℕ) (nodes u0 u1 : I → K) (Q : Poly4 K) : Prop :=
  MvPolynomial.weightedTotalDegree ![1, w, w - 1, 0] Q < D ∧
  MvPolynomial.weightedTotalDegree ![0, 1, 1, 1] Q ≤ L ∧
  Q.degreeOf 2 ≤ s ∧
  ∀ i, contactAtLeast K (nodes i) (u0 i) (u1 i) (m i) Q

end
end ProximityUniversalReplacementV1


