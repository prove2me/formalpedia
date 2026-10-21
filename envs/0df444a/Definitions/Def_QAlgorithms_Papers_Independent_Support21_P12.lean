-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Support21_P12
-- name    : QAlgorithms_Papers_Independent_Support21_P12
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-21T04:05:07.187983+00:00
-- url     : https://prove2.me/theorems/c2ba810b-d458-4e12-88f5-a3ffb642053d
-- title:
--   Definitions for Remarks on Cyclotomic and Degenerate Cyclotomic BMW Algebras
-- statement:
--   The objects the formalized statements of *Remarks on Cyclotomic and Degenerate Cyclotomic BMW Algebras* (arXiv:1011.3284) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `WLetter`: Free generators for Definition 2.3, PDF p.4. At positive level the affine letter and its inverse are present, together with braid and contraction letters.
--   - `wg`: Free g_(i+1); only indices i+1<n are used, PDF p.4.
--   - `wgi`: Free inverse braid letter, PDF p.4.
--   - `we`: Free contraction letter, PDF p.4.
--   - `wy`: The free affine letter, PDF p.4.
--   - `wyi`: The free inverse affine letter, PDF p.4.
--   - `WRel`: Exactly the eight groups of relations in Definition 2.3, PDF p.4. The adjacent contraction/braid relations use neighboring INDICES, not inverse braids: the superscripts ±1 on g are confined to group (1) and the skein relation. Both signs of each neighboring-index relation and both unwrapping equations are retained. All scalar conditions are separately carried by `Kind`.
--   - `WAffine`: Positive-level ordinary affine BMW presentation, Definition 2.3, PDF p.4.
--   - `wMap`: Presentation map, PDF p.4.
--   - `Kind`: The two flavors of Definition 2.1 and Definition 2.3. Ordinary parameters include exactly the unit conditions and scalar relation (2.1), PDF pp.3--4.
--   - `Affine`: Actual affine algebra of the selected flavor. Only positive levels occur in affine statements; level zero is explicitly the ground ring, PDF pp.3--4.
--   - `ay`: Affine y_1; the level-zero helper is zero and is never a source generator.
--   - `ae`: Affine contraction e_(i+1); valid range i+1<n, PDF pp.3--4.
--   - `ag`: Affine braid s_(i+1) or g_(i+1), PDF pp.3--4.
--   - `rootPolynomial`: The root polynomial as a product, equation (2.2), PDF p.4. Repeated roots retain their multiplicity.
--   - `cyclRel`: The cyclotomic relation, Definitions 2.2 and 2.4, PDF pp.3--4.
--   - `Cyclotomic`: Actual presented cyclotomic algebra, with the explicit level-zero convention A_0=S. No presentation relation in a nonexistent y_1 is imposed.
--   - `toCycl`: Canonical affine-to-cyclotomic quotient map; at level zero it is the identity.
--   - `cy`: y_1 in the cyclotomic quotient, PDF pp.3--4.
--   - `ce`: e_(i+1) in the cyclotomic quotient, PDF pp.3--4.
--   - `cg`: s_(i+1) or g_(i+1) in the cyclotomic quotient, PDF pp.3--4.
--   - `ValidRoots`: Root domain: r is positive; ordinary roots are units, Definition 2.4.
--   - `leftIdealSpan`: S-span of the left ideal A e (not the two-sided ideal), PDF p.4.
--   - `contractionIdeal`: S-span of A e A, the contraction ideal, PDF pp.13--15.
--   - `cyclicFamily`: The indexed cyclic family of length d, Definitions 2.8 and 5.2.
--   - `CyclicAdmissible`: Admissibility in the ACTUAL two-strand quotient, Definition 2.8, PDF p.5.
--   - `IdealTorsionFree`: Torsion freedom of the WHOLE left ideal, Assumption 5.1, PDF p.10. The equation is tested on every ideal element and every nonzero scalar.
--   - `SemiAdmissible`: d-semi-admissibility; no monic annihilator is assumed, Definition 5.2.
--   - `firstRoots`: The first d roots, retaining order and multiplicity, PDF p.11.
--   - `SplitSemi`: Assumption 5.3 after choosing the root ordering, PDF p.11.
--   - `RootRecurrence`: Scalar recurrence (2.3) for a specified root list, PDF p.4.
--   - `schurFactor`: The geometric factor (1+v z)/(1-v z) as a formal series over Z[u], PDF p.6. Its constant coefficient is 1, and its positive coefficients are 2v^a.
--   - `schurQ`: Schur q-polynomial: coefficient of the displayed product, PDF p.6.
--   - `powerSum`: The power-sum polynomial p_a, PDF p.6.
--   - `integerHalf`: Coefficientwise INTEGER division by two. It is applied to polynomials whose coefficients are even; no division in a target ring is performed, PDF p.6.
--   - `halfSchurQ`: Integer lift of q_a/2 for a>0, PDF p.6. Its a=0 helper is not used as q_0/2.
--   - `etaRational`: The rational polynomial eta_a^± of equation (3.3), PDF p.6. `plus=true` means the plus sign, `plus=false` the minus sign.
--   - `etaIntegral`: Explicit integral lift of eta_a^±: divide the numerator's INTEGER coefficients by two, then evaluate in S, never evaluate 1/2 in S, PDF p.6.
--   - `evalIntegral`: Evaluate an integer polynomial in any commutative target ring, PDF pp.6--7.
--   - `universalOmega`: The actual universal integral admissible sequence (3.8), PDF p.7.
--   - `RootAdmissible`: Root-admissibility of Definition 3.5, with the integral interpretation.
--   - `TriangularRelations`: Scalar triangular equations (3.1), with j<r and no truncated last term.
--   - `twoStrandBasisFamily`: The three tagged r-by-r families in Theorem 3.12(2), PDF p.8. The tags are retained even when images happen to coincide.
--   - `IsIndexedBasis`: An indexed family is a basis precisely when it is independent and spans.
--   - `conjugateY`: The two conjugate families on PDF p.12. For `reverse=false` use g_j y'_j g_j^{-1}; for `reverse=true` use g_j^{-1} y''_j g_j.
--   - `agi`: Named inverse braids in the ordinary affine presentation; degenerate braids are their own inverses. Only the ordinary case is used below.
--   - `cgi`: Named inverse braids in the cyclotomic quotient, PDF p.12.
--   - `ConjugateCommutation`: Both contractions and braids commute with both conjugate families away from the two exceptional indices, Lemma 5.6, PDF p.12.
--   - `diagramCount`: Brauer diagrams are perfect matchings of the top and bottom vertex sets. A fixed-point-free involutive permutation records each edge twice, uniquely. The empty diagram at n=0 is included, PDF pp.7,13.
--   - `horizontalDiagramCount`: b'(n) counts actual Brauer matchings with a horizontal edge, PDF p.13. A top horizontal edge forces a bottom one; b'(0)=b'(1)=0.
--   - `HasSpanningSetCard`: Spanning by a set of EXACTLY k distinct elements. This does not assume linear independence, Lemmas 5.8 and 5.10, PDF pp.13,15.
--   - `CellDatumFor`: The cell equations of Definition 6.1, PDF p.16, for a SPECIFIED anti-involution. The accepted weak basis predicate swaps indices modulo higher cells. The optional size is the cardinality of the indexed cellular basis. No integral-domain requirement is built in, so Theorem 3.11 covers CommRing.
--   - `CanonicalCellular`: Cellularity for the canonical generator-fixing anti-involution, PDF pp.3--4,16. The anti-involution is required in the conclusion and fixes every presentation generator: y_1, all contractions and all braids generate the algebra (the remaining degenerate y_j are determined recursively by the skein relations). At level zero fixing 1 together with S-linearity gives the identity on S.
--   - `HasFiniteModule`: A finite dimensional module with nonzero e-action, expressed in a chosen finite basis as a unital F-algebra representation. No simplicity is imposed.
--   - `HasAdmissibleRoots`: Existence of admissible positive-degree cyclotomic parameters, PDF p.17. Ordinary roots must be units; degenerate roots may be zero.
--   - `RationalSequence`: Rationality of the generating series at infinity, PDF p.18. With z=t^{-1}, Q(z) times the formal series is P(z), and Q(0) is explicitly nonzero.
--   - `RecurrenceFrom`: A monic homogeneous recurrence after threshold N, Theorem 7.1(2), PDF p.18.
-- source:
--   Remarks on Cyclotomic and Degenerate Cyclotomic BMW Algebras, arXiv:1011.3284v3, https://arxiv.org/abs/1011.3284v3

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Renew46_P16

/-!
Goodman, Remarks on Cyclotomic and Degenerate Cyclotomic BMW Algebras,
arXiv:1011.3284v3. Statements only; proofs are intentionally omitted.
All new definitions are local to this paper. Source indices are shifted by one:
Lean index 0 denotes the source's first generator. The accepted P16 presentation
is used only for the degenerate affine algebra, whose relations agree exactly
with Definition 2.1 here. Its cyclotomic level-zero convention is NOT reused.
-/

noncomputable section

open scoped BigOperators

namespace QAlgorithms.Papers.Independent.Support21.P12

/-- Free generators for Definition 2.3, PDF p.4. At positive level the affine
letter and its inverse are present, together with braid and contraction letters. -/
inductive WLetter (n : ℕ)
  | g : Fin (n - 1) → WLetter n
  | gi : Fin (n - 1) → WLetter n
  | e : Fin (n - 1) → WLetter n
  | y : WLetter n
  | yi : WLetter n

/-- Free g_(i+1); only indices i+1<n are used, PDF p.4. -/
def wg (S : Type*) [CommRing S] (n i : ℕ) : FreeAlgebra S (WLetter n) :=
  if h : i < n - 1 then FreeAlgebra.ι S (.g ⟨i,h⟩) else 0

/-- Free inverse braid letter, PDF p.4. -/
def wgi (S : Type*) [CommRing S] (n i : ℕ) : FreeAlgebra S (WLetter n) :=
  if h : i < n - 1 then FreeAlgebra.ι S (.gi ⟨i,h⟩) else 0

/-- Free contraction letter, PDF p.4. -/
def we (S : Type*) [CommRing S] (n i : ℕ) : FreeAlgebra S (WLetter n) :=
  if h : i < n - 1 then FreeAlgebra.ι S (.e ⟨i,h⟩) else 0

/-- The free affine letter, PDF p.4. -/
def wy (S : Type*) [CommRing S] (n : ℕ) : FreeAlgebra S (WLetter n) :=
  FreeAlgebra.ι S .y

/-- The free inverse affine letter, PDF p.4. -/
def wyi (S : Type*) [CommRing S] (n : ℕ) : FreeAlgebra S (WLetter n) :=
  FreeAlgebra.ι S .yi

section WPresentation

variable (S : Type*) [CommRing S] (omega : ℕ → S) (rho q : Sˣ) (n : ℕ)

/-- Exactly the eight groups of relations in Definition 2.3, PDF p.4.
The adjacent contraction/braid relations use neighboring INDICES, not inverse
braids: the superscripts ±1 on g are confined to group (1) and the skein relation.
Both signs of each neighboring-index relation and both unwrapping equations
are retained. All scalar conditions are separately carried by `Kind`. -/
inductive WRel (S : Type*) [CommRing S] (omega : ℕ → S) (rho q : Sˣ) (n : ℕ) :
    FreeAlgebra S (WLetter n) → FreeAlgebra S (WLetter n) → Prop
  | gInv (i : ℕ) (hi : i + 1 < n) : WRel S omega rho q n ((wg S n) i * (wgi S n) i) 1
  | invG (i : ℕ) (hi : i + 1 < n) : WRel S omega rho q n ((wgi S n) i * (wg S n) i) 1
  | yInv : WRel S omega rho q n ((wy S n) * (wyi S n)) 1
  | invY : WRel S omega rho q n ((wyi S n) * (wy S n)) 1
  | braid (i : ℕ) (hi : i + 2 < n) :
      WRel S omega rho q n ((wg S n) i * (wg S n) (i+1) * (wg S n) i) ((wg S n) (i+1) * (wg S n) i * (wg S n) (i+1))
  | farBraid (i j : ℕ) (hi : i+1<n) (hj : j+1<n)
      (hd : i + 1 < j ∨ j + 1 < i) : WRel S omega rho q n ((wg S n) i * (wg S n) j) ((wg S n) j * (wg S n) i)
  | affineBraid (hn : 2 ≤ n) : WRel S omega rho q n ((wy S n) * (wg S n) 0 * (wy S n) * (wg S n) 0) ((wg S n) 0 * (wy S n) * (wg S n) 0 * (wy S n))
  | affineFar (j : ℕ) (hj : j+1<n) (hpos : 1 ≤ j) : WRel S omega rho q n ((wy S n) * (wg S n) j) ((wg S n) j * (wy S n))
  | idem (i : ℕ) (hi : i+1<n) : WRel S omega rho q n ((we S n) i ^ 2) ((algebraMap S (FreeAlgebra S (WLetter n))) (omega 0) * (we S n) i)
  | compress (a : ℕ) (ha : 0<a) (hn : 2≤n) :
      WRel S omega rho q n ((we S n) 0 * (wy S n) ^ a * (we S n) 0) ((algebraMap S (FreeAlgebra S (WLetter n))) (omega a) * (we S n) 0)
  | farGE (i j : ℕ) (hi : i+1<n) (hj : j+1<n)
      (hd : i + 1 < j ∨ j + 1 < i) : WRel S omega rho q n ((wg S n) i * (we S n) j) ((we S n) j * (wg S n) i)
  | farEE (i j : ℕ) (hi : i+1<n) (hj : j+1<n)
      (hd : i + 1 < j ∨ j + 1 < i) : WRel S omega rho q n ((we S n) i * (we S n) j) ((we S n) j * (we S n) i)
  | affineFarE (j : ℕ) (hj : j+1<n) (hpos : 1≤j) : WRel S omega rho q n ((wy S n) * (we S n) j) ((we S n) j * (wy S n))
  | ge (i : ℕ) (hi : i+1<n) : WRel S omega rho q n ((wg S n) i * (we S n) i) ((algebraMap S (FreeAlgebra S (WLetter n))) (↑(rho⁻¹)) * (we S n) i)
  | eg (i : ℕ) (hi : i+1<n) : WRel S omega rho q n ((we S n) i * (wg S n) i) ((algebraMap S (FreeAlgebra S (WLetter n))) (↑(rho⁻¹)) * (we S n) i)
  | ege (i j : ℕ) (hi : i+1<n) (hj : j+1<n)
      (hadj : i + 1 = j ∨ j + 1 = i) : WRel S omega rho q n ((we S n) i * (wg S n) j * (we S n) i) ((algebraMap S (FreeAlgebra S (WLetter n))) (↑rho) * (we S n) i)
  | eee (i j : ℕ) (hi : i+1<n) (hj : j+1<n)
      (hadj : i + 1 = j ∨ j + 1 = i) : WRel S omega rho q n ((we S n) i * (we S n) j * (we S n) i) ((we S n) i)
  | gge (i j : ℕ) (hi : i+1<n) (hj : j+1<n)
      (hadj : i + 1 = j ∨ j + 1 = i) : WRel S omega rho q n ((wg S n) i * (wg S n) j * (we S n) i) ((we S n) j * (we S n) i)
  | egg (i j : ℕ) (hi : i+1<n) (hj : j+1<n)
      (hadj : i + 1 = j ∨ j + 1 = i) : WRel S omega rho q n ((we S n) i * (wg S n) j * (wg S n) i) ((we S n) i * (we S n) j)
  | skein (i : ℕ) (hi : i+1<n) :
      WRel S omega rho q n ((wg S n) i - (wgi S n) i) ((algebraMap S (FreeAlgebra S (WLetter n))) ((↑q : S) - ↑(q⁻¹)) * (1 - (we S n) i))
  | unwrapLeft (hn : 2≤n) : WRel S omega rho q n ((we S n) 0 * (wy S n) * (wg S n) 0 * (wy S n) * (wg S n) 0) ((we S n) 0)
  | unwrapRight (hn : 2≤n) : WRel S omega rho q n ((wg S n) 0 * (wy S n) * (wg S n) 0 * (wy S n) * (we S n) 0) ((we S n) 0)

/-- Positive-level ordinary affine BMW presentation, Definition 2.3, PDF p.4. -/
abbrev WAffine := RingQuot (WRel S omega rho q n)

/-- Presentation map, PDF p.4. -/
def wMap : FreeAlgebra S (WLetter n) →ₐ[S] WAffine S omega rho q n :=
  RingQuot.mkAlgHom S (WRel S omega rho q n)

/-- Presentation sanity: g_1 and its named inverse multiply to one at level 2. -/
example : wMap S omega rho q 2 (wg S 2 0) *
    wMap S omega rho q 2 (wgi S 2 0) = 1 := by
  have h := RingQuot.mkAlgHom_rel S
    (WRel.gInv (S := S) (omega := omega) (rho := rho) (q := q) (n := 2) 0 (by decide))
  simpa only [wMap, map_mul, map_one] using h

end WPresentation

/-- The two flavors of Definition 2.1 and Definition 2.3. Ordinary parameters
include exactly the unit conditions and scalar relation (2.1), PDF pp.3--4. -/
inductive Kind (S : Type*) [CommRing S] (omega : ℕ → S)
  | degenerate : Kind S omega
  | ordinary (rho q : Sˣ)
      (compat : (↑(rho⁻¹) : S) - ↑rho =
        ((↑(q⁻¹) : S) - ↑q) * (omega 0 - 1)) : Kind S omega

/-- Actual affine algebra of the selected flavor. Only positive levels occur
in affine statements; level zero is explicitly the ground ring, PDF pp.3--4. -/
def Affine (S : Type*) [CommRing S] (omega : ℕ → S) (K : Kind S omega) : ℕ → Type _
  | 0 => S
  | n+1 => match K with
    | .degenerate => QAlgorithms.Papers.Independent.Renew46.P16.AffineBMW S omega (n+1)
    | .ordinary rho q _ => WAffine S omega rho q (n+1)

instance affineRing (S : Type*) [CommRing S] (omega : ℕ → S) (K : Kind S omega)
    (n : ℕ) : Ring (Affine S omega K n) := by
  cases n with
  | zero => exact inferInstanceAs (Ring S)
  | succ n => cases K <;> dsimp [Affine] <;> infer_instance

instance affineAlgebra (S : Type*) [CommRing S] (omega : ℕ → S) (K : Kind S omega)
    (n : ℕ) : Algebra S (Affine S omega K n) := by
  cases n with
  | zero => exact inferInstanceAs (Algebra S S)
  | succ n => cases K <;> dsimp [Affine, affineRing] <;> infer_instance

/-- Affine y_1; the level-zero helper is zero and is never a source generator. -/
def ay (S : Type*) [CommRing S] (omega : ℕ → S) (K : Kind S omega) :
    (n : ℕ) → Affine S omega K n
  | 0 => 0
  | n+1 => match K with
    | .degenerate => QAlgorithms.Papers.Independent.Renew46.P16.affineX S omega (n+1) 0
    | .ordinary rho q _ => wMap S omega rho q (n+1) (wy S (n+1))

/-- Affine contraction e_(i+1); valid range i+1<n, PDF pp.3--4. -/
def ae (S : Type*) [CommRing S] (omega : ℕ → S) (K : Kind S omega) :
    (n : ℕ) → ℕ → Affine S omega K n
  | 0, _ => 0
  | n+1, i => match K with
    | .degenerate => QAlgorithms.Papers.Independent.Renew46.P16.affineE S omega (n+1) i
    | .ordinary rho q _ => wMap S omega rho q (n+1) (we S (n+1) i)

/-- Affine braid s_(i+1) or g_(i+1), PDF pp.3--4. -/
def ag (S : Type*) [CommRing S] (omega : ℕ → S) (K : Kind S omega) :
    (n : ℕ) → ℕ → Affine S omega K n
  | 0, _ => 0
  | n+1, i => match K with
    | .degenerate => QAlgorithms.Papers.Independent.Renew46.P16.affineS S omega (n+1) i
    | .ordinary rho q _ => wMap S omega rho q (n+1) (wg S (n+1) i)

/-- The root polynomial as a product, equation (2.2), PDF p.4.
Repeated roots retain their multiplicity. -/
def rootPolynomial {S : Type*} [CommRing S] {r : ℕ} (u : Fin r → S) : Polynomial S :=
  ∏ i, (Polynomial.X - Polynomial.C (u i))

/-- The cyclotomic relation, Definitions 2.2 and 2.4, PDF pp.3--4. -/
def cyclRel (S : Type*) [CommRing S] (omega : ℕ → S) (K : Kind S omega)
    (n r : ℕ) (u : Fin r → S) (a b : Affine S omega K n) : Prop :=
  a = (List.ofFn fun i : Fin r => ay S omega K n - algebraMap S _ (u i)).prod ∧ b = 0

/-- Actual presented cyclotomic algebra, with the explicit level-zero
convention A_0=S. No presentation relation in a nonexistent y_1 is imposed. -/
def Cyclotomic (S : Type*) [CommRing S] (omega : ℕ → S) (K : Kind S omega)
    (r : ℕ) (u : Fin r → S) : ℕ → Type _
  | 0 => S
  | n+1 => RingQuot (cyclRel S omega K (n+1) r u)

instance cyclRing (S : Type*) [CommRing S] (omega : ℕ → S) (K : Kind S omega)
    (r : ℕ) (u : Fin r → S) (n : ℕ) : Ring (Cyclotomic S omega K r u n) := by
  cases n <;> dsimp [Cyclotomic] <;> infer_instance

instance cyclAlgebra (S : Type*) [CommRing S] (omega : ℕ → S) (K : Kind S omega)
    (r : ℕ) (u : Fin r → S) (n : ℕ) : Algebra S (Cyclotomic S omega K r u n) := by
  cases n <;> dsimp [Cyclotomic, cyclRing] <;> infer_instance

/-- Canonical affine-to-cyclotomic quotient map; at level zero it is the identity. -/
def toCycl (S : Type*) [CommRing S] (omega : ℕ → S) (K : Kind S omega)
    (r : ℕ) (u : Fin r → S) : (n : ℕ) → Affine S omega K n →ₐ[S] Cyclotomic S omega K r u n
  | 0 => AlgHom.id S S
  | n+1 => RingQuot.mkAlgHom S (cyclRel S omega K (n+1) r u)

/-- y_1 in the cyclotomic quotient, PDF pp.3--4. -/
def cy (S : Type*) [CommRing S] (omega : ℕ → S) (K : Kind S omega)
    (r : ℕ) (u : Fin r → S) (n : ℕ) : Cyclotomic S omega K r u n :=
  toCycl S omega K r u n (ay S omega K n)

/-- e_(i+1) in the cyclotomic quotient, PDF pp.3--4. -/
def ce (S : Type*) [CommRing S] (omega : ℕ → S) (K : Kind S omega)
    (r : ℕ) (u : Fin r → S) (n i : ℕ) : Cyclotomic S omega K r u n :=
  toCycl S omega K r u n (ae S omega K n i)

/-- s_(i+1) or g_(i+1) in the cyclotomic quotient, PDF pp.3--4. -/
def cg (S : Type*) [CommRing S] (omega : ℕ → S) (K : Kind S omega)
    (r : ℕ) (u : Fin r → S) (n i : ℕ) : Cyclotomic S omega K r u n :=
  toCycl S omega K r u n (ag S omega K n i)

/-- Root domain: r is positive; ordinary roots are units, Definition 2.4. -/
def ValidRoots {S : Type*} [CommRing S] {omega : ℕ → S} (K : Kind S omega)
    {r : ℕ} (u : Fin r → S) : Prop :=
  0 < r ∧ match K with
    | .degenerate => True
    | .ordinary _ _ _ => ∀ i, IsUnit (u i)

/-- Ground-ring level-zero sanity, avoiding the accepted library's
out-of-range affine generator convention in its cyclotomic level zero. -/
example (S : Type*) [CommRing S] (omega : ℕ → S) (K : Kind S omega)
    (r : ℕ) (u : Fin r → S) : Cyclotomic S omega K r u 0 = S := rfl

/-- S-span of the left ideal A e (not the two-sided ideal), PDF p.4. -/
def leftIdealSpan {S A : Type*} [CommRing S] [Ring A] [Algebra S A]
    (e : A) : Submodule S A := Submodule.span S (Set.range fun a : A => a * e)

/-- S-span of A e A, the contraction ideal, PDF pp.13--15. -/
def contractionIdeal {S A : Type*} [CommRing S] [Ring A] [Algebra S A]
    (e : A) : Submodule S A :=
  Submodule.span S {z | ∃ a b : A, z = a * e * b}

/-- The indexed cyclic family of length d, Definitions 2.8 and 5.2. -/
def cyclicFamily {S A : Type*} [CommRing S] [Ring A] [Algebra S A]
    (y e : A) (d : ℕ) : Fin d → A := fun j => y ^ j.val * e

/-- Admissibility in the ACTUAL two-strand quotient, Definition 2.8, PDF p.5. -/
def CyclicAdmissible (S : Type*) [CommRing S] (omega : ℕ → S) (K : Kind S omega)
    (r : ℕ) (u : Fin r → S) : Prop :=
  LinearIndependent S (cyclicFamily (S := S) (cy S omega K r u 2) (ce S omega K r u 2 0) r)

/-- Torsion freedom of the WHOLE left ideal, Assumption 5.1, PDF p.10.
The equation is tested on every ideal element and every nonzero scalar. -/
def IdealTorsionFree (S : Type*) [CommRing S] (omega : ℕ → S) (K : Kind S omega)
    (r : ℕ) (u : Fin r → S) : Prop :=
  ∀ s : S, s ≠ 0 → ∀ z ∈ leftIdealSpan (S := S) (ce S omega K r u 2 0), s • z = 0 → z = 0

/-- d-semi-admissibility; no monic annihilator is assumed, Definition 5.2. -/
def SemiAdmissible (S : Type*) [CommRing S] (omega : ℕ → S) (K : Kind S omega)
    (r : ℕ) (u : Fin r → S) (d : ℕ) : Prop :=
  0 < d ∧ d < r ∧
  LinearIndependent S (cyclicFamily (S := S) (cy S omega K r u 2) (ce S omega K r u 2 0) d) ∧
  ¬ LinearIndependent S (cyclicFamily (S := S) (cy S omega K r u 2) (ce S omega K r u 2 0) (d+1))

/-- The first d roots, retaining order and multiplicity, PDF p.11. -/
def firstRoots {S : Type*} {r d : ℕ} (u : Fin r → S) (h : d ≤ r) : Fin d → S :=
  fun i => u ⟨i.val, lt_of_lt_of_le i.isLt h⟩

/-- Assumption 5.3 after choosing the root ordering, PDF p.11. -/
def SplitSemi (S : Type*) [CommRing S] (omega : ℕ → S) (K : Kind S omega)
    (r : ℕ) (u : Fin r → S) (d : ℕ) (h : d ≤ r) : Prop :=
  SemiAdmissible S omega K r u d ∧
  Polynomial.aeval (cy S omega K r u 2) (rootPolynomial (firstRoots u h)) * ce S omega K r u 2 0 = 0

/-- Scalar recurrence (2.3) for a specified root list, PDF p.4. -/
def RootRecurrence {S : Type*} [CommRing S] (omega : ℕ → S)
    {r : ℕ} (u : Fin r → S) : Prop :=
  ∀ l : ℕ, ∑ j ∈ Finset.range (r+1), (rootPolynomial u).coeff j * omega (j+l) = 0

/-- At e=0 its left and two-sided ideals have zero span. -/
example {S A : Type*} [CommRing S] [Ring A] [Algebra S A] :
    leftIdealSpan (S := S) (0 : A) = ⊥ ∧ contractionIdeal (S := S) (0 : A) = ⊥ := by
  simp [leftIdealSpan, contractionIdeal]

/-- The geometric factor (1+v z)/(1-v z) as a formal series over Z[u],
PDF p.6. Its constant coefficient is 1, and its positive coefficients are 2v^a. -/
def schurFactor (r : ℕ) (i : Fin r) : PowerSeries (MvPolynomial (Fin r) ℤ) :=
  PowerSeries.mk fun a => if a = 0 then 1 else 2 * MvPolynomial.X i ^ a

/-- Schur q-polynomial: coefficient of the displayed product, PDF p.6. -/
def schurQ (r a : ℕ) : MvPolynomial (Fin r) ℤ :=
  PowerSeries.coeff a (∏ i : Fin r, schurFactor r i)

/-- The power-sum polynomial p_a, PDF p.6. -/
def powerSum (r a : ℕ) : MvPolynomial (Fin r) ℤ := ∑ i : Fin r, MvPolynomial.X i ^ a

/-- Coefficientwise INTEGER division by two. It is applied to polynomials whose
coefficients are even; no division in a target ring is performed, PDF p.6. -/
def integerHalf {r : ℕ} (p : MvPolynomial (Fin r) ℤ) : MvPolynomial (Fin r) ℤ :=
  AddMonoidAlgebra.ofCoeff
    (Finsupp.mapRange (fun z : ℤ => z / 2) (by decide) (AddMonoidAlgebra.coeff p))

/-- Integer lift of q_a/2 for a>0, PDF p.6. Its a=0 helper is not used as q_0/2. -/
def halfSchurQ (r a : ℕ) : MvPolynomial (Fin r) ℤ := integerHalf (schurQ r a)

/-- The rational polynomial eta_a^± of equation (3.3), PDF p.6.
`plus=true` means the plus sign, `plus=false` the minus sign. -/
def etaRational (r a : ℕ) (plus : Bool) : MvPolynomial (Fin r) ℚ :=
  MvPolynomial.map (Int.castRingHom ℚ) (schurQ r (a+1)) +
  MvPolynomial.C (((if plus then 1 else -1 : ℚ) * (-1) ^ (r-1)) / 2) *
    MvPolynomial.map (Int.castRingHom ℚ) (schurQ r a) +
  (if a = 0 then MvPolynomial.C (1/2 : ℚ) else 0)

/-- Explicit integral lift of eta_a^±: divide the numerator's INTEGER
coefficients by two, then evaluate in S, never evaluate 1/2 in S, PDF p.6. -/
def etaIntegral (r a : ℕ) (plus : Bool) : MvPolynomial (Fin r) ℤ :=
  integerHalf (2 * schurQ r (a+1) +
    MvPolynomial.C ((if plus then 1 else -1 : ℤ) * (-1) ^ (r-1)) * schurQ r a +
    (if a = 0 then 1 else 0))

/-- Evaluate an integer polynomial in any commutative target ring, PDF pp.6--7. -/
def evalIntegral {S : Type*} [CommRing S] {r : ℕ} (u : Fin r → S)
    (p : MvPolynomial (Fin r) ℤ) : S := MvPolynomial.eval₂Hom (Int.castRingHom S) u p

/-- The actual universal integral admissible sequence (3.8), PDF p.7. -/
def universalOmega (r a : ℕ) : MvPolynomial (Fin r) ℤ := etaIntegral r a true

/-- Root-admissibility of Definition 3.5, with the integral interpretation. -/
def RootAdmissible {S : Type*} [CommRing S] (omega : ℕ → S)
    {r : ℕ} (u : Fin r → S) : Prop :=
  ∀ a : ℕ, omega a = evalIntegral u (universalOmega r a)

/-- Polynomial sanity: a single geometric factor has constant term one. -/
example : PowerSeries.coeff 0 (schurFactor 1 0) = 1 := by
  simp [schurFactor, PowerSeries.coeff_mk]

/-- Scalar triangular equations (3.1), with j<r and no truncated last term. -/
def TriangularRelations {S : Type*} [CommRing S] (omega : ℕ → S)
    {r : ℕ} (u : Fin r → S) : Prop :=
  ∀ j : Fin r,
    ∑ m ∈ Finset.range (r-j.val), omega m * (rootPolynomial u).coeff (m+j.val+1) =
      -2 * (if Odd (r-j.val) then (rootPolynomial u).coeff j.val else 0) +
        (if Even j.val then (rootPolynomial u).coeff (j.val+1) else 0)

/-- The three tagged r-by-r families in Theorem 3.12(2), PDF p.8.
The tags are retained even when images happen to coincide. -/
def twoStrandBasisFamily (S : Type*) [CommRing S] (omega : ℕ → S)
    (r : ℕ) (u : Fin r → S) : Fin 3 × Fin r × Fin r → Cyclotomic S omega .degenerate r u 2 :=
  fun z =>
    let y1 := cy S omega .degenerate r u 2
    let y2 := toCycl S omega .degenerate r u 2 (QAlgorithms.Papers.Independent.Renew46.P16.affineX S omega 2 1)
    let e1 := ce S omega .degenerate r u 2 0
    let s1 := cg S omega .degenerate r u 2 0
    if z.1.val = 0 then y1 ^ z.2.1.val * e1 * y1 ^ z.2.2.val
    else if z.1.val = 1 then s1 * y1 ^ z.2.1.val * y2 ^ z.2.2.val
    else y1 ^ z.2.1.val * y2 ^ z.2.2.val

/-- An indexed family is a basis precisely when it is independent and spans. -/
def IsIndexedBasis {S A I : Type*} [CommRing S] [AddCommGroup A] [Module S A]
    (f : I → A) : Prop := LinearIndependent S f ∧ Submodule.span S (Set.range f) = ⊤

/-- The two conjugate families on PDF p.12. For `reverse=false` use
 g_j y'_j g_j^{-1}; for `reverse=true` use g_j^{-1} y''_j g_j. -/
def conjugateY {A : Type*} [Ring A] (g gi : ℕ → A) (y : A) (reverse : Bool) : ℕ → A
  | 0 => y
  | j+1 => if reverse then gi j * conjugateY g gi y reverse j * g j
    else g j * conjugateY g gi y reverse j * gi j

/-- Named inverse braids in the ordinary affine presentation; degenerate
braids are their own inverses. Only the ordinary case is used below. -/
def agi (S : Type*) [CommRing S] (omega : ℕ → S) (K : Kind S omega) :
    (n : ℕ) → ℕ → Affine S omega K n
  | 0, _ => 0
  | n+1, i => match K with
    | .degenerate => QAlgorithms.Papers.Independent.Renew46.P16.affineS S omega (n+1) i
    | .ordinary rho q _ => wMap S omega rho q (n+1) (wgi S (n+1) i)

/-- Named inverse braids in the cyclotomic quotient, PDF p.12. -/
def cgi (S : Type*) [CommRing S] (omega : ℕ → S) (K : Kind S omega)
    (r : ℕ) (u : Fin r → S) (n i : ℕ) : Cyclotomic S omega K r u n :=
  toCycl S omega K r u n (agi S omega K n i)

/-- Both contractions and braids commute with both conjugate families away
from the two exceptional indices, Lemma 5.6, PDF p.12. -/
def ConjugateCommutation {A : Type*} [Ring A] (n : ℕ) (g gi e : ℕ → A) (y : A) : Prop :=
  ∀ i j : ℕ, i+1 < n → j < n → j ≠ i → j ≠ i+1 → ∀ rev : Bool,
    Commute (e i) (conjugateY g gi y rev j) ∧ Commute (g i) (conjugateY g gi y rev j)

/-- Conjugation sanity: both families start at the affine generator. -/
example {A : Type*} [Ring A] (g gi : ℕ → A) (y : A) (rev : Bool) :
    conjugateY g gi y rev 0 = y := rfl

/-- Brauer diagrams are perfect matchings of the top and bottom vertex sets.
A fixed-point-free involutive permutation records each edge twice, uniquely.
The empty diagram at n=0 is included, PDF pp.7,13. -/
def diagramCount (n : ℕ) : ℕ := by
  classical
  exact Fintype.card {p : Equiv.Perm (Bool × Fin n) //
    Function.Involutive p ∧ ∀ x, p x ≠ x}

/-- b'(n) counts actual Brauer matchings with a horizontal edge, PDF p.13.
A top horizontal edge forces a bottom one; b'(0)=b'(1)=0. -/
def horizontalDiagramCount (n : ℕ) : ℕ := by
  classical
  exact Fintype.card {p : Equiv.Perm (Bool × Fin n) //
    Function.Involutive p ∧ (∀ x, p x ≠ x) ∧
      ∃ i j : Fin n, p (false,i) = (false,j)}

/-- Spanning by a set of EXACTLY k distinct elements. This does not assume
linear independence, Lemmas 5.8 and 5.10, PDF pp.13,15. -/
def HasSpanningSetCard {S A : Type*} [CommRing S] [AddCommGroup A] [Module S A]
    (V : Submodule S A) (k : ℕ) : Prop :=
  ∃ f : Fin k → A, Function.Injective f ∧ Submodule.span S (Set.range f) = V

universe u

/-- The cell equations of Definition 6.1, PDF p.16, for a SPECIFIED
anti-involution. The accepted weak basis predicate swaps indices modulo higher
cells. The optional size is the cardinality of the indexed cellular basis.
No integral-domain requirement is built in, so Theorem 3.11 covers CommRing. -/
def CellDatumFor {S A : Type u} [CommRing S] [Ring A] [Algebra S A]
    (star : A →ₗ[S] A) (size : Option ℕ) : Prop :=
  ∃ (L : Type u) (ord : PartialOrder L) (T : L → Type u)
    (fin : ∀ l, Fintype (T l))
    (c : QAlgorithms.Papers.Independent.Renew46.P16.CellIndex L T → A),
    letI : PartialOrder L := ord
    letI : ∀ l, Fintype (T l) := fin
    QAlgorithms.Papers.Independent.Renew46.P16.IsWeakCellularBasis (R := S) c star ∧
    match size with
    | none => True
    | some k => Nonempty (QAlgorithms.Papers.Independent.Renew46.P16.CellIndex L T ≃ Fin k)

/-- Cellularity for the canonical generator-fixing anti-involution, PDF pp.3--4,16.
The anti-involution is required in the conclusion and fixes every presentation
generator: y_1, all contractions and all braids generate the algebra (the
remaining degenerate y_j are determined recursively by the skein relations).
At level zero fixing 1 together with S-linearity gives the identity on S. -/
def CanonicalCellular (S : Type u) [CommRing S] (omega : ℕ → S)
    (K : Kind S omega) (r : ℕ) (u : Fin r → S) (n : ℕ) (size : Option ℕ) : Prop :=
  ∃ star : Cyclotomic S omega K r u n →ₗ[S] Cyclotomic S omega K r u n,
    CellDatumFor star size ∧ star 1 = 1 ∧
    star (cy S omega K r u n) = cy S omega K r u n ∧
    (∀ i : ℕ, i+1 < n →
      star (ce S omega K r u n i) = ce S omega K r u n i ∧
      star (cg S omega K r u n i) = cg S omega K r u n i)

/-- A finite dimensional module with nonzero e-action, expressed in a chosen
finite basis as a unital F-algebra representation. No simplicity is imposed. -/
def HasFiniteModule {F A : Type*} [Field F] [Ring A] [Algebra F A] (e : A) : Prop :=
  ∃ m : ℕ, 0 < m ∧ ∃ pi : A →ₐ[F] Matrix (Fin m) (Fin m) F, pi e ≠ 0

/-- Existence of admissible positive-degree cyclotomic parameters, PDF p.17.
Ordinary roots must be units; degenerate roots may be zero. -/
def HasAdmissibleRoots (F : Type*) [Field F] (omega : ℕ → F) (K : Kind F omega) : Prop :=
  ∃ (r : ℕ) (u : Fin r → F), ValidRoots K u ∧ CyclicAdmissible F omega K r u

/-- Rationality of the generating series at infinity, PDF p.18. With z=t^{-1},
Q(z) times the formal series is P(z), and Q(0) is explicitly nonzero. -/
def RationalSequence {F : Type*} [Field F] (omega : ℕ → F) : Prop :=
  ∃ P Q : Polynomial F, Q.coeff 0 ≠ 0 ∧
    (Q : PowerSeries F) * PowerSeries.mk omega = (P : PowerSeries F)

/-- A monic homogeneous recurrence after threshold N, Theorem 7.1(2), PDF p.18. -/
def RecurrenceFrom {F : Type*} [Field F] (omega : ℕ → F) (N : ℕ) : Prop :=
  ∃ (r : ℕ) (a : Fin r → F), 0 < r ∧ ∀ l : ℕ, N ≤ l →
    omega (r+l) + ∑ j : Fin r, a j * omega (j.val+l) = 0

/-- Finite-module sanity: the zero contraction cannot have nonzero action. -/
example {F A : Type*} [Field F] [Ring A] [Algebra F A] :
    ¬ HasFiniteModule (F := F) (0 : A) := by
  simp [HasFiniteModule]

/-- Formal rationality sanity: the zero series has numerator zero and denominator one. -/
example {F : Type*} [Field F] : RationalSequence (fun _ => (0 : F)) := by
  refine ⟨0, 1, by simp, ?_⟩
  ext n
  simp [PowerSeries.coeff_mk]

end QAlgorithms.Papers.Independent.Support21.P12


