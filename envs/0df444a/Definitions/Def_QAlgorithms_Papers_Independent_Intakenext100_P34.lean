-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P34
-- name    : QAlgorithms_Papers_Independent_Intakenext100_P34
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-31T05:03:19.434973+00:00
-- url     : https://prove2.me/theorems/de1028f2-92ce-4f75-b271-215389ad83fa
-- title:
--   Definitions for Affine and degenerate affine BMW algebras: The center
-- statement:
--   The objects the formalized statements of *Affine and degenerate affine BMW algebras: The center* (arXiv:1105.4207) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `Adj`: Valid adjacent-generator positions; this is empty at level one.
--   - `adjacentLeft`: Left endpoint of a valid adjacent pair, in zero-based coordinates.
--   - `adjacentRight`: Right endpoint of a valid adjacent pair.
--   - `trans`: The source's adjacent transposition.
--   - `DLetter`: Letters of (2.1); false/true label kappa_0/kappa_1.
--   - `DFree`: Free algebra before imposing (2.2)--(2.5).
--   - `dt`: Permutation letter in the free algebra.
--   - `dk`: Kappa letter in the free algebra.
--   - `dy`: Commuting-variable letter before the quotient.
--   - `dg`: Adjacent gamma as defined in (2.5).
--   - `DRel`: Exactly (2.2)--(2.5); the permutation identity represents the algebra unit.
--   - `DBraid`: The unspecialized degenerate affine braid algebra of Section 2.1.
--   - `dbMap`: Its canonical quotient homomorphism.
--   - `GIndex`: Indices 0,...,k, with none representing 0 and some j representing j+1.
--   - `GLetter`: Letters of the alternative presentation (2.8), with distinct gamma endpoints.
--   - `GFree`: Free algebra for the alternate presentation.
--   - `gt`: Permutation generator in the alternate presentation.
--   - `gk`: Kappa generator in the alternate presentation.
--   - `gg`: Gamma generator; the diagonal value is unused in every relation.
--   - `gAction`: Permutations fix index zero.
--   - `GRel`: Precisely the relations (2.9)--(2.11).
--   - `GBraid`: The algebra defined by the second presentation, with no scalar kappa specialization.
--   - `gbMap`: Its canonical quotient map.
--   - `gY`: The generator change y_j=kappa_j/2+sum_(0≤l<j) gamma_(l,j), (2.16).
--   - `de`: The source's e_i, defined by (2.21), before the BMW quotient.
--   - `DParams`: Parameter data, including the implicit invertibility of 2. No admissibility assumed.
--   - `DWRel`: All BMW relations (2.23)--(2.24), optionally specializing the two kappas.
--   - `DW`: The actual degenerate affine BMW algebra, including the chosen scalar specialization.
--   - `dwMap`: Canonical map into the presented algebra.
--   - `ps`: Constant series in a possibly noncommutative coefficient algebra.
--   - `geometric`: Geometric series (1-a u⁻¹)⁻¹, with its coefficients specified directly.
--   - `infinityResolvent`: The formal resolvent (u-a)⁻¹.
--   - `halfResolvent`: The formal series (2u-a)⁻¹ when h represents 1/2.
--   - `DAdmissible`: The admissibility identity (4.5), multiplied by u⁻² and written in X=u⁻¹.
--   - `DCancel`: Formal substitution for the additive cancellation test, with no test at level one.
--   - `dEval`: Canonical evaluation in the commuting y-generators, ordered by variable index.
--   - `DCenterDescription`: Equality of the center with the canonically evaluated cancellation ring.
--   - `dRatio`: The rational factor in (3.8), expanded at infinity using its unit constant denominator.
--   - `dRatioProduct`: Ordered product of the (3.8) factors for a finite family of commuting variables.
--   - `seriesTail`: Removing the constant coefficient shifts Xⁿ⁺¹ to Xⁿ, hence multiplies by u.
--   - `dMomentPolynomial`: Constructive compression representatives: coefficients of (z_0(u)+epsilon*u-1/2) product R(y_j,u)-epsilon*u+1/2. The cancelled principal part is implemented by seriesTail(product-1). These are polynomials, not arbitrary representatives of a compression equation.
--   - `dMomentAt`: Canonical representative evaluated in a larger level by the initial-variable inclusion.
--   - `dMomentSeries`: The positive or sign-reversed representative generating series at a specified level.
--   - `AParams`: Unit parameters and all integer-indexed moments from Section 2.4. The zeroth moment is supplied as parameter data, even when E_1 vanishes.
--   - `ALetter`: Group generators and their inverse letters; false/true means generator/inverse.
--   - `AFree`: Free algebra used to present the affine braid group algebra and its BMW quotient.
--   - `aCrossing`: A crossing or inverse crossing.
--   - `ax`: The flagpole group generator or its inverse.
--   - `affineYWord`: Y_j and Y_j⁻¹ from (2.38)--(2.39), constructed without any arbitrary inverse.
--   - `affineContractionWord`: E_i=1-(T_i-T_i⁻¹)/Q, (2.45).
--   - `signedPow`: Integer powers represented using an element and its specified inverse.
--   - `AWRel`: Exactly the group presentation (2.33)--(2.36) and quotient (2.42)--(2.43). All signs and both sides of each two-sided relation are retained.
--   - `AW`: The unrestricted affine BMW algebra; there is no cyclotomic polynomial relation.
--   - `awMap`: The canonical quotient map.
--   - `multiplicativeResolvent`: Y/(u-Y), expanded at infinity.
--   - `pairResolvent`: Y_i Y_(i+1)/(u²-Y_i Y_(i+1)), expanded at infinity.
--   - `AAdmissible`: The scalar admissibility condition (4.20); u²/(u²-1)=1+g.
--   - `Laurent`: Laurent polynomials with integer exponent vectors and finite support.
--   - `aEval`: Canonical Laurent evaluation using the actual Y_j and their constructed inverses.
--   - `laurentVariable`: A Laurent variable, or its inverse, as a finite exponent-vector monomial.
--   - `aRatio`: The factor of (3.27) after division by its leading u⁴ coefficient.
--   - `aScalarFraction`: The normalized numerator (u²-q²)(u²-q⁻²)/(u²-1)² in (3.26).
--   - `aShiftedPositive`: The shifted positive series Z_n^++z⁻¹/Q-u²/(u²-1), constructed by (3.28).
--   - `aMomentPolynomial`: Explicit integer-moment representatives as Laurent polynomials. At n=0 the supplied bilateral scalar sequence is retained. At higher n, positive moments come from (3.28) and negative ones from (3.26), using the unit constant z/Q of its positive factor. No E_i is cancelled.
--   - `aMomentAt`: Canonical evaluation of the n-variable representative at a larger level.
--   - `aMomentSeries`: The two series both use u⁻ˡ as degree; only the moment index changes sign.
--   - `ACancel`: Permutation invariance of Laurent coefficients and the formal reciprocal-pair test. The substitutions send (d_1,d_2,...) to (d_1-d_2,0,...) or (0,0,...).
--   - `ACenterDescription`: Center equality in the actual affine quotient via its canonical Laurent embedding.
--   - `leftMultiples`: Principal left ideal as the actual set of left multiples.
--   - `CyclotomicIntegers`: The actual ring Z[zeta] inside the complex numbers.
--   - `CyclotomicField`: The actual field Q(zeta) inside the complex numbers.
--   - `integralRoot`: The distinguished root as an element of its integer coefficient ring.
--   - `Wheel`: The r-variable root-of-unity wheel condition, as a formal polynomial identity.
--   - `coefficientPowerSum`: The integral power sum from the frozen library, extended along the canonical integer map.
-- source:
--   Affine and degenerate affine BMW algebras: The center, arXiv:1105.4207v2, https://arxiv.org/abs/1105.4207v2

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P08
import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P12

/-!
Statements from Daugherty--Ram--Virk, arXiv:1105.4207v2.
Indices in Fin k are the source's indices 1,...,k shifted down by one.
All presentations below are actual quotients of free algebras. No basis,
centrality, admissibility, or tower injectivity is included in a presentation.
The formal variable X in PowerSeries is u⁻¹, never a numerical specialization.
-/

namespace QAlgorithms.Papers.Independent.Intakenext100.P34

open QAlgorithms.Papers.Independent.Support21.P08 (Central)

noncomputable section

universe u

variable (C : Type u) [CommRing C]

/-- Valid adjacent-generator positions; this is empty at level one. -/
abbrev Adj (k : ℕ) := Fin (k - 1)

/-- Left endpoint of a valid adjacent pair, in zero-based coordinates. -/
def adjacentLeft {k : ℕ} (i : Adj k) : Fin k := ⟨i.val, by have := i.isLt; omega⟩

/-- Right endpoint of a valid adjacent pair. -/
def adjacentRight {k : ℕ} (i : Adj k) : Fin k := ⟨i.val + 1, by have := i.isLt; omega⟩

/-- The source's adjacent transposition. -/
def trans {k : ℕ} (i : Adj k) : Equiv.Perm (Fin k) := Equiv.swap (adjacentLeft i) (adjacentRight i)

/-- Letters of (2.1); false/true label kappa_0/kappa_1. -/
inductive DLetter (k : ℕ)
| perm : Equiv.Perm (Fin k) → DLetter k
| kappa : Bool → DLetter k
| y : Fin k → DLetter k

/-- Free algebra before imposing (2.2)--(2.5). -/
abbrev DFree (k : ℕ) := FreeAlgebra C (DLetter k)

/-- Permutation letter in the free algebra. -/
def dt {k : ℕ} (w : Equiv.Perm (Fin k)) : DFree C k := FreeAlgebra.ι C (.perm w)

/-- Kappa letter in the free algebra. -/
def dk {k : ℕ} (b : Bool) : DFree C k := FreeAlgebra.ι C (.kappa b)

/-- Commuting-variable letter before the quotient. -/
def dy {k : ℕ} (j : Fin k) : DFree C k := FreeAlgebra.ι C (.y j)

/-- Adjacent gamma as defined in (2.5). -/
def dg {k : ℕ} (i : Adj k) : DFree C k :=
  dy C (adjacentRight i) - dt C (trans i) * dy C (adjacentLeft i) * dt C (trans i)

/-- Exactly (2.2)--(2.5); the permutation identity represents the algebra unit. -/
inductive DRel (k : ℕ) : DFree C k → DFree C k → Prop
| identity : DRel k (dt C (1 : Equiv.Perm (Fin k))) 1
| perm (w v) : DRel k (dt C w * dt C v) (dt C (w * v))
| yy (i j) : DRel k (dy C i * dy C j) (dy C j * dy C i)
| kappas : DRel k (dk C false * dk C true) (dk C true * dk C false)
| kappay (b j) : DRel k (dk C b * dy C j) (dy C j * dk C b)
| kappa0t (i : Adj k) :
    DRel k (dk C false * dt C (trans i)) (dt C (trans i) * dk C false)
| kappa1first (i : Adj k) (h : i.val = 0) :
    DRel k (dk C true * dt C (trans i) * dk C true * dt C (trans i))
      (dt C (trans i) * dk C true * dt C (trans i) * dk C true)
| kappa1other (i : Adj k) (h : i.val ≠ 0) :
    DRel k (dk C true * dt C (trans i)) (dt C (trans i) * dk C true)
| sum (i : Adj k) :
    DRel k (dt C (trans i) * (dy C (adjacentLeft i) + dy C (adjacentRight i)))
      ((dy C (adjacentLeft i) + dy C (adjacentRight i)) * dt C (trans i))
| distant (i : Adj k) (j : Fin k) (h1 : j ≠ adjacentLeft i) (h2 : j ≠ adjacentRight i) :
    DRel k (dy C j * dt C (trans i)) (dt C (trans i) * dy C j)
| gamma (i j : Adj k) (h : j.val = i.val + 1) :
    DRel k (dt C (trans i) * dt C (trans j) * dg C i * dt C (trans j) * dt C (trans i))
      (dg C j)

/-- The unspecialized degenerate affine braid algebra of Section 2.1. -/
abbrev DBraid (k : ℕ) := RingQuot (DRel C k)

/-- Its canonical quotient homomorphism. -/
def dbMap (k : ℕ) : DFree C k →ₐ[C] DBraid C k := RingQuot.mkAlgHom C (DRel C k)

/-- Indices 0,...,k, with none representing 0 and some j representing j+1. -/
abbrev GIndex (k : ℕ) := Option (Fin k)

/-- Letters of the alternative presentation (2.8), with distinct gamma endpoints. -/
inductive GLetter (k : ℕ)
| perm : Equiv.Perm (Fin k) → GLetter k
| kappa : GIndex k → GLetter k
| gamma : {p : GIndex k × GIndex k // p.1 ≠ p.2} → GLetter k

/-- Free algebra for the alternate presentation. -/
abbrev GFree (k : ℕ) := FreeAlgebra C (GLetter k)

/-- Permutation generator in the alternate presentation. -/
def gt {k : ℕ} (w : Equiv.Perm (Fin k)) : GFree C k := FreeAlgebra.ι C (.perm w)

/-- Kappa generator in the alternate presentation. -/
def gk {k : ℕ} (j : GIndex k) : GFree C k := FreeAlgebra.ι C (.kappa j)

/-- Gamma generator; the diagonal value is unused in every relation. -/
def gg {k : ℕ} (i j : GIndex k) : GFree C k :=
  if h : i ≠ j then FreeAlgebra.ι C (.gamma ⟨(i,j),h⟩) else 0

/-- Permutations fix index zero. -/
def gAction {k : ℕ} (w : Equiv.Perm (Fin k)) : GIndex k → GIndex k := Option.map w

/-- Precisely the relations (2.9)--(2.11). -/
inductive GRel (k : ℕ) : GFree C k → GFree C k → Prop
| identity : GRel k (gt C (1 : Equiv.Perm (Fin k))) 1
| perm (w v) : GRel k (gt C w * gt C v) (gt C (w*v))
| conjugateKappa (w) (i : GIndex k) :
    GRel k (gt C w * gk C i * gt C w⁻¹) (gk C (gAction w i))
| conjugateGamma (w) (i j : GIndex k) (h : i ≠ j) :
    GRel k (gt C w * gg C i j * gt C w⁻¹) (gg C (gAction w i) (gAction w j))
| kappas (i j : GIndex k) : GRel k (gk C i * gk C j) (gk C j * gk C i)
| kappaGamma (i l m : GIndex k) (h : l ≠ m) :
    GRel k (gk C i * gg C l m) (gg C l m * gk C i)
| symmetry (i j : GIndex k) (h : i ≠ j) : GRel k (gg C i j) (gg C j i)
| disjoint (p r l m : GIndex k) (hpr : p ≠ r) (hlm : l ≠ m)
    (hpl : p ≠ l) (hpm : p ≠ m) (hrl : r ≠ l) (hrm : r ≠ m) :
    GRel k (gg C p r * gg C l m) (gg C l m * gg C p r)
| triangle (i j r : GIndex k) (hij : i ≠ j) (hir : i ≠ r) (hjr : j ≠ r) :
    GRel k (gg C i j * (gg C i r + gg C j r))
      ((gg C i r + gg C j r) * gg C i j)

/-- The algebra defined by the second presentation, with no scalar kappa specialization. -/
abbrev GBraid (k : ℕ) := RingQuot (GRel C k)

/-- Its canonical quotient map. -/
def gbMap (k : ℕ) : GFree C k →ₐ[C] GBraid C k := RingQuot.mkAlgHom C (GRel C k)

/-- The generator change y_j=kappa_j/2+sum_(0≤l<j) gamma_(l,j), (2.16). -/
def gY (k : ℕ) (half : C) (j : Fin k) : GFree C k :=
  algebraMap C (GFree C k) half*gk C (some j) + gg C none (some j) +
    ∑ l : Fin k, if l.val < j.val then gg C (some l) (some j) else 0

example (half : C) : gY C 1 half (0 : Fin 1) =
    algebraMap C (GFree C 1) half*gk C (some 0) + gg C none (some 0) := by
  simp [gY]

/-- The source's e_i, defined by (2.21), before the BMW quotient. -/
def de {k : ℕ} (i : Adj k) : DFree C k :=
  1 + dt C (trans i) * dy C (adjacentLeft i) - dy C (adjacentRight i) * dt C (trans i)

/-- Parameter data, including the implicit invertibility of 2. No admissibility assumed. -/
structure DParams where
  two : Cˣ
  two_val : (two : C) = 2
  epsilon : C
  epsilon_sign : epsilon = 1 ∨ epsilon = -1
  moment : ℕ → C
  scalarKappa : Option (C × C)

/-- All BMW relations (2.23)--(2.24), optionally specializing the two kappas. -/
inductive DWRel (P : DParams C) (k : ℕ) : DFree C k → DFree C k → Prop
| braid {a b} (h : DRel C k a b) : DWRel P k a b
| et (i : Adj k) : DWRel P k (de C i * dt C (trans i))
    (algebraMap C (DFree C k) P.epsilon * de C i)
| te (i : Adj k) : DWRel P k (dt C (trans i) * de C i)
    (algebraMap C (DFree C k) P.epsilon * de C i)
| neighbor (i j : Adj k) (h : i.val + 1 = j.val ∨ j.val + 1 = i.val) :
    DWRel P k (de C i * dt C (trans j) * de C i)
      (algebraMap C (DFree C k) P.epsilon * de C i)
| compression (i : Adj k) (h : i.val = 0) (n : ℕ) :
    DWRel P k (de C i * dy C (adjacentLeft i) ^ n * de C i)
      (algebraMap C (DFree C k) (P.moment n) * de C i)
| killLeft (i : Adj k) : DWRel P k (de C i * (dy C (adjacentLeft i) + dy C (adjacentRight i))) 0
| killRight (i : Adj k) : DWRel P k ((dy C (adjacentLeft i) + dy C (adjacentRight i)) * de C i) 0
| scalar0 (a b : C) (h : P.scalarKappa = some (a,b)) :
    DWRel P k (dk C false) (algebraMap C (DFree C k) a)
| scalar1 (a b : C) (h : P.scalarKappa = some (a,b)) :
    DWRel P k (dk C true) (algebraMap C (DFree C k) b)

/-- The actual degenerate affine BMW algebra, including the chosen scalar specialization. -/
abbrev DW (P : DParams C) (k : ℕ) := RingQuot (DWRel C P k)

/-- Canonical map into the presented algebra. -/
def dwMap (P : DParams C) (k : ℕ) : DFree C k →ₐ[C] DW C P k :=
  RingQuot.mkAlgHom C (DWRel C P k)

/-- Constant series in a possibly noncommutative coefficient algebra. -/
abbrev ps {A : Type*} [Semiring A] (a : A) : PowerSeries A := PowerSeries.C a

/-- Geometric series (1-a u⁻¹)⁻¹, with its coefficients specified directly. -/
def geometric {A : Type*} [Semiring A] (a : A) : PowerSeries A := PowerSeries.mk (fun n => a ^ n)

/-- The formal resolvent (u-a)⁻¹. -/
def infinityResolvent {A : Type*} [Semiring A] (a : A) : PowerSeries A := PowerSeries.X * geometric a

/-- The formal series (2u-a)⁻¹ when h represents 1/2. -/
def halfResolvent {A : Type*} [Semiring A] (h a : A) : PowerSeries A :=
  ps h * PowerSeries.X * geometric (h * a)

example {A : Type*} [Semiring A] (a : A) : PowerSeries.coeff 0 (geometric a) = 1 := by
  simp [geometric]

example {A : Type*} [Semiring A] (a : A) : PowerSeries.coeff 0 (infinityResolvent a) = 0 := by
  simp [infinityResolvent]

/-- The admissibility identity (4.5), multiplied by u⁻² and written in X=u⁻¹. -/
def DAdmissible (P : DParams C) : Prop :=
  let h : C := ↑P.two⁻¹
  let z := PowerSeries.mk P.moment
  let zm := PowerSeries.mk (fun n => (-1 : C)^n * P.moment n)
  (PowerSeries.X*zm-ps h*PowerSeries.X-ps P.epsilon) *
    (PowerSeries.X*z-ps h*PowerSeries.X+ps P.epsilon) =
    (ps h*PowerSeries.X-ps P.epsilon)*(ps h*PowerSeries.X+ps P.epsilon)

/-- Formal substitution for the additive cancellation test, with no test at level one. -/
def DCancel (k : ℕ) (f : MvPolynomial (Fin k) C) : Prop :=
  MvPolynomial.IsSymmetric f ∧ ∀ h : 2 ≤ k,
    let a : Fin k := ⟨0, by omega⟩
    let b : Fin k := ⟨1, by omega⟩
    MvPolynomial.eval₂ MvPolynomial.C
      (fun j => if j = a then MvPolynomial.X a else if j = b then -MvPolynomial.X a
        else MvPolynomial.X j) f =
    MvPolynomial.eval₂ MvPolynomial.C
      (fun j => if j = a ∨ j = b then 0 else MvPolynomial.X j) f

/-- Canonical evaluation in the commuting y-generators, ordered by variable index. -/
def dEval (P : DParams C) (k : ℕ) (f : MvPolynomial (Fin k) C) : DW C P k :=
  (AddMonoidAlgebra.coeff f).sum (fun d c => algebraMap C (DW C P k) c *
    (List.ofFn (fun j : Fin k => (dwMap C P k (dy C j)) ^ d j)).prod)

/-- Equality of the center with the canonically evaluated cancellation ring. -/
def DCenterDescription (P : DParams C) (k : ℕ) : Prop :=
  Function.Injective (dEval C P k) ∧
    ∀ a : DW C P k, Central a ↔ ∃ f, DCancel C k f ∧ dEval C P k f = a

/-- The rational factor in (3.8), expanded at infinity using its unit constant denominator. -/
def dRatio {A : Type*} [Ring A] (a : A) : PowerSeries A :=
  let t : PowerSeries A := PowerSeries.X
  let plus := 1+ps a*t
  let minus := 1-ps a*t
  let numerator := (plus^2-t^2)*minus^2
  let denominator := (minus^2-t^2)*plus^2
  numerator*PowerSeries.invOfUnit denominator 1

/-- Ordered product of the (3.8) factors for a finite family of commuting variables. -/
def dRatioProduct {A : Type*} [Ring A] {n : ℕ} (y : Fin n → A) : PowerSeries A :=
  (List.ofFn (fun j => dRatio (y j))).prod

/-- Removing the constant coefficient shifts Xⁿ⁺¹ to Xⁿ, hence multiplies by u. -/
def seriesTail {A : Type*} [Semiring A] (s : PowerSeries A) : PowerSeries A :=
  PowerSeries.mk (fun n => PowerSeries.coeff (n+1) s)

/-- Constructive compression representatives: coefficients of
(z_0(u)+epsilon*u-1/2) product R(y_j,u)-epsilon*u+1/2.
The cancelled principal part is implemented by seriesTail(product-1).
These are polynomials, not arbitrary representatives of a compression equation. -/
def dMomentPolynomial (P : DParams C) (n ell : ℕ) : MvPolynomial (Fin n) C :=
  let product := dRatioProduct (fun j : Fin n => (MvPolynomial.X j : MvPolynomial (Fin n) C))
  let z := PowerSeries.mk (fun m => MvPolynomial.C (P.moment m) : ℕ → MvPolynomial (Fin n) C)
  let half := MvPolynomial.C (↑P.two⁻¹ : C)
  PowerSeries.coeff ell ((z-ps half)*product+ps half+
    ps (MvPolynomial.C P.epsilon)*seriesTail (product-1))

/-- Canonical representative evaluated in a larger level by the initial-variable inclusion. -/
def dMomentAt (P : DParams C) (n level ell : ℕ) (h : n ≤ level) : DW C P level :=
  dEval C P level (MvPolynomial.rename (Fin.castLE h) (dMomentPolynomial C P n ell))

/-- The positive or sign-reversed representative generating series at a specified level. -/
def dMomentSeries (P : DParams C) (n level : ℕ) (h : n ≤ level) (negative : Bool := false) :
    PowerSeries (DW C P level) :=
  PowerSeries.mk (fun ell => (if negative then (-1 : DW C P level)^ell else 1)*
    dMomentAt C P n level ell h)

example (P : DParams C) (ell : ℕ) :
    dMomentPolynomial C P 0 ell = MvPolynomial.C (P.moment ell) := by
  simp [dMomentPolynomial, dRatioProduct, seriesTail]

/-- Unit parameters and all integer-indexed moments from Section 2.4.
The zeroth moment is supplied as parameter data, even when E_1 vanishes. -/
structure AParams where
  q : Cˣ
  z : Cˣ
  Q : Cˣ
  Q_val : (Q : C) = (q : C) - (↑q⁻¹ : C)
  moment : ℤ → C
  moment_zero : moment 0 = 1 + ((z : C) - (↑z⁻¹ : C)) * (↑Q⁻¹ : C)

/-- Group generators and their inverse letters; false/true means generator/inverse. -/
inductive ALetter (k : ℕ)
| crossing : Adj k → Bool → ALetter k
| flag : Bool → ALetter k

/-- Free algebra used to present the affine braid group algebra and its BMW quotient. -/
abbrev AFree (k : ℕ) := FreeAlgebra C (ALetter k)

/-- A crossing or inverse crossing. -/
def aCrossing {k : ℕ} (i : Adj k) (inverse : Bool := false) : AFree C k :=
  FreeAlgebra.ι C (.crossing i inverse)

/-- The flagpole group generator or its inverse. -/
def ax {k : ℕ} (inverse : Bool := false) : AFree C k := FreeAlgebra.ι C (.flag inverse)

/-- Y_j and Y_j⁻¹ from (2.38)--(2.39), constructed without any arbitrary inverse. -/
def affineYWord (P : AParams C) {k : ℕ} (j : Fin k) (inverse : Bool := false) : AFree C k :=
  let word := List.ofFn (fun i : Fin j.val =>
    aCrossing C (⟨i.val, by have := i.isLt; have := j.isLt; omega⟩ : Adj k) inverse)
  let middle := algebraMap C (AFree C k) (if inverse then (↑P.z⁻¹ : C) else (P.z : C)) * ax C inverse
  word.reverse.prod * middle * word.prod

/-- E_i=1-(T_i-T_i⁻¹)/Q, (2.45). -/
def affineContractionWord (P : AParams C) {k : ℕ} (i : Adj k) : AFree C k :=
  1-algebraMap C (AFree C k) (↑P.Q⁻¹ : C)*(aCrossing C i false-aCrossing C i true)

/-- Integer powers represented using an element and its specified inverse. -/
def signedPow {A : Type*} [Monoid A] (a inverse : A) (n : ℤ) : A :=
  if 0 ≤ n then a ^ n.toNat else inverse ^ (-n).toNat

/-- Exactly the group presentation (2.33)--(2.36) and quotient (2.42)--(2.43).
All signs and both sides of each two-sided relation are retained. -/
inductive AWRel (P : AParams C) (k : ℕ) : AFree C k → AFree C k → Prop
| inverseT (i : Adj k) (b : Bool) : AWRel P k (aCrossing C i b * aCrossing C i (!b)) 1
| inverseX (b : Bool) : AWRel P k (ax C b * ax C (!b)) 1
| distant (i j : Adj k) (h1 : i.val+1 ≠ j.val) (h2 : j.val+1 ≠ i.val) :
    AWRel P k (aCrossing C i * aCrossing C j) (aCrossing C j * aCrossing C i)
| braid (i j : Adj k) (h : j.val = i.val+1) :
    AWRel P k (aCrossing C i * aCrossing C j * aCrossing C i) (aCrossing C j * aCrossing C i * aCrossing C j)
| flagFirst (i : Adj k) (h : i.val = 0) :
    AWRel P k (ax C * aCrossing C i * ax C * aCrossing C i) (aCrossing C i * ax C * aCrossing C i * ax C)
| flagOther (i : Adj k) (h : 0 < i.val) : AWRel P k (ax C * aCrossing C i) (aCrossing C i * ax C)
| et (i : Adj k) (b : Bool) : AWRel P k (affineContractionWord C P i * aCrossing C i b)
    (algebraMap C (AFree C k) (if b then (P.z : C) else (↑P.z⁻¹ : C)) * affineContractionWord C P i)
| te (i : Adj k) (b : Bool) : AWRel P k (aCrossing C i b * affineContractionWord C P i)
    (algebraMap C (AFree C k) (if b then (P.z : C) else (↑P.z⁻¹ : C)) * affineContractionWord C P i)
| neighbor (i j : Adj k) (h : i.val+1 = j.val ∨ j.val+1 = i.val) (b : Bool) :
    AWRel P k (affineContractionWord C P i * aCrossing C j b * affineContractionWord C P i)
      (algebraMap C (AFree C k) (if b then (↑P.z⁻¹ : C) else (P.z : C)) * affineContractionWord C P i)
| compression (i : Adj k) (h : i.val = 0) (n : ℤ) :
    AWRel P k (affineContractionWord C P i * signedPow (affineYWord C P (adjacentLeft i) false) (affineYWord C P (adjacentLeft i) true) n * affineContractionWord C P i)
      (algebraMap C (AFree C k) (P.moment n) * affineContractionWord C P i)
| killLeft (i : Adj k) : AWRel P k (affineContractionWord C P i * affineYWord C P (adjacentLeft i) * affineYWord C P (adjacentRight i)) (affineContractionWord C P i)
| killRight (i : Adj k) : AWRel P k (affineYWord C P (adjacentLeft i) * affineYWord C P (adjacentRight i) * affineContractionWord C P i) (affineContractionWord C P i)

/-- The unrestricted affine BMW algebra; there is no cyclotomic polynomial relation. -/
abbrev AW (P : AParams C) (k : ℕ) := RingQuot (AWRel C P k)

/-- The canonical quotient map. -/
def awMap (P : AParams C) (k : ℕ) : AFree C k →ₐ[C] AW C P k :=
  RingQuot.mkAlgHom C (AWRel C P k)

/-- Y/(u-Y), expanded at infinity. -/
def multiplicativeResolvent {A : Type*} [Semiring A] (a : A) : PowerSeries A :=
  ps a * infinityResolvent a

/-- Y_i Y_(i+1)/(u²-Y_i Y_(i+1)), expanded at infinity. -/
def pairResolvent {A : Type*} [Ring A] (a : A) : PowerSeries A :=
  PowerSeries.mk (fun n => if n % 2 = 0 then a ^ (n/2) else 0) - 1

example {A : Type*} [Semiring A] (a : A) :
    PowerSeries.coeff 0 (multiplicativeResolvent a) = 0 := by
  simp [multiplicativeResolvent, infinityResolvent]

example {A : Type*} [Ring A] (a : A) : PowerSeries.coeff 0 (pairResolvent a) = 0 := by
  simp [pairResolvent]

/-- The scalar admissibility condition (4.20); u²/(u²-1)=1+g. -/
def AAdmissible (P : AParams C) : Prop :=
  let zp := PowerSeries.mk (fun n => P.moment (n : ℤ))
  let zm := PowerSeries.mk (fun n => P.moment (-(n : ℤ)))
  let g : PowerSeries C := pairResolvent (1 : C)
  let qi := ps (↑P.Q⁻¹ : C)
  (zm-ps (P.z : C)*qi-(1+g))*(zp+ps (↑P.z⁻¹ : C)*qi-(1+g)) =
    -(qi^2*(1+ps (2-(P.q : C)^2-(↑P.q⁻¹ : C)^2)*(g+g^2)))

/-- Laurent polynomials with integer exponent vectors and finite support. -/
abbrev Laurent (k : ℕ) := AddMonoidAlgebra C (Fin k → ℤ)

/-- Canonical Laurent evaluation using the actual Y_j and their constructed inverses. -/
def aEval (P : AParams C) (k : ℕ) (f : Laurent C k) : AW C P k :=
  (AddMonoidAlgebra.coeff f).sum (fun d c => algebraMap C (AW C P k) c *
    (List.ofFn (fun j : Fin k => signedPow (awMap C P k (affineYWord C P j false))
      (awMap C P k (affineYWord C P j true)) (d j))).prod)

/-- A Laurent variable, or its inverse, as a finite exponent-vector monomial. -/
def laurentVariable {k : ℕ} (j : Fin k) (inverse : Bool := false) : Laurent C k :=
  AddMonoidAlgebra.single (Pi.single j (if inverse then (-1 : ℤ) else 1)) 1

/-- The factor of (3.27) after division by its leading u⁴ coefficient. -/
def aRatio {A : Type*} [Ring A] (q qi y yi : A) : PowerSeries A :=
  let t : PowerSeries A := PowerSeries.X
  let f (a : A) := 1-ps a*t
  (f y)^2*f (qi^2*yi)*f (q^2*yi)*
    PowerSeries.invOfUnit ((f yi)^2*f (q^2*y)*f (qi^2*y)) 1

/-- The normalized numerator (u²-q²)(u²-q⁻²)/(u²-1)² in (3.26). -/
def aScalarFraction {A : Type*} [Ring A] (q qi : A) : PowerSeries A :=
  let g := pairResolvent (1 : A)
  1+ps (2-q^2-qi^2)*(g+g^2)

/-- The shifted positive series Z_n^++z⁻¹/Q-u²/(u²-1), constructed by (3.28). -/
def aShiftedPositive (P : AParams C) (n : ℕ) : PowerSeries (Laurent C n) :=
  let c := algebraMap C (Laurent C n)
  let h := 1+pairResolvent (1 : Laurent C n)
  let initial := PowerSeries.mk (fun ell => c (P.moment (ell : ℤ)))+
    ps (c ((↑P.z⁻¹ : C)*(↑P.Q⁻¹ : C)))-h
  initial*(List.ofFn (fun j : Fin n => aRatio (c (P.q : C)) (c (↑P.q⁻¹ : C))
    (laurentVariable C j false) (laurentVariable C j true))).prod

/-- Explicit integer-moment representatives as Laurent polynomials.
At n=0 the supplied bilateral scalar sequence is retained. At higher n,
positive moments come from (3.28) and negative ones from (3.26), using the
unit constant z/Q of its positive factor. No E_i is cancelled. -/
def aMomentPolynomial (P : AParams C) (n : ℕ) (ell : ℤ) : Laurent C n :=
  let c := algebraMap C (Laurent C n)
  if n = 0 then c (P.moment ell) else
    let h := 1+pairResolvent (1 : Laurent C n)
    let shifted := aShiftedPositive C P n
    let positive := shifted-ps (c ((↑P.z⁻¹ : C)*(↑P.Q⁻¹ : C)))+h
    let unitConstant : (Laurent C n)ˣ := Units.map c (P.z*P.Q⁻¹)
    let negative := ps (c ((P.z : C)*(↑P.Q⁻¹ : C)))+h-
      ps (c ((↑P.Q⁻¹ : C)^2))*aScalarFraction (c (P.q : C)) (c (↑P.q⁻¹ : C))*
        PowerSeries.invOfUnit shifted unitConstant
    if 0 ≤ ell then PowerSeries.coeff ell.toNat positive
      else PowerSeries.coeff (-ell).toNat negative

/-- Canonical evaluation of the n-variable representative at a larger level. -/
def aMomentAt (P : AParams C) (n level : ℕ) (ell : ℤ) (h : n ≤ level) : AW C P level :=
  (AddMonoidAlgebra.coeff (aMomentPolynomial C P n ell)).sum (fun d c => algebraMap C (AW C P level) c *
    (List.ofFn (fun j : Fin n =>
      let a : Fin level := ⟨j.val, lt_of_lt_of_le j.isLt h⟩
      signedPow (awMap C P level (affineYWord C P a false))
        (awMap C P level (affineYWord C P a true)) (d j))).prod)

/-- The two series both use u⁻ˡ as degree; only the moment index changes sign. -/
def aMomentSeries (P : AParams C) (n level : ℕ) (h : n ≤ level) (negative : Bool := false) :
    PowerSeries (AW C P level) :=
  PowerSeries.mk (fun ell => aMomentAt C P n level
    (if negative then -(ell : ℤ) else (ell : ℤ)) h)

example (P : AParams C) (ell : ℤ) :
    aMomentPolynomial C P 0 ell = algebraMap C (Laurent C 0) (P.moment ell) := by
  simp [aMomentPolynomial]

/-- Permutation invariance of Laurent coefficients and the formal reciprocal-pair test.
The substitutions send (d_1,d_2,...) to (d_1-d_2,0,...) or (0,0,...). -/
def ACancel (k : ℕ) (f : Laurent C k) : Prop :=
  (∀ (w : Equiv.Perm (Fin k)) (d : Fin k → ℤ), AddMonoidAlgebra.coeff f (d ∘ w) = AddMonoidAlgebra.coeff f d) ∧
  ∀ h : 2 ≤ k,
    let a : Fin k := ⟨0, by omega⟩
    let b : Fin k := ⟨1, by omega⟩
    (AddMonoidAlgebra.coeff f).sum (fun d c => (AddMonoidAlgebra.single
      (fun j => if j = a then d a-d b else if j = b then 0 else d j) c : Laurent C k)) =
    (AddMonoidAlgebra.coeff f).sum (fun d c => (AddMonoidAlgebra.single
      (fun j => if j = a ∨ j = b then 0 else d j) c : Laurent C k))

/-- Center equality in the actual affine quotient via its canonical Laurent embedding. -/
def ACenterDescription (P : AParams C) (k : ℕ) : Prop :=
  Function.Injective (aEval C P k) ∧
    ∀ a : AW C P k, Central a ↔ ∃ f, ACancel C k f ∧ aEval C P k f = a

/-- Principal left ideal as the actual set of left multiples. -/
def leftMultiples {A : Type*} [Mul A] (e : A) : Set A := {a | ∃ b, a = b*e}

/-- The actual ring Z[zeta] inside the complex numbers. -/
def CyclotomicIntegers (zeta : ℂ) := Algebra.adjoin ℤ ({zeta} : Set ℂ)

/-- The actual field Q(zeta) inside the complex numbers. -/
def CyclotomicField (zeta : ℂ) := IntermediateField.adjoin ℚ ({zeta} : Set ℂ)

/-- The distinguished root as an element of its integer coefficient ring. -/
def integralRoot (zeta : ℂ) : CyclotomicIntegers zeta :=
  ⟨zeta, Algebra.subset_adjoin (by simp)⟩

/-- The r-variable root-of-unity wheel condition, as a formal polynomial identity. -/
def Wheel (k r : ℕ) (hk : 0 < k) (zeta : C) (f : MvPolynomial (Fin k) C) : Prop :=
  MvPolynomial.IsSymmetric f ∧
    MvPolynomial.eval₂ MvPolynomial.C
      (fun j => if j.val < r then MvPolynomial.C (zeta^j.val)*MvPolynomial.X (⟨0,hk⟩ : Fin k)
        else MvPolynomial.X j) f =
    MvPolynomial.eval₂ MvPolynomial.C
      (fun j => if j.val < r then 0 else MvPolynomial.X j) f

/-- The integral power sum from the frozen library, extended along the canonical integer map. -/
def coefficientPowerSum (k n : ℕ) : MvPolynomial (Fin k) C :=
  MvPolynomial.map (Int.castRingHom C)
    (QAlgorithms.Papers.Independent.Support21.P12.powerSum k n)

example (k : ℕ) : coefficientPowerSum C k 1 = ∑ j : Fin k, MvPolynomial.X j := by
  simp [coefficientPowerSum, QAlgorithms.Papers.Independent.Support21.P12.powerSum]

end

end QAlgorithms.Papers.Independent.Intakenext100.P34


