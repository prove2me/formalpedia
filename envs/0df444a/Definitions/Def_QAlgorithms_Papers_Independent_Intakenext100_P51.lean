-- Prove2me | Definitions.Def_QAlgorithms_Papers_Independent_Intakenext100_P51
-- name    : QAlgorithms_Papers_Independent_Intakenext100_P51
-- status  : Definition
-- author  : @Gohan
-- created : 2026-10-30T22:56:18.068786+00:00
-- url     : https://prove2.me/theorems/23bbe940-6a8f-418f-b5ab-77cb05795533
-- title:
--   Definitions for The representations of cyclotomic BMW algebras
-- statement:
--   The objects the formalized statements of *The representations of cyclotomic BMW algebras* (arXiv:0801.0465) are stated in. Each was checked against the paper by a blind read-back and a moderator.
--
--   - `RuiXuUnitParameters`: Unit ground data before choosing moments, Definition 2.1, PDF p.2.
--   - `Ground`: Full ground data, PDF p.2. No nonzero or unit condition on omega_0.
--   - `RuiXuLetter`: Source one-based generator labels. No out-of-range generators are present.
--   - `ruiXuFreeT`: Free T_i, with zero outside 1 <= i < n; Definition 2.1, PDF p.2.
--   - `ruiXuFreeE`: Free E_i, with zero outside 1 <= i < n; Definition 2.1, PDF p.2.
--   - `ruiXuFreeX`: Free X_j or X_j inverse (true), with zero outside 1 <= j <= n.
--   - `signedPower`: Integer powers in an algebra with specified inverse. All subtraction occurs in Z; nonnegative exponents include the zeroth power.
--   - `RuiXuBMWRelations`: ALL relations (a)--(k) of Definition 2.1, PDF p.2. Both skein, both untwisting and both tangle equalities are imposed.
--   - `RuiXuBMW`: Actual presented algebra, not an arbitrary algebra with chosen generators.
--   - `ruiXuBMWMap`: Canonical free-algebra projection, Definition 2.1, PDF p.2.
--   - `T`: T_i in the source presentation.
--   - `ruiXuE`: E_i in the source presentation.
--   - `ruiXuX`: X_j or its inverse in the source presentation.
--   - `XPow`: Integer power of the actual invertible X_j, PDF pp.2--3.
--   - `TInv`: T_i inverse expressed by the Kauffman relation, PDF p.3.
--   - `evenIndicator`: The integer parity indicator (1+(-1)^a)/2, without requiring 2 invertible.
--   - `geometric`: The exact geometric expansion 1/(1-v t) in a formal variable t.
--   - `qSeries`: Q-series of (3.10), PDF p.10: product (u_i-t)/(1-u_i t).
--   - `qCoeff`: Q_a(u), Definition 3.9, PDF p.10.
--   - `RhoChoice`: The parity-dependent rho alternatives, Proposition 3.2(2), PDF p.5.
--   - `positiveMoment`: Right side of (3.12), PDF p.10, for every a>=0.
--   - `negativeMoment`: Right side of (3.13), PDF p.10, used only for a>0. In the even case a=1, range (a-1) is empty, exactly the printed sum through -1.
--   - `RuiXuUAdmissible`: Definition 3.15, PDF p.11, over an arbitrary commutative unital ring.
--   - `positiveSeries`: Positive moment series, with t=y inverse and constant omega_0, PDF p.11.
--   - `negativeSeries`: Negative moment series starts at a=1; its constant is zero, PDF p.11.
--   - `paritySeries`: Exact expansion y^2/(y^2-1)=1/(1-t^2) at infinity.
--   - `positiveRHS`: Positive displayed rational function in Lemma 3.16, PDF p.11, expanded at infinity. Q(u;t)=product u_i product (y-u_i inverse)/(y-u_i). The gamma term y gamma_r(y)/(y^2-1) expands to tG for odd r and -G for even r.
--   - `negativeRHS`: Negative displayed rational function in Lemma 3.16, PDF p.11, expanded at infinity. Q(u inverse;t)=product u_i inverse product (y-u_i)/(y-u_i inverse). The term y/(gamma_r(y)(y^2-1)) expands to tG or -t^2G.
--   - `cyclotomicCoeff`: Cyclotomic coefficients (-1)^(r-s) sigma_(r-s)(u), Definition 2.6, p.3.
--   - `RuiXuAdmissible`: BOTH admissibility identities (2.5), PDF p.3, with all integer shifts b.
--   - `gammaParity`: gamma_r(z) in Proposition 3.2(1), PDF p.5.
--   - `ruiXuSpectralWeight`: The rational gamma_i weight in Proposition 3.2(1), PDF p.5, mapped into an actual field. Products omit i and all exponents below are integer exponents.
--   - `spectralMoment`: The computed integer moment, not a freely chosen variable, PDF pp.5,10.
--   - `genericGenerators`: The displayed r+1 transcendental generators, section 3, PDF p.4.
--   - `IsGenericField`: K is precisely Q(u_1,...,u_r,q), not an arbitrary field extension, p.4.
--   - `twoStrandMonomial`: The SPECIFIED 3r^2 indexed monomials in Theorem 3.8, PDF p.9.
--   - `SimpleAction`: Nonzero unital simple left representation. Invariant subspaces are quantified explicitly; no action or simplicity is inferred from dimensions.
--   - `EquivalentActions`: Actual intertwining linear isomorphism of the whole left action.
--   - `OneLabel`: The 2r one-dimensional labels, Proposition 3.1(a), PDF p.4.
--   - `TwoLabel`: Unordered distinct parameter pairs, with a canonical increasing order, Proposition 3.1(b), PDF p.4. The cardinality is binomial(r,2).
--   - `heckeEigenvalue`: The two allowed eigenvalues q and -q inverse, PDF p.4.
--   - `twoTMatrix`: Exactly the 2x2 T matrix in Proposition 3.1(b), PDF p.4, including the common factor u_j/(u_j-u_i). Columns give images of basis vectors.
--   - `twoXMatrix`: X_1 or X_2 diagonal matrix of Proposition 3.1(b), PDF p.4.
--   - `HeckeLetter`: Exact Hecke generator alphabet from PDF p.3, with one-based helpers.
--   - `ruiXuFreeG`: Free normalized Hecke generator g_i.
--   - `ruiXuFreeY`: Free Hecke generator y_j; no inverse letters or extra contractions.
--   - `RuiXuHeckeRelations`: All seven normalized Hecke relation groups (a)--(g), PDF p.3.
--   - `RuiXuHecke`: The exact normalized Ariki--Koike algebra, PDF p.3.
--   - `heckeMap`: Canonical Hecke quotient map.
--   - `HG`: g_i in the normalized Hecke presentation.
--   - `HY`: y_j in the normalized Hecke presentation.
--   - `ruiXuContractionIdeal`: Actual two-sided ideal B E_1 B, as the R-span of all products a E_1 b, PDF p.34. It is zero at levels 0 and 1.
--   - `RuiXuHeckeQuotient`: Quotient by the actual contraction ideal, Proposition 5.2, PDF p.34.
--   - `toHeckeQuotient`: Actual quotient projection used in Proposition 5.2, PDF p.34.
--   - `lowerImage`: Canonical lower-level image, PDF p.34. Adjoining generators describes the image without assuming injectivity of the strand homomorphism. At m=0 this is the scalar subalgebra.
--   - `lowerContraction`: Image of the lower contraction ideal, zero at m=0,1; PDF pp.34--35.
--   - `contractionChain`: E^f = E_(n-1) E_(n-3) ... E_(n-2f+1), in the printed order, p.35.
--   - `idealLayer`: The actual two-sided contraction layer, with the terminal layer set to zero as in Definition 5.3, PDF p.35.
--   - `exponentWord`: Exactly the active coordinates of kappa in N_r^(f,n), PDF p.35. They correspond to the distinct positions n-1,n-3,...,n-2f+1.
--   - `intervalWord`: T_(a,b) in the exact ordered word for s_(a,b), PDF p.35. The downward branch is T_(a-1)...T_b and the upward branch is T_a...T_(b-1).
--   - `pairWord`: The prescribed D_(1,m) representative s_(m-1,i) s_(m,j), with 1<=i<j<=m, evaluated in the ambient algebra. Formula (5.6), PDF p.35.
--   - `ValidPair`: The named D_(1,m) indices; the identity pair is (m-1,m), p.35.
--   - `nOne`: N_1 is the actual span in Lemma 5.11, PDF p.36. Its D_1 indexing is expanded using the ordered representative formula (5.6); no abstract right module is substituted for this submodule of the actual presented algebra.
--   - `lowerProduct`: Lower-image product submodule B'_(n-2) h, PDF p.38.
--   - `nThree`: BOTH generating families of N_3, Lemma 5.14, PDF p.38. The second family has the exact nonidentity d_1 s_(n-1,n-3) s_(n,n-2) word.
--   - `LastWords`: The three d_2 words in Lemmas 5.15 and 5.17, PDF pp.38--39.
--   - `nFourBound`: N_(4,k), with |l_1|<=p and |k_1|<=bound. Lemma 5.15, PDF p.38.
--   - `nFour`: The actual N_4 of Lemma 5.17, with BOTH exponents bounded, PDF p.39.
--   - `mSpan`: M_l of Lemma 5.18, PDF p.39. The first integer exponent k is UNBOUNDED.
--   - `LowerInduction`: Full induction hypothesis shared by 5.18 and 5.22, PDF pp.39--40. At l=0 the strict absolute-value condition admits no l_prime.
--   - `nTwo`: Actual N_2 of Proposition 5.27, PDF p.41. D_(2,n) is expanded by (5.6) in the order s_(n-3,i_2) s_(n-2,j_2) s_(n-1,i_1) s_(n,j_1), with i_2<i_1 and both pairs in their specified ranges.
--   - `laurentEval`: Evaluation of a Laurent word in the first m variables in an ambient BMW algebra. Both signs are letters, as in Definition 2.1, PDF p.2. Only m<=n is used as an inclusion; no injectivity is assumed.
--   - `laurentImage`: The actual Laurent coefficient subalgebra R[X_1^{+-1},...,X_m^{+-1}] in the ambient algebra, Lemma 4.21, PDF p.17.
--   - `CentralLaurentWord`: Centrality is checked in the actual lower algebra, not just in a possibly collapsed upper image; Lemma 4.21, PDF p.17.
--   - `ncGeometric`: Exact geometric expansion (1-v t) inverse in a possibly noncommutative coefficient ring. This is a complete formal series, not a truncation.
--   - `linearFactor`: The factor 1-v t in the formal variable t=y inverse.
--   - `transitionNumerator`: The numerator of (4.22) after normalizing every y-c to 1-c t, PDF p.17. Every X_k superscript -1 is inversion, never k-1.
--   - `transitionDenominator`: The denominator of (4.22), with unit constant coefficient 1, p.17.
--   - `transitionSeries`: The entire ratio of (4.22), expanded constructively using geometric series. No division in a noncommutative fraction field is used, PDF p.17.
--   - `centralParitySeries`: G(t)=1/(1-t^2)=y^2/(y^2-1), in the actual algebra coefficient ring.
--   - `shiftedMomentBase`: The base shifted series Wtilde_1+delta inverse rho-G, with coefficients mapped from the prescribed moments; (4.28), PDF p.21.
--   - `shiftedMomentProduct`: Ordered constructive product in (4.28). j counts factors, so j=0 is the prescribed scalar base and j=k-1 gives level k; PDF p.21.
--   - `centralMomentSeries`: Canonically constructed Wtilde_k, obtained from the base and the complete product (4.28); not an arbitrary sequence satisfying the theorem.
--   - `ruiXuCentralMoment`: The constructed coefficient omega_k^(a) in the ambient algebra, p.17.
--   - `signedT`: The two generator choices T_i and T_i inverse used in Corollary 4.27.
--   - `ruiXuAdjacentPerm`: One-based adjacent transposition s_i in S_n. The identity helper value outside 1<=i<n is never used as a source generator. PDF p.15.
--   - `intervalPerm`: Source ordered s_(a,b), PDF p.35. Permutations act on tableau labels on the RIGHT, so the list is reversed before Mathlib's function-composition product. This convention is also used in representativePerm below.
--   - `pairPerm`: Source s_(m-1,i) s_(m,j), interpreted as a right action, PDF p.35.
--   - `permEntry`: One-based label at a zero-based cell position after the right action; the out-of-range helper is unused in a valid row condition.
--   - `sourceTransversal`: The actual row-standard transversal in PDF p.35: an increasing first row of n-2f entries, then f increasing pairs whose first column increases. This definition uses tableau conditions, independently of (5.6).
--   - `RepresentativeIndices`: Exactly the inequalities of (5.6), with Fin f coordinate j meaning source k=j+1: 1<=i_f<...<i_1 and 1<=i_k<j_k<=n-2k+2.
--   - `representativePerm`: The exact ordered representative s_(n-2f+1,i_f) s_(n-2f+2,j_f) ... s_(n-1,i_1) s_(n,j_1), as a permutation, PDF p.35. The Mathlib product is in reverse source order because the action is right.
--   - `representativeSet`: The right side of (5.6) is a SET of actual permutations, not words.
-- source:
--   The representations of cyclotomic BMW algebras, arXiv:0801.0465v2, https://arxiv.org/abs/0801.0465v2

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P12

/-!
Rui--Xu, arXiv:0801.0465v2. Paper-local definitions use the exact presentation
of Definition 2.1, including arbitrary integer moments and possibly zero omega_0.
No prior BMW admissibility predicate is substituted for Definition 3.15.
The accepted generic two-sided contraction span is reused through a guarded
source-level wrapper. Other similarly named frozen objects have different
parameter types or meanings; RuiXu names distinguish the source constructions.
Constructor operands are explicit so their level is the inductive binder n.
Compilation is pending the batch mechanical check.
-/

noncomputable section

open scoped BigOperators Classical

namespace QAlgorithms.Papers.Independent.Intakenext100.P51

/-- Unit ground data before choosing moments, Definition 2.1, PDF p.2. -/
structure RuiXuUnitParameters (R : Type*) [CommRing R] (r : ℕ) where
  positive : 0 < r
  q : Rˣ
  delta : Rˣ
  rho : Rˣ
  u : Fin r → Rˣ
  delta_eq : (delta : R) = (q : R) - ↑q⁻¹

/-- Full ground data, PDF p.2. No nonzero or unit condition on omega_0. -/
structure Ground (R : Type*) [CommRing R] (r : ℕ) extends RuiXuUnitParameters R r where
  omega : ℤ → R
  omega_zero : omega 0 = 1 - (↑delta⁻¹ : R) * ((rho : R) - ↑rho⁻¹)

/-- Source one-based generator labels. No out-of-range generators are present. -/
inductive RuiXuLetter (n : ℕ)
  | t : Fin (n - 1) → RuiXuLetter n
  | e : Fin (n - 1) → RuiXuLetter n
  | x : Fin n → Bool → RuiXuLetter n

/-- Free T_i, with zero outside 1 <= i < n; Definition 2.1, PDF p.2. -/
def ruiXuFreeT (R : Type*) [CommRing R] (n i : ℕ) : FreeAlgebra R (RuiXuLetter n) :=
  if h : 1 ≤ i ∧ i < n then FreeAlgebra.ι R (.t ⟨i - 1, by omega⟩) else 0

/-- Free E_i, with zero outside 1 <= i < n; Definition 2.1, PDF p.2. -/
def ruiXuFreeE (R : Type*) [CommRing R] (n i : ℕ) : FreeAlgebra R (RuiXuLetter n) :=
  if h : 1 ≤ i ∧ i < n then FreeAlgebra.ι R (.e ⟨i - 1, by omega⟩) else 0

/-- Free X_j or X_j inverse (true), with zero outside 1 <= j <= n. -/
def ruiXuFreeX (R : Type*) [CommRing R] (n j : ℕ) (inverse : Bool) :
    FreeAlgebra R (RuiXuLetter n) :=
  if h : 1 ≤ j ∧ j ≤ n then FreeAlgebra.ι R (.x ⟨j - 1, by omega⟩ inverse) else 0

/-- Integer powers in an algebra with specified inverse. All subtraction occurs
in Z; nonnegative exponents include the zeroth power. -/
def signedPower {A : Type*} [Monoid A] (x xi : A) (a : ℤ) : A :=
  if 0 ≤ a then x ^ a.toNat else xi ^ (-a).toNat

/-- The negative first power uses the inverse generator, not truncated subtraction. -/
example {A : Type*} [Monoid A] (x xi : A) : signedPower x xi (-1) = xi := by
  simp [signedPower]

section Presentation

variable {R : Type*} [CommRing R] {r : ℕ} (P : Ground R r) (n : ℕ)

local notation "t" => ruiXuFreeT R n
local notation "e" => ruiXuFreeE R n
local notation "x" => ruiXuFreeX R n
local notation "c" => algebraMap R (FreeAlgebra R (RuiXuLetter n))

/-- ALL relations (a)--(k) of Definition 2.1, PDF p.2. Both skein,
both untwisting and both tangle equalities are imposed. -/
inductive RuiXuBMWRelations (P : Ground R r) (n : ℕ) : FreeAlgebra R (RuiXuLetter n) → FreeAlgebra R (RuiXuLetter n) → Prop
  | inverseL (j : ℕ) (hj : 1 ≤ j ∧ j ≤ n) : RuiXuBMWRelations P n ((ruiXuFreeX R n) j false * (ruiXuFreeX R n) j true) 1
  | inverseR (j : ℕ) (hj : 1 ≤ j ∧ j ≤ n) : RuiXuBMWRelations P n ((ruiXuFreeX R n) j true * (ruiXuFreeX R n) j false) 1
  | kauffman (i : ℕ) (hi : 1 ≤ i ∧ i < n) :
      RuiXuBMWRelations P n ((ruiXuFreeT R n) i ^ 2 - (algebraMap R (FreeAlgebra R (RuiXuLetter n))) (P.delta : R) * (ruiXuFreeT R n) i + (algebraMap R (FreeAlgebra R (RuiXuLetter n))) ((P.delta : R) * ↑P.rho) * (ruiXuFreeE R n) i) 1
  | far (i j : ℕ) (hi : 1 ≤ i ∧ i < n) (hj : 1 ≤ j ∧ j < n)
      (hd : i + 1 < j ∨ j + 1 < i) : RuiXuBMWRelations P n ((ruiXuFreeT R n) i * (ruiXuFreeT R n) j) ((ruiXuFreeT R n) j * (ruiXuFreeT R n) i)
  | braid (i : ℕ) (hi : 1 ≤ i ∧ i + 1 < n) :
      RuiXuBMWRelations P n ((ruiXuFreeT R n) i * (ruiXuFreeT R n) (i+1) * (ruiXuFreeT R n) i) ((ruiXuFreeT R n) (i+1) * (ruiXuFreeT R n) i * (ruiXuFreeT R n) (i+1))
  | txFar (i j : ℕ) (hi : 1 ≤ i ∧ i < n) (hj : 1 ≤ j ∧ j ≤ n)
      (hd : j ≠ i ∧ j ≠ i+1) : RuiXuBMWRelations P n ((ruiXuFreeT R n) i * (ruiXuFreeX R n) j false) ((ruiXuFreeX R n) j false * (ruiXuFreeT R n) i)
  | idempotent (i : ℕ) (hi : 1 ≤ i ∧ i < n) :
      RuiXuBMWRelations P n ((ruiXuFreeE R n) i ^ 2) ((algebraMap R (FreeAlgebra R (RuiXuLetter n))) (P.omega 0) * (ruiXuFreeE R n) i)
  | xx (i j : ℕ) (hi : 1 ≤ i ∧ i ≤ n) (hj : 1 ≤ j ∧ j ≤ n) :
      RuiXuBMWRelations P n ((ruiXuFreeX R n) i false * (ruiXuFreeX R n) j false) ((ruiXuFreeX R n) j false * (ruiXuFreeX R n) i false)
  | skeinL (i : ℕ) (hi : 1 ≤ i ∧ i < n) :
      RuiXuBMWRelations P n ((ruiXuFreeT R n) i * (ruiXuFreeX R n) i false - (ruiXuFreeX R n) (i+1) false * (ruiXuFreeT R n) i)
        ((algebraMap R (FreeAlgebra R (RuiXuLetter n))) (P.delta : R) * (ruiXuFreeX R n) (i+1) false * ((ruiXuFreeE R n) i - 1))
  | skeinR (i : ℕ) (hi : 1 ≤ i ∧ i < n) :
      RuiXuBMWRelations P n ((ruiXuFreeX R n) i false * (ruiXuFreeT R n) i - (ruiXuFreeT R n) i * (ruiXuFreeX R n) (i+1) false)
        ((algebraMap R (FreeAlgebra R (RuiXuLetter n))) (P.delta : R) * ((ruiXuFreeE R n) i - 1) * (ruiXuFreeX R n) (i+1) false)
  | unwrap (a : ℤ) (hn : 2 ≤ n) :
      RuiXuBMWRelations P n ((ruiXuFreeE R n) 1 * signedPower ((ruiXuFreeX R n) 1 false) ((ruiXuFreeX R n) 1 true) a * (ruiXuFreeE R n) 1) ((algebraMap R (FreeAlgebra R (RuiXuLetter n))) (P.omega a) * (ruiXuFreeE R n) 1)
  | untwistL (i : ℕ) (hi : 1 ≤ i ∧ i < n) : RuiXuBMWRelations P n ((ruiXuFreeE R n) i * (ruiXuFreeT R n) i) ((algebraMap R (FreeAlgebra R (RuiXuLetter n))) (P.rho : R) * (ruiXuFreeE R n) i)
  | untwistR (i : ℕ) (hi : 1 ≤ i ∧ i < n) : RuiXuBMWRelations P n ((ruiXuFreeT R n) i * (ruiXuFreeE R n) i) ((algebraMap R (FreeAlgebra R (RuiXuLetter n))) (P.rho : R) * (ruiXuFreeE R n) i)
  | tangleL (i : ℕ) (hi : 1 ≤ i ∧ i + 1 < n) :
      RuiXuBMWRelations P n ((ruiXuFreeE R n) (i+1) * (ruiXuFreeE R n) i) ((ruiXuFreeE R n) (i+1) * (ruiXuFreeT R n) i * (ruiXuFreeT R n) (i+1))
  | tangleR (i : ℕ) (hi : 1 ≤ i ∧ i + 1 < n) :
      RuiXuBMWRelations P n ((ruiXuFreeE R n) (i+1) * (ruiXuFreeE R n) i) ((ruiXuFreeT R n) i * (ruiXuFreeT R n) (i+1) * (ruiXuFreeE R n) i)
  | tripleL (i : ℕ) (hi : 1 ≤ i ∧ i + 1 < n) : RuiXuBMWRelations P n ((ruiXuFreeE R n) (i+1) * (ruiXuFreeE R n) i * (ruiXuFreeE R n) (i+1)) ((ruiXuFreeE R n) (i+1))
  | tripleR (i : ℕ) (hi : 1 ≤ i ∧ i + 1 < n) : RuiXuBMWRelations P n ((ruiXuFreeE R n) i * (ruiXuFreeE R n) (i+1) * (ruiXuFreeE R n) i) ((ruiXuFreeE R n) i)
  | antisymL (i : ℕ) (hi : 1 ≤ i ∧ i < n) : RuiXuBMWRelations P n ((ruiXuFreeE R n) i * (ruiXuFreeX R n) i false * (ruiXuFreeX R n) (i+1) false) ((ruiXuFreeE R n) i)
  | antisymR (i : ℕ) (hi : 1 ≤ i ∧ i < n) : RuiXuBMWRelations P n ((ruiXuFreeX R n) i false * (ruiXuFreeX R n) (i+1) false * (ruiXuFreeE R n) i) ((ruiXuFreeE R n) i)
  | cyclotomic (hn : 1 ≤ n) :
      RuiXuBMWRelations P n ((List.ofFn fun j : Fin r => (ruiXuFreeX R n) 1 false - (algebraMap R (FreeAlgebra R (RuiXuLetter n))) (P.u j : R)).prod) 0

/-- Actual presented algebra, not an arbitrary algebra with chosen generators. -/
abbrev RuiXuBMW := RingQuot (RuiXuBMWRelations P n)

/-- Canonical free-algebra projection, Definition 2.1, PDF p.2. -/
def ruiXuBMWMap : FreeAlgebra R (RuiXuLetter n) →ₐ[R] RuiXuBMW P n := RingQuot.mkAlgHom R (RuiXuBMWRelations P n)

/-- T_i in the source presentation. -/
def T (i : ℕ) : RuiXuBMW P n := ruiXuBMWMap P n (t i)

/-- E_i in the source presentation. -/
def ruiXuE (i : ℕ) : RuiXuBMW P n := ruiXuBMWMap P n (e i)

/-- X_j or its inverse in the source presentation. -/
def ruiXuX (j : ℕ) (inverse : Bool := false) : RuiXuBMW P n := ruiXuBMWMap P n (x j inverse)

/-- Integer power of the actual invertible X_j, PDF pp.2--3. -/
def XPow (j : ℕ) (a : ℤ) : RuiXuBMW P n := signedPower (ruiXuX P n j false) (ruiXuX P n j true) a

/-- T_i inverse expressed by the Kauffman relation, PDF p.3. -/
def TInv (i : ℕ) : RuiXuBMW P n :=
  T P n i - algebraMap R (RuiXuBMW P n) (P.delta : R) +
    algebraMap R (RuiXuBMW P n) (P.delta : R) * ruiXuE P n i

/-- The zeroth X power is the unit even before any relations are used. -/
example (j : ℕ) : XPow P n j 0 = 1 := by simp [XPow, signedPower]

end Presentation

section Moments

variable {R : Type*} [CommRing R] {r : ℕ}

/-- The integer parity indicator (1+(-1)^a)/2, without requiring 2 invertible. -/
def evenIndicator (R : Type*) [CommRing R] (a : ℕ) : R := if Even a then 1 else 0

/-- The exact geometric expansion 1/(1-v t) in a formal variable t. -/
def geometric (v : R) : PowerSeries R := PowerSeries.mk fun a => v ^ a

/-- Q-series of (3.10), PDF p.10: product (u_i-t)/(1-u_i t). -/
def qSeries (u : Fin r → R) : PowerSeries R :=
  ∏ i, (PowerSeries.C (u i) - PowerSeries.X) * geometric (u i)

/-- Q_a(u), Definition 3.9, PDF p.10. -/
def qCoeff (u : Fin r → R) (a : ℕ) : R := PowerSeries.coeff a (qSeries u)

/-- The empty Q-product is 1, pinning the series normalization. -/
example : qSeries (fun i : Fin 0 => (Fin.elim0 i : R)) = 1 := by
  simp [qSeries]

/-- The parity-dependent rho alternatives, Proposition 3.2(2), PDF p.5. -/
def RhoChoice (P : RuiXuUnitParameters R r) : Prop :=
  if Odd r then (↑P.rho⁻¹ : R) = ∏ i, (P.u i : R) ∨
    (↑P.rho⁻¹ : R) = -(∏ i, (P.u i : R))
  else (↑P.rho⁻¹ : R) = (↑P.q⁻¹ : R) * ∏ i, (P.u i : R) ∨
    (↑P.rho⁻¹ : R) = -(P.q : R) * ∏ i, (P.u i : R)

/-- Right side of (3.12), PDF p.10, for every a>=0. -/
def positiveMoment (P : RuiXuUnitParameters R r) (a : ℕ) : R :=
  let u : Fin r → R := fun i => P.u i
  let base := evenIndicator R a + (↑P.delta⁻¹ : R) * ↑P.rho * qCoeff u a * ∏ i, u i
  (if Odd r then base + ∑ k ∈ Finset.range a, evenIndicator R k * qCoeff u (a-1-k)
   else base - ∑ k ∈ Finset.range (a+1), evenIndicator R k * qCoeff u (a-k)) -
    if a = 0 then (↑P.delta⁻¹ : R) * ↑P.rho else 0

/-- Right side of (3.13), PDF p.10, used only for a>0. In the even case
a=1, range (a-1) is empty, exactly the printed sum through -1. -/
def negativeMoment (P : RuiXuUnitParameters R r) (a : ℕ) : R :=
  let u : Fin r → R := fun i => P.u i
  let ui : Fin r → R := fun i => ↑(P.u i)⁻¹
  let base := evenIndicator R a - (↑P.delta⁻¹ : R) * ↑P.rho * qCoeff ui a * ∏ i, u i
  if Odd r then base + ∑ k ∈ Finset.range a, evenIndicator R k * qCoeff ui (a-1-k)
  else base - ∑ k ∈ Finset.range (a-1), evenIndicator R k * qCoeff ui (a-2-k)

/-- Definition 3.15, PDF p.11, over an arbitrary commutative unital ring. -/
def RuiXuUAdmissible (P : Ground R r) : Prop :=
  RhoChoice P.toRuiXuUnitParameters ∧
  (∀ a : ℕ, P.omega (a : ℤ) = positiveMoment P.toRuiXuUnitParameters a) ∧
  (∀ a : ℕ, 0 < a → P.omega (-(a : ℤ)) = negativeMoment P.toRuiXuUnitParameters a)

/-- Positive moment series, with t=y inverse and constant omega_0, PDF p.11. -/
def positiveSeries (P : Ground R r) : PowerSeries R := PowerSeries.mk fun a => P.omega (a : ℤ)

/-- Negative moment series starts at a=1; its constant is zero, PDF p.11. -/
def negativeSeries (P : Ground R r) : PowerSeries R :=
  PowerSeries.mk fun a => if a = 0 then 0 else P.omega (-(a : ℤ))

/-- Exact expansion y^2/(y^2-1)=1/(1-t^2) at infinity. -/
def paritySeries (R : Type*) [CommRing R] : PowerSeries R := PowerSeries.mk (evenIndicator R)

/-- Positive displayed rational function in Lemma 3.16, PDF p.11, expanded
at infinity. Q(u;t)=product u_i product (y-u_i inverse)/(y-u_i).
The gamma term y gamma_r(y)/(y^2-1) expands to tG for odd r and -G for even r. -/
def positiveRHS (P : RuiXuUnitParameters R r) : PowerSeries R :=
  let U := ∏ i, (P.u i : R)
  let D := (↑P.delta⁻¹ : R) * ↑P.rho
  let G := paritySeries R
  G - PowerSeries.C D +
    (PowerSeries.C (D * U) + if Odd r then PowerSeries.X * G else -G) *
      qSeries (fun i => (P.u i : R))

/-- Negative displayed rational function in Lemma 3.16, PDF p.11, expanded
at infinity. Q(u inverse;t)=product u_i inverse product (y-u_i)/(y-u_i inverse).
The term y/(gamma_r(y)(y^2-1)) expands to tG or -t^2G. -/
def negativeRHS (P : RuiXuUnitParameters R r) : PowerSeries R :=
  let U := ∏ i, (P.u i : R)
  let D := (↑P.delta⁻¹ : R) * ↑P.rho
  let G := paritySeries R
  PowerSeries.X ^ 2 * G + PowerSeries.C D -
    (PowerSeries.C (D * U) - if Odd r then PowerSeries.X * G else -(PowerSeries.X ^ 2 * G)) *
      qSeries (fun i => (↑(P.u i)⁻¹ : R))

/-- The negative series has no constant moment. -/
example (P : Ground R r) : PowerSeries.coeff 0 (negativeSeries P) = 0 := by
  simp [negativeSeries]

/-- Cyclotomic coefficients (-1)^(r-s) sigma_(r-s)(u), Definition 2.6, p.3. -/
def cyclotomicCoeff (P : RuiXuUnitParameters R r) (s : ℕ) : R :=
  (∏ i : Fin r, (Polynomial.X - Polynomial.C (P.u i : R))).coeff s

/-- BOTH admissibility identities (2.5), PDF p.3, with all integer shifts b. -/
def RuiXuAdmissible (P : Ground R r) : Prop :=
  (∀ b : ℤ, ∑ s : Fin (r+1), cyclotomicCoeff P.toRuiXuUnitParameters s.val *
    P.omega ((s.val : ℤ) + b) = 0) ∧
  (∀ a : ℕ, 0 < a → P.omega (a : ℤ) = P.omega (-(a : ℤ)) +
    ∑ i ∈ Finset.Icc 1 a, (↑P.rho⁻¹ : R) * ↑P.delta *
      (P.omega ((a : ℤ) - i) * P.omega (-(i : ℤ)) - P.omega ((a : ℤ) - 2*i)))

end Moments

section SpectralMoments

variable {R : Type*} [CommRing R] {r : ℕ}

/-- gamma_r(z) in Proposition 3.2(1), PDF p.5. -/
def gammaParity {K : Type*} [Ring K] (r : ℕ) (z : K) : K := if Odd r then 1 else -z

/-- The rational gamma_i weight in Proposition 3.2(1), PDF p.5, mapped into
an actual field. Products omit i and all exponents below are integer exponents. -/
def ruiXuSpectralWeight {K : Type*} [Field K] [Algebra R K] (P : RuiXuUnitParameters R r) (i : Fin r) : K :=
  let u : Fin r → K := fun j => algebraMap R K (P.u j : R)
  (gammaParity r (u i) + algebraMap R K ((↑P.delta⁻¹ : R) * ↑P.rho) *
      ((u i)^2 - 1) * ∏ j ∈ Finset.univ.erase i, u j) *
    ∏ j ∈ Finset.univ.erase i, (u i * u j - 1) / (u i - u j)

/-- The computed integer moment, not a freely chosen variable, PDF pp.5,10. -/
def spectralMoment {K : Type*} [Field K] [Algebra R K] (P : RuiXuUnitParameters R r) (a : ℤ) : K :=
  ∑ i : Fin r, (algebraMap R K (P.u i : R)) ^ a * ruiXuSpectralWeight (K := K) P i

end SpectralMoments

section GenericTwoStrand

variable {K : Type*} [Field K] [Algebra ℚ K] {r : ℕ}

/-- The displayed r+1 transcendental generators, section 3, PDF p.4. -/
def genericGenerators (P : RuiXuUnitParameters K r) : Fin r ⊕ Unit → K :=
  Sum.elim (fun i => (P.u i : K)) (fun _ => (P.q : K))

/-- K is precisely Q(u_1,...,u_r,q), not an arbitrary field extension, p.4. -/
def IsGenericField (P : RuiXuUnitParameters K r) : Prop :=
  AlgebraicIndependent ℚ (genericGenerators P) ∧
    IntermediateField.adjoin ℚ (Set.range (genericGenerators P)) = ⊤

/-- The SPECIFIED 3r^2 indexed monomials in Theorem 3.8, PDF p.9. -/
def twoStrandMonomial (P : Ground K r) (i : Fin 3 × Fin r × Fin r) : RuiXuBMW P 2 :=
  let a := i.2.1.val
  let b := i.2.2.val
  if i.1.val = 0 then ruiXuX P 2 1 false ^ a * ruiXuX P 2 2 false ^ b
  else if i.1.val = 1 then ruiXuX P 2 1 false ^ a * ruiXuX P 2 2 false ^ b * T P 2 1
  else ruiXuX P 2 1 false ^ a * ruiXuE P 2 1 * ruiXuX P 2 1 false ^ b

end GenericTwoStrand

section TrivialContractionSimples

variable {K : Type*} [Field K] [Algebra ℚ K] {r : ℕ}

/-- Nonzero unital simple left representation. Invariant subspaces are
quantified explicitly; no action or simplicity is inferred from dimensions. -/
def SimpleAction {A V : Type*} [Ring A] [Algebra K A]
    [AddCommGroup V] [Module K V] (act : A →ₐ[K] Module.End K V) : Prop :=
  Nontrivial V ∧ ∀ W : Submodule K V,
    (∀ a v, v ∈ W → act a v ∈ W) → W = ⊥ ∨ W = ⊤

/-- Actual intertwining linear isomorphism of the whole left action. -/
def EquivalentActions {A V W : Type*} [Ring A] [Algebra K A]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (a : A →ₐ[K] Module.End K V) (b : A →ₐ[K] Module.End K W) : Prop :=
  ∃ e : V ≃ₗ[K] W, ∀ x v, e (a x v) = b x (e v)

/-- The 2r one-dimensional labels, Proposition 3.1(a), PDF p.4. -/
abbrev OneLabel (r : ℕ) := Fin r × Bool

/-- Unordered distinct parameter pairs, with a canonical increasing order,
Proposition 3.1(b), PDF p.4. The cardinality is binomial(r,2). -/
abbrev TwoLabel (r : ℕ) := {ij : Fin r × Fin r // ij.1 < ij.2}

/-- The two allowed eigenvalues q and -q inverse, PDF p.4. -/
def heckeEigenvalue (P : RuiXuUnitParameters K r) (b : Bool) : K :=
  if b then -(↑P.q⁻¹ : K) else (P.q : K)

/-- Exactly the 2x2 T matrix in Proposition 3.1(b), PDF p.4, including
the common factor u_j/(u_j-u_i). Columns give images of basis vectors. -/
def twoTMatrix (P : RuiXuUnitParameters K r) (l : TwoLabel r) : Matrix (Fin 2) (Fin 2) K :=
  let u := (P.u l.val.1 : K)
  let v := (P.u l.val.2 : K)
  (v / (v-u)) • ![![(P.delta : K), (P.q : K) - u * (↑P.q⁻¹ : K) * v⁻¹],
    ![(↑P.q⁻¹ : K) - (P.q : K) * u * v⁻¹, -(P.delta : K) * u * v⁻¹]]

/-- X_1 or X_2 diagonal matrix of Proposition 3.1(b), PDF p.4. -/
def twoXMatrix (P : RuiXuUnitParameters K r) (l : TwoLabel r) (second : Bool) :
    Matrix (Fin 2) (Fin 2) K :=
  let u := (P.u l.val.1 : K)
  let v := (P.u l.val.2 : K)
  if second then ![![v, 0], ![0, u]] else ![![u, 0], ![0, v]]

/-- Lemma-free sanity check of the two one-dimensional eigenvalue choices. -/
example (P : RuiXuUnitParameters K r) : heckeEigenvalue P false = (P.q : K) := by
  simp [heckeEigenvalue]

end TrivialContractionSimples

section RuiXuHecke

variable {R : Type*} [CommRing R] {r : ℕ}

/-- Exact Hecke generator alphabet from PDF p.3, with one-based helpers. -/
inductive HeckeLetter (n : ℕ)
  | g : Fin (n-1) → HeckeLetter n
  | y : Fin n → HeckeLetter n

/-- Free normalized Hecke generator g_i. -/
def ruiXuFreeG (R : Type*) [CommRing R] (n i : ℕ) : FreeAlgebra R (HeckeLetter n) :=
  if h : 1 ≤ i ∧ i < n then FreeAlgebra.ι R (.g ⟨i-1, by omega⟩) else 0

/-- Free Hecke generator y_j; no inverse letters or extra contractions. -/
def ruiXuFreeY (R : Type*) [CommRing R] (n j : ℕ) : FreeAlgebra R (HeckeLetter n) :=
  if h : 1 ≤ j ∧ j ≤ n then FreeAlgebra.ι R (.y ⟨j-1, by omega⟩) else 0

variable (P : Ground R r) (n : ℕ)

local notation "g" => ruiXuFreeG R n
local notation "y" => ruiXuFreeY R n
local notation "c" => algebraMap R (FreeAlgebra R (HeckeLetter n))

/-- All seven normalized Hecke relation groups (a)--(g), PDF p.3. -/
inductive RuiXuHeckeRelations (P : Ground R r) (n : ℕ) : FreeAlgebra R (HeckeLetter n) → FreeAlgebra R (HeckeLetter n) → Prop
  | quadratic (i : ℕ) (hi : 1 ≤ i ∧ i < n) :
      RuiXuHeckeRelations P n (((ruiXuFreeG R n) i - (algebraMap R (FreeAlgebra R (HeckeLetter n))) (P.q : R)) * ((ruiXuFreeG R n) i + (algebraMap R (FreeAlgebra R (HeckeLetter n))) (↑P.q⁻¹ : R))) 0
  | far (i j : ℕ) (hi : 1 ≤ i ∧ i < n) (hj : 1 ≤ j ∧ j < n)
      (hd : i+1 < j ∨ j+1 < i) : RuiXuHeckeRelations P n ((ruiXuFreeG R n) i * (ruiXuFreeG R n) j) ((ruiXuFreeG R n) j * (ruiXuFreeG R n) i)
  | braid (i : ℕ) (hi : 1 ≤ i ∧ i+1 < n) :
      RuiXuHeckeRelations P n ((ruiXuFreeG R n) i * (ruiXuFreeG R n) (i+1) * (ruiXuFreeG R n) i) ((ruiXuFreeG R n) (i+1) * (ruiXuFreeG R n) i * (ruiXuFreeG R n) (i+1))
  | gyFar (i j : ℕ) (hi : 1 ≤ i ∧ i < n) (hj : 1 ≤ j ∧ j ≤ n)
      (hd : j ≠ i ∧ j ≠ i+1) : RuiXuHeckeRelations P n ((ruiXuFreeG R n) i * (ruiXuFreeY R n) j) ((ruiXuFreeY R n) j * (ruiXuFreeG R n) i)
  | yy (i j : ℕ) (hi : 1 ≤ i ∧ i ≤ n) (hj : 1 ≤ j ∧ j ≤ n) :
      RuiXuHeckeRelations P n ((ruiXuFreeY R n) i * (ruiXuFreeY R n) j) ((ruiXuFreeY R n) j * (ruiXuFreeY R n) i)
  | affine (i : ℕ) (hi : 1 ≤ i ∧ i < n) : RuiXuHeckeRelations P n ((ruiXuFreeY R n) (i+1)) ((ruiXuFreeG R n) i * (ruiXuFreeY R n) i * (ruiXuFreeG R n) i)
  | cyclotomic (hn : 1 ≤ n) :
      RuiXuHeckeRelations P n ((List.ofFn fun i : Fin r => (ruiXuFreeY R n) 1 - (algebraMap R (FreeAlgebra R (HeckeLetter n))) (P.u i : R)).prod) 0

/-- The exact normalized Ariki--Koike algebra, PDF p.3. -/
abbrev RuiXuHecke := RingQuot (RuiXuHeckeRelations P n)

/-- Canonical Hecke quotient map. -/
def heckeMap : FreeAlgebra R (HeckeLetter n) →ₐ[R] RuiXuHecke P n :=
  RingQuot.mkAlgHom R (RuiXuHeckeRelations P n)

/-- g_i in the normalized Hecke presentation. -/
def HG (i : ℕ) : RuiXuHecke P n := heckeMap P n (g i)

/-- y_j in the normalized Hecke presentation. -/
def HY (j : ℕ) : RuiXuHecke P n := heckeMap P n (y j)

/-- Actual two-sided ideal B E_1 B, as the R-span of all products a E_1 b,
PDF p.34. It is zero at levels 0 and 1. -/
def ruiXuContractionIdeal : Submodule R (RuiXuBMW P n) :=
  if 2 ≤ n then
    QAlgorithms.Papers.Independent.Support21.P12.contractionIdeal (S := R) (ruiXuE P n 1)
  else ⊥

/-- Quotient by the actual contraction ideal, Proposition 5.2, PDF p.34. -/
abbrev RuiXuHeckeQuotient := RingQuot (fun a b : RuiXuBMW P n => a - b ∈ ruiXuContractionIdeal P n)

/-- Actual quotient projection used in Proposition 5.2, PDF p.34. -/
def toHeckeQuotient : RuiXuBMW P n →ₐ[R] RuiXuHeckeQuotient P n :=
  RingQuot.mkAlgHom R (fun a b : RuiXuBMW P n => a - b ∈ ruiXuContractionIdeal P n)

/-- The scalar and one-strand contraction ideals are zero (no E_0). -/
example : ruiXuContractionIdeal P 1 = ⊥ := by simp [ruiXuContractionIdeal]

end RuiXuHecke

section IdealFiltration

variable {R : Type*} [CommRing R] {r : ℕ} (P : Ground R r) (n : ℕ)

/-- Canonical lower-level image, PDF p.34. Adjoining generators describes
the image without assuming injectivity of the strand homomorphism. At m=0
this is the scalar subalgebra. -/
def lowerImage (m : ℕ) : Subalgebra R (RuiXuBMW P n) :=
  Algebra.adjoin R {z | (∃ i, 1 ≤ i ∧ i < m ∧ (z = T P n i ∨ z = ruiXuE P n i)) ∨
    ∃ j, 1 ≤ j ∧ j ≤ m ∧ (z = ruiXuX P n j false ∨ z = ruiXuX P n j true)}

/-- Image of the lower contraction ideal, zero at m=0,1; PDF pp.34--35. -/
def lowerContraction (m : ℕ) : Submodule R (RuiXuBMW P n) :=
  if 2 ≤ m then Submodule.span R {z | ∃ a ∈ lowerImage P n m, ∃ b ∈ lowerImage P n m,
    z = a * ruiXuE P n 1 * b} else ⊥

/-- E^f = E_(n-1) E_(n-3) ... E_(n-2f+1), in the printed order, p.35. -/
def contractionChain (f : ℕ) : RuiXuBMW P n :=
  (List.ofFn fun j : Fin f => ruiXuE P n (n - (2*j.val+1))).prod

/-- The actual two-sided contraction layer, with the terminal layer set to
zero as in Definition 5.3, PDF p.35. -/
def idealLayer (f : ℕ) : Submodule R (RuiXuBMW P n) :=
  if 2*f ≤ n then Submodule.span R {z | ∃ a b : RuiXuBMW P n, z = a * contractionChain P n f * b}
  else ⊥

/-- Exactly the active coordinates of kappa in N_r^(f,n), PDF p.35.
They correspond to the distinct positions n-1,n-3,...,n-2f+1. -/
def exponentWord (f : ℕ) (kappa : Fin f → ℤ) : RuiXuBMW P n :=
  (List.ofFn fun j : Fin f => XPow P n (n - (2*j.val+1)) (kappa j)).prod

/-- E^0 is the identity, including the maximal-f boundary convention. -/
example : contractionChain P n 0 = 1 := by simp [contractionChain]

end IdealFiltration

section ExplicitSpans

variable {R : Type*} [CommRing R] {r : ℕ} (P : Ground R r) (n : ℕ)

/-- T_(a,b) in the exact ordered word for s_(a,b), PDF p.35.
The downward branch is T_(a-1)...T_b and the upward branch is T_a...T_(b-1). -/
def intervalWord (a b : ℕ) : RuiXuBMW P n :=
  if b ≤ a then (List.ofFn fun j : Fin (a-b) => T P n (a-1-j.val)).prod
  else (List.ofFn fun j : Fin (b-a) => T P n (a+j.val)).prod

/-- The prescribed D_(1,m) representative s_(m-1,i) s_(m,j),
with 1<=i<j<=m, evaluated in the ambient algebra. Formula (5.6), PDF p.35. -/
def pairWord (m i j : ℕ) : RuiXuBMW P n := intervalWord P n (m-1) i * intervalWord P n m j

/-- The named D_(1,m) indices; the identity pair is (m-1,m), p.35. -/
def ValidPair (m i j : ℕ) : Prop := 1 ≤ i ∧ i < j ∧ j ≤ m

/-- N_1 is the actual span in Lemma 5.11, PDF p.36. Its D_1 indexing is
expanded using the ordered representative formula (5.6); no abstract right
module is substituted for this submodule of the actual presented algebra. -/
def nOne (p : ℕ) : Submodule R (RuiXuBMW P n) :=
  Submodule.span R {z | ∃ b ∈ lowerImage P n (n-2), ∃ a : ℤ, |a| ≤ (p : ℤ) ∧
    ∃ i j, ValidPair n i j ∧
      z = b * ruiXuE P n (n-1) * XPow P n (n-1) a * pairWord P n n i j}

/-- Lower-image product submodule B'_(n-2) h, PDF p.38. -/
def lowerProduct (h : RuiXuBMW P n) : Submodule R (RuiXuBMW P n) :=
  Submodule.span R {z | ∃ b ∈ lowerImage P n (n-2), z = b * h}

/-- BOTH generating families of N_3, Lemma 5.14, PDF p.38. The second
family has the exact nonidentity d_1 s_(n-1,n-3) s_(n,n-2) word. -/
def nThree (p : ℕ) : Submodule R (RuiXuBMW P n) :=
  Submodule.span R {z | ∃ b ∈ lowerImage P n (n-4), ∃ l : ℤ, |l| ≤ (p : ℤ) ∧
    (z = b * ruiXuE P n (n-1) * XPow P n (n-1) l * ruiXuE P n (n-3) ∨
      ∃ i j, ValidPair (n-2) i j ∧ (i ≠ n-3 ∨ j ≠ n-2) ∧
        z = b * ruiXuE P n (n-3) * XPow P n (n-3) l * ruiXuE P n (n-1) *
          (pairWord P n (n-2) i j * intervalWord P n (n-1) (n-3) *
            intervalWord P n n (n-2)))}

/-- The three d_2 words in Lemmas 5.15 and 5.17, PDF pp.38--39. -/
def LastWords (h : RuiXuBMW P n) : Prop :=
  h = 1 ∨ h = T P n (n-2) ∨ h = T P n (n-2) * T P n (n-1)

/-- N_(4,k), with |l_1|<=p and |k_1|<=bound. Lemma 5.15, PDF p.38. -/
def nFourBound (p : ℕ) (bound : ℤ) : Submodule R (RuiXuBMW P n) :=
  Submodule.span R {z | ∃ b ∈ lowerImage P n (n-4), ∃ l k : ℤ,
    |l| ≤ (p : ℤ) ∧ |k| ≤ bound ∧ ∃ i j, ValidPair (n-2) i j ∧
      ∃ h, LastWords P n h ∧ z = b * ruiXuE P n (n-3) * XPow P n (n-3) l *
        ruiXuE P n (n-1) * XPow P n (n-1) k * pairWord P n (n-2) i j * h}

/-- The actual N_4 of Lemma 5.17, with BOTH exponents bounded, PDF p.39. -/
def nFour (p : ℕ) : Submodule R (RuiXuBMW P n) := nFourBound P n p (p : ℤ)

/-- M_l of Lemma 5.18, PDF p.39. The first integer exponent k is UNBOUNDED. -/
def mSpan (l : ℤ) : Submodule R (RuiXuBMW P n) :=
  Submodule.span R {z | ∃ b ∈ lowerImage P n (n-4), ∃ k i : ℤ, |i| ≤ |l| ∧
    z = b * ruiXuE P n (n-1) * XPow P n (n-1) k * ruiXuE P n (n-3) * XPow P n (n-3) i}

/-- Full induction hypothesis shared by 5.18 and 5.22, PDF pp.39--40.
At l=0 the strict absolute-value condition admits no l_prime. -/
def LowerInduction (p : ℕ) (l : ℤ) : Prop :=
  ∀ lprime m : ℤ, |lprime| < |l| → |m| ≤ (p : ℤ) →
    ruiXuE P n (n-1) * XPow P n (n-1) lprime * ruiXuE P n (n-3) * XPow P n (n-3) m *
      T P n (n-2) * T P n (n-3) ∈ nFour P n p

/-- Actual N_2 of Proposition 5.27, PDF p.41. D_(2,n) is expanded by
(5.6) in the order s_(n-3,i_2) s_(n-2,j_2) s_(n-1,i_1) s_(n,j_1),
with i_2<i_1 and both pairs in their specified ranges. -/
def nTwo (p : ℕ) : Submodule R (RuiXuBMW P n) :=
  Submodule.span R {z | ∃ b ∈ lowerImage P n (n-4), ∃ k l : ℤ,
    |k| ≤ (p : ℤ) ∧ |l| ≤ (p : ℤ) ∧ ∃ i2 j2 i1 j1,
      ValidPair (n-2) i2 j2 ∧ ValidPair n i1 j1 ∧ i2 < i1 ∧
      z = b * ruiXuE P n (n-3) * XPow P n (n-3) k * ruiXuE P n (n-1) * XPow P n (n-1) l *
        (pairWord P n (n-2) i2 j2 * pairWord P n n i1 j1)}

/-- An empty interval is the identity, pinning the orientation at a=b. -/
example (a : ℕ) : intervalWord P n a a = 1 := by simp [intervalWord]

/-- The identity D_1 representative is the last valid pair. -/
example (m : ℕ) : pairWord P n m (m-1) m = 1 := by
  simp [pairWord, intervalWord]

end ExplicitSpans

section CentralSeries

variable {R : Type*} [CommRing R] {r : ℕ} (P : Ground R r)

/-- Evaluation of a Laurent word in the first m variables in an ambient
BMW algebra. Both signs are letters, as in Definition 2.1, PDF p.2.
Only m<=n is used as an inclusion; no injectivity is assumed. -/
def laurentEval (n m : ℕ) : FreeAlgebra R (Fin m × Bool) →ₐ[R] RuiXuBMW P n :=
  FreeAlgebra.lift R (fun j => ruiXuX P n (j.1.val+1) j.2)

/-- The actual Laurent coefficient subalgebra R[X_1^{+-1},...,X_m^{+-1}]
in the ambient algebra, Lemma 4.21, PDF p.17. -/
def laurentImage (n m : ℕ) : Subalgebra R (RuiXuBMW P n) := (laurentEval P n m).range

/-- Centrality is checked in the actual lower algebra, not just in a
possibly collapsed upper image; Lemma 4.21, PDF p.17. -/
def CentralLaurentWord (m : ℕ) (f : FreeAlgebra R (Fin m × Bool)) : Prop :=
  ∀ b : RuiXuBMW P m, laurentEval P m m f * b = b * laurentEval P m m f

/-- Exact geometric expansion (1-v t) inverse in a possibly noncommutative
coefficient ring. This is a complete formal series, not a truncation. -/
def ncGeometric {A : Type*} [Ring A] (v : A) : PowerSeries A :=
  PowerSeries.mk fun a => v ^ a

/-- The factor 1-v t in the formal variable t=y inverse. -/
def linearFactor {A : Type*} [Ring A] (v : A) : PowerSeries A :=
  1 - PowerSeries.C v * PowerSeries.X

/-- The numerator of (4.22) after normalizing every y-c to 1-c t,
PDF p.17. Every X_k superscript -1 is inversion, never k-1. -/
def transitionNumerator (n k : ℕ) : PowerSeries (RuiXuBMW P n) :=
  let q := algebraMap R (RuiXuBMW P n) ((P.q : R)^2)
  let qi := algebraMap R (RuiXuBMW P n) ((↑P.q⁻¹ : R)^2)
  linearFactor (ruiXuX P n k false)^2 * linearFactor (qi * ruiXuX P n k true) *
    linearFactor (q * ruiXuX P n k true)

/-- The denominator of (4.22), with unit constant coefficient 1, p.17. -/
def transitionDenominator (n k : ℕ) : PowerSeries (RuiXuBMW P n) :=
  let q := algebraMap R (RuiXuBMW P n) ((P.q : R)^2)
  let qi := algebraMap R (RuiXuBMW P n) ((↑P.q⁻¹ : R)^2)
  linearFactor (ruiXuX P n k true)^2 * linearFactor (qi * ruiXuX P n k false) *
    linearFactor (q * ruiXuX P n k false)

/-- The entire ratio of (4.22), expanded constructively using geometric
series. No division in a noncommutative fraction field is used, PDF p.17. -/
def transitionSeries (n k : ℕ) : PowerSeries (RuiXuBMW P n) :=
  let q := algebraMap R (RuiXuBMW P n) ((P.q : R)^2)
  let qi := algebraMap R (RuiXuBMW P n) ((↑P.q⁻¹ : R)^2)
  linearFactor (ruiXuX P n k false)^2 * ncGeometric (ruiXuX P n k true)^2 *
    linearFactor (qi * ruiXuX P n k true) * ncGeometric (qi * ruiXuX P n k false) *
    linearFactor (q * ruiXuX P n k true) * ncGeometric (q * ruiXuX P n k false)

/-- G(t)=1/(1-t^2)=y^2/(y^2-1), in the actual algebra coefficient ring. -/
def centralParitySeries (n : ℕ) : PowerSeries (RuiXuBMW P n) :=
  PowerSeries.mk fun a => if Even a then 1 else 0

/-- The base shifted series Wtilde_1+delta inverse rho-G, with coefficients
mapped from the prescribed moments; (4.28), PDF p.21. -/
def shiftedMomentBase (n : ℕ) : PowerSeries (RuiXuBMW P n) :=
  (PowerSeries.mk fun a => algebraMap R (RuiXuBMW P n) (P.omega (a : ℤ))) +
    PowerSeries.C (algebraMap R (RuiXuBMW P n) ((↑P.delta⁻¹ : R) * ↑P.rho)) -
    centralParitySeries P n

/-- Ordered constructive product in (4.28). j counts factors, so j=0
is the prescribed scalar base and j=k-1 gives level k; PDF p.21. -/
def shiftedMomentProduct (n j : ℕ) : PowerSeries (RuiXuBMW P n) :=
  shiftedMomentBase P n *
    (List.ofFn fun i : Fin j => transitionSeries P n (i.val+1)).prod

/-- Canonically constructed Wtilde_k, obtained from the base and the
complete product (4.28); not an arbitrary sequence satisfying the theorem. -/
def centralMomentSeries (n k : ℕ) : PowerSeries (RuiXuBMW P n) :=
  shiftedMomentProduct P n (k-1) + centralParitySeries P n -
    PowerSeries.C (algebraMap R (RuiXuBMW P n) ((↑P.delta⁻¹ : R) * ↑P.rho))

/-- The constructed coefficient omega_k^(a) in the ambient algebra, p.17. -/
def ruiXuCentralMoment (n k a : ℕ) : RuiXuBMW P n :=
  PowerSeries.coeff a (centralMomentSeries P n k)

/-- Laurent-word evaluation preserves the scalar unit, including m=0. -/
example (n m : ℕ) : laurentEval P n m 1 = 1 := map_one _

/-- The initial product has no factors; the level convention is pinned. -/
example (n : ℕ) : shiftedMomentProduct P n 0 = shiftedMomentBase P n := by
  simp [shiftedMomentProduct]

/-- Denominators have constant 1, so no nonunit series inversion is hidden. -/
example (n k : ℕ) : PowerSeries.coeff 0 (transitionDenominator P n k) = 1 := by
  simp [transitionDenominator, linearFactor]

/-- The two generator choices T_i and T_i inverse used in Corollary 4.27. -/
def signedT (n i : ℕ) (inverse : Bool) : RuiXuBMW P n :=
  if inverse then TInv P n i else T P n i

end CentralSeries

section PermutationTransversal

/-- One-based adjacent transposition s_i in S_n. The identity helper value
outside 1<=i<n is never used as a source generator. PDF p.15. -/
def ruiXuAdjacentPerm (n i : ℕ) : Equiv.Perm (Fin n) :=
  if h : 1 ≤ i ∧ i < n then Equiv.swap ⟨i-1, by omega⟩ ⟨i, h.2⟩ else 1

/-- Source ordered s_(a,b), PDF p.35. Permutations act on tableau labels
on the RIGHT, so the list is reversed before Mathlib's function-composition
product. This convention is also used in representativePerm below. -/
def intervalPerm (n a b : ℕ) : Equiv.Perm (Fin n) :=
  if b ≤ a then ((List.ofFn fun j : Fin (a-b) => ruiXuAdjacentPerm n (a-1-j.val)).reverse).prod
  else ((List.ofFn fun j : Fin (b-a) => ruiXuAdjacentPerm n (a+j.val)).reverse).prod

/-- Source s_(m-1,i) s_(m,j), interpreted as a right action, PDF p.35. -/
def pairPerm (n m i j : ℕ) : Equiv.Perm (Fin n) :=
  intervalPerm n m j * intervalPerm n (m-1) i

/-- One-based label at a zero-based cell position after the right action;
the out-of-range helper is unused in a valid row condition. -/
def permEntry (n : ℕ) (w : Equiv.Perm (Fin n)) (a : ℕ) : ℕ :=
  if h : a < n then (w ⟨a, h⟩).val+1 else 0

/-- The actual row-standard transversal in PDF p.35: an increasing first
row of n-2f entries, then f increasing pairs whose first column increases.
This definition uses tableau conditions, independently of (5.6). -/
def sourceTransversal (n f : ℕ) : Set (Equiv.Perm (Fin n)) :=
  {w | (∀ i j, i < j → j < n-2*f → permEntry n w i < permEntry n w j) ∧
    (∀ k, k < f → permEntry n w (n-2*f+2*k) < permEntry n w (n-2*f+2*k+1)) ∧
    (∀ k l, k < l → l < f →
      permEntry n w (n-2*f+2*k) < permEntry n w (n-2*f+2*l))}

/-- Exactly the inequalities of (5.6), with Fin f coordinate j meaning
source k=j+1: 1<=i_f<...<i_1 and 1<=i_k<j_k<=n-2k+2. -/
def RepresentativeIndices (n f : ℕ) (i j : Fin f → ℕ) : Prop :=
  (∀ k, 1 ≤ i k ∧ i k < j k ∧ j k ≤ n-2*k.val) ∧
    (∀ k l, k < l → i l < i k)

/-- The exact ordered representative s_(n-2f+1,i_f) s_(n-2f+2,j_f)
... s_(n-1,i_1) s_(n,j_1), as a permutation, PDF p.35.
The Mathlib product is in reverse source order because the action is right. -/
def representativePerm (n f : ℕ) (i j : Fin f → ℕ) : Equiv.Perm (Fin n) :=
  (List.ofFn fun k : Fin f => pairPerm n (n-2*k.val) (i k) (j k)).prod

/-- The right side of (5.6) is a SET of actual permutations, not words. -/
def representativeSet (n f : ℕ) : Set (Equiv.Perm (Fin n)) :=
  {w | ∃ i j : Fin f → ℕ, RepresentativeIndices n f i j ∧ w = representativePerm n f i j}

/-- An empty representative product is the identity, including f=0. -/
example (n : ℕ) (i j : Fin 0 → ℕ) : representativePerm n 0 i j = 1 := by
  simp [representativePerm]

/-- The interval s_(a,a) is the identity, fixing its endpoint convention. -/
example (n a : ℕ) : intervalPerm n a a = 1 := by simp [intervalPerm]

end PermutationTransversal

end QAlgorithms.Papers.Independent.Intakenext100.P51


