-- Prove2me | Definitions.Def_WeilConjectures_Etale_WeilData
-- name    : WeilConjectures_Etale_WeilData
-- status  : Definition
-- author  : @Idealson
-- created : 2026-11-25T12:21:29.011473+00:00
-- url     : https://prove2.me/theorems/cd41486e-2221-5079-b049-28e4bb8183ac
-- title:
--   Frobenius on $H^i(X_{\bar k},\mathbb Q_\ell)$ and the Weil-cohomology package (finiteness, trace formula, Poincaré duality)
-- statement:
--   Let $k=\mathbb F_q$, $f\colon X\to\operatorname{Spec}k$, $\ell$ a prime, and $X_{\bar k}$, $F$ as in `WeilConjectures_Etale_BaseChange`.
--
--   * $F^*$ (`Frob p f ℓ i`) is the $\mathbb Q_\ell$-linear endomorphism of $H^i(X_{\bar k},\mathbb Q_\ell)$ induced by pullback along the relative Frobenius $F$.
--   * `WeilCohomologyHolds p f ℓ n` is the conjunction of: (i) every $H^i(X_{\bar k},\mathbb Q_\ell)$ is finite-dimensional; (ii) the Lefschetz trace formula $N_m=\sum_{i=0}^{2n}(-1)^i\operatorname{Tr}\big((F^*)^m\mid H^i(X_{\bar k},\mathbb Q_\ell)\big)$ for every $m\ge1$, where $N_m$ is the number of $\mathbb F_{q^m}$-points of $X$; (iii) for $0\le i\le 2n$ there is a perfect pairing $H^i\times H^{2n-i}\to\mathbb Q_\ell$ with $\langle F^*x,F^*y\rangle=q^n\langle x,y\rangle$.
--
--   These are exactly the cohomological inputs of Grothendieck's proof of rationality and the functional equation.
-- source:
--   P. Deligne, La conjecture de Weil. I, Publ. Math. IHÉS 43 (1974), §1, (1.5) and (1.5.1) (Lefschetz trace formula), and §2, Théorème (2.3) with (2.5) (Poincaré duality); R. Hartshorne, Algebraic Geometry, Appendix C, §3–§4.

import Mathlib
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.CharP.Frobenius
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Group.Abelian
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
import Mathlib.CategoryTheory.Abelian.ShortExact
import Mathlib.CategoryTheory.Adjunction.CompositionIso
import Mathlib.CategoryTheory.Adjunction.Unique
import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.CategoryTheory.Limits.ExactFunctor
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.CategoryTheory.Sites.Pullback
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Trace
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.SetTheory.Cardinal.Finite
import Definitions.Def_FiniteFields_Dwork_Foundations
import Definitions.Def_FiniteFields_Etale_Cohomology
import Definitions.Def_FiniteFields_Etale_ConstantPullback
import Definitions.Def_FiniteFields_Etale_ExactPullback
import Definitions.Def_FiniteFields_Etale_FiniteCoefficients
import Definitions.Def_FiniteFields_Etale_Functoriality
import Definitions.Def_FiniteFields_Etale_Sites
import Definitions.Def_FiniteFields_Schemes_GeneralFrobenius
import Definitions.Def_WeilConjectures_Etale_BaseChange
import Definitions.Def_WeilConjectures_Etale_Coefficients
import Definitions.Def_WeilConjectures_Etale_Pullback
import Definitions.Def_WeilConjectures_projectiveSpace
import Definitions.Def_WeilConjectures_zetaFunction

noncomputable section

open CategoryTheory AlgebraicGeometry Polynomial

namespace WeilConjectures.Etale

variable {k : Type} [Field k] [Finite k] (p : ℕ) [Fact p.Prime] [CharP k p]
  {X : Scheme.{0}} (f : X ⟶ Spec (.of k)) (ℓ : ℕ) [Fact ℓ.Prime]

/-- **D6.** Le Frobenius `F^*` sur `Hⁱ(X_k̄, ℚ_ℓ)`. -/
def Frob (i : ℕ) : Hrat ℓ (geom f) i →ₗ[ℚ_[ℓ]] Hrat ℓ (geom f) i :=
  pullbackRat ℓ (geomFrob p f) i

/-- **D7 (N4f).** Les propriétés de la cohomologie ℓ-adique dont N4e a besoin : finitude, formule
des traces de Lefschetz, et dualité de Poincaré sous forme d'accouplements parfaits. -/
def WeilCohomologyHolds (n : ℕ) : Prop :=
  (∀ i, FiniteDimensional ℚ_[ℓ] (Hrat ℓ (geom f) i)) ∧
  (∀ m, 1 ≤ m → (pointCount p f m : ℚ_[ℓ]) =
    ∑ i ∈ Finset.range (2 * n + 1),
      (-1) ^ i * LinearMap.trace ℚ_[ℓ] (Hrat ℓ (geom f) i) (Frob p f ℓ i ^ m)) ∧
  ∃ pair : ∀ i, Hrat ℓ (geom f) i →ₗ[ℚ_[ℓ]] Hrat ℓ (geom f) (2 * n - i) →ₗ[ℚ_[ℓ]] ℚ_[ℓ],
    (∀ i ≤ 2 * n, (pair i).IsPerfPair) ∧
    ∀ i ≤ 2 * n, ∀ x y, pair i (Frob p f ℓ i x) (Frob p f ℓ (2 * n - i) y) =
      (Nat.card k : ℚ_[ℓ]) ^ n * pair i x y





end WeilConjectures.Etale


