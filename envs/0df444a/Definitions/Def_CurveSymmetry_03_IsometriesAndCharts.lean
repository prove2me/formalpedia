-- Prove2me | Definitions.Def_CurveSymmetry_03_IsometriesAndCharts
-- name    : CurveSymmetry_03_IsometriesAndCharts
-- status  : Definition
-- author  : @carlok
-- created : 2026-10-07T12:11:40.015917+00:00
-- url     : https://prove2.me/theorems/2c104eff-d00c-42f7-8af3-d9afd50b0817
-- title:
--   Direct isometries, $C_{m,\alpha}$ and its spherical closure, Möbius actions, charts of $\mathbb P^1\times\mathbb P^1$
-- statement:
--   Let $m\in\mathbb N$ and $\alpha\in\mathbb C$. Polynomials in $\mathbb C[X,Y]$ are read in the coordinates $X=z$, $Y=\bar z$, with real locus $Z(P)=\{z : P(z,\bar z)=0\}$, and $P_\alpha=X^m(\alpha+XY)+Y^m(\bar\alpha+XY)$. Write $\mathrm{Isom}(\mathbb C)$ for the group of distance-preserving bijections of $\mathbb C$. Let $\widehat{\mathbb C}=\mathbb C\cup\{\infty\}$ be the Riemann sphere and $\mathbb P^1$ the complex projective line, identified by $z\mapsto[z:1]$ and $\infty\mapsto[1:0]$. A Möbius matrix is any $g\in\mathrm{GL}_2(\mathbb C)$, acting on $\mathbb P^1$ through homogeneous coordinates, and $\bar g$ is the matrix with conjugate entries.
--
--   The central objects are the direct isometry group of a set $S\subseteq\mathbb C$, the extremal curve of equation (1), and its spherical closure:
--   $$\mathrm{Sym}^+(S)=\{T\in\mathrm{Isom}(\mathbb C) : T(z)\in S\iff z\in S\ \text{for all}\ z,\ \text{and}\ T(z)=az+b\ \text{for some}\ a,b\in\mathbb C\ \text{with}\ |a|=1\},$$
--   $$C_{m,\alpha}=\{z\in\mathbb C : \operatorname{Re}\big(z^m(|z|^2+\alpha)\big)=0\},\qquad \widehat C_{m,\alpha}=\text{the closure of}\ C_{m,\alpha}\ \text{in}\ \widehat{\mathbb C}.$$
--   The file also defines:
--
--   1. The map sending a direct symmetry pair $(a,b)$ of $Z(P)$ to $z\mapsto az+b$ in $\mathrm{Sym}^+(Z(P))$, and the homomorphism $T\mapsto T(1)-T(0)$ from $\mathrm{Sym}^+(S)$ to the multiplicative monoid of $\mathbb C$.
--   2. The bihomogeneous form of bidegree $(m+1,m+1)$ in pairs $x=(x_0,x_1)$, $y=(y_0,y_1)$, $F_\alpha(x,y)=\alpha x_0^mx_1y_1^{m+1}+x_0^{m+1}y_0y_1^m+\bar\alpha x_1^{m+1}y_0^my_1+x_0x_1^my_0^{m+1}$, which equals $P_\alpha(X,Y)$ at $x=(X,1)$, $y=(Y,1)$; the set $V_\alpha\subseteq\mathbb P^1\times\mathbb P^1$ of points where $F_\alpha$ vanishes; the subset where $F_\alpha$ and its derivative on $\mathbb C^2\times\mathbb C^2$ both vanish at the representative; and the real diagonal $p\mapsto(p,\bar p)$ from $\widehat{\mathbb C}$ to $\mathbb P^1\times\mathbb P^1$.
--   3. Actions: $(p,q)\mapsto(gp,\bar gq)$ (Möbius) and $(p,q)\mapsto(gq,\bar gp)$ (anti-Möbius) on $\mathbb P^1\times\mathbb P^1$; the linear map $(u,v)\mapsto(gu,\bar gv)$ of $\mathbb C^2\times\mathbb C^2$; and, on $\widehat{\mathbb C}$, the dilation $z\mapsto cz$ fixing $\infty$ and the inversion that exchanges $0$ and $\infty$ and sends $z\ne0$ to $c/z$.
--   4. Equations: the pullback $F_\beta\big(g\,(X,1)^{\mathsf T},\ \bar g\,(Y,1)^{\mathsf T}\big)\in\mathbb C[X,Y]$ for $\beta\in\mathbb C$; the binary forms $a_1X^m+a_2Y^m$ and the four-term forms $a_1X^m+a_2Y^m+XY(a_3X^m+a_4Y^m)$, among them the polynomial obtained from $P_\beta(c/X,\bar c/Y)$ by clearing the denominator $X^{m+1}Y^{m+1}$, and the equation $u^m+v^m+uv(\bar\alpha u^m+\alpha v^m)$ of $P_\alpha=0$ in the reciprocal coordinates $u=1/X$, $v=1/Y$; and the mixed-chart polynomial $aX+Y+bX^{m+1}Y^m+X^mY^{m+1}$.
--   5. Charts and topology: the four charts $\mathbb C^2\to\mathbb P^1\times\mathbb P^1$ sending $(w_0,w_1)$ to $([w_0:1],[w_1:1])$, $([1:w_0],[w_1:1])$, $([w_1:1],[1:w_0])$ and $([1:w_0],[1:w_1])$; the Zariski topology on $\mathbb C^2$, induced from the prime spectrum of $\mathbb C[X,Y]$ by sending a point to the kernel of evaluation there; the affine real diagonal $\{(z,\bar z) : z\in Z(P)\}$; evaluation at a point, the Jacobian condition $P=\partial_XP=\partial_YP=0$, and the differential given by the formal partial derivatives; and, for a function $F$ on a normed space, the critical-zero condition $F(x)=0$ and $DF(x)=0$.
--
--   $\mathrm{Sym}^+(C)$ is the group whose order $N$ is bounded in Theorem 1. Theorem 2 concerns the Möbius and anti-Möbius maps preserving $\widehat C_{m,\alpha}$; as in the proof of Theorem 2 they act on $V_\alpha$ by $(X,Y)\mapsto(M(X),\overline M(Y))$ and $(X,Y)\mapsto(M(Y),\overline M(X))$, and the pulled-back equations give the coefficient ratios (8). The charts, the Zariski topology, the Jacobian and critical-zero conditions and the chart equations are where the closure $V_\alpha$ and the singular points $(0,0)$ and $(\infty,\infty)$ of Lemma 4 are computed.
--
--   **Formalization Note**: The sphere is `OnePoint ℂ`, $\mathbb P^1$ is Mathlib's projectivization of $\mathbb C^2$, isometries are `ℂ ≃ᵢ ℂ`, and Möbius matrices are arbitrary elements of `GL (Fin 2) ℂ`. Points of $\mathbb P^1$ are evaluated on Mathlib's chosen representative; the agreement of $V_\alpha$ with the Zariski closure of the affine curve, and of the homogeneous critical set with the chart Jacobians, are separate statements. The critical-zero condition uses a genuine Fréchet derivative (`HasFDerivAt`), and the Zariski topology on $\mathbb C^2$ is installed only locally. The file also proves that $at^m+b$ is separable when $m\ge1$ and $a,b\ne0$.
-- source:
--   C. Perassi, Sharp symmetry bounds for real algebraic curves (note), definitions of the formalization, https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/sharp_symmetry_bounds.pdf. Lean modules DirectIsometries, PaperBounds, FamilySingularities, FamilyCharts, FamilyTransport, SphereGeometry, FamilyProjective, MobiusPair, FamilyMobiusPullback, HomogeneousDifferential, PolynomialDifferential, HomogeneousCharts, AffineClosure, ProjectiveChartMaps, AffineZariskiTopology, PolynomialZariskiMaps in https://github.com/carlok/curve-symmetry-lean/tree/d99bc17a1c397956c05d7417de50f9beed56580f/lean (C. Perassi)

-- Definitions, part 03 of 12, generated from curve-symmetry-lean by skeleton
-- subtraction: the source modules below, in dependency order, each in its own
-- section; only definitions, instances and the theorems they need are kept.
import Definitions.Def_CurveSymmetry_01_RealLoci
import Definitions.Def_CurveSymmetry_02_FamilyBasics
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Analysis.Complex.Isometry
import Mathlib.Analysis.Complex.OperatorNorm
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Normed.Affine.MazurUlam
import Mathlib.Data.Complex.Basic
import Mathlib.FieldTheory.Separable
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.RingTheory.Polynomial.Eisenstein.Criterion
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.Tactic
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine

-- lean/DirectIsometries.lean
section

namespace CurveSymmetry

set_option autoImplicit false

/-- The orientation-preserving Euclidean isometries, in their complex affine form. -/
def directIsometryGroup (S : Set ℂ) : Subgroup (ℂ ≃ᵢ ℂ) where
  carrier := {f | (∀ z : ℂ, f z ∈ S ↔ z ∈ S) ∧
    ∃ a b : ℂ, ‖a‖ = 1 ∧ ∀ z : ℂ, f z = a * z + b}
  one_mem' := ⟨by simp, 1, 0, norm_one, by simp⟩
  mul_mem' := by
    rintro f g ⟨hf, a, b, ha, he⟩ ⟨hg, c, d, hc, hk⟩
    refine ⟨fun z => (hf (g z)).trans (hg z), a * c, a * d + b, ?_, ?_⟩
    · rw [norm_mul, ha, hc, one_mul]
    · intro z
      change f (g z) = _
      rw [he, hk]
      ring
  inv_mem' := by
    rintro f ⟨hf, a, b, ha, he⟩
    have ha0 : a ≠ 0 := by intro h; simp [h] at ha
    refine ⟨?_, a⁻¹, -a⁻¹ * b, ?_, ?_⟩
    · intro z
      simpa using (hf (f⁻¹ z)).symm
    · rw [norm_inv, ha, inv_one]
    · intro z
      have h := he (f⁻¹ z)
      have heq : a * (f⁻¹ z) + b = z := by simpa using h.symm
      calc
        f⁻¹ z = a⁻¹ * (a * (f⁻¹ z)) := by rw [← mul_assoc, inv_mul_cancel₀ ha0, one_mul]
        _ = a⁻¹ * z + -a⁻¹ * b := by linear_combination a⁻¹ * heq

noncomputable def directParametersToIsometry (P : BPoly) :
    DirectSymmetries P → directIsometryGroup (realLocus P) := fun u =>
  ⟨affineDirectIsometry u.val.1 u.val.2 u.prop.1,
    u.prop.2, u.val.1, u.val.2, u.prop.1, fun _ => rfl⟩

lemma direct_isometry_formula {S : Set ℂ} (f : directIsometryGroup S) (z : ℂ) :
    f.val z = (f.val 1 - f.val 0) * z + f.val 0 := by
  obtain ⟨a, b, _, he⟩ := f.prop.2
  rw [he z, he 1, he 0]
  ring

noncomputable def directSlope (S : Set ℂ) : directIsometryGroup S →* ℂ where
  toFun f := f.val 1 - f.val 0
  map_one' := by simp
  map_mul' := by
    intro f g
    change f.val (g.val 1) - f.val (g.val 0) = _
    rw [direct_isometry_formula f (g.val 1), direct_isometry_formula f (g.val 0)]
    ring

end CurveSymmetry

end

-- lean/PaperBounds.lean
section

namespace CurveSymmetry

set_option autoImplicit false

def extremalCurve (m : ℕ) (α : ℂ) : Set ℂ :=
  {z | (z ^ m * ((‖z‖ : ℂ) ^ 2 + α)).re = 0}

end CurveSymmetry

end

-- lean/FamilySingularities.lean
section

namespace CurveSymmetry

set_option autoImplicit false

open MvPolynomial

noncomputable def planeEval (x y : ℂ) : BPoly →+* ℂ :=
  eval (fun i : Fin 2 => if i = 0 then x else y)

/-- The affine hypersurface Jacobian condition, using Mathlib's formal partial derivatives. -/
def JacobianSingular (P : BPoly) (x y : ℂ) : Prop :=
  planeEval x y P = 0 ∧ planeEval x y (pderiv 0 P) = 0 ∧ planeEval x y (pderiv 1 P) = 0

noncomputable def binaryForm (m : ℕ) (a b : ℂ) : BPoly := C a * X 0 ^ m + C b * X 1 ^ m

noncomputable def fourTermForm (m : ℕ) (a b c d : ℂ) : BPoly :=
  binaryForm m a b + X 0 * X 1 * binaryForm m c d

/-- The equation in reciprocal coordinates `u=1/X`, `v=1/Y`. -/
noncomputable def familyInfinityPolynomial (m : ℕ) (α : ℂ) : BPoly :=
  fourTermForm m 1 1 (star α) α

end CurveSymmetry

end

-- lean/FamilyCharts.lean
section

namespace CurveSymmetry

set_option autoImplicit false

open MvPolynomial

noncomputable def familyMixedPolynomial (m : ℕ) (a b : ℂ) : BPoly :=
  C a * X 0 + X 1 + C b * X 0 ^ (m + 1) * X 1 ^ m + X 0 ^ m * X 1 ^ (m + 1)

/-- The one-variable tangent-direction polynomial has no repeated root.
This is the algebraic ingredient for ordinary multiple points, not yet an
interface to the singularity or normalization of a projective scheme. -/
theorem binary_tangent_separable {m : ℕ} (hm : 0 < m) {a b : ℂ} (ha : a ≠ 0) (hb : b ≠ 0) :
    Polynomial.Separable (Polynomial.C a * Polynomial.X ^ m + Polynomial.C b) := by
  have he : Polynomial.C a * Polynomial.X ^ m + Polynomial.C b =
      (Polynomial.X ^ m - Polynomial.C (-b / a)) * Polynomial.C a := by
    rw [sub_mul, ← Polynomial.C_mul]
    have heq : -b / a * a = -b := div_mul_cancel₀ _ ha
    rw [heq, Polynomial.C_neg]
    ring
  rw [he]
  apply Polynomial.Separable.mul_unit
  · apply Polynomial.separable_X_pow_sub_C
    · exact_mod_cast hm.ne'
    · exact div_ne_zero (neg_ne_zero.mpr hb) ha
  · exact (isUnit_iff_ne_zero.mpr ha).map Polynomial.C

end CurveSymmetry

end

-- lean/FamilyTransport.lean
section

namespace CurveSymmetry

set_option autoImplicit false

open MvPolynomial

noncomputable def inversionFamily (m : ℕ) (β c : ℂ) : BPoly :=
  fourTermForm m (star c ^ m * (c * star c)) (c ^ m * (c * star c))
    (star c ^ m * star β) (c ^ m * β)

end CurveSymmetry

end

-- lean/SphereGeometry.lean
section

namespace CurveSymmetry

set_option autoImplicit false

open scoped LinearAlgebra.Projectivization

open OnePoint

/-- The ordinary one-point compactification of the complex plane. -/
abbrev Sphere := OnePoint ℂ

/-- Arbitrary invertible matrices, not just the anticipated classified forms. -/
abbrev MobiusMatrix := Matrix.GeneralLinearGroup (Fin 2) ℂ

/-- Mathlib's standard finite-chart/infinity identification with the projective line.
This is a set equivalence; no unproved projective-topology compatibility is asserted. -/
noncomputable def sphereProjectiveEquiv : Sphere ≃ Projectivization ℂ (Fin 2 → ℂ) :=
  OnePoint.equivProjectivization ℂ

/-- Spherical closure has its ordinary topological meaning from the outset. -/
def sphericalFamily (m : ℕ) (α : ℂ) : Set Sphere :=
  closure (((↑) : ℂ → Sphere) '' extremalCurve m α)

end CurveSymmetry

end

-- lean/FamilyProjective.lean
section

namespace CurveSymmetry

set_option autoImplicit false

open OnePoint

abbrev ProjectiveLine := Projectivization ℂ (Fin 2 → ℂ)

/-- The bihomogeneous equation in two pairs of homogeneous coordinates.
On `x=[X:1]`, `y=[Y:1]` this is precisely `familyPolynomial m α`. -/
def familyBihomogeneous (m : ℕ) (α : ℂ) (x y : Fin 2 → ℂ) : ℂ :=
  α * x 0 ^ m * x 1 * y 1 ^ (m + 1) +
  x 0 ^ (m + 1) * y 0 * y 1 ^ m +
  star α * x 1 ^ (m + 1) * y 0 ^ m * y 1 +
  x 0 * x 1 ^ m * y 0 ^ (m + 1)

/-- The bihomogeneous zero locus on the standard product of projective lines.
The next lemma proves that its meaning does not depend on chosen representatives.
Its identification with the Zariski closure is a separate pending obligation. -/
def familyProjectiveCurve (m : ℕ) (α : ℂ) : Set (ProjectiveLine × ProjectiveLine) :=
  {p | familyBihomogeneous m α p.1.rep p.2.rep = 0}

/-- The real sphere sits in the complexification by `p ↦ (p, conjugate p)`. -/
noncomputable def sphereRealDiagonal (p : Sphere) : ProjectiveLine × ProjectiveLine :=
  (sphereProjectiveEquiv p, sphereProjectiveEquiv (OnePoint.map (star : ℂ → ℂ) p))

/-- The ordinary product-projective extension of an arbitrary Möbius matrix. -/
noncomputable def complexifiedMobius (g : MobiusMatrix)
    (p : ProjectiveLine × ProjectiveLine) : ProjectiveLine × ProjectiveLine :=
  (g • p.1, (g.map (starRingEnd ℂ)) • p.2)

/-- For an anti-Möbius map, the two projective factors are exchanged first. -/
noncomputable def complexifiedAntiMobius (g : MobiusMatrix)
    (p : ProjectiveLine × ProjectiveLine) : ProjectiveLine × ProjectiveLine :=
  complexifiedMobius g p.swap

end CurveSymmetry

end

-- lean/MobiusPair.lean
section

namespace CurveSymmetry

set_option autoImplicit false

open OnePoint

def sphereDilation (c : ℂ) : Sphere → Sphere := OnePoint.map (fun z : ℂ => c * z)

noncomputable def sphereInversion (c : ℂ) (p : Sphere) : Sphere :=
  p.elim ((0 : ℂ) : Sphere) (fun z : ℂ => if z = 0 then ∞ else ((c / z : ℂ) : Sphere))

end CurveSymmetry

end

-- lean/FamilyMobiusPullback.lean
section

namespace CurveSymmetry

set_option autoImplicit false

open MvPolynomial

noncomputable def mobiusX (g : MobiusMatrix) (i : Fin 2) : BPoly :=
  C (g i 0) * X 0 + C (g i 1)

noncomputable def mobiusY (g : MobiusMatrix) (i : Fin 2) : BPoly :=
  C (star (g i 0)) * X 1 + C (star (g i 1))

/-- The actual denominator-cleared pullback for an arbitrary invertible matrix.
No preservation of the singular pair or special matrix form is assumed. -/
noncomputable def familyMobiusPullback (m : ℕ) (β : ℂ) (g : MobiusMatrix) : BPoly :=
  C β * mobiusX g 0 ^ m * mobiusX g 1 * mobiusY g 1 ^ (m + 1) +
  mobiusX g 0 ^ (m + 1) * mobiusY g 0 * mobiusY g 1 ^ m +
  C (star β) * mobiusX g 1 ^ (m + 1) * mobiusY g 0 ^ m * mobiusY g 1 +
  mobiusX g 0 * mobiusX g 1 ^ m * mobiusY g 0 ^ (m + 1)

end CurveSymmetry

end

-- lean/HomogeneousDifferential.lean
section

namespace CurveSymmetry

set_option autoImplicit false

/-- Vanishing of a function and its differential over the base normed field. `HasFDerivAt` is used
instead of the totalized `fderiv`, so nondifferentiability cannot satisfy this
condition accidentally. Its chart-Jacobian interpretation is a separate lemma. -/
def CriticalZero {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    (F : E → 𝕜) (x : E) : Prop := F x = 0 ∧ HasFDerivAt F (0 : E →L[𝕜] 𝕜) x

abbrev HomogeneousPairs := (Fin 2 → ℂ) × (Fin 2 → ℂ)

/-- The actual invertible linear map on the two homogeneous coordinate blocks. -/
noncomputable def homogeneousMobius (g : MobiusMatrix) :
    HomogeneousPairs ≃L[ℂ] HomogeneousPairs :=
  ((DistribMulAction.toLinearEquiv ℂ (Fin 2 → ℂ) g).prodCongr
    (DistribMulAction.toLinearEquiv ℂ (Fin 2 → ℂ) (g.map (starRingEnd ℂ)))).toContinuousLinearEquiv

/-- The homogeneous Jacobian condition on the standard product of projective
lines. Representative independence is proved below; equivalence with the
previously computed chart Jacobians remains a separate obligation. -/
def familyProjectiveCritical (m : ℕ) (α : ℂ) : Set (ProjectiveLine × ProjectiveLine) :=
  {p | CriticalZero (fun q : HomogeneousPairs => familyBihomogeneous m α q.1 q.2)
    (p.1.rep, p.2.rep)}

end CurveSymmetry

end

-- lean/PolynomialDifferential.lean
section

namespace CurveSymmetry

set_option autoImplicit false

open MvPolynomial

/-- The differential specified by the formal partial derivatives, as a genuine
continuous linear map on the finite coordinate space. -/
noncomputable def polynomialDifferential {𝕜 σ : Type*} [NontriviallyNormedField 𝕜]
    [Fintype σ] (P : MvPolynomial σ 𝕜) (x : σ → 𝕜) : (σ → 𝕜) →L[𝕜] 𝕜 :=
  ∑ i, eval x (pderiv i P) • ContinuousLinearMap.proj i

end CurveSymmetry

end

-- lean/HomogeneousCharts.lean
section

namespace CurveSymmetry

set_option autoImplicit false

open Filter

open scoped Topology

def homogeneousChart (v : Fin 2 → ℂ) : HomogeneousPairs :=
  (![v 0, 1], ![v 1, 1])

/-- Exchanging the two coordinates of a homogeneous pair. -/
noncomputable def reverseCoordinates : (Fin 2 → ℂ) ≃L[ℂ] (Fin 2 → ℂ) :=
  (LinearEquiv.piCongrLeft ℂ (fun _ : Fin 2 => ℂ) (Equiv.swap 0 1)).toContinuousLinearEquiv

end CurveSymmetry

end

-- lean/AffineClosure.lean
section

namespace CurveSymmetry

set_option autoImplicit false

open MvPolynomial

def affineRealDiagonal (P : BPoly) : Set (Fin 2 → ℂ) :=
  (fun z : ℂ => ![z, star z]) '' realLocus P

/-- The ordinary complex-valued point of the prime spectrum obtained by
evaluation, not a custom point or a modified topology. -/
noncomputable def affineSpectrumPoint (v : Fin 2 → ℂ) : PrimeSpectrum BPoly :=
  ⟨RingHom.ker (eval v), RingHom.ker_isPrime (eval v)⟩

end CurveSymmetry

end

-- lean/ProjectiveChartMaps.lean
section

namespace CurveSymmetry

noncomputable section

open OnePoint

set_option autoImplicit false

/-- Standard projective-line charts `[z:1]` and `[1:z]`. These definitions
make no topological assertion. -/
def affineLinePoint (z : ℂ) : ProjectiveLine :=
  Projectivization.mk ℂ ![z, 1] (by simp)

def reciprocalLinePoint (z : ℂ) : ProjectiveLine :=
  Projectivization.mk ℂ ![1, z] (by simp)

def affineProjectiveChart (w : Fin 2 → ℂ) : ProjectiveLine × ProjectiveLine :=
  (affineLinePoint (w 0), affineLinePoint (w 1))

def mixedProjectiveChart (w : Fin 2 → ℂ) : ProjectiveLine × ProjectiveLine :=
  (reciprocalLinePoint (w 0), affineLinePoint (w 1))

/-- The second mixed chart uses the order `(1/Y,X)`, as in the closure proof. -/
def otherMixedProjectiveChart (w : Fin 2 → ℂ) : ProjectiveLine × ProjectiveLine :=
  (affineLinePoint (w 1), reciprocalLinePoint (w 0))

def reciprocalProjectiveChart (w : Fin 2 → ℂ) : ProjectiveLine × ProjectiveLine :=
  (reciprocalLinePoint (w 0), reciprocalLinePoint (w 1))

end

end CurveSymmetry

end

-- lean/AffineZariskiTopology.lean
section

namespace CurveSymmetry

set_option autoImplicit false

open MvPolynomial

/-- Zariski topology on complex coordinate points, induced by their evaluation
ideals in Mathlib's prime spectrum. This does not replace the Euclidean
topology on `ℂ` or install a global instance on coordinate vectors. -/
noncomputable abbrev affineZariskiTopology : TopologicalSpace (Fin 2 → ℂ) :=
  TopologicalSpace.induced affineSpectrumPoint inferInstance

noncomputable section

local instance instTopologicalSpaceForallFinOfNatNatComplex_affineZariskiTopology : TopologicalSpace (Fin 2 → ℂ) := affineZariskiTopology

end

end CurveSymmetry

end

-- lean/PolynomialZariskiMaps.lean
section

namespace CurveSymmetry

set_option autoImplicit false

open MvPolynomial

/-- The point map whose two coordinates are the given polynomials. -/
noncomputable def polynomialPointMap (F : Fin 2 → BPoly) (v : Fin 2 → ℂ) : Fin 2 → ℂ :=
  fun i => eval v (F i)

noncomputable section

local instance instTopologicalSpaceForallFinOfNatNatComplex_polynomialZariskiMaps : TopologicalSpace (Fin 2 → ℂ) := affineZariskiTopology

end

end CurveSymmetry

end


