-- Prove2me | Definitions.Def_CurveSymmetry_04_ProjectiveClosure
-- name    : CurveSymmetry_04_ProjectiveClosure
-- status  : Definition
-- author  : @carlok
-- created : 2026-10-07T12:12:57.925367+00:00
-- url     : https://prove2.me/theorems/2a5f8e3a-17be-423a-8792-cc99130ce021
-- title:
--   Atlas topology on $\mathbb P^1\times\mathbb P^1$, the ambient Möbius group of $\widehat C_{m,\alpha}$, dihedral maps
-- statement:
--   Let $\mathbb C^2$ carry its Zariski topology, and let $\phi_0,\phi_1,\phi_2,\phi_3:\mathbb C^2\to\mathbb P^1\times\mathbb P^1$ be the four standard charts, sending $(w_0,w_1)$ to $([w_0:1],[w_1:1])$, $([1:w_0],[w_1:1])$, $([w_1:1],[1:w_0])$ and $([1:w_0],[1:w_1])$. The group $\mathrm{GL}_2(\mathbb C)$ acts on the Riemann sphere $\widehat{\mathbb C}=\mathbb C\cup\{\infty\}$ by Möbius transformations $z\mapsto(az+b)/(cz+d)$. For $m\in\mathbb N$ and $\alpha\in\mathbb C$, $\widehat C_{m,\alpha}$ is the closure in $\widehat{\mathbb C}$ of $C_{m,\alpha}=\{z\in\mathbb C : \operatorname{Re}(z^m(|z|^2+\alpha))=0\}$.
--
--   The main definitions are the atlas topology on $\mathbb P^1\times\mathbb P^1$, the finest topology for which the map
--   $$\bigsqcup_{i=0}^{3}\mathbb C^2\longrightarrow\mathbb P^1\times\mathbb P^1,\qquad (i,w)\longmapsto\phi_i(w),$$
--   is continuous, and the ambient Möbius symmetry group of $\widehat C_{m,\alpha}$,
--   $$G_{m,\alpha}=\{\sigma\ \text{a holomorphic Möbius transformation of}\ \widehat{\mathbb C} : \sigma(p)\in\widehat C_{m,\alpha}\iff p\in\widehat C_{m,\alpha}\ \text{for all}\ p\in\widehat{\mathbb C}\}.$$
--   The file also defines:
--
--   1. Coordinate maps of $\mathbb C^2$: the exchange $(v_0,v_1)\mapsto(v_1,v_0)$; the inversion of one coordinate, as a formula on all of $\mathbb C^2$; the open set where a given coordinate is nonzero; and, on the torus $(\mathbb C^\times)^2$, the inversion of one coordinate and the simultaneous inversion $(v_0,v_1)\mapsto(v_0^{-1},v_1^{-1})$.
--   2. On $\mathbb P^1\times\mathbb P^1$: the flip $[x_0:x_1]\mapsto[x_1:x_0]$ of $\mathbb P^1$, applied to the left factor; and the property of a subset that its preimage under every $\phi_i$ is Zariski closed.
--   3. Möbius transformations as permutations: the homomorphism from $\mathrm{GL}_2(\mathbb C)$ to the permutation group of $\widehat{\mathbb C}$; the stabilizer of a subset $S$, the permutations $\sigma$ with $\sigma(p)\in S\iff p\in S$; the matrices with rows $(c,0),(0,1)$ and $(0,c),(1,0)$ for $c\ne0$, with the permutations $z\mapsto cz$ and $z\mapsto c/z$ they induce; and the matrix with rows $(a,b),(0,1)$, for $a\ne0$, representing $z\mapsto az+b$.
--   4. A dihedral action: for $n\ge1$, a chosen isomorphism from $\mathbb Z/n$ to the group of complex $n$-th roots of unity, $i\mapsto\omega^i$ with $\omega$ a primitive $n$-th root of unity; and, for $b\ne0$, the map from the dihedral group of order $2n$, with rotations $r^i$ and reflections $sr^i$, to permutations of $\widehat{\mathbb C}$, given by $r^i\mapsto(z\mapsto\omega^iz)$ and $sr^i\mapsto(z\mapsto b\,\omega^{-i}/z)$.
--   5. The tangent directions of a binary form: $\{[p_0:p_1]\in\mathbb P^1 : ap_0^m+bp_1^m=0\}$.
--   6. The arc $\theta\mapsto e^{i\theta}$ for $\theta\in\mathbb R$; the quintic expression $(x^2+y^2)(x^3-3xy^2)-3x^2y+y^3$ of equation (2), as a function of $z=x+iy$; and the coefficient $e^{\pi i/3}$.
--
--   The atlas topology is the setting in which the closure $V_\alpha$ of $P_\alpha=0$ in $\mathbb P^1\times\mathbb P^1$, introduced after equation (6), is identified and shown irreducible. $G_{m,\alpha}$ is the full ambient Möbius symmetry group of Theorem 2 and equation (3); its elements are holomorphic by construction, the absence of anti-Möbius symmetries being a separate statement, and the dihedral map with $n=2m$ and $b^{2m}=\bar\alpha^{\,2}$ is used to show that it is dihedral of order $4m$. Tangent directions count the branches at the ordinary $m$-fold points of Lemma 4; $e^{i\theta}$ parametrizes the examples $\alpha=e^{i\theta}$, $0<\theta<\pi$, of Remark 5; the quintic and $e^{\pi i/3}$ are the example (2) and its rotation by sixty degrees.
--
--   **Formalization Note**: The total inversion formula uses Lean's convention $0^{-1}=0$. The topologies on $\mathbb C^2$ and on $\mathbb P^1\times\mathbb P^1$ are local instances, so the usual topologies are unchanged, and the definition does not assert that the atlas topology agrees with the standard Zariski topology of $\mathbb P^1\times\mathbb P^1$. Möbius transformations are permutations of `OnePoint ℂ` in the image of `GL (Fin 2) ℂ` under Mathlib's action, so proportional matrices give the same element; the dihedral group is Mathlib's `DihedralGroup n`, and $\omega$ comes from an abstract isomorphism of cyclic groups rather than an explicit exponential. The file also proves $|e^{\pi i/3}|=1$.
-- source:
--   C. Perassi, Sharp symmetry bounds for real algebraic curves (note), definitions of the formalization, https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/sharp_symmetry_bounds.pdf. Lean modules CoordinateExchange, InversionDenominators, InversionContinuity, SimultaneousInversion, ProjectiveClosureGluing, ProjectiveAtlasTopology, ProjectiveAtlasClosure, ProjectiveAtlasOpenCover, ProjectiveAffineEmbedding, ProjectiveAtlasEmbeddings, ProjectiveAtlasUniqueness, ProjectiveCurveIrreducibility, FamilyAmbientGroup, FamilyDihedral, FamilyEuclidean, FamilyParameterArc, BinaryTangentDirections, QuinticExample in https://github.com/carlok/curve-symmetry-lean/tree/d99bc17a1c397956c05d7417de50f9beed56580f/lean (C. Perassi)

-- Definitions, part 04 of 12, generated from curve-symmetry-lean by skeleton
-- subtraction: the source modules below, in dependency order, each in its own
-- section; only definitions, instances and the theorems they need are kept.
import Definitions.Def_CurveSymmetry_01_RealLoci
import Definitions.Def_CurveSymmetry_02_FamilyBasics
import Definitions.Def_CurveSymmetry_03_IsometriesAndCharts
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
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.FieldTheory.Separable
import Mathlib.GroupTheory.SpecificGroups.Dihedral
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.RingTheory.Polynomial.Eisenstein.Criterion
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.Spectrum.Prime.Jacobson
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.Tactic
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine
import Mathlib.Topology.Constructions

-- lean/CoordinateExchange.lean
section

namespace CurveSymmetry

set_option autoImplicit false

open MvPolynomial

def exchangeCoordinates (v : Fin 2 → ℂ) : Fin 2 → ℂ := ![v 1, v 0]

noncomputable section

local instance instTopologicalSpaceForallFinOfNatNatComplex_coordinateExchange : TopologicalSpace (Fin 2 → ℂ) := affineZariskiTopology

end

end CurveSymmetry

end

-- lean/InversionDenominators.lean
section

namespace CurveSymmetry

set_option autoImplicit false

open MvPolynomial

/-- Invert exactly one coordinate. The continuity results will restrict this
total formula to the domain on which that coordinate is nonzero. -/
noncomputable def invertCoordinate (i : Fin 2) (v : Fin 2 → ℂ) (j : Fin 2) : ℂ :=
  if j = i then (v j)⁻¹ else v j

end CurveSymmetry

end

-- lean/InversionContinuity.lean
section

namespace CurveSymmetry

set_option autoImplicit false

open MvPolynomial

noncomputable section

local instance instTopologicalSpaceForallFinOfNatNatComplex_inversionContinuity : TopologicalSpace (Fin 2 → ℂ) := affineZariskiTopology

abbrev CoordinateNonzero (i : Fin 2) := {v : Fin 2 → ℂ // v i ≠ 0}

end

end CurveSymmetry

end

-- lean/SimultaneousInversion.lean
section

namespace CurveSymmetry

set_option autoImplicit false

noncomputable section

local instance instTopologicalSpaceForallFinOfNatNatComplex_simultaneousInversion : TopologicalSpace (Fin 2 → ℂ) := affineZariskiTopology

abbrev AffineTorus := {v : Fin 2 → ℂ // v 0 ≠ 0 ∧ v 1 ≠ 0}

def torusInvertCoordinate (i : Fin 2) (v : AffineTorus) : AffineTorus :=
  ⟨invertCoordinate i v.val, by
    fin_cases i <;> simp [invertCoordinate, v.property.1, v.property.2]⟩

def simultaneousInversion (v : AffineTorus) : AffineTorus :=
  torusInvertCoordinate 1 (torusInvertCoordinate 0 v)

end

end CurveSymmetry

end

-- lean/ProjectiveClosureGluing.lean
section

namespace CurveSymmetry

set_option autoImplicit false

open MvPolynomial

noncomputable section

local instance instTopologicalSpaceForallFinOfNatNatComplex_projectiveClosureGluing : TopologicalSpace (Fin 2 → ℂ) := affineZariskiTopology

/-- A property of a subset of the product of projective lines, using the
already checked affine Zariski topology on each chart. This does not declare
a topology on the projective product or assume chart open embeddings. -/
def ClosedInProjectiveCharts (S : Set (ProjectiveLine × ProjectiveLine)) : Prop :=
  IsClosed (affineProjectiveChart ⁻¹' S) ∧
  IsClosed (mixedProjectiveChart ⁻¹' S) ∧
  IsClosed (otherMixedProjectiveChart ⁻¹' S) ∧
  IsClosed (reciprocalProjectiveChart ⁻¹' S)

section AmbientTopology

variable [TopologicalSpace (ProjectiveLine × ProjectiveLine)]

end AmbientTopology

end

end CurveSymmetry

end

-- lean/ProjectiveAtlasTopology.lean
section

namespace CurveSymmetry

set_option autoImplicit false

noncomputable section

local instance instTopologicalSpaceForallFinOfNatNatComplex_projectiveAtlasTopology : TopologicalSpace (Fin 2 → ℂ) := affineZariskiTopology

def projectiveChart (i : Fin 4) : (Fin 2 → ℂ) → ProjectiveLine × ProjectiveLine :=
  ![affineProjectiveChart, mixedProjectiveChart, otherMixedProjectiveChart,
    reciprocalProjectiveChart] i

abbrev ProjectiveAtlasDomain := Σ _ : Fin 4, (Fin 2 → ℂ)

def projectiveAtlasMap (p : ProjectiveAtlasDomain) : ProjectiveLine × ProjectiveLine :=
  projectiveChart p.1 p.2

/-- Final topology from the disjoint union of the four affine Zariski charts.
The definition is independent of every family equation and parameter. Agreement
with standard projective Zariski geometry still requires chart compatibility;
this name intentionally does not assert that identification. -/
abbrev projectiveAtlasTopology : TopologicalSpace (ProjectiveLine × ProjectiveLine) :=
  TopologicalSpace.coinduced projectiveAtlasMap inferInstance

local instance instTopologicalSpaceProdProjectiveLine_projectiveAtlasTopology : TopologicalSpace (ProjectiveLine × ProjectiveLine) := projectiveAtlasTopology

end

end CurveSymmetry

end

-- lean/ProjectiveAtlasClosure.lean
section

namespace CurveSymmetry

set_option autoImplicit false

open MvPolynomial

noncomputable section

local instance instTopologicalSpaceForallFinOfNatNatComplex_projectiveAtlasClosure : TopologicalSpace (Fin 2 → ℂ) := affineZariskiTopology

local instance instTopologicalSpaceProdProjectiveLine_projectiveAtlasClosure : TopologicalSpace (ProjectiveLine × ProjectiveLine) :=
  projectiveAtlasTopology

end

end CurveSymmetry

end

-- lean/ProjectiveAtlasOpenCover.lean
section

namespace CurveSymmetry

set_option autoImplicit false

open OnePoint

noncomputable section

local instance instTopologicalSpaceForallFinOfNatNatComplex_projectiveAtlasOpenCover : TopologicalSpace (Fin 2 → ℂ) := affineZariskiTopology

local instance instTopologicalSpaceProdProjectiveLine_projectiveAtlasOpenCover : TopologicalSpace (ProjectiveLine × ProjectiveLine) := projectiveAtlasTopology

end

end CurveSymmetry

end

-- lean/ProjectiveAffineEmbedding.lean
section

namespace CurveSymmetry

set_option autoImplicit false

noncomputable section

local instance instTopologicalSpaceForallFinOfNatNatComplex_projectiveAffineEmbedding : TopologicalSpace (Fin 2 → ℂ) := affineZariskiTopology

local instance instTopologicalSpaceProdProjectiveLine_projectiveAffineEmbedding : TopologicalSpace (ProjectiveLine × ProjectiveLine) := projectiveAtlasTopology

end

end CurveSymmetry

end

-- lean/ProjectiveAtlasEmbeddings.lean
section

namespace CurveSymmetry

set_option autoImplicit false

noncomputable section

local instance instTopologicalSpaceForallFinOfNatNatComplex_projectiveAtlasEmbeddings : TopologicalSpace (Fin 2 → ℂ) := affineZariskiTopology

local instance instTopologicalSpaceProdProjectiveLine_projectiveAtlasEmbeddings : TopologicalSpace (ProjectiveLine × ProjectiveLine) := projectiveAtlasTopology

def homogeneousSwap : (Fin 2 → ℂ) →ₗ[ℂ] (Fin 2 → ℂ) where
  toFun v := ![v 1, v 0]
  map_add' v w := by ext i; fin_cases i <;> rfl
  map_smul' c v := by ext i; fin_cases i <;> rfl

theorem homogeneousSwap_injective : Function.Injective homogeneousSwap := by
  intro v w h
  have h0 := congrFun h 1
  have h1 := congrFun h 0
  ext i
  fin_cases i
  · exact h0
  · exact h1

/-- The ordinary homogeneous coordinate exchange `[x:y] ↦ [y:x]`. -/
def projectiveLineFlip : ProjectiveLine → ProjectiveLine :=
  Projectivization.map homogeneousSwap homogeneousSwap_injective

def projectiveFlipFirst (p : ProjectiveLine × ProjectiveLine) :=
  (projectiveLineFlip p.1, p.2)

end

end CurveSymmetry

end

-- lean/ProjectiveAtlasUniqueness.lean
section

namespace CurveSymmetry

set_option autoImplicit false

noncomputable section

local instance instTopologicalSpaceForallFinOfNatNatComplex_projectiveAtlasUniqueness : TopologicalSpace (Fin 2 → ℂ) := affineZariskiTopology

end

end CurveSymmetry

end

-- lean/ProjectiveCurveIrreducibility.lean
section

namespace CurveSymmetry

set_option autoImplicit false

noncomputable section

local instance instTopologicalSpaceForallFinOfNatNatComplex_projectiveCurveIrreducibility : TopologicalSpace (Fin 2 → ℂ) := affineZariskiTopology

local instance instTopologicalSpaceProdProjectiveLine_projectiveCurveIrreducibility : TopologicalSpace (ProjectiveLine × ProjectiveLine) := projectiveAtlasTopology

end

end CurveSymmetry

end

-- lean/FamilyAmbientGroup.lean
section

namespace CurveSymmetry

set_option autoImplicit false

open OnePoint

noncomputable section

/-- Permutations preserving a set in both directions. -/
def sphereSetStabilizer (S : Set Sphere) : Subgroup (Equiv.Perm Sphere) where
  carrier := {f | ∀ p, f p ∈ S ↔ p ∈ S}
  one_mem' := by intro p; rfl
  mul_mem' := by
    intro f g hf hg p
    exact (hf (g p)).trans (hg p)
  inv_mem' := by
    intro f hf p
    simpa using (hf (f⁻¹ p)).symm

/-- The full image of GL(2,C) in actual sphere permutations. Scalar-equivalent
matrices therefore represent the same element, not extra group elements. -/
def sphereMobiusHom : MobiusMatrix →* Equiv.Perm Sphere :=
  MulAction.toPermHom MobiusMatrix Sphere

/-- Actual ambient Möbius symmetries, independently of the anticipated normal
forms or root conditions. The no-anti-map theorem excludes the other parity. -/
def familyAmbientGroup (m : ℕ) (α : ℂ) : Subgroup (Equiv.Perm Sphere) :=
  sphereMobiusHom.range ⊓ sphereSetStabilizer (sphericalFamily m α)

def dilationMatrix (c : ℂ) (hc : c ≠ 0) : MobiusMatrix :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![c, 0; 0, 1]
    (by simpa [Matrix.det_fin_two] using hc)

def inversionMatrix (c : ℂ) (hc : c ≠ 0) : MobiusMatrix :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![0, c; 1, 0]
    (by simpa [Matrix.det_fin_two] using hc)

def sphereDilationPerm (c : ℂ) (hc : c ≠ 0) : Equiv.Perm Sphere :=
  sphereMobiusHom (dilationMatrix c hc)

def sphereInversionPerm (c : ℂ) (hc : c ≠ 0) : Equiv.Perm Sphere :=
  sphereMobiusHom (inversionMatrix c hc)

end

end CurveSymmetry

end

-- lean/FamilyDihedral.lean
section

namespace CurveSymmetry

set_option autoImplicit false

open OnePoint

noncomputable section

/-- A cyclic parametrization of all complex nth roots. -/
def complexRootEquiv (n : ℕ) [NeZero n] :
    Multiplicative (ZMod n) ≃* rootsOfUnity n ℂ :=
  mulEquivOfCyclicCardEq (by rw [Complex.card_rootsOfUnity]; simp)

def rootCharacter (n : ℕ) [NeZero n] (i : ZMod n) : ℂ :=
  ((complexRootEquiv n (Multiplicative.ofAdd i)).val : ℂ)

theorem rootCharacter_ne_zero (n : ℕ) [NeZero n] (i : ZMod n) :
    rootCharacter n i ≠ 0 := Units.ne_zero _

/-- The standard dihedral action: r(i) is multiplication by the ith root,
and sr(i) is inversion with coefficient b divided by that root. -/
def dihedralSphereMap (n : ℕ) [NeZero n] (b : ℂ) (hb : b ≠ 0) :
    DihedralGroup n → Equiv.Perm Sphere
  | .r i => sphereDilationPerm (rootCharacter n i) (rootCharacter_ne_zero n i)
  | .sr i => sphereInversionPerm (b / rootCharacter n i)
      (div_ne_zero hb (rootCharacter_ne_zero n i))

end

end CurveSymmetry

end

-- lean/FamilyEuclidean.lean
section

namespace CurveSymmetry

set_option autoImplicit false

open OnePoint

noncomputable section

/-- An affine map as an actual ambient Möbius transformation. -/
def affineMobiusMatrix (a b : ℂ) (ha : a ≠ 0) : MobiusMatrix :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![a, b; 0, 1]
    (by simpa [Matrix.det_fin_two] using ha)

end

end CurveSymmetry

end

-- lean/FamilyParameterArc.lean
section

namespace CurveSymmetry

set_option autoImplicit false

noncomputable def arcParameter (θ : ℝ) : ℂ := Complex.exp ((θ : ℂ) * Complex.I)

end CurveSymmetry

end

-- lean/BinaryTangentDirections.lean
section

namespace CurveSymmetry

set_option autoImplicit false

open OnePoint

noncomputable section

/-- Homogeneous tangent directions on the ordinary projective line. -/
def binaryTangentDirections (m : ℕ) (a b : ℂ) : Set ProjectiveLine :=
  {p | a * p.rep 0 ^ m + b * p.rep 1 ^ m = 0}

end

end CurveSymmetry

end

-- lean/QuinticExample.lean
section

namespace CurveSymmetry

set_option autoImplicit false

noncomputable section

/-- The actual Cartesian expression printed in the paper. -/
def quinticValue (z : ℂ) : ℝ :=
  (z.re ^ 2 + z.im ^ 2) * (z.re ^ 3 - 3 * z.re * z.im ^ 2) -
    3 * z.re ^ 2 * z.im + z.im ^ 3

def sixtyDegreeCoefficient : ℂ := Complex.exp ((Real.pi : ℂ) * Complex.I / 3)

theorem sixtyDegree_norm : ‖sixtyDegreeCoefficient‖ = 1 := by
  simp [sixtyDegreeCoefficient, Complex.norm_exp]

end

end CurveSymmetry

end


