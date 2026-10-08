-- Prove2me | Definitions.Def_CurveSymmetry_09_Genus
-- name    : CurveSymmetry_09_Genus
-- status  : Definition
-- author  : @carlok
-- created : 2026-10-07T12:20:37.416715+00:00
-- url     : https://prove2.me/theorems/c97a97e4-045b-4032-9c56-9a5dd057415f
-- title:
--   The genus of a function field over $\mathbb C$, and holomorphic differentials on the double cover $w^2=h_{m,\alpha}(t)$
-- statement:
--   Let $K$ be a field containing $\mathbb C$, with Kähler differentials $\Omega_{K/\mathbb C}$ and derivation $d:K\to\Omega_{K/\mathbb C}$. A place of $K$ is a valuation subring $O\ne K$ containing $\mathbb C$. Let $h\in\mathbb C[t]$ be squarefree with $W^2-h$ irreducible over $\mathbb C(t)$, let $L_h=\mathbb C(t)[W]/(W^2-h)$, with $t$ and $w$ the images of the variables, and for $(c,d)\in\mathbb C^2$ with $d^2=h(c)$ let $\mathcal O_{c,d}\subseteq L_h$ be the local ring of the curve $w^2=h(t)$ at $(c,d)$. For the extremal family let $m\ge1$ and $\alpha\in\mathbb C$ with $\alpha\ne\bar\alpha$, $h_{m,\alpha}(t)=-t(t^m+1)(\alpha t^m+\bar\alpha)$, and $L=L_{h_{m,\alpha}}$.
--
--   The genus is defined from the field alone. The differentials regular at a place $O$ are the complex span of the $a\,db$ with $a,b\in O$, the holomorphic differentials are those regular at every place, and
--   $$g(K)=\dim_{\mathbb C}\ \bigcap_{O\ \text{a place of}\ K}\operatorname{span}_{\mathbb C}\{a\,db : a,b\in O\}.$$
--   An isomorphism of $\mathbb C$-algebras $K\to K'$ induces $\mathbb C$-linear isomorphisms $\Omega_{K/\mathbb C}\to\Omega_{K'/\mathbb C}$ and between the spaces of holomorphic differentials, both defined in the file.
--
--   For the double cover, the file defines concrete regularity conditions and candidate differentials:
--
--   1. A differential $\omega$ of $L_h$ is regular at the point $(c,d)$ if, for every uniformizer $u$ of $\mathcal O_{c,d}$ and every $f\in L_h$ with $\omega=f\,du$, one has $f\in\mathcal O_{c,d}$.
--   2. A differential $\omega$ of $L$ is regular at infinity if its transport along the chart isomorphism $L\to L_{h_{m,\bar\alpha}}$, $t\mapsto1/s$, $w\mapsto w's^{-(m+1)}$, is regular at the point $(0,0)$ of the conjugate curve $w'^2=h_{m,\bar\alpha}(s)$.
--   3. $\omega$ is holomorphic if it is regular at every point $(c,d)$ with $d^2=h_{m,\alpha}(c)$ and at infinity; these $\omega$ form a complex subspace of $\Omega_{L/\mathbb C}$.
--   4. The differentials $t^i\,dt/w$ of $L$ for $i\in\mathbb N$, with coefficients $t^i/w$, and the element $t-c$ of $\mathbb C[t][W]/(W^2-h)$.
--
--   The genus is the invariant in Lemma 4, where the normalization of $V_\alpha$ has genus $m$, and in Remark 5, where $\operatorname{Re}(z^4)=1$ has genus three against two for $m=2$. Since it depends only on the function field up to $\mathbb C$-isomorphism, a similarity between real loci, which induces such an isomorphism, preserves it. The regularity conditions on the double cover and the differentials $t^i\,dt/w$, $0\le i<m$, are the explicit description through which the genus $m$ of the family is computed.
--
--   **Formalization Note**: The dimension is `Module.finrank`, which is $0$ for an infinite-dimensional space, and places are `ValuationSubring`s. For the family, $m\ge1$ and $\alpha\ne\bar\alpha$ are `Fact` instances; regularity at infinity is defined by transport rather than through a separate local ring, and a separate theorem shows that the point places and the place over $t=\infty$ are all the places of $L$. The file also proves that a single uniformizer decides regularity at a point and that regularity is preserved by sums and complex multiples.
-- source:
--   C. Perassi, Sharp symmetry bounds for real algebraic curves (note), definitions of the formalization, https://github.com/carlok/curve-symmetry-lean/blob/d99bc17a1c397956c05d7417de50f9beed56580f/sharp_symmetry_bounds.pdf. Lean modules PlaceUniformizers, InfinityDifferentials, HolomorphicDifferentials, InfinityRegularity, HolomorphicSpace, HolomorphicBasis, FunctionFieldGenus in https://github.com/carlok/curve-symmetry-lean/tree/d99bc17a1c397956c05d7417de50f9beed56580f/lean (C. Perassi)

-- Definitions, part 09 of 12, generated from curve-symmetry-lean by skeleton
-- subtraction: the source modules below, in dependency order, each in its own
-- section; only definitions, instances and the theorems they need are kept.
import Definitions.Def_CurveSymmetry_01_RealLoci
import Definitions.Def_CurveSymmetry_02_FamilyBasics
import Definitions.Def_CurveSymmetry_03_IsometriesAndCharts
import Definitions.Def_CurveSymmetry_05_FamilyFunctionField
import Definitions.Def_CurveSymmetry_06_QuadraticRing
import Definitions.Def_CurveSymmetry_07_Places
import Definitions.Def_CurveSymmetry_08_Differentials
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.Analysis.Complex.Isometry
import Mathlib.Analysis.Complex.OperatorNorm
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Normed.Affine.MazurUlam
import Mathlib.Data.Complex.Basic
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.FieldTheory.Separable
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.RingTheory.Kaehler.Polynomial
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.Localization.AsSubring
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.Nakayama
import Mathlib.RingTheory.Polynomial.Eisenstein.Criterion
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.Tactic

-- lean/PlaceUniformizers.lean
section

namespace CurveSymmetry

set_option autoImplicit false

open Polynomial

section

variable (h : ℂ[X]) [Fact (Squarefree h)] [Fact (Irreducible (quadRat h))]
  (c d : ℂ) (hd : d ^ 2 = h.eval c)

/-- The coordinate `t − c` of the coordinate ring of the double cover. -/
noncomputable def quadShift : QuadRing h := algebraMap ℂ[X] (QuadRing h) (X - C c)

omit [Fact (Irreducible (quadRat h))] in
/-- A simple root splits off a factor that does not vanish there. -/
lemma exists_factor_of_root (hc : h.eval c = 0) :
    ∃ k : ℂ[X], h = (X - C c) * k ∧ k.eval c ≠ 0 := by
  obtain ⟨k, hk⟩ := (dvd_iff_isRoot (a := c) (p := h)).mpr hc
  refine ⟨k, hk, ?_⟩
  intro hk0
  obtain ⟨j, hj⟩ := (dvd_iff_isRoot (a := c) (p := k)).mpr hk0
  have hsq : (X - C c) * (X - C c) ∣ h := ⟨j, by rw [hk, hj]; ring⟩
  exact Polynomial.not_isUnit_X_sub_C c ((Fact.out : Squarefree h) _ hsq)

end

variable {m : ℕ} {α : ℂ} [hm : Fact (0 < m)] [ha : Fact (α ≠ star α)]

omit hm ha in
/-- A root of `h_α` gives a point of the double cover with `d = 0`. -/
lemma familyH_root_point (c : ℂ) (hc : (familyH m α).eval c = 0) :
    (0 : ℂ) ^ 2 = (familyH m α).eval c := by
  rw [hc]; ring

end CurveSymmetry

end

-- lean/InfinityDifferentials.lean
section

namespace CurveSymmetry

set_option autoImplicit false

open Polynomial

variable {m : ℕ} {α : ℂ} [hm : Fact (0 < m)] [ha : Fact (α ≠ star α)]

lemma familyInfinityEquiv_coe (x : QuadField (familyH m α)) :
    familyInfinityEquiv m α x = familyInfinityMap m α x := rfl

variable (m α) in
/-- The chart isomorphism of G07b-3 as an isomorphism of `ℂ`-algebras. -/
noncomputable def familyInfinityAlgEquiv :
    QuadField (familyH m α) ≃ₐ[ℂ] QuadField (familyH m (star α)) :=
  AlgEquiv.ofRingEquiv (f := familyInfinityEquiv m α) fun r => by
    rw [familyInfinityEquiv_coe,
      IsScalarTower.algebraMap_apply ℂ ℂ[X] (QuadField (familyH m α)),
      ← Polynomial.C_eq_algebraMap, familyInfinityMap_polyC, Polynomial.C_eq_algebraMap,
      ← IsScalarTower.algebraMap_apply ℂ ℂ[X] (QuadField (familyH m (star α)))]

@[simp] lemma familyInfinityAlgEquiv_apply (x : QuadField (familyH m α)) :
    familyInfinityAlgEquiv m α x = familyInfinityMap m α x := rfl

end CurveSymmetry

end

-- lean/HolomorphicDifferentials.lean
section

namespace CurveSymmetry

set_option autoImplicit false

open Polynomial

section

variable (h : ℂ[X]) [Fact (Squarefree h)] [Fact (Irreducible (quadRat h))]
  (c d : ℂ) (hd : d ^ 2 = h.eval c)

instance quadField_charZero : CharZero (QuadField h) :=
  charZero_of_injective_algebraMap (algebraMap ℂ (QuadField h)).injective

/-- A differential is regular at the point place `(c, d)` when its coefficient against a
uniformizer there lies in the local ring. -/
def IsRegularAt (ω : Ω[QuadField h⁄ℂ]) : Prop :=
  ∀ (u : quadLocalRing h c d hd) (f : QuadField h),
    IsLocalRing.maximalIdeal (quadLocalRing h c d hd) = Ideal.span {u} →
      ω = f • KaehlerDifferential.D ℂ (QuadField h) (u : QuadField h) →
        f ∈ quadLocalRing h c d hd

/-- One uniformizer decides regularity. -/
theorem isRegularAt_iff {u : quadLocalRing h c d hd}
    (hu : IsLocalRing.maximalIdeal (quadLocalRing h c d hd) = Ideal.span {u})
    {ω : Ω[QuadField h⁄ℂ]} {f : QuadField h}
    (hf : ω = f • KaehlerDifferential.D ℂ (QuadField h) (u : QuadField h)) :
    IsRegularAt h c d hd ω ↔ f ∈ quadLocalRing h c d hd := by
  constructor
  · intro hreg
    exact hreg u f hu hf
  · intro hfmem u' f' hu' hf'
    obtain ⟨e, he, -, hfe⟩ := quadLocal_coeff_unit h c d hd hu' hu hf' hf
    rw [hfe]
    exact Subalgebra.mul_mem _ he hfmem

/-- Constants lie in every point place's local ring. -/
lemma quadLocal_const_mem (z : ℂ) :
    algebraMap ℂ (QuadField h) z ∈ quadLocalRing h c d hd := by
  have : algebraMap ℂ (QuadField h) z =
      algebraMap (QuadRing h) (QuadField h) (algebraMap ℂ (QuadRing h) z) := by
    rw [← IsScalarTower.algebraMap_apply ℂ (QuadRing h) (QuadField h)]
  rw [this]
  exact Subalgebra.algebraMap_mem _ _

/-- The zero differential is regular. -/
theorem isRegularAt_zero : IsRegularAt h c d hd 0 := by
  obtain ⟨u, hu, -⟩ := quadLocal_exists_uniformizer h c d hd
  exact (isRegularAt_iff h c d hd hu (f := 0) (by rw [zero_smul])).mpr
    (Subalgebra.zero_mem _)

/-- A sum of regular differentials is regular. -/
theorem isRegularAt_add {ω₁ ω₂ : Ω[QuadField h⁄ℂ]} (h₁ : IsRegularAt h c d hd ω₁)
    (h₂ : IsRegularAt h c d hd ω₂) : IsRegularAt h c d hd (ω₁ + ω₂) := by
  obtain ⟨u, hu, -⟩ := quadLocal_exists_uniformizer h c d hd
  obtain ⟨f₁, hf₁⟩ := quadLocal_exists_coeff h c d hd hu ω₁
  obtain ⟨f₂, hf₂⟩ := quadLocal_exists_coeff h c d hd hu ω₂
  have m₁ := (isRegularAt_iff h c d hd hu hf₁).mp h₁
  have m₂ := (isRegularAt_iff h c d hd hu hf₂).mp h₂
  exact (isRegularAt_iff h c d hd hu (f := f₁ + f₂) (by rw [hf₁, hf₂, add_smul])).mpr
    (Subalgebra.add_mem _ m₁ m₂)

/-- A complex multiple of a regular differential is regular. -/
theorem isRegularAt_smul (z : ℂ) {ω : Ω[QuadField h⁄ℂ]} (h₁ : IsRegularAt h c d hd ω) :
    IsRegularAt h c d hd (z • ω) := by
  obtain ⟨u, hu, -⟩ := quadLocal_exists_uniformizer h c d hd
  obtain ⟨f₁, hf₁⟩ := quadLocal_exists_coeff h c d hd hu ω
  have m₁ := (isRegularAt_iff h c d hd hu hf₁).mp h₁
  refine (isRegularAt_iff h c d hd hu (f := algebraMap ℂ (QuadField h) z * f₁) ?_).mpr
    (Subalgebra.mul_mem _ (quadLocal_const_mem h c d hd z) m₁)
  rw [hf₁, mul_smul, algebraMap_smul]

end

variable {m : ℕ} {α : ℂ} [hm : Fact (0 < m)] [ha : Fact (α ≠ star α)]

end CurveSymmetry

end

-- lean/InfinityRegularity.lean
section

namespace CurveSymmetry

set_option autoImplicit false

open Polynomial

variable {m : ℕ} {α : ℂ} [hm : Fact (0 < m)] [ha : Fact (α ≠ star α)]

/-- A differential is regular at the place over `t = ∞` when its transport along the chart
isomorphism is regular at the conjugate family's point place `(0, 0)`. -/
def IsRegularAtInfinity (ω : Ω[QuadField (familyH m α)⁄ℂ]) : Prop :=
  IsRegularAt (familyH m (star α)) 0 0 (familyH_star_zero_point m α)
    (kaehlerTransport (familyInfinityAlgEquiv m α) ω)

end CurveSymmetry

end

-- lean/HolomorphicSpace.lean
section

namespace CurveSymmetry

set_option autoImplicit false

open Polynomial

variable {m : ℕ} {α : ℂ} [hm : Fact (0 < m)] [ha : Fact (α ≠ star α)]

/-- Regularity at the place over `t = ∞` is closed under the vector-space operations. -/
lemma isRegularAtInfinity_zero : IsRegularAtInfinity (m := m) (α := α) 0 := by
  rw [IsRegularAtInfinity, map_zero]
  exact isRegularAt_zero _ _ _ _

lemma isRegularAtInfinity_add {ω₁ ω₂ : Ω[QuadField (familyH m α)⁄ℂ]}
    (h₁ : IsRegularAtInfinity ω₁) (h₂ : IsRegularAtInfinity ω₂) :
    IsRegularAtInfinity (ω₁ + ω₂) := by
  rw [IsRegularAtInfinity, map_add]
  exact isRegularAt_add _ _ _ _ h₁ h₂

lemma isRegularAtInfinity_smul (z : ℂ) {ω : Ω[QuadField (familyH m α)⁄ℂ]}
    (h₁ : IsRegularAtInfinity ω) : IsRegularAtInfinity (z • ω) := by
  rw [IsRegularAtInfinity, kaehlerTransport_smul_base]
  exact isRegularAt_smul _ _ _ _ z h₁

/-- A differential of the family's function field is holomorphic when it is regular at every
point place and at the place over `t = ∞`, which by `family_place_classification` are all
the places. -/
def IsHolomorphic (ω : Ω[QuadField (familyH m α)⁄ℂ]) : Prop :=
  (∀ (c d : ℂ) (hd : d ^ 2 = (familyH m α).eval c),
      IsRegularAt (familyH m α) c d hd ω) ∧
    IsRegularAtInfinity ω

variable (m α) in
/-- **G09b-3b**: the holomorphic differentials, as a complex vector subspace of `Ω[K⁄ℂ]`. -/
def holomorphicDifferentials : Submodule ℂ Ω[QuadField (familyH m α)⁄ℂ] where
  carrier := {ω | IsHolomorphic ω}
  zero_mem' := ⟨fun c d hd => isRegularAt_zero _ c d hd, isRegularAtInfinity_zero⟩
  add_mem' := fun {_ _} ha hb =>
    ⟨fun c d hd => isRegularAt_add _ c d hd (ha.1 c d hd) (hb.1 c d hd),
      isRegularAtInfinity_add ha.2 hb.2⟩
  smul_mem' := fun z {_} ha =>
    ⟨fun c d hd => isRegularAt_smul _ c d hd z (ha.1 c d hd),
      isRegularAtInfinity_smul z ha.2⟩

end CurveSymmetry

end

-- lean/HolomorphicBasis.lean
section

namespace CurveSymmetry

set_option autoImplicit false

open Polynomial

section Point

variable (h : ℂ[X]) [Fact (Squarefree h)] [Fact (Irreducible (quadRat h))]
  (c d : ℂ) (hd : d ^ 2 = h.eval c)

end Point

variable {m : ℕ} {α : ℂ} [hm : Fact (0 < m)] [ha : Fact (α ≠ star α)]

variable (m α) in
/-- The coefficient `tⁱ/w` of the candidate basis differential. -/
noncomputable def holoCoeff (i : ℕ) : QuadField (familyH m α) :=
  quadT (familyH m α) ^ i * (AdjoinRoot.root (quadRat (familyH m α)))⁻¹

variable (m α) in
/-- The differential `tⁱ·dt/w`. -/
noncomputable def holoBasisVec (i : ℕ) : Ω[QuadField (familyH m α)⁄ℂ] :=
  holoCoeff m α i • KaehlerDifferential.D ℂ (QuadField (familyH m α)) (quadT (familyH m α))

end CurveSymmetry

end

-- lean/FunctionFieldGenus.lean
section

namespace CurveSymmetry

set_option autoImplicit false

section Genus

variable {K : Type*} [Field K] [Algebra ℂ K]

/-- A place of `K` over `ℂ`: a valuation subring other than `K` containing the constants. -/
def IsComplexPlace (O : ValuationSubring K) : Prop :=
  O ≠ ⊤ ∧ ∀ z : ℂ, algebraMap ℂ K z ∈ O

/-- The differentials regular at `O`: the `ℂ`-combinations of `a·db` with `a, b ∈ O`. -/
noncomputable def regularAt (O : ValuationSubring K) : Submodule ℂ Ω[K⁄ℂ] :=
  Submodule.span ℂ {ω | ∃ a ∈ O, ∃ b ∈ O, ω = a • KaehlerDifferential.D ℂ K b}

variable (K) in
/-- The holomorphic differentials: those regular at every place. -/
noncomputable def holomorphicSpace : Submodule ℂ Ω[K⁄ℂ] :=
  ⨅ (O : ValuationSubring K) (_ : IsComplexPlace O), regularAt O

theorem mem_holomorphicSpace {ω : Ω[K⁄ℂ]} :
    ω ∈ holomorphicSpace K ↔ ∀ O : ValuationSubring K, IsComplexPlace O → ω ∈ regularAt O := by
  simp only [holomorphicSpace, Submodule.mem_iInf]

variable (K) in
/-- **R01a**: the genus of `K`, the dimension over `ℂ` of its holomorphic differentials. -/
noncomputable def genus : ℕ :=
  Module.finrank ℂ (holomorphicSpace K)

end Genus

section Transport

variable {K L : Type*} [Field K] [Algebra ℂ K] [Field L] [Algebra ℂ L]

lemma kaehlerTransport_symm_apply (e : K ≃ₐ[ℂ] L) (ω : Ω[K⁄ℂ]) :
    kaehlerTransport e.symm (kaehlerTransport e ω) = ω := by
  have hω : ω ∈ Submodule.span K (Set.range (KaehlerDifferential.D ℂ K)) := by
    rw [KaehlerDifferential.span_range_derivation]; trivial
  induction hω using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, rfl⟩ := hx
    rw [kaehlerTransport_D, kaehlerTransport_D, AlgEquiv.symm_apply_apply]
  | zero => rw [map_zero, map_zero]
  | add x y _ _ hx hy => rw [map_add, map_add, hx, hy]
  | smul a x _ hx =>
    rw [kaehlerTransport_smul, kaehlerTransport_smul, AlgEquiv.symm_apply_apply, hx]

/-- `kaehlerTransport` along a `ℂ`-algebra isomorphism, as a `ℂ`-linear equivalence. -/
noncomputable def kaehlerTransportEquiv (e : K ≃ₐ[ℂ] L) : Ω[K⁄ℂ] ≃ₗ[ℂ] Ω[L⁄ℂ] where
  toFun := kaehlerTransport e
  invFun := kaehlerTransport e.symm
  map_add' := map_add _
  map_smul' := kaehlerTransport_smul_base e
  left_inv := kaehlerTransport_symm_apply e
  right_inv ω := by
    simpa only [AlgEquiv.symm_symm] using kaehlerTransport_symm_apply e.symm ω

@[simp] lemma kaehlerTransportEquiv_apply (e : K ≃ₐ[ℂ] L) (ω : Ω[K⁄ℂ]) :
    kaehlerTransportEquiv e ω = kaehlerTransport e ω :=
  rfl

/-- Places pull back to places along an isomorphism. -/
lemma IsComplexPlace.comap {O : ValuationSubring L} (hO : IsComplexPlace O) (e : K ≃ₐ[ℂ] L) :
    IsComplexPlace (O.comap (e : K →+* L)) := by
  refine ⟨fun htop => hO.1 ?_, fun z => ?_⟩
  · refine eq_top_iff.mpr fun y _ => ?_
    have hy : e.symm y ∈ O.comap (e : K →+* L) := by
      rw [htop]; exact ValuationSubring.mem_top _
    rw [ValuationSubring.mem_comap] at hy
    simpa using hy
  · rw [ValuationSubring.mem_comap]
    simpa using hO.2 z

/-- The transport carries differentials regular at the pulled-back place to differentials
regular at the place. -/
lemma kaehlerTransport_mem_regularAt (e : K ≃ₐ[ℂ] L) (O : ValuationSubring L)
    {ω : Ω[K⁄ℂ]} (hω : ω ∈ regularAt (O.comap (e : K →+* L))) :
    kaehlerTransport e ω ∈ regularAt O := by
  change kaehlerTransportEquiv e ω ∈ regularAt O
  have hmap : (regularAt (O.comap (e : K →+* L))).map
      (kaehlerTransportEquiv e : Ω[K⁄ℂ] →ₗ[ℂ] Ω[L⁄ℂ]) ≤ regularAt O := by
    rw [regularAt, Submodule.map_span, Submodule.span_le]
    rintro _ ⟨_, ⟨a, ha, b, hb, rfl⟩, rfl⟩
    rw [ValuationSubring.mem_comap] at ha hb
    refine Submodule.subset_span ⟨e a, ha, e b, hb, ?_⟩
    rw [LinearEquiv.coe_coe, kaehlerTransportEquiv_apply, kaehlerTransport_smul,
      kaehlerTransport_D]
  exact hmap ⟨ω, hω, rfl⟩

/-- An isomorphism of `ℂ`-algebras carries holomorphic differentials to holomorphic
differentials. With `L = K` this is invariance under automorphisms. -/
theorem kaehlerTransport_mem_holomorphicSpace (e : K ≃ₐ[ℂ] L) {ω : Ω[K⁄ℂ]}
    (hω : ω ∈ holomorphicSpace K) : kaehlerTransport e ω ∈ holomorphicSpace L := by
  rw [mem_holomorphicSpace] at hω ⊢
  exact fun O hO => kaehlerTransport_mem_regularAt e O (hω _ (hO.comap e))

theorem holomorphicSpace_map (e : K ≃ₐ[ℂ] L) :
    (holomorphicSpace K).map (kaehlerTransportEquiv e : Ω[K⁄ℂ] →ₗ[ℂ] Ω[L⁄ℂ]) =
      holomorphicSpace L := by
  apply le_antisymm
  · rintro _ ⟨ω, hω, rfl⟩
    exact kaehlerTransport_mem_holomorphicSpace e hω
  · intro ω hω
    refine ⟨kaehlerTransport e.symm ω, kaehlerTransport_mem_holomorphicSpace e.symm hω, ?_⟩
    change kaehlerTransport e (kaehlerTransport e.symm ω) = ω
    simpa only [AlgEquiv.symm_symm] using kaehlerTransport_symm_apply e.symm ω

/-- The holomorphic differentials of isomorphic fields are isomorphic. -/
noncomputable def holomorphicSpaceEquiv (e : K ≃ₐ[ℂ] L) :
    holomorphicSpace K ≃ₗ[ℂ] holomorphicSpace L :=
  ((kaehlerTransportEquiv e).submoduleMap (holomorphicSpace K)).trans
    (LinearEquiv.ofEq _ _ (holomorphicSpace_map e))

@[simp] lemma holomorphicSpaceEquiv_apply (e : K ≃ₐ[ℂ] L) (ω : holomorphicSpace K) :
    (holomorphicSpaceEquiv e ω : Ω[L⁄ℂ]) = kaehlerTransport e ω :=
  rfl

end Transport

end CurveSymmetry

end


