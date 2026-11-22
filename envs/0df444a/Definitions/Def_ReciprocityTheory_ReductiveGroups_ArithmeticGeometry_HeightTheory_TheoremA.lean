-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_TheoremA
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_TheoremA
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:17:49.3549+00:00
-- url     : https://prove2.me/theorems/93740799-d4a5-4784-bc1e-b3dc01e0a655
-- title:
--   Theorem A
-- statement:
--   Definitions and structural lemmas for Theorem A, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/TheoremA.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.T0
open scoped TensorProduct BigOperators ComplexOrder
open NumberField
noncomputable def ratio {Ω V : Type*} [Field Ω] [AddCommGroup V] [Module Ω V] (f g : V) : Ω :=
  open Classical in if h : ∃ a : Ω, f = a • g then h.choose else 0
def IsNormDiscrete {Ω : Type*} [Field Ω] (v : AddValuation Ω (WithTop ℤ)) : Prop :=
  (∀ a : Ω, a ≠ 0 → v a ≠ ⊤) ∧ ∃ π : Ω, v π = 1
abbrev vRing {Ω : Type*} [Field Ω] (v : AddValuation Ω (WithTop ℤ)) : ValuationSubring Ω :=
  Valuation.valuationSubring v
def comapIncl {F Ω : Type*} [Field F] [Field Ω] (V : ValuationSubring Ω) (f : F →+* Ω) :
    V.comap f →+* V :=
  f.restrict (V.comap f) V fun _ hx => hx
instance comapIncl_isLocalHom {F Ω : Type*} [Field F] [Field Ω] (V : ValuationSubring Ω)
    (f : F →+* Ω) : IsLocalHom (comapIncl V f) := by
  constructor
  intro x hx
  obtain ⟨u, hu⟩ := isUnit_iff_exists_inv.mp hx
  have hu' : f (x : F) * (u : Ω) = 1 := congrArg Subtype.val hu
  have hx0 : (x : F) ≠ 0 := fun h => zero_ne_one (by rw [h, map_zero, zero_mul] at hu'; exact hu')
  have hinv : f ((x : F)⁻¹) = (u : Ω) := by rw [map_inv₀]; exact inv_eq_of_mul_eq_one_right hu'
  have hmem : (x : F)⁻¹ ∈ V.comap f := by rw [ValuationSubring.mem_comap, hinv]; exact u.2
  exact isUnit_iff_exists_inv.mpr ⟨⟨_, hmem⟩, Subtype.ext (mul_inv_cancel₀ hx0)⟩
noncomputable abbrev resAlg {F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω]
    (v : AddValuation Ω (WithTop ℤ)) :
    Algebra (IsLocalRing.ResidueField ((vRing v).comap (algebraMap F Ω)))
      (IsLocalRing.ResidueField (vRing v)) :=
  (IsLocalRing.ResidueField.map (comapIncl (vRing v) (algebraMap F Ω))).toAlgebra
def IsOver {K Ω : Type*} [Field K] [NumberField K] [Field Ω] [Algebra K Ω]
    (v : AddValuation Ω (WithTop ℤ)) (la : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) : Prop :=
  ∀ a : 𝓞 K, (0 < v (algebraMap K Ω (a : K)) ↔ a ∈ la.asIdeal)
def IsTrivOn (K : Type*) {Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]
    (v : AddValuation Ω (WithTop ℤ)) : Prop :=
  ∀ a : K, a ≠ 0 → v (algebraMap K Ω a) = 0
noncomputable def ramIdx {K Ω : Type*} [Field K] [NumberField K] [Field Ω] [Algebra K Ω]
    (v : AddValuation Ω (WithTop ℤ)) (la : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) : ℤ :=
  sInf {n : ℤ | ∃ a ∈ la.asIdeal, a ≠ 0 ∧ v (algebraMap K Ω (a : K)) = n}
noncomputable def logNorm {K : Type*} [Field K] [NumberField K]
    (la : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) : ℝ :=
  Real.log (Ideal.absNorm la.asIdeal : ℝ)
def LenLE (x : ℕ∞) (b : ℝ) : Prop := ∃ n : ℕ, x = n ∧ (n : ℝ) ≤ b
def PT {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω] (sg : K →+* ℂ) : Set (Ω →+* ℂ) :=
  {P | P.comp (algebraMap K Ω) = sg}
noncomputable def meanK {K : Type*} [Field K] [NumberField K] (F : (K →+* ℂ) → ℝ) : ℝ :=
  (∑ sg, F sg) / (Fintype.card (K →+* ℂ) : ℝ)
abbrev TVar (D N : ℕ) : Type := Fin (D + 1) × Fin (N + 1)
abbrev SVar (D N : ℕ) : Type := Unit ⊕ (Fin (D + 1) × Fin N)
abbrev OmS (Ω : Type) [Field Ω] (D N : ℕ) : Type := FractionRing (MvPolynomial (SVar D N) Ω)
noncomputable def sImg {Ω : Type} [Field Ω] {D N : ℕ} (j₀ : Fin (N + 1)) (x : Fin N → Ω)
    (p : TVar D N) : OmS Ω D N :=
  algebraMap (MvPolynomial (SVar D N) Ω) (OmS Ω D N)
    (Fin.succAboveCases (α := fun _ => MvPolynomial (SVar D N) Ω) j₀
      (if p.1 = 0 then MvPolynomial.X (Sum.inl ())
        else -∑ k, MvPolynomial.X (Sum.inr (p.1, k)) * MvPolynomial.C (x k))
      (fun k => MvPolynomial.X (Sum.inr (p.1, k))) p.2)
noncomputable def sHom {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] {D N : ℕ}
    (j₀ : Fin (N + 1)) (x : Fin N → Ω) : MvPolynomial (TVar D N) K →ₐ[K] OmS Ω D N :=
  MvPolynomial.aeval (sImg j₀ x)
variable (K : Type) [Field K] [NumberField K] (ι : Type) [Fintype ι]
  (Ω : ι → Type) [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  (WT : Type) [AddCommGroup WT]
  (A : ι → Type) [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  (𝒜 : (c : ι) → WT → Submodule (Ω c) (A c))
structure Data where

  D : ℕ

  N : ℕ

  T : ℕ

  i : ℕ
  g0 : ℕ

  cc : ℝ

  wL : WT
  wF : WT
  wde : WT

  ord : (c : ι) → AddValuation (Ω c) (WithTop ℤ) → WT → A c → ℤ

  nrm : (c : ι) → WT → A c → (Ω c →+* ℂ) → ℝ

  M : Submodule (𝓞 K) (∀ c, A c)
  WW : Submodule (𝓞 K) (∀ c, A c)
  Thp : Submodule (𝓞 K) (∀ c, A c)
  Th0 : Submodule (𝓞 K) (∀ c, A c)
  Thk : Submodule (𝓞 K) (∀ c, A c)

  w : Fin (N + 1) → ∀ c, A c

  jc : ι → Fin (N + 1)
  np : ℕ
  thp : Fin np → ∀ c, A c
  n0 : ℕ
  th0 : Fin n0 → ∀ c, A c
  nk : ℕ
  thk : Fin nk → ∀ c, A c

  et : ∀ c, A c
  ta1 : ∀ c, A c
  ta2 : ∀ c, A c

  nu : IsDedekindDomain.HeightOneSpectrum (𝓞 K) → ℝ

  ip : (K →+* ℂ) → (∀ c, A c) → (∀ c, A c) → ℂ

  wsize : WT → ℝ

  DF : ℝ

  PN : ℝ
  PQ : ℝ
  tableDegreeThreeBase : ℝ
  PP0' : ℝ
  Pd : ℝ
  Gc : ℝ
  PI4 : ℝ
  Pet : ℝ
  tableLineDegreeFive : ℝ
  tableLineDegreeTwo : ℝ
  Prw : ℝ
  PO : ℝ
  f : ℝ
  r : ℝ
namespace Data
variable {K ι Ω WT A}
variable (d : Data K ι Ω WT A)
def G1 : WT := d.wL - d.wde
def G2 : WT := (d.D + 4 : ℕ) • d.wL - d.wF
def F0 : WT := d.wF + d.D • d.wL
def ka : WT := d.wF + d.T • d.wL
def n1 : ℕ := d.i * d.g0
noncomputable def x (c : ι) (k : Fin d.N) : Ω c :=
  ratio (Ω := Ω c) (d.w ((d.jc c).succAbove k) c) (d.w (d.jc c) c)
def Theta : Submodule (𝓞 K) (∀ c, A c) :=
  d.WW ^ d.T * d.Thp + d.WW ^ (d.T - d.D) * d.Th0 + d.Thk
noncomputable def rk : ℕ := Module.finrank K (Submodule.span K (d.M : Set (∀ c, A c)))
def ResCond (c : ι) (v : AddValuation (Ω c) (WithTop ℤ)) (n : ℕ) : Prop :=
  letI := resAlg (F := K) v
  Algebra.trdeg (IsLocalRing.ResidueField ((vRing v).comap (algebraMap K (Ω c))))
      (IsLocalRing.ResidueField (vRing v)) = n ∧
  ∃ j0 : Fin (d.N + 1), d.w j0 c ≠ 0 ∧
    (∀ j, 0 ≤ v (ratio (Ω := Ω c) (d.w j c) (d.w j0 c))) ∧
    Algebra.trdeg (IsLocalRing.ResidueField ((vRing v).comap (algebraMap K (Ω c))))
      (IntermediateField.adjoin
        (IsLocalRing.ResidueField ((vRing v).comap (algebraMap K (Ω c))))
        {r | ∃ j, ∃ h : ratio (Ω := Ω c) (d.w j c) (d.w j0 c) ∈ vRing v,
          r = IsLocalRing.residue (vRing v) ⟨_, h⟩}) = n
def admitted (c : ι) (v : AddValuation (Ω c) (WithTop ℤ)) : Prop :=
  IsNormDiscrete v ∧
    ((∃ la, IsOver (K := K) v la ∧ d.ResCond c v d.D) ∨
      (IsTrivOn K v ∧ d.ResCond c v (d.D - 1)))
noncomputable def supN (sg : K →+* ℂ) (G : WT) (f : ∀ c, A c) : ℝ :=
  ⨆ p : (Σ c, PT (Ω := Ω c) sg), d.nrm p.1 G (f p.1) p.2
noncomputable def supNc (c : ι) (sg : K →+* ℂ) (G : WT) (fc : A c) : ℝ :=
  ⨆ P : PT (Ω := Ω c) sg, d.nrm c G fc P
noncomputable def be (c : ι) (P : Ω c →+* ℂ) : ℝ :=
  Real.sqrt (∑ j, d.nrm c d.wL (d.w j c) P ^ 2)
def ST (c : ι) (sg : K →+* ℂ) (t : Fin d.D → Fin (d.N + 1) → ℂ) : Set (Ω c →+* ℂ) :=
  {P | P ∈ PT sg ∧ ∀ i, ∑ j, t i j * P (ratio (Ω := Ω c) (d.w j c) (d.w (d.jc c) c)) = 0}
noncomputable def sH (c : ι) : MvPolynomial (TVar d.D d.N) K →ₐ[K] OmS (Ω c) d.D d.N :=
  sHom (d.jc c) (d.x c)
noncomputable abbrev KT (c : ι) : IntermediateField K (OmS (Ω c) d.D d.N) :=
  IntermediateField.adjoin K (Set.range (sImg (D := d.D) (d.jc c) (d.x c)))
noncomputable def delc (c : ι) : ℕ := Module.finrank (d.KT c) (OmS (Ω c) d.D d.N)
noncomputable def del : ℕ := ∑ c, d.delc c
def a0 : ℕ := d.T - d.D
noncomputable def sP (i : Fin (d.D + 1)) : MvPolynomial (TVar d.D d.N) (∀ c, A c) :=
  ∑ j, MvPolynomial.X (i, j) * MvPolynomial.C (d.w j)
noncomputable def sPow (α : Fin d.D → Fin (d.T + 1)) : MvPolynomial (TVar d.D d.N) (∀ c, A c) :=
  ∏ k, d.sP k.succ ^ (α k : ℕ)
def absα (α : Fin d.D → Fin (d.T + 1)) : ℕ := ∑ k, (α k : ℕ)
def PH : ℝ := d.PP0' + d.PN + d.tableLineDegreeFive + d.tableLineDegreeTwo + d.PI4 + d.Prw
noncomputable def PD : ℝ := 2 * d.Gc + d.Prw + d.tableDegreeThreeBase + 3 / 2 * (d.Pd + d.PO)
noncomputable def P1' : ℝ := 60 * d.Gc + 180 * d.PH + 22 * (d.PD + d.PQ)
def P2 : ℝ := 5 * d.Gc * d.f * d.r ^ 2 + d.Pd
noncomputable def P3 : ℝ := d.Pet / 2
noncomputable def n96 : ℕ :=
  8 * ((d.D + 2) * (d.N + 1)) ^ 2 * (d.D + 1) * d.del * (1 + ⌈d.PO⌉₊)
noncomputable def nrm2 (sg : K →+* ℂ) (f : ∀ c, A c) : ℝ := Real.sqrt (d.ip sg f f).re
noncomputable def sphMeasure : MeasureTheory.Measure
    (Fin d.D → Metric.sphere (0 : EuclideanSpace ℂ (Fin (d.N + 1))) 1) :=
  MeasureTheory.Measure.pi fun _ => (MeasureTheory.volume :
    MeasureTheory.Measure (EuclideanSpace ℂ (Fin (d.N + 1)))).toSphere
end Data
namespace Data
variable {K ι Ω WT A}
variable (d : Data K ι Ω WT A)
noncomputable def thetaGenerator (α : Fin d.D → Fin (d.T + 1)) (k : Fin d.np) :
    MvPolynomial (TVar d.D d.N) (∀ c, A c) :=
  d.sPow α * d.sP 0 ^ (d.T - d.absα α) * MvPolynomial.C (d.thp k)
noncomputable def genZ (α : Fin d.D → Fin (d.T + 1)) (k : Fin d.n0) :
    MvPolynomial (TVar d.D d.N) (∀ c, A c) :=
  d.sPow α * MvPolynomial.C (d.th0 k)
structure Ax : Type 1 where

  nonempty : Nonempty ι
  tower : ∀ c, IsScalarTower K (Ω c) (A c)
  towerO : ∀ c, IsScalarTower (𝓞 K) K (A c)
  D_ge : 3 ≤ d.D
  fg : ∀ c, (⊤ : IntermediateField K (Ω c)).FG
  trdeg : ∀ c, Algebra.trdeg K (Ω c) = d.D
  algClosed : ∀ c (a : Ω c), IsAlgebraic K a → a ∈ (algebraMap K (Ω c)).range
  graded : ∀ c, SetLike.GradedMonoid (𝒜 c)
  finrank_one : ∀ c G, Module.finrank (Ω c) (𝒜 c G) = 1
  mul_ne_zero : ∀ c {G G' : WT} {f g : A c}, f ∈ 𝒜 c G → g ∈ 𝒜 c G' → f ≠ 0 → g ≠ 0 →
    f * g ≠ 0

  M_mem : ∀ f ∈ d.M, ∀ c, f c ∈ 𝒜 c d.ka
  M_fg : d.M.FG
  WW_span : d.WW = Submodule.span (𝓞 K) (Set.range d.w)
  w_mem : ∀ j c, d.w j c ∈ 𝒜 c d.wL
  w_base : ∀ c, d.w (d.jc c) c ≠ 0
  Thp_span : d.Thp = Submodule.span (𝓞 K) (Set.range d.thp)
  thp_mem : ∀ k c, d.thp k c ∈ 𝒜 c d.wF
  Th0_span : d.Th0 = Submodule.span (𝓞 K) (Set.range d.th0)
  thetaMem : ∀ k c, d.th0 k c ∈ 𝒜 c d.F0
  Thk_span : d.Thk = Submodule.span (𝓞 K) (Set.range d.thk)
  Thk_le : d.Thk ≤ d.M
  et_mem : ∀ c, d.et c ∈ 𝒜 c (d.n1 • d.wde)
  firstSectionMem : ∀ c, d.ta1 c ∈ 𝒜 c ((2 : ℕ) • d.G1)
  secondSectionMem : ∀ c, d.ta2 c ∈ 𝒜 c d.G2
  et_ne : ∀ c, d.et c ≠ 0
  firstSectionNeZero : ∀ c, d.ta1 c ≠ 0
  secondSectionNeZero : ∀ c, d.ta2 c ≠ 0
  Theta_le : d.Theta ≤ d.M

  ord_mul : ∀ c v, d.admitted c v → ∀ {G G' : WT} {f g : A c}, f ∈ 𝒜 c G → g ∈ 𝒜 c G' →
    f ≠ 0 → g ≠ 0 → d.ord c v (G + G') (f * g) = d.ord c v G f + d.ord c v G' g
  ord_smul : ∀ c v, d.admitted c v → ∀ {G : WT} {f : A c} (a : Ω c), f ∈ 𝒜 c G → f ≠ 0 → a ≠ 0 →
    ((d.ord c v G (a • f) : ℤ) : WithTop ℤ) = v a + (d.ord c v G f : WithTop ℤ)

  nrm_pos : ∀ c {G : WT} {f : A c} (P : Ω c →+* ℂ), f ∈ 𝒜 c G → f ≠ 0 → 0 < d.nrm c G f P
  nrm_zero : ∀ c (G : WT) (P : Ω c →+* ℂ), d.nrm c G 0 P = 0
  nrm_mul : ∀ c {G G' : WT} {f g : A c} (P : Ω c →+* ℂ), f ∈ 𝒜 c G → g ∈ 𝒜 c G' →
    f ≠ 0 → g ≠ 0 → d.nrm c (G + G') (f * g) P = d.nrm c G f P * d.nrm c G' g P
  nrm_smul : ∀ c {G : WT} {f : A c} (P : Ω c →+* ℂ) (a : Ω c), f ∈ 𝒜 c G → f ≠ 0 → a ≠ 0 →
    d.nrm c G (a • f) P = ‖P a‖ * d.nrm c G f P
  nrm_conj : ∀ c (G : WT) (f : A c) (P : Ω c →+* ℂ),
    d.nrm c G f ((starRingEnd ℂ).comp P) = d.nrm c G f P
  bdd : ∀ (sg : K →+* ℂ) (G : WT) (f : ∀ c, A c),
    ((f ∈ d.M ∧ G = d.ka) ∨ (f ∈ d.WW ∧ G = d.wL) ∨ (f ∈ d.Thp ∧ G = d.wF) ∨
      (f ∈ d.Th0 ∧ G = d.F0) ∨ (f = d.et ∧ G = d.n1 • d.wde) ∨
      (f = d.ta1 ∧ G = (2 : ℕ) • d.G1) ∨ (f = d.ta2 ∧ G = d.G2)) →
    BddAbove (Set.range fun p : (Σ c, PT (Ω := Ω c) sg) => d.nrm p.1 G (f p.1) p.2)

  a1 : ∀ c, ∃ J : Fin d.D → Fin d.N,
    LinearIndependent (Ω c) fun k => KaehlerDifferential.D K (Ω c) (d.x c (J k))

  ord_nonneg_M : ∀ c v, d.admitted c v → ∀ f ∈ d.M, f c ≠ 0 → 0 ≤ d.ord c v d.ka (f c)
  ord_nonneg_WW : ∀ c v, d.admitted c v → ∀ f ∈ d.WW, f c ≠ 0 → 0 ≤ d.ord c v d.wL (f c)
  ord_nonneg_Thp : ∀ c v, d.admitted c v → ∀ f ∈ d.Thp, f c ≠ 0 → 0 ≤ d.ord c v d.wF (f c)
  ordThetaNonneg : ∀ c v, d.admitted c v → ∀ f ∈ d.Th0, f c ≠ 0 → 0 ≤ d.ord c v d.F0 (f c)
  ord_nonneg_et : ∀ c v, d.admitted c v → 0 ≤ d.ord c v (d.n1 • d.wde) (d.et c)
  ordDoubleFirstSection_nonneg : ∀ c v, d.admitted c v → 0 ≤ d.ord c v ((2 : ℕ) • d.G1) (d.ta1 c)
  ordSecondSectionNonneg : ∀ c v, d.admitted c v → 0 ≤ d.ord c v d.G2 (d.ta2 c)

  nu_nonneg : ∀ la, 0 ≤ d.nu la
  nu_fin : (Function.support d.nu).Finite
  nu_sum : (∑ᶠ la, d.nu la * logNorm la) / (Module.finrank ℚ K : ℝ) ≤ d.PN * d.wsize d.wL
  minOrd_le_finite : ∀ c v la, d.admitted c v → IsOver (K := K) v la →
    ((⨅ j : {j // d.w j c ≠ 0}, d.ord c v d.wL (d.w j c) : ℤ) : ℝ) ≤
      (ramIdx (K := K) v la : ℝ) * d.nu la +
        d.cc / (2 * d.i) * d.ord c v (d.n1 • d.wde) (d.et c)
  minOrd_le_trivial : ∀ c v, d.admitted c v → IsTrivOn K v →
    ((⨅ j : {j // d.w j c ≠ 0}, d.ord c v d.wL (d.w j c) : ℤ) : ℝ) ≤
      d.cc / (2 * d.i) * d.ord c v (d.n1 • d.wde) (d.et c)
  a3' : ∀ c {G : WT} {f : A c}, f ∈ 𝒜 c G → f ≠ 0 → {v | d.admitted c v ∧ d.ord c v G f ≠ 0}.Finite

  sel : Fin d.del → Fin d.np
  a4 : ∃ e : ∀ c, A c, (∀ c, e c ∈ 𝒜 c d.wF ∧ e c ≠ 0) ∧
    (∀ p : Fin d.del → MvPolynomial (TVar d.D d.N) K,
      (∀ c, ∑ k, d.sH c (p k) *
        algebraMap (Ω c) (OmS (Ω c) d.D d.N) (ratio (Ω := Ω c) (d.thp (sel k) c) (e c)) = 0) →
      ∀ k, p k = 0) ∧
    (∀ y : ∀ c, OmS (Ω c) d.D d.N, ∃ q : MvPolynomial (TVar d.D d.N) K, (∀ c, d.sH c q ≠ 0) ∧
      ∃ p : Fin d.del → MvPolynomial (TVar d.D d.N) K, ∀ c, d.sH c q * y c = ∑ k, d.sH c (p k) *
        algebraMap (Ω c) (OmS (Ω c) d.D d.N) (ratio (Ω := Ω c) (d.thp (sel k) c) (e c)))

  K1 : Type
  [twistedCentralTestFunction : Field K1]
  [numberFieldDegreeOne : NumberField K1]
  [fieldDegreeAxiom : Algebra K K1]
  MD : Submodule K1 (K1 ⊗[K] (∀ c, A c))
  MD_le : MD ≤ Submodule.span K1 ((fun a => (1 : K1) ⊗ₜ[K] a) '' (d.M : Set (∀ c, A c)))
  a5 : ∀ m ∈ MD, ∃ q : MvPolynomial (TVar d.D d.N) K1, q ≠ 0 ∧
    ∃ c1 : (Fin d.D → Fin (d.T + 1)) → Fin d.del → MvPolynomial (TVar d.D d.N) K1,
    ∃ c2 : (Fin d.D → Fin (d.T + 1)) → Fin d.n0 → MvPolynomial (TVar d.D d.N) K1,
      MvPolynomial.map (algebraMap K1 (K1 ⊗[K] (∀ c, A c))) q * MvPolynomial.C m =
        (∑ α ∈ Finset.univ.filter (fun α => d.absα α < d.a0), ∑ k,
          MvPolynomial.map (algebraMap K1 (K1 ⊗[K] (∀ c, A c))) (c1 α k) *
            MvPolynomial.map (Algebra.TensorProduct.includeRight :
              (∀ c, A c) →ₐ[K] K1 ⊗[K] (∀ c, A c)).toRingHom (d.thetaGenerator α (sel k))) +
        (∑ α ∈ Finset.univ.filter (fun α => d.absα α = d.a0), ∑ k,
          MvPolynomial.map (algebraMap K1 (K1 ⊗[K] (∀ c, A c))) (c2 α k) *
            MvPolynomial.map (Algebra.TensorProduct.includeRight :
              (∀ c, A c) →ₐ[K] K1 ⊗[K] (∀ c, A c)).toRingHom (d.genZ α k))

  rank_le_alt : d.rk ≤ d.del * (d.T + 2 * d.D + 6).choose d.D
  corank_le_alt : ((d.rk - Module.finrank K1 MD : ℕ) : ℝ) ≤ d.D * (d.D + 6) * d.rk / d.T

  th : Fin (d.rk - Module.finrank K1 MD) → Fin d.nk
  th_inj : Function.Injective th
  q : IsDedekindDomain.HeightOneSpectrum (𝓞 K1) → ℝ
  q_nonneg : ∀ la1, 0 ≤ q la1
  q_fin : (Function.support q).Finite
  a7 : ∀ la1 : IsDedekindDomain.HeightOneSpectrum (𝓞 K1),
    let R1 := (la1.valuationSubringAtPrime K1).toSubring
    letI : Module R1 (K1 ⊗[K] (∀ c, A c)) := Module.compHom _ R1.subtype
    let M1 := Submodule.span R1 ((fun a => (1 : K1) ⊗ₜ[K] a) '' (d.M : Set (∀ c, A c)))
    let N1 := (Submodule.span R1 (MD : Set (K1 ⊗[K] (∀ c, A c))) ⊓ M1) ⊔
      Submodule.span R1 (Set.range fun j => (1 : K1) ⊗ₜ[K] d.thk (th j))
    LenLE (Module.length R1 (M1 ⧸ N1.comap M1.subtype))
      ((la1.asIdeal.ramificationIdx (𝓞 K) : ℕ) * q la1)
  length_sum_le_alt : (∑ᶠ la1, (la1.asIdeal.ramificationIdx (𝓞 K) : ℝ) * q la1 * logNorm la1) /
      (Module.finrank ℚ K1 : ℝ) ≤ (d.rk - Module.finrank K1 MD : ℕ) * d.PQ * d.wsize d.ka

  a8 : ∀ f ∈ d.M, f ≠ 0 →
    -(d.tableDegreeThreeBase * d.wsize d.ka) ≤ meanK fun sg => Real.log (d.supN sg d.ka f)
  a8' : ∀ c, ∀ g ∈ Submodule.span (𝓞 K)
      (Set.range fun s : Fin d.n96 → Fin (d.N + 1) => ∏ k, d.w (s k)), g c ≠ 0 →
    -(d.PP0' * d.n96 * d.wsize d.wL) ≤
      meanK fun sg => Real.log (d.supNc c sg (d.n96 • d.wL) (g c))

  ip_add : ∀ sg f g h, d.ip sg f (g + h) = d.ip sg f g + d.ip sg f h
  ip_smul : ∀ sg f g (k : K), d.ip sg f (k • g) = sg k * d.ip sg f g
  ip_conj : ∀ sg f g, d.ip sg g f = star (d.ip sg f g)
  ip_conjEmb : ∀ sg f g, d.ip ((starRingEnd ℂ).comp sg) f g = star (d.ip sg f g)
  ip_posDef : ∀ sg (n : ℕ) (v : Fin n → ∀ c, A c), (∀ k, v k ∈ d.M) → LinearIndependent K v →
    (Matrix.of fun a b => d.ip sg (v a) (v b)).PosDef
  a9 : ∀ sg, ∀ f ∈ d.M, d.nrm2 sg f ≤ d.supN sg d.ka f ∧
    d.supN sg d.ka f ≤ Real.exp (d.Pd / 2) * d.nrm2 sg f
  log_rank_le : Real.log d.rk ≤ d.Pd

  logSup_w_le : meanK (fun sg => ⨆ j, Real.log (d.supN sg d.wL (d.w j))) ≤ d.Gc * d.wsize d.wL
  logSup_thp_le : ∀ k, meanK (fun sg => Real.log (d.supN sg d.wF (d.thp k))) ≤ d.Gc * d.wsize d.wF
  meanLogSupTheta : ∀ k, meanK (fun sg => Real.log (d.supN sg d.F0 (d.th0 k))) ≤ d.Gc * d.wsize d.F0
  logSup_thk_le : ∀ k, meanK (fun sg => Real.log (d.supN sg d.ka (d.thk k))) ≤ d.Gc * d.wsize d.ka
  meanLogSupFirst : meanK (fun sg => Real.log (d.supN sg ((2 : ℕ) • d.G1) d.ta1)) ≤
    2 * d.PI4 * d.D * d.wsize d.wL
  meanLogSupSecond : meanK (fun sg => Real.log (d.supN sg d.G2 d.ta2)) ≤ d.PI4 * d.D * d.wsize d.wL
  logSup_et_le : meanK (fun sg => Real.log (d.supN sg (d.n1 • d.wde) d.et)) / d.i ≤ d.Pet
  log_beta_lower : ∀ c (P : Ω c →+* ℂ),
    -Real.log (d.be c P) ≤
      d.tableLineDegreeFive * d.DF + d.cc / d.i * (-Real.log (d.nrm c (d.n1 • d.wde) (d.et c) P)) + d.cc * d.tableLineDegreeTwo

  T_ge : 11 * d.D ^ 2 ≤ d.T
  i_ge : 1 ≤ d.i
  g_zero_ge_ask_sum : 1 ≤ d.g0
  Tcg0 : (d.T : ℝ) * d.cc * d.g0 ≤ 1
  cc_nonneg : 0 ≤ d.cc
  cc_le : d.cc ≤ 1
  ccg0 : d.cc * d.g0 ≤ 1 / 2
  size_TL : (d.T : ℝ) * d.wsize d.wL ≤ 2 * d.wsize d.ka
  size_F : d.wsize d.wF ≤ (d.D + 2) * d.wsize d.wL + 5 * d.f * d.r ^ 2 * d.T
  sizeBaseIdentity : ((d.T : ℝ) - d.D) * d.wsize d.wL + d.wsize d.F0 = d.wsize d.ka + d.T - d.D
  sizeBaseNonneg : 0 ≤ d.wsize d.F0
  size_alt : (d.T : ℝ) ≤ d.wsize d.ka
  size_L : 1 ≤ d.wsize d.wL
  DF_le : d.DF ≤ d.wsize d.wL
  rw_le : Real.log (d.N + 1 : ℕ) + 1 / 2 ≤ d.Prw * (d.wsize d.wL - 1)
  del_le : Real.log d.del ≤ d.Pd
  nK_le : Real.log (Module.finrank ℚ K) ≤ d.PO
  rd_le : Real.log (|(NumberField.discr K : ℝ)| ^ (1 / (Module.finrank ℚ K : ℝ))) ≤ d.PO
  P_ge : 1 ≤ d.PN ∧ 1 ≤ d.PQ ∧ 1 ≤ d.tableDegreeThreeBase ∧ 1 ≤ d.PP0' ∧ 1 ≤ d.Pd ∧ 1 ≤ d.Gc ∧ 1 ≤ d.PI4 ∧
    1 ≤ d.Pet ∧ 1 ≤ d.tableLineDegreeFive ∧ 1 ≤ d.tableLineDegreeTwo ∧ 1 ≤ d.Prw ∧ 1 ≤ d.PO
  f_nonneg : 0 ≤ d.f
  r_nonneg : 0 ≤ d.r

  a12 : Submodule.span K (d.Thk : Set (∀ c, A c)) = Submodule.span K (d.M : Set (∀ c, A c))

  a13 : ∀ c (sg : K →+* ℂ) {G : WT} {f : A c}, f ∈ 𝒜 c G → f ≠ 0 →
    AEMeasurable (fun t : Fin d.D → Metric.sphere (0 : EuclideanSpace ℂ (Fin (d.N + 1))) 1 =>
      ∑ᶠ P ∈ d.ST c sg (fun i j => (t i : EuclideanSpace ℂ (Fin (d.N + 1))) j),
        Real.log (d.nrm c G f P)) d.sphMeasure
end Data
open Data in

def TheoremA : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (ι : Type) [Fintype ι]
    (Ω : ι → Type) [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
    (WT : Type) [AddCommGroup WT]
    (A : ι → Type) [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
    [∀ c, Algebra (𝓞 K) (A c)]
    (𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)) (d : Data K ι Ω WT A), d.Ax (𝒜 := 𝒜) →
    ∃ r : IsDedekindDomain.HeightOneSpectrum (𝓞 K) → ℝ,
      (∀ la, 0 ≤ r la) ∧ (Function.support r).Finite ∧
      (∀ la (e : ℕ), (d.T : ℝ) * d.nu la ≤ e →
        let R := (la.valuationSubringAtPrime K).toSubring
        letI : Module R (∀ c, A c) := Module.compHom _ R.subtype
        let Θ := Submodule.span R (d.Theta : Set (∀ c, A c))
        let X := Submodule.span R
          ((la.asIdeal ^ e • d.M : Submodule (𝓞 K) (∀ c, A c)) : Set (∀ c, A c))
        LenLE (Module.length R (↥(X ⊔ Θ) ⧸ Θ.comap (X ⊔ Θ).subtype)) (r la)) ∧
      (∑ᶠ la, r la * logNorm la) / (Module.finrank ℚ K : ℝ) ≤
        d.rk * (d.P1' * d.D ^ 2 * d.wsize d.ka / d.T + d.P2 * d.T + d.P3 * d.T * d.cc)
end ReciprocityTheory.ChartRestriction.G.T0


