-- Prove2me | Definitions.Def_AutomorphicForm_LocalOrbitalBase
-- name    : AutomorphicForm_LocalOrbitalBase
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.014713+00:00
-- url     : https://prove2.me/theorems/95c54c89-f13a-543c-a332-1449abd9db7f
-- title:
--   Local test functions, Haar measure, orbital integrals on GL(2)
-- statement:
--   Throughout, $K$ is a number field and $v$ a finite place, i.e. a height-one prime of $\mathcal O_K$, with completion $K_v$ and valuation ring $\mathcal O_v$. For a subset $U$ of a ring $A$, `integralMatrixSet` is the set of $2\times 2$ matrices with all entries in $U$, and `integralUnitsSet` the set of $g \in \mathrm{GL}_2(A)$ such that both $g$ and $g^{-1}$ have all entries in $U$; these are shown to be open, resp. compact, when $U$ is, by identifying the unit set with a preimage under `Units.embedProduct`. Taking $U = \mathcal O_v$ gives `localIntegralSet`, a compact open subset of $\mathrm{GL}_2(K_v)$ containing $1$, packaged as a `PositiveCompacts` datum; `localHaar` is the Haar measure on $\mathrm{GL}_2(K_v)$ for the Borel $\sigma$-algebra normalised so that this set has measure $1$. A local test function at $v$ is a locally constant, compactly supported $f_v \colon \mathrm{GL}_2(K_v) \to \mathbb C$; `localAt` is the composite projection $\mathrm{GL}_2(\mathbb A_K) \to \mathrm{GL}_2(K_v)$.
--
--   Orbital integrals are introduced as a relation, not a function. Given $\gamma$, an arbitrary measure $\tau$ on the centraliser of $\{\gamma\}$, and $f_v$, a real function $w$ is a section function when $w \ge 0$, $w$ is measurable with compact support, and $\int_{T_\gamma} w(tx)\,d\tau = 1$ for every $x$ with $f_v(x^{-1}\gamma x) \ne 0$; then $I \in \mathbb C$ is an orbital integral when $I = \int f_v(x^{-1}\gamma x) w(x)\, d\mu_v$ for some such $w$. Nothing about existence, uniqueness or convergence is asserted; the zero function admits $I = 0$ and not $I = 1$.
--
--   Adelically, `unitFinSet` is the set of finite-adelic matrices integral at every place, equal to `finiteIntegralGL2`; bi-invariance under a subgroup $U$ means $f(ug) = f(g) = f(gu)$ for $u \in U$; `IsUnitFactorizableAt U S f` adds to bi-invariance a factorisation $f = f_\infty \cdot f_{\mathrm{fin}}$ with $f_\infty$ an archimedean test factor, $f_{\mathrm{fin}}$ locally constant with compact support, given by $\prod_{v \in S} f_v$ on adeles integral outside $S$ and zero elsewhere. `IsIntegralLevel U` requires each $u \in U$ to be trivial archimedeally and integral finitely; the level-one group intersected with the archimedean kernel qualifies. Finally, $g \in \mathrm{GL}_2(A)$ is regular semisimple when the discriminant $\mathrm{tr}(g)^2 - 4\det(g)$ is a unit, a condition invariant under conjugation and, over a field, equivalent to its non-vanishing.
--
--   **Relation to Mathlib.** The Haar measure, `PositiveCompacts` and Borel machinery are Mathlib's; the notions of local, archimedean and finite test factors, section functions, orbital integrals, integral levels and regular semisimplicity for $\mathrm{GL}_2$ are the project's own definitions.
--
--   **Where it is used.** These definitions supply the local harmonic-analytic vocabulary on $\mathrm{GL}_2$ over completions and adeles of a number field used in the automorphic side of the argument, where test functions factorised over places and orbital integrals at regular semisimple elements enter trace computations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AutomorphicForm_LocalOrbitalBase.lean

import Definitions.Def_AutomorphicForm_FactorizableTestFn

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain MeasureTheory TopologicalSpace

noncomputable section

namespace AutomorphicForm

section IntegralUnits

variable {A : Type*}

def integralMatrixSet (U : Set A) : Set (Matrix (Fin 2) (Fin 2) A) := {m | ∀ i j, m i j ∈ U}

theorem integralMatrixSet_eq_pi (U : Set A) :
    integralMatrixSet U = Set.pi Set.univ fun _ : Fin 2 => Set.pi Set.univ fun _ : Fin 2 => U := by
  ext m
  exact ⟨fun h i _ j _ => h i j, fun h i j => h i (Set.mem_univ _) j (Set.mem_univ _)⟩

theorem isCompact_integralMatrixSet [TopologicalSpace A] {U : Set A} (hU : IsCompact U) :
    IsCompact (integralMatrixSet U) := by
  rw [integralMatrixSet_eq_pi]
  exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hU

theorem isOpen_integralMatrixSet [TopologicalSpace A] {U : Set A} (hU : IsOpen U) : IsOpen (integralMatrixSet U) := by
  rw [integralMatrixSet_eq_pi]
  exact isOpen_set_pi Set.finite_univ fun _ _ => isOpen_set_pi Set.finite_univ fun _ _ => hU

variable [CommRing A]

def integralUnitsSet (U : Set A) : Set (GL (Fin 2) A) :=
  {g | (g : Matrix (Fin 2) (Fin 2) A) ∈ integralMatrixSet U ∧
    ((g⁻¹ : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) ∈ integralMatrixSet U}

theorem mem_integralUnitsSet {U : Set A} {g : GL (Fin 2) A} :
    g ∈ integralUnitsSet U ↔ (∀ i j, (g : Matrix (Fin 2) (Fin 2) A) i j ∈ U) ∧
      ∀ i j, ((g⁻¹ : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) i j ∈ U :=
  Iff.rfl

theorem one_mem_integralUnitsSet {U : Set A} (h0 : (0 : A) ∈ U) (h1 : (1 : A) ∈ U) :
    (1 : GL (Fin 2) A) ∈ integralUnitsSet U := by
  have hmat : (1 : Matrix (Fin 2) (Fin 2) A) ∈ integralMatrixSet U := fun i j => by
    by_cases h : i = j
    · subst h; rw [Matrix.one_apply_eq]; exact h1
    · rw [Matrix.one_apply_ne h]; exact h0
  refine ⟨?_, ?_⟩
  · rw [Units.val_one]; exact hmat
  · rw [inv_one, Units.val_one]; exact hmat

theorem integralUnitsSet_eq_preimage (U : Set A) :
    integralUnitsSet U = (Units.embedProduct (Matrix (Fin 2) (Fin 2) A)) ⁻¹'
      (integralMatrixSet U ×ˢ (MulOpposite.op '' integralMatrixSet U)) := by
  ext g
  simp only [integralUnitsSet, Set.mem_setOf_eq, Set.mem_preimage, Units.embedProduct_apply,
    Set.mem_prod, Set.mem_image]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, _, h2, rfl⟩
  · rintro ⟨h1, m, hm, hm'⟩
    refine ⟨h1, ?_⟩
    have : m = ((g⁻¹ : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) := MulOpposite.op_injective hm'
    rw [← this]
    exact hm

theorem isCompact_integralUnitsSet [TopologicalSpace A] [IsTopologicalRing A] [T2Space A] {U : Set A}
    (hU : IsCompact U) :
    IsCompact (integralUnitsSet U) := by
  rw [integralUnitsSet_eq_preimage]
  exact Units.isClosedEmbedding_embedProduct.isCompact_preimage
    ((isCompact_integralMatrixSet hU).prod
      ((isCompact_integralMatrixSet hU).image MulOpposite.continuous_op))

theorem isOpen_integralUnitsSet [TopologicalSpace A] [IsTopologicalRing A] [T2Space A] {U : Set A}
    (hU : IsOpen U) : IsOpen (integralUnitsSet U) := by
  rw [integralUnitsSet_eq_preimage]
  exact ((isOpen_integralMatrixSet hU).prod
    (MulOpposite.opHomeomorph.isOpenMap _ (isOpen_integralMatrixSet hU))).preimage
    Units.continuous_embedProduct

end IntegralUnits

section Local

variable (K : Type*) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

def IsLocalTestFn (fv : GL (Fin 2) (v.adicCompletion K) → ℂ) : Prop :=
  IsLocallyConstant fv ∧ HasCompactSupport fv

theorem isLocalTestFn_zero : IsLocalTestFn K v (fun _ => 0) :=
  ⟨IsLocallyConstant.const 0, HasCompactSupport.zero⟩

def localAt : GL (Fin 2) (AdeleRing (𝓞 K) K) →* GL (Fin 2) (v.adicCompletion K) :=
  (AdelicLevel.finComponent (𝓞 K) K v).comp (AdelicLevel.glFin (𝓞 K) K)

theorem continuous_localAt : Continuous (localAt K v) :=
  (AdelicLevel.continuous_finComponent (𝓞 K) K v).comp (AdelicLevel.continuous_glFin (𝓞 K) K)

def localIntegralSet : Set (GL (Fin 2) (v.adicCompletion K)) :=
  integralUnitsSet (v.adicCompletionIntegers K : Set (v.adicCompletion K))

theorem mem_localIntegralSet {g : GL (Fin 2) (v.adicCompletion K)} :
    g ∈ localIntegralSet K v ↔
      (∀ i j, (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j ∈ v.adicCompletionIntegers K) ∧
      ∀ i j, ((g⁻¹ : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j
        ∈ v.adicCompletionIntegers K :=
  Iff.rfl

theorem one_mem_localIntegralSet : (1 : GL (Fin 2) (v.adicCompletion K)) ∈ localIntegralSet K v :=
  one_mem_integralUnitsSet (zero_mem _) (one_mem _)

theorem isCompact_localIntegralSet : IsCompact (localIntegralSet K v) :=
  isCompact_integralUnitsSet
    (isCompact_iff_compactSpace.2 (AdelicHaar.compactSpace_adicCompletionIntegers (𝓞 K) K v))

theorem isOpen_localIntegralSet : IsOpen (localIntegralSet K v) :=
  isOpen_integralUnitsSet ((AdelicHaar.fact_isOpen_adicCompletionIntegers (𝓞 K) K).out v)

def localIntegralCompacts : PositiveCompacts (GL (Fin 2) (v.adicCompletion K)) where
  carrier := localIntegralSet K v
  isCompact' := isCompact_localIntegralSet K v
  interior_nonempty' := by
    rw [(isOpen_localIntegralSet K v).interior_eq]
    exact ⟨1, one_mem_localIntegralSet K v⟩

theorem coe_localIntegralCompacts :
    (localIntegralCompacts K v : Set (GL (Fin 2) (v.adicCompletion K))) = localIntegralSet K v :=
  rfl

theorem isLocallyConstant_indicator_one {X : Type*} [TopologicalSpace X] {U : Set X}
    (hU : IsOpen U) (hU' : IsClosed U) : IsLocallyConstant (U.indicator fun _ => (1 : ℂ)) := by
  intro s
  by_cases h1 : (1 : ℂ) ∈ s <;> by_cases h0 : (0 : ℂ) ∈ s
  · have : U.indicator (fun _ => (1 : ℂ)) ⁻¹' s = Set.univ := by
      ext x; by_cases hx : x ∈ U <;> simp [hx, h1, h0]
    rw [this]; exact isOpen_univ
  · have : U.indicator (fun _ => (1 : ℂ)) ⁻¹' s = U := by
      ext x; by_cases hx : x ∈ U <;> simp [hx, h1, h0]
    rw [this]; exact hU
  · have : U.indicator (fun _ => (1 : ℂ)) ⁻¹' s = Uᶜ := by
      ext x; by_cases hx : x ∈ U <;> simp [hx, h1, h0]
    rw [this]; exact hU'.isOpen_compl
  · have : U.indicator (fun _ => (1 : ℂ)) ⁻¹' s = ∅ := by
      ext x; by_cases hx : x ∈ U <;> simp [hx, h1, h0]
    rw [this]; exact isOpen_empty

theorem isLocalTestFn_indicator_localIntegralSet :
    IsLocalTestFn K v ((localIntegralSet K v).indicator fun _ => (1 : ℂ)) :=
  ⟨isLocallyConstant_indicator_one (isOpen_localIntegralSet K v)
      (isCompact_localIntegralSet K v).isClosed,
    HasCompactSupport.intro (isCompact_localIntegralSet K v) fun _ hg => by simp [hg]⟩

@[reducible] def localGLBorel : MeasurableSpace (GL (Fin 2) (v.adicCompletion K)) := borel _

theorem borelSpace_localGLBorel :
    @BorelSpace (GL (Fin 2) (v.adicCompletion K)) _ (localGLBorel K v) :=
  @BorelSpace.mk _ _ (localGLBorel K v) rfl

theorem locallyCompactSpace_matrix_adicCompletion :
    LocallyCompactSpace (Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) :=
  inferInstanceAs (LocallyCompactSpace (Fin 2 → Fin 2 → v.adicCompletion K))

theorem locallyCompactSpace_localGL : LocallyCompactSpace (GL (Fin 2) (v.adicCompletion K)) := by
  haveI := locallyCompactSpace_matrix_adicCompletion K v
  infer_instance

def localHaar : @Measure (GL (Fin 2) (v.adicCompletion K)) (localGLBorel K v) := by
  letI := localGLBorel K v
  haveI := borelSpace_localGLBorel K v
  haveI := locallyCompactSpace_localGL K v
  exact Measure.haarMeasure (localIntegralCompacts K v)

theorem isHaarMeasure_localHaar :
    @Measure.IsHaarMeasure (GL (Fin 2) (v.adicCompletion K)) _ _ (localGLBorel K v) (localHaar K v) := by
  letI := localGLBorel K v
  haveI := borelSpace_localGLBorel K v
  haveI := locallyCompactSpace_localGL K v
  exact Measure.isHaarMeasure_haarMeasure _

theorem localHaar_localIntegralSet : localHaar K v (localIntegralSet K v) = 1 := by
  letI := localGLBorel K v
  haveI := borelSpace_localGLBorel K v
  haveI := locallyCompactSpace_localGL K v
  exact Measure.haarMeasure_self

end Local

section OrbitalIntegral

variable (K : Type*) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

abbrev localCentralizer (γ : GL (Fin 2) (v.adicCompletion K)) :
    Subgroup (GL (Fin 2) (v.adicCompletion K)) :=
  Subgroup.centralizer {γ}

@[reducible] def localCentralizerBorel (γ : GL (Fin 2) (v.adicCompletion K)) :
    MeasurableSpace (localCentralizer K v γ) := borel _

def IsSectionFn (γ : GL (Fin 2) (v.adicCompletion K))
    (τ : @Measure (localCentralizer K v γ) (localCentralizerBorel K v γ))
    (fv : GL (Fin 2) (v.adicCompletion K) → ℂ) (w : GL (Fin 2) (v.adicCompletion K) → ℝ) : Prop :=
  letI := localGLBorel K v
  letI := localCentralizerBorel K v γ
  (∀ x, 0 ≤ w x) ∧ Measurable w ∧ HasCompactSupport w ∧
    ∀ x, fv (x⁻¹ * γ * x) ≠ 0 → ∫ t : localCentralizer K v γ, w (t * x) ∂τ = 1

def IsOrbitalIntegral (γ : GL (Fin 2) (v.adicCompletion K))
    (τ : @Measure (localCentralizer K v γ) (localCentralizerBorel K v γ))
    (fv : GL (Fin 2) (v.adicCompletion K) → ℂ) (I : ℂ) : Prop :=
  letI := localGLBorel K v
  ∃ w : GL (Fin 2) (v.adicCompletion K) → ℝ, IsSectionFn K v γ τ fv w ∧
    I = ∫ x, fv (x⁻¹ * γ * x) * (w x : ℂ) ∂(localHaar K v)

theorem isSectionFn_zero (γ : GL (Fin 2) (v.adicCompletion K))
    (τ : @Measure (localCentralizer K v γ) (localCentralizerBorel K v γ)) :
    IsSectionFn K v γ τ (fun _ => 0) (fun _ => 0) :=
  ⟨fun _ => le_rfl, measurable_const, HasCompactSupport.zero, fun _ h => absurd rfl h⟩

theorem isOrbitalIntegral_zero (γ : GL (Fin 2) (v.adicCompletion K))
    (τ : @Measure (localCentralizer K v γ) (localCentralizerBorel K v γ)) :
    IsOrbitalIntegral K v γ τ (fun _ => 0) 0 :=
  ⟨fun _ => 0, isSectionFn_zero K v γ τ, by simp⟩

theorem not_isOrbitalIntegral_zero_one (γ : GL (Fin 2) (v.adicCompletion K))
    (τ : @Measure (localCentralizer K v γ) (localCentralizerBorel K v γ)) :
    ¬ IsOrbitalIntegral K v γ τ (fun _ => 0) 1 := by
  rintro ⟨w, -, h⟩
  simp at h

end OrbitalIntegral

section UnitFactor

variable (K : Type) [Field K] [NumberField K]

def unitFinSet : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)) :=
  {h | ∀ v : HeightOneSpectrum (𝓞 K), AdelicLevel.finComponent (𝓞 K) K v h ∈ localIntegralSet K v}

theorem unitFinSet_eq :
    unitFinSet K = integralUnitsSet (AdelicLevel.integralFiniteAdeles (𝓞 K) K) := by
  ext h
  simp only [unitFinSet, Set.mem_setOf_eq, mem_localIntegralSet, mem_integralUnitsSet,
    AdelicLevel.integralFiniteAdeles, ← map_inv, AdelicLevel.finComponent_apply]
  exact ⟨fun H => ⟨fun i j v => (H v).1 i j, fun i j v => (H v).2 i j⟩,
    fun H v => ⟨fun i j => H.1 i j v, fun i j => H.2 i j v⟩⟩

theorem one_mem_unitFinSet : (1 : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)) ∈ unitFinSet K :=
  fun v => by rw [map_one]; exact one_mem_localIntegralSet K v

theorem isCompact_unitFinSet : IsCompact (unitFinSet K) := by
  rw [unitFinSet_eq]
  exact isCompact_integralUnitsSet (AdelicLevel.isCompact_integralFiniteAdeles (𝓞 K) K)

theorem isOpen_unitFinSet : IsOpen (unitFinSet K) := by
  rw [unitFinSet_eq]
  exact isOpen_integralUnitsSet (AdelicLevel.isOpen_integralFiniteAdeles (𝓞 K) K)

theorem isFinTestFactor_indicator_unitFinSet :
    IsFinTestFactor K ((unitFinSet K).indicator fun _ => (1 : ℂ)) :=
  ⟨isLocallyConstant_indicator_one (isOpen_unitFinSet K) (isCompact_unitFinSet K).isClosed,
    HasCompactSupport.intro (isCompact_unitFinSet K) fun _ hg => by simp [hg]⟩

end UnitFactor

section Tier

variable (K : Type) [Field K] [NumberField K]

theorem unitFinSet_eq_finiteIntegralGL2 :
    unitFinSet K = (AdelicLevel.finiteIntegralGL2 (𝓞 K) K : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 K) K))) := by
  ext h
  rw [unitFinSet_eq, SetLike.mem_coe, AdelicLevel.mem_finiteIntegralGL2_iff]
  exact Iff.rfl

theorem indicator_unitFinSet_mul_left {u : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)}
    (hu : u ∈ AdelicLevel.finiteIntegralGL2 (𝓞 K) K) (x : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)) :
    (unitFinSet K).indicator (fun _ => (1 : ℂ)) (u * x) =
      (unitFinSet K).indicator (fun _ => (1 : ℂ)) x := by
  have key : u * x ∈ unitFinSet K ↔ x ∈ unitFinSet K := by
    rw [unitFinSet_eq_finiteIntegralGL2, SetLike.mem_coe, SetLike.mem_coe]
    exact Subgroup.mul_mem_cancel_left _ hu
  by_cases hx : x ∈ unitFinSet K
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (key.2 hx)]
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (fun h => hx (key.1 h))]

theorem indicator_unitFinSet_mul_right {u : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)}
    (hu : u ∈ AdelicLevel.finiteIntegralGL2 (𝓞 K) K) (x : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)) :
    (unitFinSet K).indicator (fun _ => (1 : ℂ)) (x * u) =
      (unitFinSet K).indicator (fun _ => (1 : ℂ)) x := by
  have key : x * u ∈ unitFinSet K ↔ x ∈ unitFinSet K := by
    rw [unitFinSet_eq_finiteIntegralGL2, SetLike.mem_coe, SetLike.mem_coe]
    exact Subgroup.mul_mem_cancel_right _ hu
  by_cases hx : x ∈ unitFinSet K
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (key.2 hx)]
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (fun h => hx (key.1 h))]

def IsBiInvariantUnder (U : Subgroup (GL (Fin 2) (AdeleRing (𝓞 K) K)))
    (f : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ) : Prop :=
  ∀ u ∈ U, ∀ g, f (u * g) = f g ∧ f (g * u) = f g

theorem IsBiInvariantUnder.mono {U V : Subgroup (GL (Fin 2) (AdeleRing (𝓞 K) K))} (hUV : U ≤ V)
    {f : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ} (hf : IsBiInvariantUnder K V f) :
    IsBiInvariantUnder K U f :=
  fun u hu => hf u (hUV hu)

theorem isBiInvariantUnder_bot (f : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ) :
    IsBiInvariantUnder K ⊥ f := by
  intro u hu g
  rw [Subgroup.mem_bot.1 hu, one_mul, mul_one]
  exact ⟨rfl, rfl⟩

def IsUnitFactorizableAt (U : Subgroup (GL (Fin 2) (AdeleRing (𝓞 K) K)))
    (S : Finset (HeightOneSpectrum (𝓞 K))) (f : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ) : Prop :=
  IsBiInvariantUnder K U f ∧
  ∃ (fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ)
    (ff : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) → ℂ)
    (fS : ∀ v : HeightOneSpectrum (𝓞 K), GL (Fin 2) (v.adicCompletion K) → ℂ),
    IsArchTestFactor K fa ∧ IsFinTestFactor K ff ∧ (∀ v ∈ S, IsLocalTestFn K v (fS v)) ∧
    (∀ h : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K),
      (∀ v ∉ S, AdelicLevel.finComponent (𝓞 K) K v h ∈ localIntegralSet K v) →
        ff h = ∏ v ∈ S, fS v (AdelicLevel.finComponent (𝓞 K) K v h)) ∧
    (∀ h : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K),
      (∃ v ∉ S, AdelicLevel.finComponent (𝓞 K) K v h ∉ localIntegralSet K v) → ff h = 0) ∧
    ∀ g, f g = fa (AdelicLevel.glArch (𝓞 K) K g) * ff (AdelicLevel.glFin (𝓞 K) K g)

theorem IsUnitFactorizableAt.mono {U V : Subgroup (GL (Fin 2) (AdeleRing (𝓞 K) K))} (hUV : U ≤ V)
    {S : Finset (HeightOneSpectrum (𝓞 K))} {f : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ}
    (hf : IsUnitFactorizableAt K V S f) : IsUnitFactorizableAt K U S f :=
  ⟨hf.1.mono K hUV, hf.2⟩

theorem IsUnitFactorizableAt.isBiInvariantUnder {U : Subgroup (GL (Fin 2) (AdeleRing (𝓞 K) K))}
    {S : Finset (HeightOneSpectrum (𝓞 K))} {f : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ}
    (hf : IsUnitFactorizableAt K U S f) : IsBiInvariantUnder K U f :=
  hf.1

theorem IsUnitFactorizableAt.isFactorizableTestFn {U : Subgroup (GL (Fin 2) (AdeleRing (𝓞 K) K))}
    {S : Finset (HeightOneSpectrum (𝓞 K))} {f : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ}
    (hf : IsUnitFactorizableAt K U S f) : IsFactorizableTestFn K f := by
  obtain ⟨-, fa, ff, _, hfa, hff, -, -, -, hf⟩ := hf
  exact ⟨fa, ff, hfa, hff, hf⟩

def IsIntegralLevel (U : Subgroup (GL (Fin 2) (AdeleRing (𝓞 K) K))) : Prop :=
  ∀ u ∈ U, AdelicLevel.glArch (𝓞 K) K u = 1 ∧
    AdelicLevel.glFin (𝓞 K) K u ∈ AdelicLevel.finiteIntegralGL2 (𝓞 K) K

theorem isIntegralLevel_bot : IsIntegralLevel K ⊥ := by
  intro u hu
  rw [Subgroup.mem_bot.1 hu, map_one, map_one]
  exact ⟨rfl, one_mem _⟩

theorem isIntegralLevel_levelOne_inf_ker (N : Ideal (𝓞 K)) :
    IsIntegralLevel K (AdelicLevel.levelOne (𝓞 K) K N ⊓ (AdelicLevel.glArch (𝓞 K) K).ker) := by
  intro u hu
  obtain ⟨hlev, harch⟩ := Subgroup.mem_inf.1 hu
  refine ⟨MonoidHom.mem_ker.1 harch, ?_⟩
  have h0 := AdelicLevel.finiteLevelOne_le_finiteLevelZero (𝓞 K) K N (AdelicLevel.mem_levelOne_iff.1 hlev)
  exact AdelicLevel.mem_finiteIntegralGL2_iff.2 ⟨h0.1.integral, h0.2.integral⟩

theorem isUnitFactorizableAt_mul_indicator_unitFinSet {fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ}
    (hfa : IsArchTestFactor K fa) {U : Subgroup (GL (Fin 2) (AdeleRing (𝓞 K) K))}
    (hU : IsIntegralLevel K U) (S : Finset (HeightOneSpectrum (𝓞 K))) :
    IsUnitFactorizableAt K U S fun g => fa (AdelicLevel.glArch (𝓞 K) K g) *
      (unitFinSet K).indicator (fun _ => (1 : ℂ)) (AdelicLevel.glFin (𝓞 K) K g) := by
  refine ⟨fun u hu g => ?_, fa, (unitFinSet K).indicator fun _ => (1 : ℂ),
    fun v => (localIntegralSet K v).indicator fun _ => (1 : ℂ), hfa,
    isFinTestFactor_indicator_unitFinSet K, fun v _ => isLocalTestFn_indicator_localIntegralSet K v,
    fun h hS => ?_, fun h hS => ?_, fun _ => rfl⟩
  · obtain ⟨hu1, hu2⟩ := hU u hu
    constructor
    · dsimp only
      rw [map_mul, map_mul, hu1, one_mul, indicator_unitFinSet_mul_left K hu2]
    · dsimp only
      rw [map_mul, map_mul, hu1, mul_one, indicator_unitFinSet_mul_right K hu2]
  · by_cases hall : h ∈ unitFinSet K
    · rw [Set.indicator_of_mem hall]
      exact (Finset.prod_eq_one fun v _ => Set.indicator_of_mem (hall v) _).symm
    · rw [Set.indicator_of_notMem hall]
      obtain ⟨v, hv⟩ : ∃ v, AdelicLevel.finComponent (𝓞 K) K v h ∉ localIntegralSet K v := by
        by_contra hcon
        exact hall fun v => by_contra fun hv => hcon ⟨v, hv⟩
      have hvS : v ∈ S := by
        by_contra hvS
        exact hv (hS v hvS)
      exact (Finset.prod_eq_zero hvS (Set.indicator_of_notMem hv _)).symm
  · obtain ⟨v, -, hv⟩ := hS
    have hnot : h ∉ unitFinSet K := fun hall => hv (hall v)
    exact Set.indicator_of_notMem hnot _

theorem isUnitFactorizableAt_zero (U : Subgroup (GL (Fin 2) (AdeleRing (𝓞 K) K)))
    (S : Finset (HeightOneSpectrum (𝓞 K))) : IsUnitFactorizableAt K U S fun _ => 0 := by
  refine ⟨fun _ _ _ => ⟨rfl, rfl⟩, ?_⟩
  simpa using
    (isUnitFactorizableAt_mul_indicator_unitFinSet K (isArchTestFactor_zero K) (isIntegralLevel_bot K) S).2

end Tier

section RegularSemisimple

variable {A : Type*} [CommRing A]

def IsRegularSemisimple (g : GL (Fin 2) A) : Prop :=
  IsUnit (Matrix.trace (g : Matrix (Fin 2) (Fin 2) A) ^ 2 - 4 * Matrix.det (g : Matrix (Fin 2) (Fin 2) A))

theorem isRegularSemisimple_iff (g : GL (Fin 2) A) :
    IsRegularSemisimple g ↔
      IsUnit (Matrix.trace (g : Matrix (Fin 2) (Fin 2) A) ^ 2 - 4 * Matrix.det (g : Matrix (Fin 2) (Fin 2) A)) :=
  Iff.rfl

theorem isRegularSemisimple_iff_ne_zero {F : Type*} [Field F] (g : GL (Fin 2) F) :
    IsRegularSemisimple g ↔
      Matrix.trace (g : Matrix (Fin 2) (Fin 2) F) ^ 2 - 4 * Matrix.det (g : Matrix (Fin 2) (Fin 2) F) ≠ 0 :=
  isUnit_iff_ne_zero

theorem IsRegularSemisimple.conj {g : GL (Fin 2) A} (hg : IsRegularSemisimple g) (x : GL (Fin 2) A) :
    IsRegularSemisimple (x⁻¹ * g * x) := by
  unfold IsRegularSemisimple at hg ⊢
  have htr : Matrix.trace ((x⁻¹ * g * x : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) =
      Matrix.trace (g : Matrix (Fin 2) (Fin 2) A) := by
    rw [Units.val_mul, Units.val_mul, Matrix.trace_mul_cycle, ← Units.val_mul, mul_inv_cancel,
      Units.val_one, Matrix.one_mul]
  have hdet : Matrix.det ((x⁻¹ * g * x : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) =
      Matrix.det (g : Matrix (Fin 2) (Fin 2) A) := by
    rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, mul_comm, ← mul_assoc,
      ← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one, one_mul]
  rw [htr, hdet]
  exact hg

end RegularSemisimple

end AutomorphicForm

end


