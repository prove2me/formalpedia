-- Prove2me | Definitions.Def_AutomorphicForm_IsotypicCuspSpace
-- name    : AutomorphicForm_IsotypicCuspSpace
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.014713+00:00
-- url     : https://prove2.me/theorems/2b1df940-0be7-5575-b45a-4b25d767eb6e
-- title:
--   Isotypic cusp spaces, archimedean type cuts, convolution traces
-- statement:
--   Fix a number field $K$ and a bundle `CarrierPins K` of carrier data on $G=\mathrm{GL}_2(\mathbb{A}_K)$ (a measurable structure and measure, a window $D$, a central subgroup $Z$ of the ideles, level subgroups $U(\mathfrak n)$, elements $\mathrm{gen}\,v$ for the finite places, and a measure on $\mathbb{A}_K$). Given a character $\xi$ of $Z$, an ideal $N$, a finite set $S$ of finite places and a Hecke eigensystem $\Phi$ with complex entries, the structure `IsIsotypicCuspFormAt` records of a function $\varphi\colon G\to\mathbb{C}$ five conditions: it satisfies the predicate `IsSmoothCuspAutomorphicFnAt` for the data $(\text{pins},\xi)$; it is continuous; it is right $U(N)$-invariant; for every $v\notin S$ it satisfies `IsHeckeCosetEigenfunctionAt` for the coset generator $\mathrm{gen}\,v$ with eigenvalue $\Phi.a\,v$; and for $v\notin S$ the central element attached to $\det(\mathrm{gen}\,v)$ acts by the scalar $\Phi.\mathrm{toRawCentral}.b\,v$. The isotypic cusp space `isotypicCuspSubmodule` is the $\mathbb{C}$-span of these functions; its elements are continuous, it vanishes exactly when every such $\varphi$ is $0$, and its non-vanishing for some $\xi$, $S$ is equivalent to `IsArithGenuineCuspRealizable` for $\Phi$. `cuspClasses` is the set of eigensystems of level exactly $N$ with $a_v=b_v=0$ on $S$ and non-zero isotypic space; such classes are determined by their entries away from $S$.
--
--   For traces, `IsStableLinearOn V T` asserts that $T$ maps the subspace $V$ into itself and is additive and homogeneous there, and `traceOn` is the trace of the induced endomorphism of $V$. `convOp` is right convolution $u\mapsto u*f$ against the adelic Haar measure, `twistedConvOp` precomposes it with the Galois-twisted action $u\mapsto u\circ\sigma$ coming from an idele Galois descent datum, and `convTraceOn`, `twistedConvTraceOn` are these traces, set to $0$ unless the operator preserves $V$. On the archimedean side, `typeSubmodule ι ρ` is spanned by ranges of linear maps $T\colon W\to(G\to\mathbb{C})$ with $T(\rho(k)v)(x)=T(v)(x\,\iota k)$; for the one-dimensional `charRep` $\chi$ membership is exactly $f(x\,\iota k)=\chi(k)f(x)$ (and $\chi(k^{-1})$ for the dual). `ArchRepAt` attaches to an infinite place $w$ a representation of the determinant-one row-isometry subgroup of $\mathrm{GL}_2(K_w)$, an `ArchTypeFamily` lists finitely many such at each place, and `archCutSubmodule` (resp. `archDualCutSubmodule`) is the intersection over places of the sum of the corresponding type subspaces, pulled into $G$ along the archimedean inclusions; `IsArchBiFinite` combines the dual cut for $f$ with the cut for $x\mapsto f(x^{-1})$, and is inherited from a factorisation through the archimedean and finite components. Finally `cutTrace` (resp. `twistedCutTrace`) is the convolution trace (resp. twisted convolution trace) on the intersection of an isotypic cusp space with an archimedean cut; non-vanishing of `cutTrace` forces the isotypic space to be non-zero, hence realizability of the eigensystem, and the twisted trace at $\sigma=1$ is the untwisted one.
--
--   **Relation to Mathlib.** Mathlib supplies `Submodule.span`, `LinearMap.trace` and `Representation`, used here; `traceOn` wraps `LinearMap.trace` for maps that are linear only on the given submodule. The isotypic cusp spaces, archimedean type cuts, and the (twisted) convolution traces are the project's own notions.
--
--   **Where it is used.** These spaces and traces are the setting in which traces of Hecke convolution operators, cut by archimedean types at each infinite place and twisted by a Galois automorphism, are compared; such comparisons underlie the cyclic base change input to the Langlands–Tunnell theorem used in the proof of Fermat's Last Theorem.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AutomorphicForm_IsotypicCuspSpace.lean

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_SigmaAdelicAction
import Definitions.Def_AutomorphicForm_ArchWeightChar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField

noncomputable section

namespace AutomorphicForm

section Isotypic

variable (K : Type) [Field K] [NumberField K]

structure IsIsotypicCuspFormAt (pins : CarrierPins K) (ξ : pins.Z →* ℂˣ) (N : Ideal (𝓞 K))
    (S : Finset (HeightOneSpectrum (𝓞 K))) (Φ : HeckeEigensystem K ℂ)
    (φ : AdelicGL2 (𝓞 K) K → ℂ) : Prop where
  smoothCusp : IsSmoothCuspAutomorphicFnAt K pins ξ φ
  continuous : Continuous φ
  level_invariant : ∀ g : AdelicGL2 (𝓞 K) K, ∀ u ∈ pins.U N, φ (g * u) = φ g
  hecke_eigen : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
    SmoothCusp.IsHeckeCosetEigenfunctionAt K (pins.U N) (pins.gen v) v φ (Φ.a v)
  central_eigen : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → ∀ g : AdelicGL2 (𝓞 K) K,
    φ (centralScalar (𝓞 K) K (Matrix.GeneralLinearGroup.det (pins.gen v)) * g)
      = Φ.toRawCentral.b v * φ g

def isotypicCuspSubmodule (pins : CarrierPins K) (ξ : pins.Z →* ℂˣ) (N : Ideal (𝓞 K))
    (S : Finset (HeightOneSpectrum (𝓞 K))) (Φ : HeckeEigensystem K ℂ) :
    Submodule ℂ (AdelicGL2 (𝓞 K) K → ℂ) :=
  Submodule.span ℂ {φ | IsIsotypicCuspFormAt K pins ξ N S Φ φ}

variable {K}

theorem IsIsotypicCuspFormAt.mem_isotypicCuspSubmodule {pins : CarrierPins K}
    {ξ : pins.Z →* ℂˣ} {N : Ideal (𝓞 K)} {S : Finset (HeightOneSpectrum (𝓞 K))}
    {Φ : HeckeEigensystem K ℂ} {φ : AdelicGL2 (𝓞 K) K → ℂ}
    (h : IsIsotypicCuspFormAt K pins ξ N S Φ φ) :
    φ ∈ isotypicCuspSubmodule K pins ξ N S Φ :=
  Submodule.subset_span h

theorem continuous_of_mem_isotypicCuspSubmodule {pins : CarrierPins K} {ξ : pins.Z →* ℂˣ}
    {N : Ideal (𝓞 K)} {S : Finset (HeightOneSpectrum (𝓞 K))} {Φ : HeckeEigensystem K ℂ}
    {φ : AdelicGL2 (𝓞 K) K → ℂ} (h : φ ∈ isotypicCuspSubmodule K pins ξ N S Φ) :
    Continuous φ := by
  refine Submodule.span_induction (p := fun φ _ => Continuous φ) ?_ ?_ ?_ ?_ h
  · exact fun φ hφ => hφ.continuous
  · exact continuous_zero
  · exact fun _ _ _ _ hu hw => hu.add hw
  · exact fun c _ _ hu => hu.const_smul c

variable (K)

theorem isotypicCuspSubmodule_eq_bot_iff (pins : CarrierPins K) (ξ : pins.Z →* ℂˣ)
    (N : Ideal (𝓞 K)) (S : Finset (HeightOneSpectrum (𝓞 K))) (Φ : HeckeEigensystem K ℂ) :
    isotypicCuspSubmodule K pins ξ N S Φ = ⊥ ↔
      ∀ φ : AdelicGL2 (𝓞 K) K → ℂ, IsIsotypicCuspFormAt K pins ξ N S Φ φ → φ = 0 :=
  Submodule.span_eq_bot

theorem isotypicCuspSubmodule_ne_bot_iff (pins : CarrierPins K) (ξ : pins.Z →* ℂˣ)
    (N : Ideal (𝓞 K)) (S : Finset (HeightOneSpectrum (𝓞 K))) (Φ : HeckeEigensystem K ℂ) :
    isotypicCuspSubmodule K pins ξ N S Φ ≠ ⊥ ↔
      ∃ φ : AdelicGL2 (𝓞 K) K → ℂ, IsIsotypicCuspFormAt K pins ξ N S Φ φ ∧ φ ≠ 0 := by
  rw [Ne, isotypicCuspSubmodule_eq_bot_iff]
  constructor
  · intro h
    by_contra hne
    exact h fun φ hφ => by_contra fun h0 => hne ⟨φ, hφ, h0⟩
  · rintro ⟨φ, hφ, h0⟩ h
    exact h0 (h φ hφ)

variable {K}

theorem SmoothCuspRealizationAt.isIsotypicCuspFormAt {pins : CarrierPins K}
    {Φ : HeckeEigensystem K ℂ} (R : SmoothCuspRealizationAt K pins Φ.toRawCentral)
    (hR : Continuous R.toFun) :
    IsIsotypicCuspFormAt K pins R.centralChar Φ.level R.exceptionalSet Φ R.toFun where
  smoothCusp := R.smoothCusp
  continuous := hR
  level_invariant := R.level_invariant
  hecke_eigen := R.hecke_eigen
  central_eigen := R.central_eigen

theorem SmoothCuspRealizationAt.toFun_mem_isotypicCuspSubmodule {pins : CarrierPins K}
    {Φ : HeckeEigensystem K ℂ} (R : SmoothCuspRealizationAt K pins Φ.toRawCentral)
    (hR : Continuous R.toFun) :
    R.toFun ∈ isotypicCuspSubmodule K pins R.centralChar Φ.level R.exceptionalSet Φ :=
  (R.isIsotypicCuspFormAt hR).mem_isotypicCuspSubmodule

theorem SmoothCuspRealizationAt.isotypicCuspSubmodule_ne_bot {pins : CarrierPins K}
    {Φ : HeckeEigensystem K ℂ} (R : SmoothCuspRealizationAt K pins Φ.toRawCentral)
    (hR : Continuous R.toFun) :
    isotypicCuspSubmodule K pins R.centralChar Φ.level R.exceptionalSet Φ ≠ ⊥ :=
  (isotypicCuspSubmodule_ne_bot_iff K pins R.centralChar Φ.level R.exceptionalSet Φ).mpr
    ⟨R.toFun, R.isIsotypicCuspFormAt hR, R.toFun_ne_zero⟩

def IsIsotypicCuspFormAt.toRealization {pins : CarrierPins K} {ξ : pins.Z →* ℂˣ}
    {S : Finset (HeightOneSpectrum (𝓞 K))} {Φ : HeckeEigensystem K ℂ}
    {φ : AdelicGL2 (𝓞 K) K → ℂ} (h : IsIsotypicCuspFormAt K pins ξ Φ.level S Φ φ)
    (h0 : φ ≠ 0) : SmoothCuspRealizationAt K pins Φ.toRawCentral where
  toFun := φ
  exists_ne_zero := Function.ne_iff.mp h0
  centralChar := ξ
  smoothCusp := h.smoothCusp
  level_invariant := h.level_invariant
  exceptionalSet := S
  hecke_eigen := h.hecke_eigen
  central_eigen := h.central_eigen

@[simp] theorem IsIsotypicCuspFormAt.toRealization_toFun {pins : CarrierPins K}
    {ξ : pins.Z →* ℂˣ} {S : Finset (HeightOneSpectrum (𝓞 K))} {Φ : HeckeEigensystem K ℂ}
    {φ : AdelicGL2 (𝓞 K) K → ℂ} (h : IsIsotypicCuspFormAt K pins ξ Φ.level S Φ φ)
    (h0 : φ ≠ 0) : (h.toRealization h0).toFun = φ :=
  rfl

theorem IsIsotypicCuspFormAt.isArithGenuineCuspRealizable {pins : CarrierPins K}
    {ξ : pins.Z →* ℂˣ} {S : Finset (HeightOneSpectrum (𝓞 K))} {Φ : HeckeEigensystem K ℂ}
    {φ : AdelicGL2 (𝓞 K) K → ℂ} (h : IsIsotypicCuspFormAt K pins ξ Φ.level S Φ φ)
    (h0 : φ ≠ 0) : IsArithGenuineCuspRealizable K pins Φ :=
  ⟨h.toRealization h0, h.continuous⟩

theorem isArithGenuineCuspRealizable_of_isotypicCuspSubmodule_ne_bot {pins : CarrierPins K}
    {ξ : pins.Z →* ℂˣ} {S : Finset (HeightOneSpectrum (𝓞 K))} {Φ : HeckeEigensystem K ℂ}
    (h : isotypicCuspSubmodule K pins ξ Φ.level S Φ ≠ ⊥) :
    IsArithGenuineCuspRealizable K pins Φ := by
  obtain ⟨φ, hφ, h0⟩ := (isotypicCuspSubmodule_ne_bot_iff K pins ξ Φ.level S Φ).mp h
  exact hφ.isArithGenuineCuspRealizable h0

theorem isArithGenuineCuspRealizable_iff_exists_isotypicCuspSubmodule_ne_bot
    (pins : CarrierPins K) (Φ : HeckeEigensystem K ℂ) :
    IsArithGenuineCuspRealizable K pins Φ ↔
      ∃ (ξ : pins.Z →* ℂˣ) (S : Finset (HeightOneSpectrum (𝓞 K))),
        isotypicCuspSubmodule K pins ξ Φ.level S Φ ≠ ⊥ := by
  constructor
  · rintro ⟨R, hR⟩
    exact ⟨R.centralChar, R.exceptionalSet, R.isotypicCuspSubmodule_ne_bot hR⟩
  · rintro ⟨ξ, S, h⟩
    exact isArithGenuineCuspRealizable_of_isotypicCuspSubmodule_ne_bot h

end Isotypic

section Classes

variable (K : Type) [Field K] [NumberField K]

def cuspClasses (pins : CarrierPins K) (ξ : pins.Z →* ℂˣ) (N : Ideal (𝓞 K))
    (S : Finset (HeightOneSpectrum (𝓞 K))) : Set (HeckeEigensystem K ℂ) :=
  {Φ | Φ.level = N ∧ (∀ v ∈ S, Φ.a v = 0 ∧ Φ.b v = 0) ∧
    isotypicCuspSubmodule K pins ξ N S Φ ≠ ⊥}

theorem mem_cuspClasses_iff (pins : CarrierPins K) (ξ : pins.Z →* ℂˣ) (N : Ideal (𝓞 K))
    (S : Finset (HeightOneSpectrum (𝓞 K))) (Φ : HeckeEigensystem K ℂ) :
    Φ ∈ cuspClasses K pins ξ N S ↔
      Φ.level = N ∧ (∀ v ∈ S, Φ.a v = 0 ∧ Φ.b v = 0) ∧
        isotypicCuspSubmodule K pins ξ N S Φ ≠ ⊥ :=
  Iff.rfl

variable {K}

theorem exists_mem_isotypicCuspSubmodule_ne_zero_of_mem_cuspClasses {pins : CarrierPins K}
    {ξ : pins.Z →* ℂˣ} {N : Ideal (𝓞 K)} {S : Finset (HeightOneSpectrum (𝓞 K))}
    {Φ : HeckeEigensystem K ℂ} (h : Φ ∈ cuspClasses K pins ξ N S) :
    ∃ φ ∈ isotypicCuspSubmodule K pins ξ N S Φ, φ ≠ 0 :=
  (Submodule.ne_bot_iff _).mp h.2.2

theorem exists_isIsotypicCuspFormAt_ne_zero_of_mem_cuspClasses {pins : CarrierPins K}
    {ξ : pins.Z →* ℂˣ} {N : Ideal (𝓞 K)} {S : Finset (HeightOneSpectrum (𝓞 K))}
    {Φ : HeckeEigensystem K ℂ} (h : Φ ∈ cuspClasses K pins ξ N S) :
    ∃ φ : AdelicGL2 (𝓞 K) K → ℂ, IsIsotypicCuspFormAt K pins ξ N S Φ φ ∧ φ ≠ 0 :=
  (isotypicCuspSubmodule_ne_bot_iff K pins ξ N S Φ).mp h.2.2

theorem isArithGenuineCuspRealizable_of_mem_cuspClasses {pins : CarrierPins K} {ξ : pins.Z →* ℂˣ}
    {N : Ideal (𝓞 K)} {S : Finset (HeightOneSpectrum (𝓞 K))} {Φ : HeckeEigensystem K ℂ}
    (h : Φ ∈ cuspClasses K pins ξ N S) : IsArithGenuineCuspRealizable K pins Φ := by
  obtain ⟨hN, -, hV⟩ := h
  subst hN
  exact isArithGenuineCuspRealizable_of_isotypicCuspSubmodule_ne_bot hV

theorem eq_of_mem_cuspClasses {pins : CarrierPins K} {ξ : pins.Z →* ℂˣ} {N : Ideal (𝓞 K)}
    {S : Finset (HeightOneSpectrum (𝓞 K))} {Φ Φ' : HeckeEigensystem K ℂ}
    (h : Φ ∈ cuspClasses K pins ξ N S) (h' : Φ' ∈ cuspClasses K pins ξ N S)
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → Φ.a v = Φ'.a v ∧ Φ.b v = Φ'.b v) :
    Φ = Φ' := by
  obtain ⟨hN, hzero, -⟩ := h
  obtain ⟨hN', hzero', -⟩ := h'
  rcases Φ with ⟨N₁, hN₁, a₁, b₁⟩
  rcases Φ' with ⟨N₂, hN₂, a₂, b₂⟩
  simp only at hN hN' hzero hzero' hS
  subst hN
  subst hN'
  have ha : a₁ = a₂ := by
    funext v
    by_cases hv : v ∈ S
    · rw [(hzero v hv).1, (hzero' v hv).1]
    · exact (hS v hv).1
  have hb : b₁ = b₂ := by
    funext v
    by_cases hv : v ∈ S
    · rw [(hzero v hv).2, (hzero' v hv).2]
    · exact (hS v hv).2
  subst ha
  subst hb
  rfl

end Classes

section Trace

variable {M : Type*} [AddCommGroup M] [Module ℂ M]

structure IsStableLinearOn (V : Submodule ℂ M) (T : M → M) : Prop where
  mapsTo : ∀ u ∈ V, T u ∈ V
  map_add : ∀ u ∈ V, ∀ w ∈ V, T (u + w) = T u + T w
  map_smul : ∀ (c : ℂ) (u : M), u ∈ V → T (c • u) = c • T u

theorem IsStableLinearOn.of_linearMap {V : Submodule ℂ M} (f : M →ₗ[ℂ] M)
    (hf : ∀ u ∈ V, f u ∈ V) : IsStableLinearOn V f where
  mapsTo := hf
  map_add u _ w _ := f.map_add u w
  map_smul c u _ := f.map_smul c u

theorem IsStableLinearOn.comp {V : Submodule ℂ M} {T₁ T₂ : M → M}
    (h₁ : IsStableLinearOn V T₁) (h₂ : IsStableLinearOn V T₂) : IsStableLinearOn V (T₁ ∘ T₂) where
  mapsTo u hu := h₁.mapsTo _ (h₂.mapsTo u hu)
  map_add u hu w hw := by
    rw [Function.comp_apply, h₂.map_add u hu w hw]
    exact h₁.map_add _ (h₂.mapsTo u hu) _ (h₂.mapsTo w hw)
  map_smul c u hu := by
    rw [Function.comp_apply, h₂.map_smul c u hu]
    exact h₁.map_smul c _ (h₂.mapsTo u hu)

def IsStableLinearOn.toEnd {V : Submodule ℂ M} {T : M → M} (h : IsStableLinearOn V T) :
    V →ₗ[ℂ] V where
  toFun u := ⟨T u, h.mapsTo u u.2⟩
  map_add' u w := Subtype.ext (h.map_add u u.2 w w.2)
  map_smul' c u := Subtype.ext (h.map_smul c u u.2)

@[simp] theorem IsStableLinearOn.coe_toEnd_apply {V : Submodule ℂ M} {T : M → M}
    (h : IsStableLinearOn V T) (u : V) : (h.toEnd u : M) = T u :=
  rfl

theorem IsStableLinearOn.toEnd_comp {V : Submodule ℂ M} {T₁ T₂ : M → M}
    (h₁ : IsStableLinearOn V T₁) (h₂ : IsStableLinearOn V T₂) :
    (h₁.comp h₂).toEnd = h₁.toEnd ∘ₗ h₂.toEnd :=
  LinearMap.ext fun _ => Subtype.ext rfl

def traceOn (V : Submodule ℂ M) (T : M → M) (h : IsStableLinearOn V T) : ℂ :=
  LinearMap.trace ℂ V h.toEnd

theorem traceOn_eq (V : Submodule ℂ M) (T : M → M) (h : IsStableLinearOn V T) :
    traceOn V T h = LinearMap.trace ℂ V h.toEnd :=
  rfl

theorem traceOn_congr {V : Submodule ℂ M} {T₁ T₂ : M → M} (h₁ : IsStableLinearOn V T₁)
    (h₂ : IsStableLinearOn V T₂) (hT : T₁ = T₂) : traceOn V T₁ h₁ = traceOn V T₂ h₂ := by
  subst hT
  rfl

theorem traceOn_eq_zero_of_eq_bot {V : Submodule ℂ M} {T : M → M} (h : IsStableLinearOn V T)
    (hV : V = ⊥) : traceOn V T h = 0 := by
  have h0 : h.toEnd = 0 := by
    refine LinearMap.ext fun u => Subtype.ext ?_
    have hu : (u : M) = 0 := (Submodule.mem_bot ℂ).mp (hV ▸ u.2)
    have hTu : (T u : M) ∈ (⊥ : Submodule ℂ M) := hV ▸ h.mapsTo u u.2
    rw [IsStableLinearOn.coe_toEnd_apply, LinearMap.zero_apply, Submodule.coe_zero]
    exact (Submodule.mem_bot ℂ).mp hTu
  rw [traceOn, h0, map_zero]

theorem ne_bot_of_traceOn_ne_zero {V : Submodule ℂ M} {T : M → M} (h : IsStableLinearOn V T)
    (ht : traceOn V T h ≠ 0) : V ≠ ⊥ :=
  fun hV => ht (traceOn_eq_zero_of_eq_bot h hV)

end Trace

section Operators

variable (K : Type) [Field K] [NumberField K]

theorem rightConv_add_left {u w f : AdelicGL2 (𝓞 K) K → ℂ} (hu : Continuous u)
    (hw : Continuous w) (hf : Continuous f) (hfc : HasCompactSupport f) :
    rightConv K (u + w) f = rightConv K u f + rightConv K w f := by
  letI : MeasurableSpace (AdelicGL2 (𝓞 K) K) := AdelicHaar.glBorel (Fin 2) (𝓞 K) K
  haveI : BorelSpace (AdelicGL2 (𝓞 K) K) := AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 K) K
  haveI : (AdelicHaar.adelicGLHaar (Fin 2) (𝓞 K) K).IsHaarMeasure :=
    AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 K) K
  have hint : ∀ {φ : AdelicGL2 (𝓞 K) K → ℂ}, Continuous φ → ∀ g : AdelicGL2 (𝓞 K) K,
      MeasureTheory.Integrable (fun x => φ (g * x) * f x)
        (AdelicHaar.adelicGLHaar (Fin 2) (𝓞 K) K) := by
    intro φ hφ g
    have hc : Continuous fun x : AdelicGL2 (𝓞 K) K => φ (g * x) * f x :=
      (hφ.comp (continuous_const.mul continuous_id)).mul hf
    have hs : HasCompactSupport fun x : AdelicGL2 (𝓞 K) K => φ (g * x) * f x := hfc.mul_left
    exact hc.integrable_of_hasCompactSupport hs
  funext g
  simp only [rightConv_apply, Pi.add_apply, add_mul]
  exact MeasureTheory.integral_add (hint hu g) (hint hw g)

def convOp (f : AdelicGL2 (𝓞 K) K → ℂ) :
    (AdelicGL2 (𝓞 K) K → ℂ) → (AdelicGL2 (𝓞 K) K → ℂ) :=
  fun u => rightConv K u f

theorem convOp_apply (f u : AdelicGL2 (𝓞 K) K → ℂ) : convOp K f u = rightConv K u f :=
  rfl

theorem convOp_zero (f : AdelicGL2 (𝓞 K) K → ℂ) : convOp K f 0 = 0 :=
  rightConv_zero_left K f

theorem convOp_smul (f : AdelicGL2 (𝓞 K) K → ℂ) (c : ℂ) (u : AdelicGL2 (𝓞 K) K → ℂ) :
    convOp K f (c • u) = c • convOp K f u := by
  funext g
  simp only [convOp, rightConv_apply, Pi.smul_apply, smul_eq_mul, mul_assoc]
  exact MeasureTheory.integral_const_mul c _

theorem convOp_add {f : AdelicGL2 (𝓞 K) K → ℂ} (hf : Continuous f) (hfc : HasCompactSupport f)
    {u w : AdelicGL2 (𝓞 K) K → ℂ} (hu : Continuous u) (hw : Continuous w) :
    convOp K f (u + w) = convOp K f u + convOp K f w :=
  rightConv_add_left K hu hw hf hfc

theorem isStableLinearOn_convOp {V : Submodule ℂ (AdelicGL2 (𝓞 K) K → ℂ)}
    (hV : ∀ u ∈ V, Continuous u) {f : AdelicGL2 (𝓞 K) K → ℂ} (hf : Continuous f)
    (hfc : HasCompactSupport f) (hmaps : ∀ u ∈ V, convOp K f u ∈ V) :
    IsStableLinearOn V (convOp K f) where
  mapsTo := hmaps
  map_add u hu w hw := convOp_add K hf hfc (hV u hu) (hV w hw)
  map_smul c u _ := convOp_smul K f c u

open Classical in

def convTraceOn (V : Submodule ℂ (AdelicGL2 (𝓞 K) K → ℂ)) (hV : ∀ u ∈ V, Continuous u)
    (f : AdelicGL2 (𝓞 K) K → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f) : ℂ :=
  if hmaps : ∀ u ∈ V, convOp K f u ∈ V then
    traceOn V (convOp K f) (isStableLinearOn_convOp K hV hf hfc hmaps) else 0

theorem convTraceOn_eq_traceOn {V : Submodule ℂ (AdelicGL2 (𝓞 K) K → ℂ)}
    (hV : ∀ u ∈ V, Continuous u) {f : AdelicGL2 (𝓞 K) K → ℂ} (hf : Continuous f)
    (hfc : HasCompactSupport f) (hmaps : ∀ u ∈ V, convOp K f u ∈ V) :
    convTraceOn K V hV f hf hfc =
      traceOn V (convOp K f) (isStableLinearOn_convOp K hV hf hfc hmaps) :=
  dif_pos hmaps

theorem convTraceOn_eq_zero {V : Submodule ℂ (AdelicGL2 (𝓞 K) K → ℂ)}
    (hV : ∀ u ∈ V, Continuous u) {f : AdelicGL2 (𝓞 K) K → ℂ} (hf : Continuous f)
    (hfc : HasCompactSupport f) (hmaps : ¬ ∀ u ∈ V, convOp K f u ∈ V) :
    convTraceOn K V hV f hf hfc = 0 :=
  dif_neg hmaps

theorem mapsTo_and_ne_bot_of_convTraceOn_ne_zero {V : Submodule ℂ (AdelicGL2 (𝓞 K) K → ℂ)}
    (hV : ∀ u ∈ V, Continuous u) {f : AdelicGL2 (𝓞 K) K → ℂ} (hf : Continuous f)
    (hfc : HasCompactSupport f) (ht : convTraceOn K V hV f hf hfc ≠ 0) :
    (∀ u ∈ V, convOp K f u ∈ V) ∧ V ≠ ⊥ := by
  by_cases hmaps : ∀ u ∈ V, convOp K f u ∈ V
  · rw [convTraceOn_eq_traceOn K hV hf hfc hmaps] at ht
    exact ⟨hmaps, ne_bot_of_traceOn_ne_zero _ ht⟩
  · exact absurd (convTraceOn_eq_zero K hV hf hfc hmaps) ht

variable (F L : Type) [Field F] [Field L] [NumberField L] [Algebra F L]
variable (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) F L)

theorem sigmaSectionActOn_add (σ : L ≃ₐ[F] L) (u w : AdelicGL2 (𝓞 L) L → ℂ) :
    sigmaSectionActOn F L D σ (u + w) = sigmaSectionActOn F L D σ u + sigmaSectionActOn F L D σ w :=
  rfl

theorem sigmaSectionActOn_smul (σ : L ≃ₐ[F] L) (c : ℂ) (u : AdelicGL2 (𝓞 L) L → ℂ) :
    sigmaSectionActOn F L D σ (c • u) = c • sigmaSectionActOn F L D σ u :=
  rfl

theorem continuous_sigmaSectionActOn (σ : L ≃ₐ[F] L) {u : AdelicGL2 (𝓞 L) L → ℂ}
    (hu : Continuous u) : Continuous (sigmaSectionActOn F L D σ u) :=
  hu.comp (continuous_sigmaAdelicAct F L D σ)

def twistedConvOp (σ : L ≃ₐ[F] L) (f : AdelicGL2 (𝓞 L) L → ℂ) :
    (AdelicGL2 (𝓞 L) L → ℂ) → (AdelicGL2 (𝓞 L) L → ℂ) :=
  fun u => rightConv L (sigmaSectionActOn F L D σ u) f

theorem twistedConvOp_apply (σ : L ≃ₐ[F] L) (f u : AdelicGL2 (𝓞 L) L → ℂ) :
    twistedConvOp F L D σ f u = rightConv L (sigmaSectionActOn F L D σ u) f :=
  rfl

theorem twistedConvOp_eq_comp (σ : L ≃ₐ[F] L) (f : AdelicGL2 (𝓞 L) L → ℂ) :
    twistedConvOp F L D σ f = convOp L f ∘ sigmaSectionActOn F L D σ :=
  rfl

theorem twistedConvOp_one (f : AdelicGL2 (𝓞 L) L → ℂ) :
    twistedConvOp F L D 1 f = convOp L f := by
  funext u
  rw [twistedConvOp_apply, sigmaSectionActOn_one, convOp_apply]

theorem twistedConvOp_smul (σ : L ≃ₐ[F] L) (f : AdelicGL2 (𝓞 L) L → ℂ) (c : ℂ)
    (u : AdelicGL2 (𝓞 L) L → ℂ) :
    twistedConvOp F L D σ f (c • u) = c • twistedConvOp F L D σ f u := by
  rw [twistedConvOp_apply, sigmaSectionActOn_smul, ← convOp_apply, convOp_smul, convOp_apply,
    ← twistedConvOp_apply]

theorem twistedConvOp_add (σ : L ≃ₐ[F] L) {f : AdelicGL2 (𝓞 L) L → ℂ} (hf : Continuous f)
    (hfc : HasCompactSupport f) {u w : AdelicGL2 (𝓞 L) L → ℂ} (hu : Continuous u)
    (hw : Continuous w) :
    twistedConvOp F L D σ f (u + w) = twistedConvOp F L D σ f u + twistedConvOp F L D σ f w := by
  rw [twistedConvOp_apply, sigmaSectionActOn_add]
  exact rightConv_add_left L (continuous_sigmaSectionActOn F L D σ hu)
    (continuous_sigmaSectionActOn F L D σ hw) hf hfc

theorem isStableLinearOn_twistedConvOp (σ : L ≃ₐ[F] L)
    {V : Submodule ℂ (AdelicGL2 (𝓞 L) L → ℂ)} (hV : ∀ u ∈ V, Continuous u)
    {f : AdelicGL2 (𝓞 L) L → ℂ} (hf : Continuous f) (hfc : HasCompactSupport f)
    (hmaps : ∀ u ∈ V, twistedConvOp F L D σ f u ∈ V) :
    IsStableLinearOn V (twistedConvOp F L D σ f) where
  mapsTo := hmaps
  map_add u hu w hw := twistedConvOp_add F L D σ hf hfc (hV u hu) (hV w hw)
  map_smul c u _ := twistedConvOp_smul F L D σ f c u

open Classical in

def twistedConvTraceOn (σ : L ≃ₐ[F] L) (V : Submodule ℂ (AdelicGL2 (𝓞 L) L → ℂ))
    (hV : ∀ u ∈ V, Continuous u) (f : AdelicGL2 (𝓞 L) L → ℂ) (hf : Continuous f)
    (hfc : HasCompactSupport f) : ℂ :=
  if hmaps : ∀ u ∈ V, twistedConvOp F L D σ f u ∈ V then
    traceOn V (twistedConvOp F L D σ f) (isStableLinearOn_twistedConvOp F L D σ hV hf hfc hmaps)
  else 0

theorem twistedConvTraceOn_eq_traceOn (σ : L ≃ₐ[F] L)
    {V : Submodule ℂ (AdelicGL2 (𝓞 L) L → ℂ)} (hV : ∀ u ∈ V, Continuous u)
    {f : AdelicGL2 (𝓞 L) L → ℂ} (hf : Continuous f) (hfc : HasCompactSupport f)
    (hmaps : ∀ u ∈ V, twistedConvOp F L D σ f u ∈ V) :
    twistedConvTraceOn F L D σ V hV f hf hfc =
      traceOn V (twistedConvOp F L D σ f)
        (isStableLinearOn_twistedConvOp F L D σ hV hf hfc hmaps) :=
  dif_pos hmaps

theorem twistedConvTraceOn_eq_zero (σ : L ≃ₐ[F] L)
    {V : Submodule ℂ (AdelicGL2 (𝓞 L) L → ℂ)} (hV : ∀ u ∈ V, Continuous u)
    {f : AdelicGL2 (𝓞 L) L → ℂ} (hf : Continuous f) (hfc : HasCompactSupport f)
    (hmaps : ¬ ∀ u ∈ V, twistedConvOp F L D σ f u ∈ V) :
    twistedConvTraceOn F L D σ V hV f hf hfc = 0 :=
  dif_neg hmaps

theorem mapsTo_and_ne_bot_of_twistedConvTraceOn_ne_zero (σ : L ≃ₐ[F] L)
    {V : Submodule ℂ (AdelicGL2 (𝓞 L) L → ℂ)} (hV : ∀ u ∈ V, Continuous u)
    {f : AdelicGL2 (𝓞 L) L → ℂ} (hf : Continuous f) (hfc : HasCompactSupport f)
    (ht : twistedConvTraceOn F L D σ V hV f hf hfc ≠ 0) :
    (∀ u ∈ V, twistedConvOp F L D σ f u ∈ V) ∧ V ≠ ⊥ := by
  by_cases hmaps : ∀ u ∈ V, twistedConvOp F L D σ f u ∈ V
  · rw [twistedConvTraceOn_eq_traceOn F L D σ hV hf hfc hmaps] at ht
    exact ⟨hmaps, ne_bot_of_traceOn_ne_zero _ ht⟩
  · exact absurd (twistedConvTraceOn_eq_zero F L D σ hV hf hfc hmaps) ht

theorem twistedConvTraceOn_one {V : Submodule ℂ (AdelicGL2 (𝓞 L) L → ℂ)}
    (hV : ∀ u ∈ V, Continuous u) {f : AdelicGL2 (𝓞 L) L → ℂ} (hf : Continuous f)
    (hfc : HasCompactSupport f) :
    twistedConvTraceOn F L D 1 V hV f hf hfc = convTraceOn L V hV f hf hfc := by
  by_cases hmaps : ∀ u ∈ V, convOp L f u ∈ V
  · have hmaps' : ∀ u ∈ V, twistedConvOp F L D 1 f u ∈ V := by rwa [twistedConvOp_one]
    rw [twistedConvTraceOn_eq_traceOn F L D 1 hV hf hfc hmaps',
      convTraceOn_eq_traceOn L hV hf hfc hmaps]
    exact traceOn_congr _ _ (twistedConvOp_one F L D f)
  · have hmaps' : ¬ ∀ u ∈ V, twistedConvOp F L D 1 f u ∈ V := by rwa [twistedConvOp_one]
    rw [twistedConvTraceOn_eq_zero F L D 1 hV hf hfc hmaps', convTraceOn_eq_zero L hV hf hfc hmaps]

end Operators

section TypePiece

variable {H G : Type*} [Group H] [Group G]
variable {W : Type*} [AddCommGroup W] [Module ℂ W]

def IsRightEquivariant (ι : H →* G) (ρ : Representation ℂ H W) (T : W →ₗ[ℂ] (G → ℂ)) :
    Prop :=
  ∀ (k : H) (v : W) (x : G), T (ρ k v) x = T v (x * ι k)

def typeSubmodule (ι : H →* G) (ρ : Representation ℂ H W) : Submodule ℂ (G → ℂ) :=
  Submodule.span ℂ
    {f | ∃ T : W →ₗ[ℂ] (G → ℂ), IsRightEquivariant ι ρ T ∧ f ∈ LinearMap.range T}

theorem mem_typeSubmodule_of_isRightEquivariant {ι : H →* G} {ρ : Representation ℂ H W}
    {T : W →ₗ[ℂ] (G → ℂ)} (hT : IsRightEquivariant ι ρ T) (v : W) :
    T v ∈ typeSubmodule ι ρ :=
  Submodule.subset_span ⟨T, hT, LinearMap.mem_range_self T v⟩

theorem comp_mul_mem_typeSubmodule {ι : H →* G} {ρ : Representation ℂ H W} {f : G → ℂ}
    (hf : f ∈ typeSubmodule ι ρ) (k : H) : (fun x => f (x * ι k)) ∈ typeSubmodule ι ρ := by
  refine Submodule.span_induction (p := fun f _ => (fun x => f (x * ι k)) ∈ typeSubmodule ι ρ)
    ?_ ?_ ?_ ?_ hf
  · rintro _ ⟨T, hT, v, rfl⟩
    have hTv : (fun x => T v (x * ι k)) = T (ρ k v) := funext fun x => (hT k v x).symm
    rw [hTv]
    exact mem_typeSubmodule_of_isRightEquivariant hT _
  · exact (typeSubmodule ι ρ).zero_mem
  · exact fun _ _ _ _ hu hw => (typeSubmodule ι ρ).add_mem hu hw
  · exact fun c _ _ hu => (typeSubmodule ι ρ).smul_mem c hu

theorem comp_mul_mem_typeSubmodule_of_commute {ι : H →* G} {ρ : Representation ℂ H W}
    {f : G → ℂ} (hf : f ∈ typeSubmodule ι ρ) (g : G) (hg : ∀ k : H, Commute g (ι k)) :
    (fun x => f (x * g)) ∈ typeSubmodule ι ρ := by
  refine Submodule.span_induction (p := fun f _ => (fun x => f (x * g)) ∈ typeSubmodule ι ρ)
    ?_ ?_ ?_ ?_ hf
  · rintro _ ⟨T, hT, v, rfl⟩
    let Rg : (G → ℂ) →ₗ[ℂ] (G → ℂ) :=
      { toFun := fun u x => u (x * g)
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    have hS : IsRightEquivariant ι ρ (Rg ∘ₗ T) := by
      intro k' v' x
      show T (ρ k' v') (x * g) = T v' (x * ι k' * g)
      rw [hT k' v' (x * g), mul_assoc, mul_assoc, (hg k').eq]
    exact mem_typeSubmodule_of_isRightEquivariant hS v
  · exact (typeSubmodule ι ρ).zero_mem
  · exact fun _ _ _ _ hu hw => (typeSubmodule ι ρ).add_mem hu hw
  · exact fun c _ _ hu => (typeSubmodule ι ρ).smul_mem c hu

theorem comp_mul_mem_typeSubmodule_of_hom {G' : Type*} [Group G'] {ι : H →* G} {ι' : H →* G'}
    (π : G →* G') (hπ : ∀ k : H, π (ι k) = ι' k) {m : G → ℂ}
    (hm : ∀ (k : H) (x : G), m (x * ι k) = m x) {ρ : Representation ℂ H W} {fa : G' → ℂ}
    (hfa : fa ∈ typeSubmodule ι' ρ) : (fun x => fa (π x) * m x) ∈ typeSubmodule ι ρ := by
  refine Submodule.span_induction (p := fun fa _ => (fun x => fa (π x) * m x) ∈ typeSubmodule ι ρ)
    ?_ ?_ ?_ ?_ hfa
  · rintro _ ⟨T', hT', v, rfl⟩
    let T : W →ₗ[ℂ] (G → ℂ) :=
      { toFun := fun v x => T' v (π x) * m x
        map_add' := fun v₁ v₂ => funext fun x => by
          show T' (v₁ + v₂) (π x) * m x = T' v₁ (π x) * m x + T' v₂ (π x) * m x
          rw [map_add, Pi.add_apply, add_mul]
        map_smul' := fun c v => funext fun x => by
          show T' (c • v) (π x) * m x = c • (T' v (π x) * m x)
          rw [map_smul, Pi.smul_apply, smul_eq_mul, smul_eq_mul, mul_assoc] }
    have hT : IsRightEquivariant ι ρ T := by
      intro k v x
      show T' (ρ k v) (π x) * m x = T' v (π (x * ι k)) * m (x * ι k)
      rw [hT' k v (π x), map_mul, hπ k, hm k x]
    exact mem_typeSubmodule_of_isRightEquivariant hT v
  · show (fun x => (0 : G' → ℂ) (π x) * m x) ∈ typeSubmodule ι ρ
    have h0 : (fun x => (0 : G' → ℂ) (π x) * m x) = 0 := funext fun x => zero_mul _
    rw [h0]
    exact Submodule.zero_mem _
  · intro a b _ _ ha hb
    have hab : (fun x => (a + b) (π x) * m x) =
        (fun x => a (π x) * m x) + fun x => b (π x) * m x :=
      funext fun x => add_mul _ _ _
    rw [hab]
    exact Submodule.add_mem _ ha hb
  · intro c a _ ha
    have hca : (fun x => (c • a) (π x) * m x) = c • fun x => a (π x) * m x :=
      funext fun x => by
        show c • a (π x) * m x = c • (a (π x) * m x)
        rw [smul_eq_mul, smul_eq_mul, mul_assoc]
    rw [hca]
    exact Submodule.smul_mem _ c ha

omit [Group G] in

theorem comp_mul_mem_iSup_of_forall {G' : Type*} {ι₀ : Type*} (π : G → G') (m : G → ℂ)
    (S' : ι₀ → Submodule ℂ (G' → ℂ)) (S : ι₀ → Submodule ℂ (G → ℂ))
    (h : ∀ i, ∀ fa ∈ S' i, (fun x => fa (π x) * m x) ∈ S i) {fa : G' → ℂ}
    (hfa : fa ∈ ⨆ i, S' i) : (fun x => fa (π x) * m x) ∈ ⨆ i, S i := by
  refine Submodule.iSup_induction _ (motive := fun fa => (fun x => fa (π x) * m x) ∈ ⨆ i, S i)
    hfa ?_ ?_ ?_
  · exact fun i fa hfa => le_iSup S i (h i fa hfa)
  · show (fun x => (0 : G' → ℂ) (π x) * m x) ∈ ⨆ i, S i
    have h0 : (fun x => (0 : G' → ℂ) (π x) * m x) = 0 := funext fun x => zero_mul _
    rw [h0]
    exact Submodule.zero_mem _
  · intro a b ha hb
    have hab : (fun x => (a + b) (π x) * m x) =
        (fun x => a (π x) * m x) + fun x => b (π x) * m x :=
      funext fun x => add_mul _ _ _
    rw [hab]
    exact Submodule.add_mem _ ha hb

def charRep (χ : H →* ℂˣ) : Representation ℂ H (Fin 1 → ℂ) :=
  (DistribMulAction.toModuleEnd ℂ (Fin 1 → ℂ)).comp ((Units.coeHom ℂ).comp χ)

@[simp] theorem charRep_apply (χ : H →* ℂˣ) (k : H) (v : Fin 1 → ℂ) :
    charRep χ k v = ((χ k : ℂˣ) : ℂ) • v :=
  rfl

theorem charRep_dual_apply (χ : H →* ℂˣ) (k : H) (l : Module.Dual ℂ (Fin 1 → ℂ)) :
    (charRep χ).dual k l = ((χ k⁻¹ : ℂˣ) : ℂ) • l := by
  rw [Representation.dual_apply, Module.Dual.transpose_apply]
  refine LinearMap.ext fun v => ?_
  rw [LinearMap.comp_apply, charRep_apply, map_smul, LinearMap.smul_apply]

theorem mem_typeSubmodule_charRep {ι : H →* G} {χ : H →* ℂˣ} {f : G → ℂ}
    (hf : ∀ (k : H) (x : G), f (x * ι k) = ((χ k : ℂˣ) : ℂ) * f x) :
    f ∈ typeSubmodule ι (charRep χ) := by
  have hT : IsRightEquivariant ι (charRep χ)
      ((LinearMap.proj 0 : (Fin 1 → ℂ) →ₗ[ℂ] ℂ).smulRight f) := by
    intro k v x
    simp only [LinearMap.smulRight_apply, LinearMap.proj_apply, charRep_apply, Pi.smul_apply,
      smul_eq_mul]
    rw [hf k x]
    ring
  have h1 : ((LinearMap.proj 0 : (Fin 1 → ℂ) →ₗ[ℂ] ℂ).smulRight f) (fun _ => 1) = f := by
    rw [LinearMap.smulRight_apply, LinearMap.proj_apply]
    exact one_smul ℂ f
  have hmem := mem_typeSubmodule_of_isRightEquivariant hT (fun _ => 1)
  rwa [h1] at hmem

theorem apply_mul_eq_of_mem_typeSubmodule_charRep {ι : H →* G} {χ : H →* ℂˣ} {f : G → ℂ}
    (hf : f ∈ typeSubmodule ι (charRep χ)) (k : H) (x : G) :
    f (x * ι k) = ((χ k : ℂˣ) : ℂ) * f x := by
  revert k x
  refine Submodule.span_induction
    (p := fun f _ => ∀ (k : H) (x : G), f (x * ι k) = ((χ k : ℂˣ) : ℂ) * f x) ?_ ?_ ?_ ?_ hf
  · rintro _ ⟨T, hT, v, rfl⟩ k x
    rw [← hT k v x, charRep_apply, map_smul, Pi.smul_apply, smul_eq_mul]
  · intro k x
    simp
  · intro f g _ _ hf hg k x
    rw [Pi.add_apply, Pi.add_apply, hf, hg, mul_add]
  · intro c f _ hf k x
    rw [Pi.smul_apply, Pi.smul_apply, hf, smul_eq_mul, smul_eq_mul]
    ring

theorem mem_typeSubmodule_charRep_iff (ι : H →* G) (χ : H →* ℂˣ) (f : G → ℂ) :
    f ∈ typeSubmodule ι (charRep χ) ↔
      ∀ (k : H) (x : G), f (x * ι k) = ((χ k : ℂˣ) : ℂ) * f x :=
  ⟨fun hf => apply_mul_eq_of_mem_typeSubmodule_charRep hf, mem_typeSubmodule_charRep⟩

theorem mem_typeSubmodule_charRep_dual {ι : H →* G} {χ : H →* ℂˣ} {f : G → ℂ}
    (hf : ∀ (k : H) (x : G), f (x * ι k) = ((χ k⁻¹ : ℂˣ) : ℂ) * f x) :
    f ∈ typeSubmodule ι (charRep χ).dual := by
  have hT : IsRightEquivariant ι (charRep χ).dual
      ((LinearMap.applyₗ (fun _ => (1 : ℂ)) :
        Module.Dual ℂ (Fin 1 → ℂ) →ₗ[ℂ] ℂ).smulRight f) := by
    intro k l x
    simp only [LinearMap.smulRight_apply, LinearMap.applyₗ_apply_apply, charRep_dual_apply,
      LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul]
    rw [hf k x]
    ring
  have h1 : ((LinearMap.applyₗ (fun _ => (1 : ℂ)) :
      Module.Dual ℂ (Fin 1 → ℂ) →ₗ[ℂ] ℂ).smulRight f) (LinearMap.proj 0) = f := by
    rw [LinearMap.smulRight_apply, LinearMap.applyₗ_apply_apply, LinearMap.proj_apply]
    exact one_smul ℂ f
  have hmem := mem_typeSubmodule_of_isRightEquivariant hT (LinearMap.proj 0)
  rwa [h1] at hmem

theorem apply_mul_eq_of_mem_typeSubmodule_charRep_dual {ι : H →* G} {χ : H →* ℂˣ}
    {f : G → ℂ} (hf : f ∈ typeSubmodule ι (charRep χ).dual) (k : H) (x : G) :
    f (x * ι k) = ((χ k⁻¹ : ℂˣ) : ℂ) * f x := by
  revert k x
  refine Submodule.span_induction
    (p := fun f _ => ∀ (k : H) (x : G), f (x * ι k) = ((χ k⁻¹ : ℂˣ) : ℂ) * f x) ?_ ?_ ?_ ?_ hf
  · rintro _ ⟨T, hT, l, rfl⟩ k x
    rw [← hT k l x, charRep_dual_apply, map_smul, Pi.smul_apply, smul_eq_mul]
  · intro k x
    simp
  · intro f g _ _ hf hg k x
    rw [Pi.add_apply, Pi.add_apply, hf, hg, mul_add]
  · intro c f _ hf k x
    rw [Pi.smul_apply, Pi.smul_apply, hf, smul_eq_mul, smul_eq_mul]
    ring

theorem mem_typeSubmodule_charRep_dual_iff (ι : H →* G) (χ : H →* ℂˣ) (f : G → ℂ) :
    f ∈ typeSubmodule ι (charRep χ).dual ↔
      ∀ (k : H) (x : G), f (x * ι k) = ((χ k⁻¹ : ℂˣ) : ℂ) * f x :=
  ⟨fun hf => apply_mul_eq_of_mem_typeSubmodule_charRep_dual hf, mem_typeSubmodule_charRep_dual⟩

end TypePiece

section ArchCut

variable (F : Type) [Field F] [NumberField F]

structure ArchRepAt (w : InfinitePlace F) where

  n : ℕ

  ρ : Representation ℂ (rowIsometrySubgroup₀ w.Completion) (Fin n → ℂ)

def ArchRepAt.ofChar {w : InfinitePlace F} (χ : rowIsometrySubgroup₀ w.Completion →* ℂˣ) :
    ArchRepAt F w where
  n := 1
  ρ := charRep χ

def rowIsometryInclAt₀ (w : InfinitePlace F) :
    rowIsometrySubgroup₀ w.Completion →* AdelicGL2 (𝓞 F) F :=
  (adelicArchGLInclAt F w).comp (rowIsometrySubgroup₀ w.Completion).subtype

theorem rowIsometryInclAt₀_apply (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion) :
    rowIsometryInclAt₀ F w k = adelicArchGLInclAt F w (k : GL (Fin 2) w.Completion) :=
  rfl

omit [NumberField F] in

theorem commute_archGLIncl_of_ne {v w : InfinitePlace F} (hvw : v ≠ w)
    (a : GL (Fin 2) v.Completion) (b : GL (Fin 2) w.Completion) :
    Commute (archGLIncl F v a) (archGLIncl F w b) := by
  refine Units.ext (Matrix.ext fun i j => funext fun u => ?_)
  show ((archGLIncl F v a * archGLIncl F w b : GL (Fin 2) (InfiniteAdeleRing F)) :
      Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j u =
    ((archGLIncl F w b * archGLIncl F v a : GL (Fin 2) (InfiniteAdeleRing F)) :
      Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j u
  rw [← AdelicLevel.archComponent_apply, ← AdelicLevel.archComponent_apply, map_mul, map_mul]
  by_cases huv : u = v
  · subst huv
    rw [archComponent_archGLIncl_self, archComponent_archGLIncl_of_ne F hvw, mul_one, one_mul]
  · rw [archComponent_archGLIncl_of_ne F huv]
    by_cases huw : u = w
    · subst huw
      rw [archComponent_archGLIncl_self, one_mul, mul_one]
    · rw [archComponent_archGLIncl_of_ne F huw, one_mul]

theorem commute_adelicArchGLInclAt_of_ne {v w : InfinitePlace F} (hvw : v ≠ w)
    (a : GL (Fin 2) v.Completion) (b : GL (Fin 2) w.Completion) :
    Commute (adelicArchGLInclAt F v a) (adelicArchGLInclAt F w b) :=
  (commute_archGLIncl_of_ne F hvw a b).map (adelicArchGLIncl F)

def archRowIsometrySubgroup₀ (w : InfinitePlace F) : Subgroup (AdelicGL2 (𝓞 F) F) :=
  (rowIsometrySubgroup₀ w.Completion).map (adelicArchGLInclAt F w)

theorem archRowIsometrySubgroup₀_eq_range (w : InfinitePlace F) :
    archRowIsometrySubgroup₀ F w = (rowIsometryInclAt₀ F w).range := by
  ext g
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨⟨k, hk⟩, rfl⟩
  · rintro ⟨k, rfl⟩
    exact ⟨k, k.2, rfl⟩

def archTypeSubmoduleAt (w : InfinitePlace F) (τ : ArchRepAt F w) :
    Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ) :=
  typeSubmodule (rowIsometryInclAt₀ F w) τ.ρ

def archDualTypeSubmoduleAt (w : InfinitePlace F) (τ : ArchRepAt F w) :
    Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ) :=
  typeSubmodule (rowIsometryInclAt₀ F w) τ.ρ.dual

structure ArchTypeFamily where

  card : InfinitePlace F → ℕ

  rep : (w : InfinitePlace F) → Fin (card w) → ArchRepAt F w

def ArchTypeFamily.ofChar (χ : ∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion →* ℂˣ) :
    ArchTypeFamily F where
  card := fun _ => 1
  rep := fun w _ => ArchRepAt.ofChar F (χ w)

def archCutSubmodule (tys : ArchTypeFamily F) : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ) :=
  ⨅ w : InfinitePlace F, ⨆ i : Fin (tys.card w), archTypeSubmoduleAt F w (tys.rep w i)

def archDualCutSubmodule (tys : ArchTypeFamily F) : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ) :=
  ⨅ w : InfinitePlace F, ⨆ i : Fin (tys.card w), archDualTypeSubmoduleAt F w (tys.rep w i)

theorem mem_archCutSubmodule_iff (tys : ArchTypeFamily F) (f : AdelicGL2 (𝓞 F) F → ℂ) :
    f ∈ archCutSubmodule F tys ↔
      ∀ w : InfinitePlace F, f ∈ ⨆ i : Fin (tys.card w), archTypeSubmoduleAt F w (tys.rep w i) :=
  Submodule.mem_iInf _

theorem mem_archDualCutSubmodule_iff (tys : ArchTypeFamily F) (f : AdelicGL2 (𝓞 F) F → ℂ) :
    f ∈ archDualCutSubmodule F tys ↔
      ∀ w : InfinitePlace F,
        f ∈ ⨆ i : Fin (tys.card w), archDualTypeSubmoduleAt F w (tys.rep w i) :=
  Submodule.mem_iInf _

theorem archCutSubmodule_eq_bot_of_card_eq_zero (tys : ArchTypeFamily F) {w : InfinitePlace F}
    (hw : tys.card w = 0) : archCutSubmodule F tys = ⊥ := by
  haveI : IsEmpty (Fin (tys.card w)) := ⟨fun i => absurd i.2 (by omega)⟩
  exact le_bot_iff.mp (le_trans (iInf_le _ w) (iSup_of_empty _).le)

def ArchTypeFamily.IsContainedIn (tys tys' : ArchTypeFamily F) : Prop :=
  ∀ (w : InfinitePlace F) (i : Fin (tys.card w)),
    ∃ j : Fin (tys'.card w), tys'.rep w j = tys.rep w i

theorem archCutSubmodule_mono {tys tys' : ArchTypeFamily F} (h : tys.IsContainedIn F tys') :
    archCutSubmodule F tys ≤ archCutSubmodule F tys' := by
  refine iInf_mono fun w => iSup_le fun i => ?_
  obtain ⟨j, hj⟩ := h w i
  rw [← hj]
  exact le_iSup (fun j => archTypeSubmoduleAt F w (tys'.rep w j)) j

theorem archDualCutSubmodule_mono {tys tys' : ArchTypeFamily F} (h : tys.IsContainedIn F tys') :
    archDualCutSubmodule F tys ≤ archDualCutSubmodule F tys' := by
  refine iInf_mono fun w => iSup_le fun i => ?_
  obtain ⟨j, hj⟩ := h w i
  rw [← hj]
  exact le_iSup (fun j => archDualTypeSubmoduleAt F w (tys'.rep w j)) j

theorem comp_mul_rowIsometryInclAt₀_mem_archCutSubmodule {tys : ArchTypeFamily F}
    {f : AdelicGL2 (𝓞 F) F → ℂ} (hf : f ∈ archCutSubmodule F tys) (w : InfinitePlace F)
    (k : rowIsometrySubgroup₀ w.Completion) :
    (fun x => f (x * rowIsometryInclAt₀ F w k)) ∈ archCutSubmodule F tys := by
  rw [mem_archCutSubmodule_iff] at hf ⊢
  intro w'
  refine Submodule.iSup_induction _
    (motive := fun f => (fun x => f (x * rowIsometryInclAt₀ F w k)) ∈
      ⨆ i : Fin (tys.card w'), archTypeSubmoduleAt F w' (tys.rep w' i)) (hf w') ?_ ?_ ?_
  · intro i f hfi
    refine le_iSup (fun j => archTypeSubmoduleAt F w' (tys.rep w' j)) i ?_
    by_cases hw : w' = w
    · subst hw
      exact comp_mul_mem_typeSubmodule hfi k
    · exact comp_mul_mem_typeSubmodule_of_commute hfi _ fun k' =>
        commute_adelicArchGLInclAt_of_ne F (fun h => hw h.symm) _ _
  · exact Submodule.zero_mem _
  · exact fun _ _ hu hw => Submodule.add_mem _ hu hw

theorem mem_archCutSubmodule_ofChar_iff
    (χ : ∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion →* ℂˣ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) :
    φ ∈ archCutSubmodule F (ArchTypeFamily.ofChar F χ) ↔ HasArchType₀ F χ φ := by
  show φ ∈ ⨅ w : InfinitePlace F,
      ⨆ _ : Fin 1, archTypeSubmoduleAt F w (ArchRepAt.ofChar F (χ w)) ↔ _
  simp only [iSup_const, Submodule.mem_iInf]
  exact forall_congr' fun w => mem_typeSubmodule_charRep_iff _ (χ w) φ

theorem mem_archTypeSubmoduleAt_ofChar_iff (w : InfinitePlace F)
    (χ : rowIsometrySubgroup₀ w.Completion →* ℂˣ) (φ : AdelicGL2 (𝓞 F) F → ℂ) :
    φ ∈ archTypeSubmoduleAt F w (ArchRepAt.ofChar F χ) ↔ HasArchCharacterAt₀ F w χ φ :=
  mem_typeSubmodule_charRep_iff _ χ φ

theorem mem_archDualTypeSubmoduleAt_ofChar_iff (w : InfinitePlace F)
    (χ : rowIsometrySubgroup₀ w.Completion →* ℂˣ) (φ : AdelicGL2 (𝓞 F) F → ℂ) :
    φ ∈ archDualTypeSubmoduleAt F w (ArchRepAt.ofChar F χ) ↔
      ∀ (k : rowIsometrySubgroup₀ w.Completion) (g : AdelicGL2 (𝓞 F) F),
        φ (g * rowIsometryInclAt₀ F w k) = ((χ k⁻¹ : ℂˣ) : ℂ) * φ g :=
  mem_typeSubmodule_charRep_dual_iff _ χ φ

def IsArchBiFinite (tys : ArchTypeFamily F) (f : AdelicGL2 (𝓞 F) F → ℂ) : Prop :=
  (fun x => f x⁻¹) ∈ archCutSubmodule F tys ∧ f ∈ archDualCutSubmodule F tys

theorem isArchBiFinite_zero (tys : ArchTypeFamily F) : IsArchBiFinite F tys 0 :=
  ⟨(archCutSubmodule F tys).zero_mem, (archDualCutSubmodule F tys).zero_mem⟩

theorem IsArchBiFinite.mono {tys tys' : ArchTypeFamily F} {f : AdelicGL2 (𝓞 F) F → ℂ}
    (hf : IsArchBiFinite F tys f) (h : tys.IsContainedIn F tys') : IsArchBiFinite F tys' f :=
  ⟨archCutSubmodule_mono F h hf.1, archDualCutSubmodule_mono F h hf.2⟩

theorem not_isArchBiFinite_const_ofChar
    {χ : ∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion →* ℂˣ} {w : InfinitePlace F}
    {k : rowIsometrySubgroup₀ w.Completion} (hχ : χ w k ≠ 1) {c : ℂ} (hc : c ≠ 0) :
    ¬ IsArchBiFinite F (ArchTypeFamily.ofChar F χ) (fun _ => c) := by
  rintro ⟨hleft, -⟩
  have h : c = ((χ w k : ℂˣ) : ℂ) * c :=
    (mem_archCutSubmodule_ofChar_iff F χ (fun _ => c)).mp hleft w k 1
  exact hχ (Units.val_eq_one.mp (mul_right_cancel₀ hc ((one_mul c).trans h).symm))

theorem comp_inv_mem_archTypeSubmoduleAt_ofChar_iff (w : InfinitePlace F)
    (χ : rowIsometrySubgroup₀ w.Completion →* ℂˣ) (f : AdelicGL2 (𝓞 F) F → ℂ) :
    (fun x => f x⁻¹) ∈ archTypeSubmoduleAt F w (ArchRepAt.ofChar F χ) ↔
      ∀ (k : rowIsometrySubgroup₀ w.Completion) (y : AdelicGL2 (𝓞 F) F),
        f (rowIsometryInclAt₀ F w k * y) = ((χ k⁻¹ : ℂˣ) : ℂ) * f y := by
  rw [mem_archTypeSubmoduleAt_ofChar_iff]
  constructor
  · intro h k y
    have h' : f (y⁻¹ * rowIsometryInclAt₀ F w k⁻¹)⁻¹ = ((χ k⁻¹ : ℂˣ) : ℂ) * f y⁻¹⁻¹ := h k⁻¹ y⁻¹
    rwa [mul_inv_rev, ← map_inv, inv_inv, inv_inv] at h'
  · intro h k g
    show f (g * adelicArchGLInclAt F w (k : GL (Fin 2) w.Completion))⁻¹ = (χ k : ℂ) * f g⁻¹
    rw [mul_inv_rev, ← rowIsometryInclAt₀_apply, ← map_inv, h k⁻¹ g⁻¹, inv_inv]

theorem hasArchCharacterAt₀_rightConv (w : InfinitePlace F)
    (χ : rowIsometrySubgroup₀ w.Completion →* ℂˣ) (φ f : AdelicGL2 (𝓞 F) F → ℂ)
    (hf : ∀ (k : rowIsometrySubgroup₀ w.Completion) (y : AdelicGL2 (𝓞 F) F),
      f (rowIsometryInclAt₀ F w k * y) = ((χ k⁻¹ : ℂˣ) : ℂ) * f y) :
    HasArchCharacterAt₀ F w χ (rightConv F φ f) := by
  intro k g
  letI : MeasurableSpace (AdelicGL2 (𝓞 F) F) := AdelicHaar.glBorel (Fin 2) (𝓞 F) F
  haveI : BorelSpace (AdelicGL2 (𝓞 F) F) := AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 F) F
  haveI : (AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F).IsHaarMeasure :=
    AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F
  have hlaw : ∀ y : AdelicGL2 (𝓞 F) F,
      f ((rowIsometryInclAt₀ F w k)⁻¹ * y) = ((χ k : ℂˣ) : ℂ) * f y := by
    intro y
    rw [← map_inv, hf k⁻¹ y, inv_inv]
  rw [← rowIsometryInclAt₀_apply, rightConv_apply, rightConv_apply]
  have key : (fun x => φ (g * rowIsometryInclAt₀ F w k * x) * f x) =
      fun x => (fun y => φ (g * y) * f ((rowIsometryInclAt₀ F w k)⁻¹ * y))
        (rowIsometryInclAt₀ F w k * x) := by
    funext x
    simp only [mul_assoc, inv_mul_cancel_left]
  rw [key, MeasureTheory.integral_mul_left_eq_self
    (fun y => φ (g * y) * f ((rowIsometryInclAt₀ F w k)⁻¹ * y)) (rowIsometryInclAt₀ F w k)]
  simp only [hlaw, mul_left_comm _ (((χ k : ℂˣ) : ℂ))]
  exact MeasureTheory.integral_const_mul _ _

theorem rightConv_mem_archTypeSubmoduleAt_ofChar (w : InfinitePlace F)
    (χ : rowIsometrySubgroup₀ w.Completion →* ℂˣ) (φ f : AdelicGL2 (𝓞 F) F → ℂ)
    (hf : (fun x => f x⁻¹) ∈ archTypeSubmoduleAt F w (ArchRepAt.ofChar F χ)) :
    rightConv F φ f ∈ archTypeSubmoduleAt F w (ArchRepAt.ofChar F χ) :=
  (mem_archTypeSubmoduleAt_ofChar_iff F w χ _).mpr
    (hasArchCharacterAt₀_rightConv F w χ φ f
      ((comp_inv_mem_archTypeSubmoduleAt_ofChar_iff F w χ f).mp hf))

end ArchCut

section ArchFactor

variable (F : Type) [Field F] [NumberField F]

def archRowIsometryInclAt₀ (w : InfinitePlace F) :
    rowIsometrySubgroup₀ w.Completion →* GL (Fin 2) (InfiniteAdeleRing F) :=
  (archGLIncl F w).comp (rowIsometrySubgroup₀ w.Completion).subtype

theorem glArch_rowIsometryInclAt₀ (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion) :
    AdelicLevel.glArch (𝓞 F) F (rowIsometryInclAt₀ F w k) = archRowIsometryInclAt₀ F w k :=
  glArch_adelicArchGLIncl F _

theorem glFin_rowIsometryInclAt₀ (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion) :
    AdelicLevel.glFin (𝓞 F) F (rowIsometryInclAt₀ F w k) = 1 :=
  glFin_adelicArchGLIncl F _

def archFactorTypeSubmoduleAt (w : InfinitePlace F) (τ : ArchRepAt F w) :
    Submodule ℂ (GL (Fin 2) (InfiniteAdeleRing F) → ℂ) :=
  typeSubmodule (archRowIsometryInclAt₀ F w) τ.ρ

def archFactorDualTypeSubmoduleAt (w : InfinitePlace F) (τ : ArchRepAt F w) :
    Submodule ℂ (GL (Fin 2) (InfiniteAdeleRing F) → ℂ) :=
  typeSubmodule (archRowIsometryInclAt₀ F w) τ.ρ.dual

def archFactorCutSubmodule (tys : ArchTypeFamily F) :
    Submodule ℂ (GL (Fin 2) (InfiniteAdeleRing F) → ℂ) :=
  ⨅ w : InfinitePlace F, ⨆ i : Fin (tys.card w), archFactorTypeSubmoduleAt F w (tys.rep w i)

def archFactorDualCutSubmodule (tys : ArchTypeFamily F) :
    Submodule ℂ (GL (Fin 2) (InfiniteAdeleRing F) → ℂ) :=
  ⨅ w : InfinitePlace F, ⨆ i : Fin (tys.card w), archFactorDualTypeSubmoduleAt F w (tys.rep w i)

def IsArchFactorBiFinite (tys : ArchTypeFamily F) (fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ) :
    Prop :=
  (fun x => fa x⁻¹) ∈ archFactorCutSubmodule F tys ∧ fa ∈ archFactorDualCutSubmodule F tys

omit [NumberField F] in

theorem isArchFactorBiFinite_zero (tys : ArchTypeFamily F) : IsArchFactorBiFinite F tys 0 :=
  ⟨(archFactorCutSubmodule F tys).zero_mem, (archFactorDualCutSubmodule F tys).zero_mem⟩

theorem IsArchBiFinite.of_factorization {tys : ArchTypeFamily F} {f : AdelicGL2 (𝓞 F) F → ℂ}
    {fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ} {ff : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) → ℂ}
    (hf : ∀ g, f g = fa (AdelicLevel.glArch (𝓞 F) F g) * ff (AdelicLevel.glFin (𝓞 F) F g))
    (hfa : IsArchFactorBiFinite F tys fa) : IsArchBiFinite F tys f := by
  obtain ⟨hl, hr⟩ := hfa
  have hmr : ∀ (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion)
      (x : AdelicGL2 (𝓞 F) F),
      ff (AdelicLevel.glFin (𝓞 F) F (x * rowIsometryInclAt₀ F w k)) =
        ff (AdelicLevel.glFin (𝓞 F) F x) := by
    intro w k x
    rw [map_mul, glFin_rowIsometryInclAt₀, mul_one]
  have hml : ∀ (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion)
      (x : AdelicGL2 (𝓞 F) F),
      ff (AdelicLevel.glFin (𝓞 F) F (x * rowIsometryInclAt₀ F w k))⁻¹ =
        ff (AdelicLevel.glFin (𝓞 F) F x)⁻¹ := by
    intro w k x
    rw [map_mul, glFin_rowIsometryInclAt₀, mul_one]
  constructor
  · have hfeq : (fun x => f x⁻¹) = fun x =>
        (fun y => fa y⁻¹) (AdelicLevel.glArch (𝓞 F) F x) * ff (AdelicLevel.glFin (𝓞 F) F x)⁻¹ := by
      funext x
      rw [hf, map_inv, map_inv]
    rw [hfeq, mem_archCutSubmodule_iff]
    intro w
    exact comp_mul_mem_iSup_of_forall (AdelicLevel.glArch (𝓞 F) F)
      (fun x => ff (AdelicLevel.glFin (𝓞 F) F x)⁻¹)
      (fun i => archFactorTypeSubmoduleAt F w (tys.rep w i))
      (fun i => archTypeSubmoduleAt F w (tys.rep w i))
      (fun i fa' hfa' => comp_mul_mem_typeSubmodule_of_hom (AdelicLevel.glArch (𝓞 F) F)
        (glArch_rowIsometryInclAt₀ F w) (hml w) hfa')
      ((Submodule.mem_iInf _).mp hl w)
  · have hfeq : f = fun x =>
        fa (AdelicLevel.glArch (𝓞 F) F x) * ff (AdelicLevel.glFin (𝓞 F) F x) := funext hf
    rw [hfeq, mem_archDualCutSubmodule_iff]
    intro w
    exact comp_mul_mem_iSup_of_forall (AdelicLevel.glArch (𝓞 F) F)
      (fun x => ff (AdelicLevel.glFin (𝓞 F) F x))
      (fun i => archFactorDualTypeSubmoduleAt F w (tys.rep w i))
      (fun i => archDualTypeSubmoduleAt F w (tys.rep w i))
      (fun i fa' hfa' => comp_mul_mem_typeSubmodule_of_hom (AdelicLevel.glArch (𝓞 F) F)
        (glArch_rowIsometryInclAt₀ F w) (hmr w) hfa')
      ((Submodule.mem_iInf _).mp hr w)

end ArchFactor

section CutTrace

variable (K : Type) [Field K] [NumberField K]

theorem continuous_of_mem_isotypicCuspSubmodule_inf {pins : CarrierPins K} {ξ : pins.Z →* ℂˣ}
    {N : Ideal (𝓞 K)} {S : Finset (HeightOneSpectrum (𝓞 K))} {Φ : HeckeEigensystem K ℂ}
    {W : Submodule ℂ (AdelicGL2 (𝓞 K) K → ℂ)} :
    ∀ u ∈ isotypicCuspSubmodule K pins ξ N S Φ ⊓ W, Continuous u :=
  fun _ hu => continuous_of_mem_isotypicCuspSubmodule (Submodule.mem_inf.mp hu).1

def cutTrace (pins : CarrierPins K) (ξ : pins.Z →* ℂˣ) (N : Ideal (𝓞 K))
    (S : Finset (HeightOneSpectrum (𝓞 K))) (Ψ : HeckeEigensystem K ℂ) (tys : ArchTypeFamily K)
    (f : AdelicGL2 (𝓞 K) K → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f) : ℂ :=
  convTraceOn K (isotypicCuspSubmodule K pins ξ N S Ψ ⊓ archCutSubmodule K tys)
    (continuous_of_mem_isotypicCuspSubmodule_inf K) f hf hfc

theorem cutTrace_eq (pins : CarrierPins K) (ξ : pins.Z →* ℂˣ) (N : Ideal (𝓞 K))
    (S : Finset (HeightOneSpectrum (𝓞 K))) (Ψ : HeckeEigensystem K ℂ) (tys : ArchTypeFamily K)
    (f : AdelicGL2 (𝓞 K) K → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f) :
    cutTrace K pins ξ N S Ψ tys f hf hfc =
      convTraceOn K (isotypicCuspSubmodule K pins ξ N S Ψ ⊓ archCutSubmodule K tys)
        (continuous_of_mem_isotypicCuspSubmodule_inf K) f hf hfc :=
  rfl

theorem mapsTo_and_ne_bot_of_cutTrace_ne_zero {pins : CarrierPins K} {ξ : pins.Z →* ℂˣ}
    {N : Ideal (𝓞 K)} {S : Finset (HeightOneSpectrum (𝓞 K))} {Ψ : HeckeEigensystem K ℂ}
    {tys : ArchTypeFamily K}
    {f : AdelicGL2 (𝓞 K) K → ℂ} {hf : Continuous f} {hfc : HasCompactSupport f}
    (ht : cutTrace K pins ξ N S Ψ tys f hf hfc ≠ 0) :
    (∀ u ∈ isotypicCuspSubmodule K pins ξ N S Ψ ⊓ archCutSubmodule K tys,
        convOp K f u ∈ isotypicCuspSubmodule K pins ξ N S Ψ ⊓ archCutSubmodule K tys) ∧
      isotypicCuspSubmodule K pins ξ N S Ψ ⊓ archCutSubmodule K tys ≠ ⊥ :=
  mapsTo_and_ne_bot_of_convTraceOn_ne_zero K _ hf hfc ht

theorem isotypicCuspSubmodule_ne_bot_of_cutTrace_ne_zero {pins : CarrierPins K}
    {ξ : pins.Z →* ℂˣ} {N : Ideal (𝓞 K)} {S : Finset (HeightOneSpectrum (𝓞 K))}
    {Ψ : HeckeEigensystem K ℂ} {tys : ArchTypeFamily K} {f : AdelicGL2 (𝓞 K) K → ℂ}
    {hf : Continuous f}
    {hfc : HasCompactSupport f} (ht : cutTrace K pins ξ N S Ψ tys f hf hfc ≠ 0) :
    isotypicCuspSubmodule K pins ξ N S Ψ ≠ ⊥ :=
  fun h => (mapsTo_and_ne_bot_of_cutTrace_ne_zero K ht).2 (by rw [h, bot_inf_eq])

theorem isArithGenuineCuspRealizable_of_cutTrace_ne_zero {pins : CarrierPins K}
    {ξ : pins.Z →* ℂˣ} {N : Ideal (𝓞 K)} {S : Finset (HeightOneSpectrum (𝓞 K))}
    {Ψ : HeckeEigensystem K ℂ} {tys : ArchTypeFamily K} {f : AdelicGL2 (𝓞 K) K → ℂ}
    {hf : Continuous f} {hfc : HasCompactSupport f} (hN : Ψ.level = N)
    (ht : cutTrace K pins ξ N S Ψ tys f hf hfc ≠ 0) : IsArithGenuineCuspRealizable K pins Ψ := by
  subst hN
  exact isArithGenuineCuspRealizable_of_isotypicCuspSubmodule_ne_bot
    (isotypicCuspSubmodule_ne_bot_of_cutTrace_ne_zero K ht)

variable (F L : Type) [Field F] [Field L] [NumberField L] [Algebra F L]
variable (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) F L)

def twistedCutTrace (σ : L ≃ₐ[F] L) (pins : CarrierPins L) (ξ : pins.Z →* ℂˣ) (N : Ideal (𝓞 L))
    (S : Finset (HeightOneSpectrum (𝓞 L))) (Ψ : HeckeEigensystem L ℂ) (tys : ArchTypeFamily L)
    (f : AdelicGL2 (𝓞 L) L → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f) : ℂ :=
  twistedConvTraceOn F L D σ (isotypicCuspSubmodule L pins ξ N S Ψ ⊓ archCutSubmodule L tys)
    (continuous_of_mem_isotypicCuspSubmodule_inf L) f hf hfc

theorem twistedCutTrace_eq (σ : L ≃ₐ[F] L) (pins : CarrierPins L) (ξ : pins.Z →* ℂˣ)
    (N : Ideal (𝓞 L)) (S : Finset (HeightOneSpectrum (𝓞 L))) (Ψ : HeckeEigensystem L ℂ)
    (tys : ArchTypeFamily L) (f : AdelicGL2 (𝓞 L) L → ℂ) (hf : Continuous f)
    (hfc : HasCompactSupport f) :
    twistedCutTrace F L D σ pins ξ N S Ψ tys f hf hfc =
      twistedConvTraceOn F L D σ (isotypicCuspSubmodule L pins ξ N S Ψ ⊓ archCutSubmodule L tys)
        (continuous_of_mem_isotypicCuspSubmodule_inf L) f hf hfc :=
  rfl

theorem mapsTo_and_ne_bot_of_twistedCutTrace_ne_zero {σ : L ≃ₐ[F] L} {pins : CarrierPins L}
    {ξ : pins.Z →* ℂˣ} {N : Ideal (𝓞 L)} {S : Finset (HeightOneSpectrum (𝓞 L))}
    {Ψ : HeckeEigensystem L ℂ} {tys : ArchTypeFamily L} {f : AdelicGL2 (𝓞 L) L → ℂ}
    {hf : Continuous f}
    {hfc : HasCompactSupport f} (ht : twistedCutTrace F L D σ pins ξ N S Ψ tys f hf hfc ≠ 0) :
    (∀ u ∈ isotypicCuspSubmodule L pins ξ N S Ψ ⊓ archCutSubmodule L tys,
        twistedConvOp F L D σ f u ∈ isotypicCuspSubmodule L pins ξ N S Ψ ⊓ archCutSubmodule L tys) ∧
      isotypicCuspSubmodule L pins ξ N S Ψ ⊓ archCutSubmodule L tys ≠ ⊥ :=
  mapsTo_and_ne_bot_of_twistedConvTraceOn_ne_zero F L D σ _ hf hfc ht

theorem twistedCutTrace_one (pins : CarrierPins L) (ξ : pins.Z →* ℂˣ) (N : Ideal (𝓞 L))
    (S : Finset (HeightOneSpectrum (𝓞 L))) (Ψ : HeckeEigensystem L ℂ) (tys : ArchTypeFamily L)
    (f : AdelicGL2 (𝓞 L) L → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f) :
    twistedCutTrace F L D 1 pins ξ N S Ψ tys f hf hfc = cutTrace L pins ξ N S Ψ tys f hf hfc :=
  twistedConvTraceOn_one F L D _ hf hfc

end CutTrace

end AutomorphicForm

end


