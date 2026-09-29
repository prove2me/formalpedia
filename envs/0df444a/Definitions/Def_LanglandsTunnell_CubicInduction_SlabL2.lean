-- Prove2me | Definitions.Def_LanglandsTunnell_CubicInduction_SlabL2
-- name    : LanglandsTunnell_CubicInduction_SlabL2
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:27.528425+00:00
-- url     : https://prove2.me/theorems/84a13e70-53bd-5c47-926a-c2a63620550a
-- title:
--   Slab L² carrier for adelic GL₃ automorphic functions
-- statement:
--   Throughout, $\mathrm{GL}_3$ of the adele ring of $\mathbb{Q}$, written `AdelicGL 3 (𝓞 ℚ) ℚ`, carries the Borel $\sigma$-algebra of its topology, the one on which [`NumberField.AdelicHaar.adelicGLHaar`](../def/NumberField_AdelicHaar.html#L189) is the Haar measure. For real $a,b$, `ideleNormDetSlab a b` is the set of $g$ whose determinant has idele norm in the closed interval $[a,b]$, the idele norm of an idele $x$ being the value at $x$ of the distributive Haar character of the adele ring, read as a real number; `mem_ideleNormDetSlab_iff` restates membership. `slabMeasure a b` is the Haar measure of $\mathrm{GL}_3(\mathbb{A}_\mathbb{Q})$ restricted to this slab, and `domainMeasure a b Φ₀` is that measure further restricted to a subset $\Phi_0$. The abbreviation `Carrier a b Φ₀` is the complex $L^2$ space of the domain measure, i.e. `Lp ℂ 2` of `domainMeasure a b Φ₀`, with no automorphy built in. The predicate `IsSlabDomain a b Φ₀` is the conjunction of $0<a$, $a<b$, and Mathlib's `IsFundamentalDomain` for the subgroup of $\mathrm{GL}_3(\mathbb{A}_\mathbb{Q})$ given by the image of $\mathrm{GL}_3(\mathbb{Q})$ under `globalPointsGL` (entrywise $\mathrm{algebraMap}$), acting on $\Phi_0$ by left translation, with respect to the slab measure; `isSlabDomain_iff` and the three projections `pos`, `lt`, `isFundamentalDomain` unpack it. Given a monoid homomorphism $\omega$ from the ideles of $\mathbb{Q}$ to $\mathbb{C}^\times$ (no unitarity or triviality on principal ideles is required), `automorphicSubmodule ω a b Φ₀` is the $\mathbb{C}$-subspace of all functions $f\colon \mathrm{GL}_3(\mathbb{A}_\mathbb{Q})\to\mathbb{C}$ satisfying: $f(\gamma g)=f(g)$ for all $\gamma\in\mathrm{GL}_3(\mathbb{Q})$; $f(zg)=\omega(z)f(g)$ for every central scalar matrix $z$ coming from an idele, via `centralScalarGL`; and `MemLp f 2` for the domain measure. Finally `toL2 ω a b Φ₀` is the $\mathbb{C}$-linear map sending such an $f$ to its almost-everywhere class in the carrier.
--
--   **Relation to Mathlib.** The measure-theoretic ingredients (`Measure.restrict`, `IsFundamentalDomain`, `MemLp`/`Lp` and the distributive Haar character) are Mathlib's; the determinant slab, the slab and domain measures, the slab-domain predicate and the automorphic submodule with its map to $L^2$ are the project's own. Note that `Carrier` is a bare $L^2$ space for the restricted measure rather than a space of automorphic functions, so `toL2` is not asserted to be injective.
--
--   **Where it is used.** These definitions fix the Hilbert space on which the $\mathrm{GL}_3$ automorphic functions of the Langlands–Tunnell step are realised: functions on $\mathrm{GL}_3(\mathbb{A}_\mathbb{Q})$ left invariant under the global points and transforming by a central character, square-integrable over a fundamental domain inside a region where the idele norm of the determinant is bounded away from $0$ and $\infty$. The resulting automorphy for the cubic induction feeds the modularity of the mod $3$ representation attached to a Frey curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_LanglandsTunnell_CubicInduction_SlabL2.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_Carrier
import Definitions.Def_NumberField_TateGlobalZeta
import Mathlib.MeasureTheory.Function.L2Space

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

open NumberField MeasureTheory
open scoped ENNReal

namespace LanglandsTunnell.CubicInduction.SlabL2

attribute [local instance] NumberField.AdelicHaar.glBorel

def ideleNormDetSlab (a b : ℝ) : Set (AdelicGL 3 (𝓞 ℚ) ℚ) :=
  {g | NumberField.TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc a b}

theorem mem_ideleNormDetSlab_iff (a b : ℝ) (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    g ∈ ideleNormDetSlab a b ↔ NumberField.TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc a b :=
  Iff.rfl

def slabMeasure (a b : ℝ) : Measure (AdelicGL 3 (𝓞 ℚ) ℚ) :=
  (NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ).restrict (ideleNormDetSlab a b)

theorem slabMeasure_def (a b : ℝ) :
    slabMeasure a b = (NumberField.AdelicHaar.adelicGLHaar (Fin 3) (𝓞 ℚ) ℚ).restrict (ideleNormDetSlab a b) := rfl

def domainMeasure (a b : ℝ) (Φ₀ : Set (AdelicGL 3 (𝓞 ℚ) ℚ)) : Measure (AdelicGL 3 (𝓞 ℚ) ℚ) :=
  (slabMeasure a b).restrict Φ₀

theorem domainMeasure_def (a b : ℝ) (Φ₀ : Set (AdelicGL 3 (𝓞 ℚ) ℚ)) :
    domainMeasure a b Φ₀ = (slabMeasure a b).restrict Φ₀ := rfl

abbrev Carrier (a b : ℝ) (Φ₀ : Set (AdelicGL 3 (𝓞 ℚ) ℚ)) : Type :=
  Lp ℂ 2 (domainMeasure a b Φ₀)

def IsSlabDomain (a b : ℝ) (Φ₀ : Set (AdelicGL 3 (𝓞 ℚ) ℚ)) : Prop :=
  0 < a ∧ a < b ∧ IsFundamentalDomain (globalPointsGL 3 (𝓞 ℚ) ℚ).range Φ₀ (slabMeasure a b)

theorem isSlabDomain_iff (a b : ℝ) (Φ₀ : Set (AdelicGL 3 (𝓞 ℚ) ℚ)) :
    IsSlabDomain a b Φ₀ ↔ 0 < a ∧ a < b ∧ IsFundamentalDomain (globalPointsGL 3 (𝓞 ℚ) ℚ).range Φ₀ (slabMeasure a b) :=
  Iff.rfl

theorem IsSlabDomain.pos {a b : ℝ} {Φ₀ : Set (AdelicGL 3 (𝓞 ℚ) ℚ)} (h : IsSlabDomain a b Φ₀) : 0 < a := h.1

theorem IsSlabDomain.lt {a b : ℝ} {Φ₀ : Set (AdelicGL 3 (𝓞 ℚ) ℚ)} (h : IsSlabDomain a b Φ₀) : a < b := h.2.1

theorem IsSlabDomain.isFundamentalDomain {a b : ℝ} {Φ₀ : Set (AdelicGL 3 (𝓞 ℚ) ℚ)} (h : IsSlabDomain a b Φ₀) :
    IsFundamentalDomain (globalPointsGL 3 (𝓞 ℚ) ℚ).range Φ₀ (slabMeasure a b) := h.2.2

def automorphicSubmodule (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (a b : ℝ) (Φ₀ : Set (AdelicGL 3 (𝓞 ℚ) ℚ)) :
    Submodule ℂ (AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) where
  carrier := {f | (∀ (γ : GL (Fin 3) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ), f (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) = f g) ∧
    (∀ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL 3 (𝓞 ℚ) ℚ), f (centralScalarGL 3 (𝓞 ℚ) ℚ z * g) = (ω z : ℂ) * f g) ∧
    MemLp f 2 (domainMeasure a b Φ₀)}
  zero_mem' := ⟨fun _ _ => rfl, fun _ _ => by simp, MemLp.zero⟩
  add_mem' := fun {f f'} hf hf' =>
    ⟨fun γ g => by rw [Pi.add_apply, Pi.add_apply, hf.1, hf'.1],
      fun z g => by rw [Pi.add_apply, Pi.add_apply, hf.2.1, hf'.2.1, mul_add], hf.2.2.add hf'.2.2⟩
  smul_mem' := fun c {f} hf =>
    ⟨fun γ g => by rw [Pi.smul_apply, Pi.smul_apply, hf.1],
      fun z g => by rw [Pi.smul_apply, Pi.smul_apply, hf.2.1, smul_eq_mul, smul_eq_mul, mul_left_comm],
      hf.2.2.const_smul c⟩

theorem mem_automorphicSubmodule_iff (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (a b : ℝ) (Φ₀ : Set (AdelicGL 3 (𝓞 ℚ) ℚ))
    (f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) :
    f ∈ automorphicSubmodule ω a b Φ₀ ↔
      (∀ (γ : GL (Fin 3) ℚ) (g : AdelicGL 3 (𝓞 ℚ) ℚ), f (globalPointsGL 3 (𝓞 ℚ) ℚ γ * g) = f g) ∧
      (∀ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) (g : AdelicGL 3 (𝓞 ℚ) ℚ), f (centralScalarGL 3 (𝓞 ℚ) ℚ z * g) = (ω z : ℂ) * f g) ∧
      MemLp f 2 (domainMeasure a b Φ₀) :=
  Iff.rfl

def toL2 (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (a b : ℝ) (Φ₀ : Set (AdelicGL 3 (𝓞 ℚ) ℚ)) :
    ↥(automorphicSubmodule ω a b Φ₀) →ₗ[ℂ] Carrier a b Φ₀ where
  toFun f := f.2.2.2.toLp (f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ)
  map_add' f f' := MemLp.toLp_add f.2.2.2 f'.2.2.2
  map_smul' c f := MemLp.toLp_const_smul c f.2.2.2

theorem toL2_apply (ω : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ) (a b : ℝ) (Φ₀ : Set (AdelicGL 3 (𝓞 ℚ) ℚ))
    (f : ↥(automorphicSubmodule ω a b Φ₀)) :
    toL2 ω a b Φ₀ f = f.2.2.2.toLp (f : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) := rfl

end LanglandsTunnell.CubicInduction.SlabL2

end


