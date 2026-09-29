-- Prove2me | Definitions.Def_ModularCurve_AutomorphicField
-- name    : ModularCurve_AutomorphicField
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.084567+00:00
-- url     : https://prove2.me/theorems/14b4cb64-5350-5d94-846c-4813fd13a480
-- title:
--   Holomorphic functions on ℍ and the field of automorphic functions
-- statement:
--   Fix the upper half plane $\mathbb{H}$. [`ModularCurve.holRing`](../def/ModularCurve_AutomorphicField.html#L13) is the $\mathbb{C}$-subalgebra of all functions $\mathbb{H}\to\mathbb{C}$ consisting of those that are holomorphic in the manifold sense, i.e. `MDifferentiable` for the model $\mathcal{I}(\mathbb{C})$ on source and target; it is nontrivial, has no zero divisors (via the fact that a product of holomorphic functions on $\mathbb{H}$ vanishes identically only if one factor does), and hence is an integral domain. Its field of fractions `FractionRing ↥holRing` plays the role of a field of meromorphic functions on $\mathbb{H}$. The map [`ModularCurve.merRealize`](../def/ModularCurve_AutomorphicField.html#L35) turns an element $x$ of this fraction field into an actual function $\mathbb{H}\to\mathbb{C}$, namely $\tau\mapsto a(\tau)/s(\tau)$ where $(a,s)$ is the numerator–denominator pair produced by the chosen section `IsLocalization.sec` of the localisation map; the realisation depends only on $x$, but its values on the zero set of that chosen denominator carry no information.
--
--   [`ModularForm.toHolRing`](../def/ModularCurve_AutomorphicField.html#L50) regards a modular form of weight $k$ for $\Gamma\le\mathrm{GL}_2(\mathbb{R})$ as an element of `holRing`, and is additive, compatible with negation, and (for $\Gamma$ with determinants $\pm 1$) multiplicative for the product of forms of weights $k_1,k_2$. For such a subgroup $\Gamma$, [`ModularCurve.automorphicRatioSet Γ`](../def/ModularCurve_AutomorphicField.html#L74) is the set of elements of `FractionRing ↥holRing` of the form $g/h$ with $g,h\in M_k(\Gamma)$ of one and the same integer weight $k$ and $h$ not identically zero. Under the standing assumption that $\Gamma$ consists of matrices of determinant one, this set is closed under the field operations — sums and products use that weights add, the unit is $1/1$ with the constant form of weight $0$ — and [`ModularCurve.automorphicField Γ`](../def/ModularCurve_AutomorphicField.html#L150) is the resulting subfield. It is made a $\mathbb{C}$-algebra through `automorphicField.constHom`, which sends a constant $c$ to the class of the constant function, compatibly with the inclusion into `FractionRing ↥holRing` as a scalar tower, and `automorphicField.realize` is `merRealize` restricted to this subfield.
--
--   **Relation to Mathlib.** Built on Mathlib's `ModularForm` and its manifold notion of holomorphy; the ring of holomorphic functions on $\mathbb{H}$, its fraction field, the realisation map and the field of automorphic functions of a subgroup are the project's own definitions.
--
--   **Where it is used.** These constructions supply the field of $\Gamma$-automorphic functions, the algebraic stand-in for the function field of a quotient $\Gamma\backslash\mathbb{H}$, for use in the treatment of modular and Shimura curves in the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_ModularCurve_AutomorphicField.lean

import Mathlib.NumberTheory.ModularForms.Basic
import Mathlib.RingTheory.Localization.FractionRing

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

open UpperHalfPlane
open scoped Manifold MatrixGroups Topology

namespace ModularCurve

def holRing : Subalgebra ℂ (ℍ → ℂ) where
  carrier := {f | MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f}
  mul_mem' hf hg := hf.mul hg
  one_mem' := mdifferentiable_const
  add_mem' hf hg := hf.add hg
  zero_mem' := mdifferentiable_const
  algebraMap_mem' _ := mdifferentiable_const

theorem mem_holRing_iff (f : ℍ → ℂ) : f ∈ holRing ↔ MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f := Iff.rfl

instance holRing.instNontrivial : Nontrivial ↥holRing :=
  ⟨⟨0, 1, fun h => by simpa using congrArg (fun f : ↥holRing => (f : ℍ → ℂ) UpperHalfPlane.I) h⟩⟩

instance holRing.instNoZeroDivisors : NoZeroDivisors ↥holRing where
  eq_zero_or_eq_zero_of_mul_eq_zero {f g} h := by
    have h' : (f : ℍ → ℂ) * (g : ℍ → ℂ) = 0 := by simpa using congrArg (fun x : ↥holRing => (x : ℍ → ℂ)) h
    rcases (UpperHalfPlane.mul_eq_zero_iff f.2 g.2).1 h' with h0 | h0
    · exact Or.inl (Subtype.ext h0)
    · exact Or.inr (Subtype.ext h0)

instance holRing.instIsDomain : IsDomain ↥holRing := NoZeroDivisors.to_isDomain _

def merRealize (x : FractionRing ↥holRing) : ℍ → ℂ := fun τ =>
  ((IsLocalization.sec (nonZeroDivisors ↥holRing) x).1 : ℍ → ℂ) τ /
    (((IsLocalization.sec (nonZeroDivisors ↥holRing) x).2 : ↥holRing) : ℍ → ℂ) τ

theorem merRealize_apply (x : FractionRing ↥holRing) (τ : ℍ) :
    merRealize x τ =
      ((IsLocalization.sec (nonZeroDivisors ↥holRing) x).1 : ℍ → ℂ) τ /
        (((IsLocalization.sec (nonZeroDivisors ↥holRing) x).2 : ↥holRing) : ℍ → ℂ) τ := rfl

end ModularCurve

namespace ModularForm

variable {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ}

def toHolRing (f : ModularForm Γ k) : ↥ModularCurve.holRing := ⟨f, f.holo'⟩

@[simp] theorem coe_toHolRing (f : ModularForm Γ k) : (f.toHolRing : ℍ → ℂ) = f := rfl

theorem toHolRing_eq_zero_iff (f : ModularForm Γ k) : f.toHolRing = 0 ↔ (f : ℍ → ℂ) = 0 := by
  rw [← coe_toHolRing f]
  exact (ZeroMemClass.coe_eq_zero).symm

theorem toHolRing_add (f g : ModularForm Γ k) : (f + g).toHolRing = f.toHolRing + g.toHolRing := rfl

theorem toHolRing_neg (f : ModularForm Γ k) : (-f).toHolRing = -f.toHolRing := rfl

theorem toHolRing_mul [Γ.HasDetPlusMinusOne] {k₁ k₂ : ℤ} (f : ModularForm Γ k₁) (g : ModularForm Γ k₂) :
    (f.mul g).toHolRing = f.toHolRing * g.toHolRing :=
  Subtype.ext (coe_mul f g)

end ModularForm

namespace ModularCurve

section

variable (Γ : Subgroup (GL (Fin 2) ℝ))

def automorphicRatioSet : Set (FractionRing ↥holRing) :=
  {x | ∃ (k : ℤ) (g h : ModularForm Γ k), (h : ℍ → ℂ) ≠ 0 ∧
    x = algebraMap (↥holRing) (FractionRing ↥holRing) g.toHolRing /
          algebraMap (↥holRing) (FractionRing ↥holRing) h.toHolRing}

variable {Γ}

theorem mem_automorphicRatioSet_iff (x : FractionRing ↥holRing) :
    x ∈ automorphicRatioSet Γ ↔ ∃ (k : ℤ) (g h : ModularForm Γ k), (h : ℍ → ℂ) ≠ 0 ∧
      x = algebraMap (↥holRing) (FractionRing ↥holRing) g.toHolRing /
            algebraMap (↥holRing) (FractionRing ↥holRing) h.toHolRing := Iff.rfl

private theorem algebraMap_toHolRing_ne_zero {k : ℤ} {h : ModularForm Γ k} (hh : (h : ℍ → ℂ) ≠ 0) :
    algebraMap (↥holRing) (FractionRing ↥holRing) h.toHolRing ≠ 0 := by
  intro h0
  apply hh
  have : h.toHolRing = 0 :=
    (IsFractionRing.injective (↥holRing) (FractionRing ↥holRing)) (by rw [h0, RingHom.map_zero])
  exact (ModularForm.toHolRing_eq_zero_iff h).1 this

private theorem neg_mem_automorphicRatioSet {x : FractionRing ↥holRing}
    (hx : x ∈ automorphicRatioSet Γ) : -x ∈ automorphicRatioSet Γ := by
  obtain ⟨k, g, h, hh, rfl⟩ := hx
  refine ⟨k, -g, h, hh, ?_⟩
  rw [ModularForm.toHolRing_neg, RingHom.map_neg, neg_div]

variable [Γ.HasDetOne]

private theorem coe_ne_zero_of_mul {k₁ k₂ : ℤ} {h₁ : ModularForm Γ k₁} {h₂ : ModularForm Γ k₂}
    (hh₁ : (h₁ : ℍ → ℂ) ≠ 0) (hh₂ : (h₂ : ℍ → ℂ) ≠ 0) : ((h₁.mul h₂ : ModularForm Γ (k₁ + k₂)) : ℍ → ℂ) ≠ 0 := by
  rw [ModularForm.coe_mul]
  intro h0
  rcases (UpperHalfPlane.mul_eq_zero_iff h₁.holo' h₂.holo').1 h0 with h | h
  · exact hh₁ h
  · exact hh₂ h

private theorem one_mem_automorphicRatioSet : (1 : FractionRing ↥holRing) ∈ automorphicRatioSet Γ := by
  have h1 : ((1 : ModularForm Γ 0) : ℍ → ℂ) ≠ 0 := by
    rw [ModularForm.one_coe_eq_one]; exact one_ne_zero
  refine ⟨0, 1, 1, h1, ?_⟩
  rw [div_self (algebraMap_toHolRing_ne_zero h1)]

private theorem zero_mem_automorphicRatioSet : (0 : FractionRing ↥holRing) ∈ automorphicRatioSet Γ := by
  have h1 : ((1 : ModularForm Γ 0) : ℍ → ℂ) ≠ 0 := by
    rw [ModularForm.one_coe_eq_one]; exact one_ne_zero
  refine ⟨0, 0, 1, h1, ?_⟩
  have : (0 : ModularForm Γ 0).toHolRing = 0 := rfl
  rw [this, RingHom.map_zero, zero_div]

private theorem mul_mem_automorphicRatioSet {x y : FractionRing ↥holRing}
    (hx : x ∈ automorphicRatioSet Γ) (hy : y ∈ automorphicRatioSet Γ) : x * y ∈ automorphicRatioSet Γ := by
  obtain ⟨k, g, h, hh, rfl⟩ := hx
  obtain ⟨k', g', h', hh', rfl⟩ := hy
  refine ⟨k + k', g.mul g', h.mul h', coe_ne_zero_of_mul hh hh', ?_⟩
  rw [ModularForm.toHolRing_mul, ModularForm.toHolRing_mul, RingHom.map_mul, RingHom.map_mul, div_mul_div_comm]

private theorem add_mem_automorphicRatioSet {x y : FractionRing ↥holRing}
    (hx : x ∈ automorphicRatioSet Γ) (hy : y ∈ automorphicRatioSet Γ) : x + y ∈ automorphicRatioSet Γ := by
  obtain ⟨k, g, h, hh, rfl⟩ := hx
  obtain ⟨k', g', h', hh', rfl⟩ := hy
  refine ⟨k + k', g.mul h' + h.mul g', h.mul h', coe_ne_zero_of_mul hh hh', ?_⟩
  rw [ModularForm.toHolRing_add, ModularForm.toHolRing_mul, ModularForm.toHolRing_mul,
    ModularForm.toHolRing_mul, RingHom.map_add, RingHom.map_mul, RingHom.map_mul, RingHom.map_mul,
    div_add_div _ _ (algebraMap_toHolRing_ne_zero hh) (algebraMap_toHolRing_ne_zero hh')]

private theorem inv_mem_automorphicRatioSet {x : FractionRing ↥holRing}
    (hx : x ∈ automorphicRatioSet Γ) : x⁻¹ ∈ automorphicRatioSet Γ := by
  obtain ⟨k, g, h, hh, rfl⟩ := hx
  by_cases hg : (g : ℍ → ℂ) = 0
  · have : g.toHolRing = 0 := (ModularForm.toHolRing_eq_zero_iff g).2 hg
    rw [this, RingHom.map_zero, zero_div, inv_zero]
    exact zero_mem_automorphicRatioSet
  · exact ⟨k, h, g, hg, by rw [inv_div]⟩

variable (Γ)

def automorphicField : Subfield (FractionRing ↥holRing) where
  carrier := automorphicRatioSet Γ
  mul_mem' := mul_mem_automorphicRatioSet
  one_mem' := one_mem_automorphicRatioSet
  add_mem' := add_mem_automorphicRatioSet
  zero_mem' := zero_mem_automorphicRatioSet
  neg_mem' := neg_mem_automorphicRatioSet
  inv_mem' _ := inv_mem_automorphicRatioSet

variable {Γ}

theorem mem_automorphicField_iff (x : FractionRing ↥holRing) :
    x ∈ automorphicField Γ ↔ ∃ (k : ℤ) (g h : ModularForm Γ k), (h : ℍ → ℂ) ≠ 0 ∧
      x = algebraMap (↥holRing) (FractionRing ↥holRing) g.toHolRing /
            algebraMap (↥holRing) (FractionRing ↥holRing) h.toHolRing := Iff.rfl

variable (Γ)

def automorphicField.constHom : ℂ →+* ↥(automorphicField Γ) :=
  ((algebraMap (↥holRing) (FractionRing ↥holRing)).comp (algebraMap ℂ ↥holRing)).codRestrict
    (automorphicField Γ) (fun c => by
      have h1 : ((1 : ModularForm Γ 0) : ℍ → ℂ) ≠ 0 := by
        rw [ModularForm.one_coe_eq_one]; exact one_ne_zero
      refine ⟨0, ModularForm.const c, 1, h1, ?_⟩
      have e1 : (1 : ModularForm Γ 0).toHolRing = 1 := Subtype.ext ModularForm.one_coe_eq_one
      have e2 : (ModularForm.const c : ModularForm Γ 0).toHolRing = algebraMap ℂ ↥holRing c :=
        Subtype.ext (funext fun τ => by simp [Algebra.algebraMap_eq_smul_one])
      rw [e1, RingHom.map_one, div_one, e2]
      rfl)

instance automorphicField.instAlgebra : Algebra ℂ ↥(automorphicField Γ) :=
  (automorphicField.constHom Γ).toAlgebra

theorem automorphicField.algebraMap_def (c : ℂ) :
    ((algebraMap ℂ ↥(automorphicField Γ) c : ↥(automorphicField Γ)) : FractionRing ↥holRing) =
      algebraMap (↥holRing) (FractionRing ↥holRing) (algebraMap ℂ ↥holRing c) := rfl

instance automorphicField.instIsScalarTower :
    IsScalarTower ℂ ↥(automorphicField Γ) (FractionRing ↥holRing) :=
  IsScalarTower.of_algebraMap_eq (fun c => (automorphicField.algebraMap_def Γ c).symm)

end

def automorphicField.realize {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.HasDetOne]
    (x : ↥(automorphicField Γ)) : ℍ → ℂ :=
  merRealize (x : FractionRing ↥holRing)

theorem automorphicField.realize_def {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.HasDetOne]
    (x : ↥(automorphicField Γ)) : automorphicField.realize x = merRealize (x : FractionRing ↥holRing) := rfl

end ModularCurve

end


