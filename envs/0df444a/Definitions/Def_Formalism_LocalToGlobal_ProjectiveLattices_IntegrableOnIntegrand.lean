-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IntegrableOnIntegrand
-- name    : Formalism_LocalToGlobal_ProjectiveLattices_IntegrableOnIntegrand
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T17:36:06.683805+00:00
-- url     : https://prove2.me/theorems/198a1c15-dbe1-436b-a740-cc6f1d3e9e57
-- title:
--   Integrable On Integrand
-- statement:
--   Definitions and structural lemmas for Integrable On Integrand, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/IntegrableOnIntegrand.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace Formalism.L2.Pj
namespace FJ
section Orbit
variable {Ω : Type} {N : ℕ}
def cube (N : ℕ) : Set (Fin N → ℝ) := Set.Icc 0 1
def chr (ph : Fin N → ℝ) (t : Fin N → ℝ) : ℂ :=
  Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I) * ((∑ k, t k * ph k : ℝ) : ℂ))
def integrand (act : (Fin N → ℝ) → Ω → Ω) (ph : Fin N → ℝ) (P : Ω → ℂ) (x : Ω)
    (t : Fin N → ℝ) : ℂ :=
  P (act t x) * chr ph t
def coefFn (act : (Fin N → ℝ) → Ω → Ω) (ph : Fin N → ℝ) (P : Ω → ℂ) (x : Ω) : ℂ :=
  ∫ t in cube N, integrand act ph P x t
theorem integrand_add (act : (Fin N → ℝ) → Ω → Ω) (ph : Fin N → ℝ) (P Q : Ω → ℂ) (x : Ω) :
    integrand act ph (P + Q) x = fun t => integrand act ph P x t + integrand act ph Q x t := by
  funext t; simp [integrand, add_mul]
theorem integrand_smul (act : (Fin N → ℝ) → Ω → Ω) (ph : Fin N → ℝ) (a : ℂ) (P : Ω → ℂ) (x : Ω) :
    integrand act ph (a • P) x = fun t => a * integrand act ph P x t := by
  funext t; simp [integrand, mul_assoc]
theorem integrand_zero (act : (Fin N → ℝ) → Ω → Ω) (ph : Fin N → ℝ) (x : Ω) :
    integrand act ph (0 : Ω → ℂ) x = fun _ => 0 := by
  funext t; simp [integrand]
def OrbInt (act : (Fin N → ℝ) → Ω → Ω) (S : Set Ω) : Submodule ℂ (Ω → ℂ) where
  carrier := {P | ∀ (ph : Fin N → ℝ), ∀ x ∈ S, IntegrableOn (integrand act ph P x) (cube N)}
  zero_mem' := by
    intro ph x _
    rw [integrand_zero]
    exact integrableOn_zero
  add_mem' := by
    intro P Q hP hQ ph x hx
    rw [integrand_add]
    exact (hP ph x hx).add (hQ ph x hx)
  smul_mem' := by
    intro a P hP ph x hx
    rw [integrand_smul]
    exact (hP ph x hx).const_mul a
open Classical in

def coefL (act : (Fin N → ℝ) → Ω → Ω) (S : Set Ω) (ph : Fin N → ℝ) :
    OrbInt act S →ₗ[ℂ] (Ω → ℂ) where
  toFun P := fun x => if x ∈ S then coefFn act ph P x else 0
  map_add' P Q := by
    funext x
    by_cases hx : x ∈ S
    · simp only [hx, if_true, coefFn, Submodule.coe_add, Pi.add_apply]
      rw [integrand_add]
      exact integral_add (P.2 ph x hx) (Q.2 ph x hx)
    · simp [hx]
  map_smul' a P := by
    funext x
    by_cases hx : x ∈ S
    · simp only [hx, if_true, coefFn, Submodule.coe_smul, RingHom.id_apply, Pi.smul_apply, smul_eq_mul]
      rw [integrand_smul]
      exact integral_const_mul a _
    · simp [hx]
end Orbit
section Via
variable {K : Type} [Field K]
def FnVia (_σ : K →+* ℂ) (Ω : Type) : Type := Ω → ℂ
variable (σ : K →+* ℂ) (Ω : Type)
instance : AddCommGroup (FnVia σ Ω) := inferInstanceAs (AddCommGroup (Ω → ℂ))
instance : Module K (FnVia σ Ω) := Module.compHom (Ω → ℂ) σ
variable {σ Ω}
def coefVia {N : ℕ} {C : Type} [AddCommGroup C] [Module K C] (act : (Fin N → ℝ) → Ω → Ω)
    (S : Set Ω) (ph : Fin N → ℝ) (rd : C →ₛₗ[σ] (Ω → ℂ)) (hrd : ∀ F, rd F ∈ OrbInt act S) :
    C →ₗ[K] FnVia σ Ω where
  toFun F := (coefL act S ph ⟨rd F, hrd F⟩ : Ω → ℂ)
  map_add' F G := by
    have h : (⟨rd (F + G), hrd (F + G)⟩ : OrbInt act S) = ⟨rd F, hrd F⟩ + ⟨rd G, hrd G⟩ :=
      Subtype.ext (by simp)
    rw [h, map_add]
    rfl
  map_smul' a F := by
    have h : (⟨rd (a • F), hrd (a • F)⟩ : OrbInt act S) = σ a • ⟨rd F, hrd F⟩ :=
      Subtype.ext (by simp)
    rw [h, map_smul]
    rfl
end Via
section FD
open ReciprocityTheory.ChartRestriction.G.FD NumberField
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r ρ : ℕ}
structure CuspFD (X : Data E r) (ρ : ℕ) where
  e : Fin ρ → Fin r → E
  ind : LinearIndependent E e
  iso : ∀ a b, herm X.Gm (e a) (e b) = 0
def CuspFD.I {X : Data E r} (cu : CuspFD X ρ) : Submodule (𝓞 E) (Fin r → E) :=
  X.Λ ⊓ (Submodule.span E (Set.range cu.e)).restrictScalars (𝓞 E)
def crdI (𝔄 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) {X : Data E r} (cu : CuspFD X ρ) :
    Submodule (𝓞 E) (Fin ρ → E) :=
  Submodule.span (𝓞 E) {v | ∃ a ∈ (𝔄 : Submodule (𝓞 E) E), ∃ x ∈ cu.I, a • x = ∑ i, v i • cu.e i}
def dualZE {n : ℕ} (Xs : Submodule (𝓞 E) (Fin n → E)) : Set (Fin n → E) :=
  {l | ∀ x ∈ Xs, Algebra.trace ℚ E (∑ i, l i * x i) ∈ Set.range (Int.cast : ℤ → ℚ)}
def dualOE {n : ℕ} (Xs : Submodule (𝓞 E) (Fin n → E)) : Set (Fin n → E) :=
  {l | ∀ x ∈ Xs, ∑ i, l i * x i ∈ Set.range (algebraMap (𝓞 E) E)}
def XcFD (𝔄 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) {X : Data E r} (cu : CuspFD X ρ) :
    Submodule (𝓞 E) (Fin ρ → E) :=
  Submodule.span (𝓞 E) (dualZE (crdI 𝔄 cu))
def IsSkew (β : Matrix (Fin ρ) (Fin ρ) E) : Prop := ∀ a b, cc (β a b) = -β b a
def IsHermE (χ : Matrix (Fin ρ) (Fin ρ) E) : Prop := ∀ a b, cc (χ a b) = χ b a
def zMatE (X : Data E r) (e : Fin ρ → Fin r → E) (β : Matrix (Fin ρ) (Fin ρ) E) :
    Matrix (Fin r) (Fin r) E :=
  Matrix.of fun k l => (if k = l then 1 else 0) + ∑ a, ∑ b, β a b * e a k * ∑ k', X.Gm l k' * cc (e b k')
def zMatC (X : Data E r) (e : Fin ρ → Fin r → E) (τ : E →+* ℂ) (β : Matrix (Fin ρ) (Fin ρ) ℂ) :
    Matrix (Fin r) (Fin r) ℂ :=
  Matrix.of fun k l => (if k = l then 1 else 0) +
    ∑ a, ∑ b, β a b * τ (e a k) * ∑ k', τ (X.Gm l k') * conj (τ (e b k'))
def zGam (X : Data E r) (cu : CuspFD X ρ) : Set (Matrix (Fin ρ) (Fin ρ) E) :=
  {β | IsSkew β ∧ ∃ γ ∈ X.Γ, (γ : Matrix (Fin r) (Fin r) E) = zMatE X cu.e β}
def nZ (X : Data E r) (ρ : ℕ) : ℕ := X.Ψ.card * ρ ^ 2
def IsZBasis (X : Data E r) (cu : CuspFD X ρ) (bs : Fin (nZ X ρ) → Matrix (Fin ρ) (Fin ρ) E) : Prop :=
  LinearIndependent ℤ bs ∧ ∀ β, β ∈ zGam X cu ↔ β ∈ Submodule.span ℤ (Set.range bs)
def zBas (X : Data E r) (cu : CuspFD X ρ) : Fin (nZ X ρ) → Matrix (Fin ρ) (Fin ρ) E :=
  Classical.epsilon (IsZBasis X cu)
def zAct (X : Data E r) (cu : CuspFD X ρ) (t : Fin (nZ X ρ) → ℝ) (x : Frame X.Ψ r) : Frame X.Ψ r :=
  fun τ => (zMatC X cu.e τ.1 (∑ k, (t k : ℂ) • (zBas X cu k).map τ.1) * mat x τ : Matrix (Fin r) (Fin r) ℂ)
def prE (X : Data E r) (χ β : Matrix (Fin ρ) (Fin ρ) E) : ℝ :=
  ∑ τ : X.Ψ, (τ.1 (Matrix.trace (χ.transpose * β) / (X.κ0 / 2))).re
def phZ (X : Data E r) (cu : CuspFD X ρ) (χ : Matrix (Fin ρ) (Fin ρ) E) : Fin (nZ X ρ) → ℝ :=
  fun k => prE X χ (zBas X cu k)
variable {Comp : Type}
abbrev CuF (X : Comp → Data E r) (ρ : ℕ) : Type := Σ c, CuspFD (X c) ρ
def XcF (X : Comp → Data E r) (𝔄 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (cu : CuF X ρ) :
    Submodule (𝓞 E) (Fin ρ → E) :=
  XcFD 𝔄 cu.2
variable {K : Type} [Field K] (σ : K →+* ℂ)
abbrev FJtF (X : Comp → Data E r) (cu : CuF X ρ) : Type := FnVia σ (Frame (X cu.1).Ψ r)
variable {C : Type} [AddCommGroup C] [Module K C]
def RdOrbInt (X : Comp → Data E r) (ρ : ℕ) (rd : C →ₛₗ[σ] (∀ c, Frame (X c).Ψ r → ℂ)) : Prop :=
  ∀ f (cu : CuF X ρ), rd f cu.1 ∈ OrbInt (zAct (X cu.1) cu.2) (X cu.1).dom
def sgF (X : Comp → Data E r) (rd : C →ₛₗ[σ] (∀ c, Frame (X c).Ψ r → ℂ)) (h : RdOrbInt σ X ρ rd)
    (cu : CuF X ρ) (χ : Matrix (Fin ρ) (Fin ρ) E) : C →ₗ[K] FJtF σ X cu :=
  coefVia (zAct (X cu.1) cu.2) (X cu.1).dom (phZ (X cu.1) cu.2 χ)
    ((LinearMap.proj (φ := fun c => Frame (X c).Ψ r → ℂ) cu.1).comp rd) (fun f => h f cu)
def OrbDom (X : Comp → Data E r) (ρ : ℕ) : Prop :=
  ∀ (cu : CuF X ρ) t, ∀ x ∈ (X cu.1).dom, zAct (X cu.1) cu.2 t x ∈ (X cu.1).dom
def LatZ (X : Comp → Data E r) (ρ : ℕ) : Prop := ∀ cu : CuF X ρ, ∃ bs, IsZBasis (X cu.1) cu.2 bs
def XcLatF (X : Comp → Data E r) (𝔄 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (ρ : ℕ) : Prop :=
  ∀ cu : CuF X ρ, Submodule.IsLattice E (XcF X 𝔄 cu)
def CuNeF (X : Comp → Data E r) (ρ : ℕ) : Prop := ∀ c, Nonempty (CuspFD (X c) ρ)
def ExpoMatch (X : Comp → Data E r) (𝔄 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (ρ g : ℕ) : Prop :=
  ∀ (cu : CuF X ρ) (χ : Matrix (Fin ρ) (Fin ρ) E), IsHermE χ →
    ((∀ β ∈ zGam (X cu.1) cu.2, ∃ n : ℤ, prE (X cu.1) χ β = n) ↔
      ∀ l ∈ dualOE (XcF X 𝔄 cu), ∀ m ∈ dualOE (XcF X 𝔄 cu),
        (g : E) * ∑ i, ∑ k, l i * χ i k * cc (m k) ∈ Set.range (algebraMap (𝓞 E) E))
end FD
end FJ
end Formalism.L2.Pj


