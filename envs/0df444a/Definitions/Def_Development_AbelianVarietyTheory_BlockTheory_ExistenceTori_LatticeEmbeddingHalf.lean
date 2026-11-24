-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_LatticeEmbeddingHalf
-- name    : Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_LatticeEmbeddingHalf
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T03:51:56.090636+00:00
-- url     : https://prove2.me/theorems/65ac4a5c-5234-48d6-9802-209c093c7aa2
-- title:
--   Lattice Embedding Half
-- statement:
--   Definitions and structural lemmas for Lattice Embedding Half, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/ExistenceTori/LatticeEmbeddingHalf.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_UnFree
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.IndefiniteRowSideFullHecke.AdelicLatticeBase
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open scoped TensorProduct
abbrev Fin𝔸 (F : Type) [Field F] [NumberField F] : Type := FiniteAdeleRing (𝓞 F) F
abbrev Inf𝔸 (F : Type) [Field F] [NumberField F] : Type := InfiniteAdeleRing F
variable (F : Type) [Field F] [NumberField F] {E : Type} [Field E] [NumberField E] [IsCMField E] [Algebra F E]
  {W : Type} [AddCommGroup W] [Module E W] [Module (𝓞 E) W] [IsScalarTower (𝓞 E) E W] {n r : ℕ}
section Lattices
variable (fr : Module.Basis (Fin n) E W) (L : Submodule (𝓞 E) W) (𝔄 : Submodule (𝓞 E) E)
def toFin (v : W) : Fin n → Fin𝔸 F ⊗[F] E := fun i => 1 ⊗ₜ fr.repr v i
def latHat : AddSubgroup (Fin n → Fin𝔸 F ⊗[F] E) :=
  AddSubgroup.closure {z | ∃ a : Fin𝔸 F, (∀ v, a v ∈ v.adicCompletionIntegers F) ∧
    ∃ x ∈ L, z = fun i => a ⊗ₜ fr.repr x i}
def latAd (g : GL (Fin n) (Fin𝔸 F ⊗[F] E)) : AddSubgroup (Fin n → Fin𝔸 F ⊗[F] E) :=
  AddSubgroup.closure {w | ∃ a ∈ 𝔄, ∃ z ∈ latHat F fr L, w = ((1 : Fin𝔸 F) ⊗ₜ[F] a) • g.1.mulVec z}
def latG (g : GL (Fin n) (Fin𝔸 F ⊗[F] E)) : Submodule (𝓞 E) W :=
  Submodule.span (𝓞 E) {v | ∃ a ∈ 𝔄, ∃ x : W, (∃ z ∈ latHat F fr L, toFin F fr x = g.1.mulVec z) ∧ v = a • x}
def latBase : Submodule (𝓞 E) W := Submodule.span (𝓞 E) {v | ∃ a ∈ 𝔄, ∃ x ∈ L, v = a • x}
def CongrAt (M : ℕ) (g : GL (Fin n) (Fin𝔸 F ⊗[F] E)) (u v : W) : Prop :=
  ∃ y ∈ latAd F fr L 𝔄 g, toFin F fr v - g.1.mulVec (toFin F fr u) = M • y
end Lattices
section Datum
variable {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
def half (Dw : Datum H) (l : Level H) : Submodule (𝓞 E) Dw.La :=
  l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) Dw.La)
def IsLatEmb (h : W → W → E) (L : Submodule (𝓞 E) W) (𝔄 : Submodule (𝓞 E) E) (ξ₀ : E) (Dw : Datum H)
    (ι : Dw.La →ₗ[𝓞 E] W) : Prop :=
  Function.Injective ι ∧ LinearMap.range ι = latBase L 𝔄 ∧
    ∃ ε : ℤˣ, ∀ x y, ((Dw.EF x y : ℤ) : ℚ) = ((ε : ℤ) : ℚ) * Algebra.trace ℚ E (ξ₀ * h (ι x) (ι y))
end Datum
section Model
def crd (hr : n = r) (fr : Module.Basis (Fin n) E W) (v : W) : Fin r → E := fun i => fr.repr v ((finCongr hr).symm i)
def vec (hr : n = r) (fr : Module.Basis (Fin n) E W) (x : Fin r → E) : W := ∑ i, x (finCongr hr i) • fr i
def IsModelOf (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (hr : n = r) (fr : Module.Basis (Fin n) E W) (h : W → W → E) (ξ₀ : E)
    (q : ℕ) (X : Data E r) : Prop :=
  (∀ x y : W, herm X.Gm (crd hr fr x) (crd hr fr y) = -h x y) ∧ X.p0 = q ∧
    (∀ τ : E →+* ℂ, τ ∈ X.Ψ ↔ τ (H.rt : E) = H.rt0) ∧
    (X.ξ0 = ξ₀ ∨ X.ξ0 = -ξ₀) ∧ ∀ τ ∈ X.Ψ, (τ X.ξ0).im < 0
def IsOrthoFrame (X : Data E r) (x₀ : (E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) : Prop :=
  ∀ τ ∈ X.Ψ, gram τ X.Gm (x₀ τ) = Matrix.diagonal fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ)
def IsArchAt (τ : E →+* ℂ) (th : Inf𝔸 F ⊗[F] E →+* ℂ) : Prop :=
  (∀ e : E, th (1 ⊗ₜ e) = τ e) ∧ Continuous fun a : Inf𝔸 F => th (a ⊗ₜ 1)
def IsRatUnitary (fr : Module.Basis (Fin n) E W) (h : W → W → E) (γ : GL (Fin n) E) : Prop :=
  ∀ x y : Fin n → E, h (fr.equivFun.symm (γ.1.mulVec x)) (fr.equivFun.symm (γ.1.mulVec y)) =
    h (fr.equivFun.symm x) (fr.equivFun.symm y)
def ratTo (A : Type) [CommRing A] [Algebra F A] (γ : GL (Fin n) E) : GL (Fin n) (A ⊗[F] E) :=
  Matrix.GeneralLinearGroup.map (Algebra.TensorProduct.includeRight : E →ₐ[F] A ⊗[F] E).toRingHom γ
end Model
section Pin
variable {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
  {σ : c.F →+* ℂ}
def LatMark (hr : n = r) (fr : Module.Basis (Fin n) E W) (L : Submodule (𝓞 E) W) (𝔄 : Submodule (𝓞 E) E)
    (l : Level H) (ι : Dw.La →ₗ[𝓞 E] W) (X : Data E r) (mk : Dw.La → X.Λ) (g : GL (Fin n) (Fin𝔸 F ⊗[F] E)) : Prop :=
  (∀ v : W, crd hr fr v ∈ X.Λ ↔ v ∈ latG F fr L 𝔄 g) ∧
    ∀ a ∈ half Dw l, CongrAt F fr L 𝔄 l.M g (ι a) (vec hr fr (mk a : Fin r → E))
def IsMarkStab (l : Level H) (X : Data E r) (mk : Dw.La → X.Λ) : Prop :=
  ∀ γ : GL (Fin r) E, γ ∈ X.Γ ↔ IsUStab X.Gm X.Λ γ ∧
    ∀ a ∈ half Dw l, ∃ y ∈ X.Λ, γ.1.mulVec (mk a : Fin r → E) - (mk a : Fin r → E) = l.M • y
def IsLevelStab (fr : Module.Basis (Fin n) E W) (L : Submodule (𝓞 E) W) (𝔄 : Submodule (𝓞 E) E) (l : Level H)
    (ι : Dw.La →ₗ[𝓞 E] W) {G : Type} [Group G] (inf : G → GL (Fin n) (Inf𝔸 F ⊗[F] E))
    (fin : G → GL (Fin n) (Fin𝔸 F ⊗[F] E)) (Kf : Subgroup G) : Prop :=
  ∀ k, k ∈ Kf ↔ inf k = 1 ∧ latAd F fr L 𝔄 (fin k) = latAd F fr L 𝔄 1 ∧
    ∀ a ∈ half Dw l, CongrAt F fr L 𝔄 l.M (fin k) (ι a) (ι a)
def IsDictOf (hr : n = r) (fr : Module.Basis (Fin n) E W) (h : W → W → E) (L : Submodule (𝓞 E) W)
    (𝔄 : Submodule (𝓞 E) E) (l : Level H) (ι : Dw.La →ₗ[𝓞 E] W) {Comp : Type} (X : Comp → Data E r)
    (mk : ∀ k, Dw.La → (X k).Λ) (th : (E →+* ℂ) → (Inf𝔸 F ⊗[F] E →+* ℂ))
    (x₀ : (E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) {G : Type} (inf : G → GL (Fin n) (Inf𝔸 F ⊗[F] E))
    (fin : G → GL (Fin n) (Fin𝔸 F ⊗[F] E)) (dict : G → Σ k, Frame (X k).Ψ r) : Prop :=
  ∀ g, ∃ γ : GL (Fin n) E, IsRatUnitary fr h γ ∧
    LatMark F hr fr L 𝔄 l ι (X (dict g).1) (mk (dict g).1) (ratTo F (Fin𝔸 F) γ * fin g) ∧
    ∀ τ : (X (dict g).1).Ψ, mat (dict g).2 τ =
      Matrix.reindex (finCongr hr) (finCongr hr) ((ratTo F (Inf𝔸 F) γ * inf g).1.map (th τ.1)) * x₀ τ.1
def IsFamilyOf (U : Unf Xo c σ r) {g : ℕ} (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ))
    (Fm : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1))
    (ik : U.Comp → Fin Fm.n) (φ : ∀ k, (Fm.Di (ik k)).La ≃ₗ[𝓞 E] (U.X k).Λ) : Prop :=
  (∀ k a b, (((Fm.Di (ik k)).EF a b : ℤ) : ℚ) =
    Algebra.trace ℚ E (-(U.X k).ξ0 * herm (U.X k).Gm (φ k a : Fin r → E) (φ k b))) ∧
  ∀ k (x : (U.X k).dom), ∃ P : (Fm.Di (ik k)).La →+ (Fin g → ℂ),
    (∀ a j, P a j = perFr (U.X k) x.1 (φ k a : Fin r → E) (relab c σ (e j).1) (e j).2) ∧
    IsPeriod (Fm.Di (ik k)) (fun j => relab c σ (e j).1) P ∧ (U.un k x).x = Fm.u (ik k) P ∧
    ∀ τ (i : Fin (Dw.mult τ)), IsDerivAt0 (fun z => (Fm.ex (ik k) P z).left) (Pi.single (e.symm ⟨τ, i⟩) 1)
      ((U.un k x).u τ i)
def AdPin (hr : n = r) (fr : Module.Basis (Fin n) E W) (h : W → W → E) (L : Submodule (𝓞 E) W)
    (𝔄 : Submodule (𝓞 E) E) (ξ₀ : E) (U : Unf Xo c σ r) {G : Type} [Group G]
    (inf : G → GL (Fin n) (Inf𝔸 F ⊗[F] E)) (fin : G → GL (Fin n) (Fin𝔸 F ⊗[F] E))
    (dict : G → Σ k, Frame (U.X k).Ψ r) (Kf : Subgroup G) : Prop :=
  ∃ (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ))
    (Fm : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1))
    (ik : U.Comp → Fin Fm.n) (φ : ∀ k, (Fm.Di (ik k)).La ≃ₗ[𝓞 E] (U.X k).Λ)
    (ι : Dw.La →ₗ[𝓞 E] W) (th : (E →+* ℂ) → (Inf𝔸 F ⊗[F] E →+* ℂ)) (x₀ : (E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ),
    IsFamilyOf U e Fm ik φ ∧ IsLatEmb h L 𝔄 ξ₀ Dw ι ∧ (∀ τ, IsArchAt F τ (th τ)) ∧
    (∀ k, IsModelOf H hr fr h ξ₀ Dw.q (U.X k) ∧ IsOrthoFrame (U.X k) x₀ ∧
      IsMarkStab l (U.X k) (fun a => φ k (Fm.t (ik k) a)) ∧
      ∃ gk : G, LatMark F hr fr L 𝔄 l ι (U.X k) (fun a => φ k (Fm.t (ik k) a)) (fin gk)) ∧
    IsLevelStab F fr L 𝔄 l ι inf fin Kf ∧
    IsDictOf F hr fr h L 𝔄 l ι U.X (fun k a => φ k (Fm.t (ik k) a)) th x₀ inf fin dict
end Pin
section Adelic
def unitaryOver (cj : E ≃ₐ[F] E) (fr : Module.Basis (Fin n) E W) (h : W → W → E) (A : Type) [CommRing A] [Algebra F A] :
    Subgroup (GL (Fin n) (A ⊗[F] E)) :=
  let B : (Fin n → A ⊗[F] E) → (Fin n → A ⊗[F] E) → A ⊗[F] E := fun x y =>
    ∑ a, ∑ b, x a * ((1 : A) ⊗ₜ[F] h (fr a) (fr b)) * Algebra.TensorProduct.map (AlgHom.id F A) (cj : E →ₐ[F] E) (y b)
  { carrier := {g | ∀ x y, B (g.1.mulVec x) (g.1.mulVec y) = B x y}
    one_mem' := fun x y => by simp
    mul_mem' := fun {a b} ha hb x y => by
      rw [Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ha, hb]
    inv_mem' := fun {a} ha x y => by
      have := ha (a⁻¹.1.mulVec x) (a⁻¹.1.mulVec y)
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        Matrix.one_mulVec, Matrix.one_mulVec] at this
      exact this.symm }
abbrev AdelicU (cj : E ≃ₐ[F] E) (fr : Module.Basis (Fin n) E W) (h : W → W → E) : Type :=
  unitaryOver F cj fr h (Inf𝔸 F) × unitaryOver F cj fr h (Fin𝔸 F)
variable {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
  {σ : c.F →+* ℂ}
def AdPinU (cj : E ≃ₐ[F] E) (hr : n = r) (fr : Module.Basis (Fin n) E W) (h : W → W → E) (L : Submodule (𝓞 E) W)
    (𝔄 : Submodule (𝓞 E) E) (ξ₀ : E) (U : Unf Xo c σ r)
    (dict : AdelicU F cj fr h → Σ k, Frame (U.X k).Ψ r) (Kf : Subgroup (AdelicU F cj fr h)) : Prop :=
  (∀ x, cj x = cc x) ∧ (∀ x : E, cc x = x → x ∈ Set.range (algebraMap F E)) ∧
    AdPin F hr fr h L 𝔄 ξ₀ U (fun g => g.1.1) (fun g => g.2.1) dict Kf
end Adelic
end GlobalTheory.IndefiniteRowSideFullHecke.AdelicLatticeBase


