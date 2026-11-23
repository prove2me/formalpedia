-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsUnitarisableOfCharIff
-- name    : Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsUnitarisableOfCharIff
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T06:24:05.916544+00:00
-- url     : https://prove2.me/theorems/8406e0aa-c2a7-461d-b7c9-556cba0d71b2
-- title:
--   Is Unitarisable Of Char Iff
-- statement:
--   Definitions and structural lemmas for Is Unitarisable Of Char Iff, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TwistedInnerProducts/IsUnitarisableOfCharIff.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil ValuativeRel
open scoped TensorProduct
namespace GlobalTheory.SmGL
section General
variable {F G H V W U : Type} [Field F] [Group G] [Group H] [AddCommGroup V] [Module F V]
  [AddCommGroup W] [Module F W] [AddCommGroup U] [Module F U]
def twist (ρ : Representation F G V) (χ : G →* Fˣ) : Representation F G V where
  toFun g := (χ g : F) • ρ g
  map_one' := by simp
  map_mul' a b := by
    ext v
    simp [smul_smul, mul_comm]
@[simp] theorem twist_apply (ρ : Representation F G V) (χ : G →* Fˣ) (g : G) (v : V) :
    twist ρ χ g v = (χ g : F) • ρ g v := rfl
@[simp] theorem twist_one (ρ : Representation F G V) : twist ρ 1 = ρ := by
  ext g v; simp
def ofChar (χ : G →* Fˣ) : Representation F G F := twist (Representation.trivial F G F) χ
@[simp] theorem ofChar_apply (χ : G →* Fˣ) (g : G) (x : F) : ofChar χ g x = (χ g : F) * x := by
  simp [ofChar]
def twistMap {ρ : Representation F G V} {σ : Representation F G W} (f : ρ.IntertwiningMap σ)
    (χ : G →* Fˣ) : (twist ρ χ).IntertwiningMap (twist σ χ) where
  toLinearMap := f.toLinearMap
  isIntertwining' g := by
    ext v
    simp [f.isIntertwining]
def compMap {ρ : Representation F G V} {σ : Representation F G W} (f : ρ.IntertwiningMap σ)
    (s : H →* G) : Representation.IntertwiningMap (ρ.comp s) (σ.comp s) where
  toLinearMap := f.toLinearMap
  isIntertwining' h := f.isIntertwining' (s h)
def IsSubquotient (σ : Representation F G W) (ρ : Representation F G V) : Prop :=
  ∃ (S : Subrepresentation ρ) (f : S.toRepresentation.IntertwiningMap σ), Function.Surjective f
def HasFiniteLength (ρ : Representation F G V) : Prop :=
  IsFiniteLength (MonoidAlgebra F G) ρ.asModule
def subQuot {ρ : Representation F G V} (S T : Subrepresentation ρ) :
    Representation F G (S.toSubmodule ⧸ T.toSubmodule.comap S.toSubmodule.subtype) :=
  S.toRepresentation.quotient _ (fun g _ hv => T.apply_mem_toSubmodule g hv)
def OccursTimes (σ : Representation F G W) (ρ : Representation F G V) (r : ℕ) : Prop :=
  ∃ S T : Fin r → Subrepresentation ρ, (∀ i, T i ≤ S i) ∧ (∀ i j, i < j → S i ≤ T j) ∧
    ∀ i, Nonempty ((subQuot (S i) (T i)).Equiv σ)
def jhMult (σ : Representation F G W) (ρ : Representation F G V) : ℕ∞ :=
  ⨆ (r : ℕ) (_ : OccursTimes σ ρ r), (r : ℕ∞)
def extTensor (ρ : Representation F G V) (σ : Representation F H W) :
    Representation F (G × H) (V ⊗[F] W) :=
  Representation.tprod (ρ.comp (MonoidHom.fst G H)) (σ.comp (MonoidHom.snd G H))
@[simp] theorem extTensor_tmul (ρ : Representation F G V) (σ : Representation F H W) (g : G × H)
    (v : V) (w : W) : extTensor ρ σ g (v ⊗ₜ w) = ρ g.1 v ⊗ₜ σ g.2 w := by
  simp [extTensor]
def piTensor {α : Type} {Γ X : α → Type} [∀ a, Group (Γ a)] [∀ a, AddCommGroup (X a)]
    [∀ a, Module F (X a)] (ρ : ∀ a, Representation F (Γ a) (X a)) :
    Representation F (∀ a, Γ a) (⨂[F] a, X a) :=
  PiTensorProduct.mapMonoidHom.comp
    (MonoidHom.pi fun a => (ρ a).comp (Pi.evalMonoidHom Γ a))
@[simp] theorem piTensor_tprod {α : Type} {Γ X : α → Type} [∀ a, Group (Γ a)]
    [∀ a, AddCommGroup (X a)] [∀ a, Module F (X a)] (ρ : ∀ a, Representation F (Γ a) (X a))
    (g : ∀ a, Γ a) (x : ∀ a, X a) :
    piTensor ρ g (PiTensorProduct.tprod F x) = PiTensorProduct.tprod F fun a => ρ a (g a) (x a) := by
  exact PiTensorProduct.map_tprod _ _
def jacquetMap {ρ : Representation F G V} {σ : Representation F G W} (f : ρ.IntertwiningMap σ)
    (N : Subgroup G) (s : H →* G) (hs : ∀ m, s m ∈ Subgroup.normalizer (N : Set G)) :
    (jacquet ρ N s hs).IntertwiningMap (jacquet σ N s hs) where
  toLinearMap := (twKer ρ N 1).mapQ (twKer σ N 1) f.toLinearMap (Submodule.span_le.2 (by
    rintro _ ⟨n, v, rfl⟩
    refine Submodule.subset_span ⟨n, f v, ?_⟩
    simp [f.isIntertwining]))
  isIntertwining' m := by
    ext v
    exact congrArg Submodule.Quotient.mk (f.isIntertwining _ _ (s m) v)
section Top
variable [TopologicalSpace G]
def IsSmoothChar (χ : G →* Fˣ) : Prop := IsOpen (χ.ker : Set G)
variable [IsTopologicalGroup G]
theorem mem_smoothPart_of_nhds {ρ : Representation F G V} {v : V}
    (h : {g : G | ρ g v = v} ∈ nhds (1 : G)) : v ∈ smoothPart ρ :=
  Subgroup.isOpen_of_mem_nhds
    { carrier := {g | ρ g v = v}
      mul_mem' := by
        intro x y hx hy
        simp only [Set.mem_ofPred_eq, map_mul, Module.End.mul_apply] at *
        rw [hy, hx]
      one_mem' := by simp
      inv_mem' := by
        intro x hx
        simp only [Set.mem_ofPred_eq] at *
        conv_lhs => rw [← hx]
        rw [← Module.End.mul_apply, ← map_mul]; simp } h
def contra (ρ : Representation F G V) : Representation F G (smoothPart ρ.dual) := smoothRep ρ.dual
@[simp] theorem contra_apply (ρ : Representation F G V) (g : G) (l : smoothPart ρ.dual) (v : V) :
    (contra ρ g l : Module.Dual F V) v = (l : Module.Dual F V) (ρ g⁻¹ v) := rfl
def smIndMap {P : Subgroup G} {σ : Representation F P W} {τ : Representation F P U}
    (f : σ.IntertwiningMap τ) : (smInd P σ).IntertwiningMap (smInd P τ) where
  toLinearMap :=
    { toFun := fun φ => ⟨⟨fun g => f (φ.1.1 g), fun h g => by
          show f (φ.1.1 (h * g)) = τ h (f (φ.1.1 g))
          rw [φ.1.2 h g, f.isIntertwining]⟩,
        mem_smoothPart_of_nhds (Filter.mem_of_superset (IsOpen.mem_nhds φ.2 (by simp)) fun g hg => by
          have hg' : ind P σ g φ.1 = φ.1 := hg
          apply Subtype.ext
          funext x
          exact congrArg f (congrFun (congrArg Subtype.val hg') x))⟩
      map_add' := fun φ ψ => by ext g; simp
      map_smul' := fun c φ => by ext g; simp }
  isIntertwining' g := by ext φ x; rfl
end Top
def IsUnitarisable {X : Type} [AddCommGroup X] [Module ℂ X] (ρ : Representation ℂ G X) : Prop :=
  ∃ B : X →ₗ[ℂ] X →ₗ⋆[ℂ] ℂ, (∀ v w, B w v = starRingEnd ℂ (B v w)) ∧ (∀ v, v ≠ 0 → 0 < (B v v).re) ∧
    ∀ g v w, B (ρ g v) (ρ g w) = B v w
def IsUnitaryChar (χ : G →* ℂˣ) : Prop := ∀ g, ‖(χ g : ℂ)‖ = 1
def IsSphericalFor (ρ : Representation F G V) (K : Subgroup G) : Prop := fixed ρ K ≠ ⊥
def IsZonal (ρ : Representation F G V) (K : Subgroup G) (ω : G → F) : Prop :=
  ∃ v ∈ fixed ρ K, ∃ l ∈ fixed ρ.dual K, l v = 1 ∧ ∀ g, ω g = l (ρ g v)
end General
end GlobalTheory.SmGL


