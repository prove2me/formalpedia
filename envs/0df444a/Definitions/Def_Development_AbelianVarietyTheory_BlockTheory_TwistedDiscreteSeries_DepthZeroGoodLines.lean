-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_DepthZeroGoodLines
-- name    : Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_DepthZeroGoodLines
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:39:53.871414+00:00
-- url     : https://prove2.me/theorems/e3344637-68ff-4bfa-b714-f68eab37ca21
-- title:
--   Depth Zero Good Lines
-- statement:
--   Definitions and structural lemmas for Depth Zero Good Lines, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/TwistedDiscreteSeries/DepthZeroGoodLines.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Theorems.Thm_GlobalTheory_SmGL_IsSmoothChar_comp
import Theorems.Thm_GlobalTheory_SmGL_isIrreducible_ofChar
import Theorems.Thm_GlobalTheory_SmGL_isSmoothChar_of_isUnram
import Theorems.Thm_GlobalTheory_SmGL_isSmooth_ofChar_iff
import Theorems.Thm_GlobalTheory_SmGL_isUnitarisable_ofChar_iff
import Theorems.Thm_GlobalTheory_SmGL_mem_unipB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL ValuativeRel
open scoped TensorProduct
namespace GlobalTheory.IndefiniteRowSideFullHecke.CuspidalSupportClasses
section Finite
variable {F : Type} [Field F] {n : ℕ} {Y : Type} [AddCommGroup Y] [Module ℂ Y]
def IsCuspFin (τ : Representation ℂ (GL (Fin n) F) Y) : Prop :=
  ∀ (s : ℕ) (d : Fin s → ℕ) (e : (Σ a, Fin (d a)) ≃ Fin n), unipRad F e ≠ ⊥ →
    Subsingleton (Jacquet τ (unipRad F e))
def hcInd {s : ℕ} {d : Fin s → ℕ} (e : (Σ a, Fin (d a)) ≃ Fin n) {X : Fin s → Type}
    [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)]
    (ρ : ∀ a, Representation ℂ (GL (Fin (d a)) F) (X a)) :=
  ind (parab F e) ((piTensor ρ).comp (leviProj F e))
def IsSuppFin (τ : Representation ℂ (GL (Fin n) F) Y) {s : ℕ} (d : Fin s → ℕ) {X : Fin s → Type}
    [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)]
    (ρ : ∀ a, Representation ℂ (GL (Fin (d a)) F) (X a)) : Prop :=
  τ.IsIrreducible ∧ (∀ a, 0 < d a ∧ (ρ a).IsIrreducible ∧ IsCuspFin (ρ a)) ∧
    ∃ e : (Σ a, Fin (d a)) ≃ Fin n, IsSubquotient τ (hcInd e ρ)
def SameClass {m : ℕ} {X : Type} [AddCommGroup X] [Module ℂ X]
    (ρ₁ : Representation ℂ (GL (Fin m) F) X) (ρ₂ : Representation ℂ (GL (Fin n) F) Y) : Prop :=
  ∃ (h : m = n) (φ : X ≃ₗ[ℂ] Y), ∀ (g : GL (Fin m) F) (x : X),
    φ (ρ₁ g x) = ρ₂ (h ▸ g : GL (Fin n) F) (φ x)
def HasRegularSupp (τ : Representation ℂ (GL (Fin n) F) Y) : Prop :=
  ∃ (s : ℕ) (d : Fin s → ℕ) (X : Fin s → Type) (_ : ∀ a, AddCommGroup (X a)) (_ : ∀ a, Module ℂ (X a))
    (ρ : ∀ a, Representation ℂ (GL (Fin (d a)) F) (X a)),
    IsSuppFin τ d ρ ∧ ∀ a b, a ≠ b → ¬ SameClass (ρ a) (ρ b)
def SameSupp {Y' : Type} [AddCommGroup Y'] [Module ℂ Y'] (τ : Representation ℂ (GL (Fin n) F) Y)
    (τ' : Representation ℂ (GL (Fin n) F) Y') : Prop :=
  ∀ (s : ℕ) (d : Fin s → ℕ) (X : Fin s → Type) [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)]
    (ρ : ∀ a, Representation ℂ (GL (Fin (d a)) F) (X a)), IsSuppFin τ d ρ ↔ IsSuppFin τ' d ρ
def superSum (u : Matrix (Fin n) (Fin n) F) : F :=
  ∑ i : Fin n, ∑ j : Fin n, if (j : ℕ) = i + 1 then u i j else 0
theorem superSum_mul (u v : unipB F (Fin n)) :
    superSum ((u * v : unipB F (Fin n)) : GL (Fin n) F).val =
      superSum (u : GL (Fin n) F).val + superSum (v : GL (Fin n) F).val := by
  obtain ⟨hu, hu1⟩ := (mem_unipB F).1 u.2
  obtain ⟨hv, hv1⟩ := (mem_unipB F).1 v.2
  unfold superSum
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs with h
  · show ((u : GL (Fin n) F).val * (v : GL (Fin n) F).val) i j = _
    rw [Matrix.mul_apply, Fintype.sum_eq_add i j (by intro e; rw [e] at h; omega), hu1, hv1]
    · ring
    · rintro l ⟨h1, h2⟩
      rcases lt_or_gt_of_ne h1 with h3 | h3
      · rw [hu i l h3, zero_mul]
      · have h4 : j < l := by
          have a1 : (i : ℕ) < l := h3
          have a2 : (l : ℕ) ≠ j := fun e => h2 (Fin.ext e)
          show (j : ℕ) < l
          omega
        rw [hv l j h4, mul_zero]
  · simp
def genChar (n : ℕ) (ψ₀ : AddChar F ℂ) : unipB F (Fin n) →* ℂˣ :=
  MonoidHom.toHomUnits
    { toFun := fun u => ψ₀ (superSum (u : GL (Fin n) F).val)
      map_one' := by
        have : superSum ((1 : unipB F (Fin n)) : GL (Fin n) F).val = 0 := by
          refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
          split_ifs with h
          · exact Matrix.one_apply_ne (by intro e; rw [e] at h; omega)
          · rfl
        rw [this, AddChar.map_zero_eq_one]
      map_mul' := fun u v => by rw [superSum_mul, AddChar.map_add_eq_mul] }
end Finite
section Local
variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
def incl (n : ℕ) : GL (Fin n) 𝒪[k] →* GL (Fin n) k :=
  Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k)
def red (n : ℕ) : GL (Fin n) 𝒪[k] →* GL (Fin n) 𝓀[k] :=
  Matrix.GeneralLinearGroup.map (IsLocalRing.residue 𝒪[k])
def diagOne (r t : ℕ) : GL (Fin r) 𝒪[k] →* GL (Fin (r + t)) k :=
  (emb₂ k (stdSum (rfl : r + t = r + t))).comp ((MonoidHom.inl _ _).comp (incl k r))
def unipLevel (r : ℕ) : Subgroup (GL (Fin r) 𝒪[k]) := (unipB 𝓀[k] (Fin r)).comap (red k r)
variable {k} {r t n : ℕ} {V W Y : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup Y] [Module ℂ Y]
def unipLevelChar (r : ℕ) (ψ₀ : AddChar 𝓀[k] ℂ) : unipLevel k r →* ℂˣ :=
  (genChar r ψ₀).comp ((red k r).subgroupComap _)
def IsLevel (J : Subgroup (GL (Fin r) 𝒪[k])) (lam : J →* ℂˣ) : Prop :=
  (red k r).ker ≤ J ∧ ∀ a : J, red k r a = 1 → lam a = 1
def typeW (σ : Representation ℂ (GL (Fin r) k) V) (J : Subgroup (GL (Fin r) 𝒪[k])) (lam : J →* ℂˣ) :
    Submodule ℂ V :=
  eig (σ.comp (incl k r)) J lam
def HasBlocks (h : GL (Fin (r + t)) 𝒪[k]) (a : GL (Fin r) 𝒪[k]) (d : GL (Fin t) 𝒪[k]) : Prop :=
  (∀ i j, h.val (Fin.castAdd t i) (Fin.castAdd t j) = a.val i j) ∧
  (∀ i j, h.val (Fin.natAdd r i) (Fin.natAdd r j) = d.val i j) ∧
  ∀ i j, h.val (Fin.natAdd r i) (Fin.castAdd t j) ∈ IsLocalRing.maximalIdeal 𝒪[k]
def typeG (π : Representation ℂ (GL (Fin (r + t)) k) W) (J : Subgroup (GL (Fin r) 𝒪[k]))
    (lam : J →* ℂˣ) (χ : kˣ →* ℂˣ) : Submodule ℂ W where
  carrier := {w | ∀ (h : GL (Fin (r + t)) 𝒪[k]) (a : J) (d : GL (Fin t) 𝒪[k]), HasBlocks h a d →
    π (incl k (r + t) h) w = ((lam a * detChar (Fin t) χ (incl k t d) : ℂˣ) : ℂ) • w}
  add_mem' := by
    intro x y hx hy h a d H
    rw [map_add, hx h a d H, hy h a d H, smul_add]
  zero_mem' := by intro h a d _; simp
  smul_mem' := by
    intro c x hx h a d H
    rw [map_smul, hx h a d H, smul_comm]
def liftRep (t : ℕ) (σ : Representation ℂ (GL (Fin r) k) V) (χW χV : kˣ →* ℂˣ) :=
  prod₂ (twist σ (detChar (Fin r) (χW * χV⁻¹))) (detRep (Fin t) χW)
def IsConstituent (τ : Representation ℂ (GL (Fin r) 𝓀[k]) Y) (π : Representation ℂ (GL (Fin r) 𝒪[k]) W)
    (T : Submodule ℂ W) : Prop :=
  τ.IsIrreducible ∧ ∃ f : Y →ₗ[ℂ] W, Function.Injective f ∧ (∀ y, f y ∈ T) ∧
    ∀ a y, f (τ (red k r a) y) = π a (f y)
def InDepthZero (τ : Representation ℂ (GL (Fin r) 𝓀[k]) Y) (σ : Representation ℂ (GL (Fin r) k) V) :
    Prop :=
  IsConstituent τ (σ.comp (incl k r)) (fixed σ (KOne k (Fin r)))
def typeGOne (π : Representation ℂ (GL (Fin (r + t)) k) W) (χ : kˣ →* ℂˣ) : Submodule ℂ W :=
  typeG π (red k r).ker 1 χ
def IsCharBlock (ρ : Representation ℂ (GL (Fin n) 𝓀[k]) Y) (χ : kˣ →* ℂˣ) : Prop :=
  n = 1 ∧ ∀ (u : GL (Fin n) 𝒪[k]) (y : Y),
    ρ (red k n u) y = (detChar (Fin n) χ (incl k n u) : ℂ) • y
def IsDepthZeroSupp (σ : Representation ℂ (GL (Fin r) k) V) {s : ℕ} (d : Fin s → ℕ) {X : Fin s → Type}
    [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)]
    (ρ : ∀ a, Representation ℂ (GL (Fin (d a)) 𝓀[k]) (X a)) : Prop :=
  ∃ (Y : Type) (_ : AddCommGroup Y) (_ : Module ℂ Y) (τ : Representation ℂ (GL (Fin r) 𝓀[k]) Y),
    InDepthZero τ σ ∧ IsSuppFin τ d ρ
def CharInSupp (σ : Representation ℂ (GL (Fin r) k) V) (χ : kˣ →* ℂˣ) : Prop :=
  ∃ (s : ℕ) (d : Fin s → ℕ) (X : Fin s → Type) (_ : ∀ a, AddCommGroup (X a)) (_ : ∀ a, Module ℂ (X a))
    (ρ : ∀ a, Representation ℂ (GL (Fin (d a)) 𝓀[k]) (X a)),
    IsDepthZeroSupp σ d ρ ∧ ∃ a, IsCharBlock (ρ a) χ
def GoodAt (σ : Representation ℂ (GL (Fin r) k) V) (χ : kˣ →* ℂˣ) : Prop :=
  ∃ (s : ℕ) (d : Fin s → ℕ) (X : Fin s → Type) (_ : ∀ a, AddCommGroup (X a)) (_ : ∀ a, Module ℂ (X a))
    (ρ : ∀ a, Representation ℂ (GL (Fin (d a)) 𝓀[k]) (X a)),
    IsDepthZeroSupp σ d ρ ∧ (∀ a b, a ≠ b → ¬ SameClass (ρ a) (ρ b)) ∧
      ∀ a, ¬ IsCharBlock (ρ a) χ ∧ ¬ IsCharBlock (ρ a) χ⁻¹
def IsDatum (σ : Representation ℂ (GL (Fin r) k) V) (χW χV : kˣ →* ℂˣ) : Prop :=
  (σ.IsIrreducible ∧ IsSmooth σ ∧ IsUnitarisable σ) ∧
    IsUnitaryChar χW ∧ IsUnitaryChar χV ∧ IsTame χW ∧ IsUnram (χW * χV⁻¹)
def DimEq (t : ℕ) (σ : Representation ℂ (GL (Fin r) k) V) (χW χV : kˣ →* ℂˣ) : Prop :=
  ∀ (J : Subgroup (GL (Fin r) 𝒪[k])) (lam : J →* ℂˣ), IsLevel J lam → ¬ CharInSupp σ χW →
    Module.rank ℂ (typeG (liftRep t σ χW χV) J lam χW) = Module.rank ℂ (typeW σ J lam)
def GoodLines (t : ℕ) (σ : Representation ℂ (GL (Fin r) k) V) (χW χV : kˣ →* ℂˣ) : Prop :=
  GoodAt σ χW → ∀ ψ₀ : AddChar 𝓀[k] ℂ, ψ₀ ≠ 1 →
    Module.rank ℂ (typeW σ (unipLevel k r) (unipLevelChar r ψ₀)) = 1 ∧
    Module.rank ℂ (typeG (liftRep t σ χW χV) (unipLevel k r) (unipLevelChar r ψ₀) χW) = 1
def RamifiedTypes (t : ℕ) (σ : Representation ℂ (GL (Fin r) k) V) (χW χV : kˣ →* ℂˣ) : Prop :=
  ¬ IsUnram χW →
    (IsSpherical σ →
      Module.rank ℂ (typeW σ ⊤ 1) = 1 ∧ Module.rank ℂ (typeG (liftRep t σ χW χV) ⊤ 1 χW) = 1) ∧
    (¬ IsSpherical σ → typeW σ ⊤ 1 = ⊥ ∧ typeG (liftRep t σ χW χV) ⊤ 1 χW = ⊥)
def SphericalLines (t : ℕ) (σ : Representation ℂ (GL (Fin r) k) V) (χW χV : kˣ →* ℂˣ) : Prop :=
  IsUnram χW → IsSpherical σ →
    Module.rank ℂ (fixed σ (KO k (Fin r))) = 1 ∧
    Module.rank ℂ (fixed (liftRep t σ χW χV) (KO k (Fin (r + t)))) = 1
def OneSupp (t : ℕ) (σ : Representation ℂ (GL (Fin r) k) V) (χW χV : kˣ →* ℂˣ) : Prop :=
  (∀ (Y Y' : Type) [AddCommGroup Y] [Module ℂ Y] [AddCommGroup Y'] [Module ℂ Y']
    (τ : Representation ℂ (GL (Fin r) 𝓀[k]) Y) (τ' : Representation ℂ (GL (Fin r) 𝓀[k]) Y'),
    InDepthZero τ σ →
      (InDepthZero τ' σ ∨ IsConstituent τ' ((liftRep t σ χW χV).comp (diagOne k r t))
        (typeGOne (liftRep t σ χW χV) χW)) → SameSupp τ τ') ∧
  (fixed σ (KOne k (Fin r)) = ⊥ → typeGOne (liftRep t σ χW χV) χW = ⊥)
def LocalAt (t : ℕ) (σ : Representation ℂ (GL (Fin r) k) V) (χW χV : kˣ →* ℂˣ) : Prop :=
  DimEq t σ χW χV ∧ GoodLines t σ χW χV ∧ RamifiedTypes t σ χW χV ∧ SphericalLines t σ χW χV ∧
    OneSupp t σ χW χV
end Local
section Places
variable {ι : Type} [Fintype ι] (k : ι → Type) [∀ v, Field (k v)] [∀ v, ValuativeRel (k v)]
  [∀ v, TopologicalSpace (k v)] [∀ v, IsNonarchimedeanLocalField (k v)] (r : ℕ)
def redAlg : MonoidAlgebra ℂ (∀ v, GL (Fin r) 𝒪[k v]) →ₐ[ℂ] MonoidAlgebra ℂ (∀ v, GL (Fin r) 𝓀[k v]) :=
  MonoidAlgebra.mapDomainAlgHom ℂ ℂ
    (MonoidHom.pi fun v => (red (k v) r).comp (Pi.evalMonoidHom (fun v => GL (Fin r) 𝒪[k v]) v))
variable {k r}
def IsRegularIdem (e : MonoidAlgebra ℂ (∀ v, GL (Fin r) 𝓀[k v])) : Prop :=
  ∀ (Y : ι → Type) [∀ v, AddCommGroup (Y v)] [∀ v, Module ℂ (Y v)]
    (τ : ∀ v, Representation ℂ (GL (Fin r) 𝓀[k v]) (Y v)), (∀ v, (τ v).IsIrreducible) →
    (piTensor τ).asAlgebraHom e = 0 ∨ ((piTensor τ).asAlgebraHom e = 1 ∧ ∀ v, HasRegularSupp (τ v))
def IdemAt (t : ℕ) {V : ι → Type} [∀ v, AddCommGroup (V v)] [∀ v, Module ℂ (V v)]
    (σ : ∀ v, Representation ℂ (GL (Fin r) (k v)) (V v)) (χW χV : ∀ v, (k v)ˣ →* ℂˣ) : Prop :=
  ∀ e' : MonoidAlgebra ℂ (∀ v, GL (Fin r) 𝒪[k v]), IsRegularIdem (redAlg k r e') →
  ∀ (Y : ι → Type) [∀ v, AddCommGroup (Y v)] [∀ v, Module ℂ (Y v)]
    (τ : ∀ v, Representation ℂ (GL (Fin r) 𝓀[k v]) (Y v)), (∀ v, InDepthZero (τ v) (σ v)) →
  ∀ c : ℂ, (∀ y, (piTensor τ).asAlgebraHom (redAlg k r e') y = c • y) →
    (∀ x : ∀ v, V v, (∀ v, x v ∈ fixed (σ v) (KOne (k v) (Fin r))) →
      (piTensor fun v => (σ v).comp (incl (k v) r)).asAlgebraHom e' (PiTensorProduct.tprod ℂ x) =
        c • PiTensorProduct.tprod ℂ x) ∧
    ∀ w, (∀ v, w v ∈ typeGOne (liftRep t (σ v) (χW v) (χV v)) (χW v)) →
      (piTensor fun v => (liftRep t (σ v) (χW v) (χV v)).comp (diagOne (k v) r t)).asAlgebraHom e'
        (PiTensorProduct.tprod ℂ w) = c • PiTensorProduct.tprod ℂ w
end Places
def LocalTypes : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (r t : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (σ : Representation ℂ (GL (Fin r) k) V)
    (χW χV : kˣ →* ℂˣ), IsDatum σ χW χV → LocalAt t σ χW χV
def IdemOnTypes : Prop :=
  ∀ (ι : Type) [Fintype ι] (k : ι → Type) [∀ v, Field (k v)] [∀ v, ValuativeRel (k v)]
    [∀ v, TopologicalSpace (k v)] [∀ v, IsNonarchimedeanLocalField (k v)] (r t : ℕ)
    (V : ι → Type) [∀ v, AddCommGroup (V v)] [∀ v, Module ℂ (V v)]
    (σ : ∀ v, Representation ℂ (GL (Fin r) (k v)) (V v)) (χW χV : ∀ v, (k v)ˣ →* ℂˣ),
    (∀ v, IsDatum (σ v) (χW v) (χV v)) → IdemAt t σ χW χV
def TypeSpaces : Prop := LocalTypes ∧ IdemOnTypes
section Examples
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
theorem isDatum_detRep (r : ℕ) {χ χW χV : kˣ →* ℂˣ} (h : IsUnram χ) (hu : IsUnitaryChar χ)
    (hW : IsUnitaryChar χW) (hV : IsUnitaryChar χV) (ht : IsTame χW) (hr : IsUnram (χW * χV⁻¹)) :
    IsDatum (detRep (Fin r) χ) χW χV :=
  ⟨⟨isIrreducible_ofChar _, (isSmooth_ofChar_iff _).2 (isSmoothChar_of_isUnram h).detChar,
    (isUnitarisable_ofChar_iff _).2 fun _ => hu _⟩, hW, hV, ht, hr⟩
example (r : ℕ) : IsDatum (detRep (Fin r) (1 : kˣ →* ℂˣ)) 1 1 :=
  isDatum_detRep r (fun _ _ => rfl) (fun _ => by simp) (fun _ => by simp) (fun _ => by simp)
    (fun _ _ => rfl) (fun _ _ => by simp)
example (r t : ℕ) : HasBlocks (k := k) (r := r) (t := t) 1 1 1 := by
  refine ⟨fun i j => ?_, fun i j => ?_, fun i j => ?_⟩
  · simp [Matrix.one_apply]
  · simp [Matrix.one_apply]
  · rw [Units.val_one, Matrix.one_apply_ne]
    · exact zero_mem _
    · intro e
      have := congrArg Fin.val e
      simp at this
      omega
end Examples
end GlobalTheory.IndefiniteRowSideFullHecke.CuspidalSupportClasses


