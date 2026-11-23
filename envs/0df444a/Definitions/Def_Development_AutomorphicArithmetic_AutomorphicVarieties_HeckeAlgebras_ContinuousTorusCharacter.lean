-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_AutomorphicVarieties_HeckeAlgebras_ContinuousTorusCharacter
-- name    : Development_AutomorphicArithmetic_AutomorphicVarieties_HeckeAlgebras_ContinuousTorusCharacter
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T17:36:10.783538+00:00
-- url     : https://prove2.me/theorems/1d5fb354-6582-487d-9e02-29cdc010e906
-- title:
--   Continuous Torus Character
-- statement:
--   Definitions and structural lemmas for Continuous Torus Character, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/AutomorphicVarieties/HeckeAlgebras/ContinuousTorusCharacter.lean

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_FixedSubgroup
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open IsLocalRing Matrix
namespace UpperTheory.V.Hi
section Rep
variable {A H M : Type} [CommRing A] [Group H] [AddCommGroup M] [Module A M]
noncomputable def fixd (ρ : Representation A H M) (K : Subgroup H) : Submodule A M :=
  _root_.UpperTheory.Reformulated.B.SubgroupFixedSubmodule.fixd ρ K
def dc (ρ : Representation A H M) (K K' : Subgroup H) (x : H) : Module.End A M :=
  ∑ᶠ q : MulAction.orbit K (x : H ⧸ K'), ρ (q : H ⧸ K').out
def rtr (A H M : Type) [CommRing A] [Group H] [AddCommGroup M] [Module A M] : Representation A H (H → M) where
  toFun h := LinearMap.funLeft A M (· * h)
  map_one' := by ext f g; simp
  map_mul' h h' := by ext f g; simp [mul_assoc]
@[simp] theorem rtr_apply (h g : H) (f : H → M) : rtr A H M h f g = f (g * h) := rfl
end Rep
structure Iwa (G : Type) [Group G] where

  Nf : Subgroup G

  Tf : Subgroup G

  N : Subgroup G

  T : Subgroup G

  Tc : ℕ → Subgroup G

  Nm : ℕ → Subgroup G

  P : Submonoid G

  z : G
  N_le : N ≤ Nf
  T_le : T ≤ Tf
  P_le : ∀ a ∈ P, a ∈ Tf
  z_mem : z ∈ P
  Tc_le : ∀ c, Tc c ≤ T
  Tc_anti : Antitone Tc
  Nm_anti : Antitone Nm
  comm : ∀ s ∈ Tf, ∀ t ∈ Tf, s * t = t * s
  Tf_Nf : ∀ t ∈ Tf, ∀ x ∈ Nf, t * x * t⁻¹ ∈ Nf
  T_N : ∀ t ∈ T, ∀ x ∈ N, t * x * t⁻¹ ∈ N
  T_Nm : ∀ c, ∀ t ∈ T, ∀ y ∈ Nm c, t * y * t⁻¹ ∈ Nm c
  P_N : ∀ a ∈ P, ∀ x ∈ N, a * x * a⁻¹ ∈ N
  P_Nm : ∀ c, ∀ a ∈ P, ∀ y ∈ Nm c, a⁻¹ * y * a ∈ Nm c
  z_Nm : ∀ c, ∀ y ∈ Nm c, z⁻¹ * y * z ∈ Nm (c + 1)
  swap : ∀ c, ∀ y ∈ Nm c, ∀ x ∈ N, ∃ x' ∈ N, ∃ t ∈ Tc c, ∃ y' ∈ Nm c, y * x = x' * t * y'
  uniq : ∀ x ∈ Nf, ∀ t ∈ Tf, ∀ y ∈ Nm 0, x * t * y = 1 → x = 1 ∧ t = 1
  fin_N : ∀ a ∈ P, (N.map (MulAut.conj a).toMonoidHom).relIndex N ≠ 0
  fin_Nm : ∀ c, (Nm c).relIndex (Nm 0) ≠ 0
  fin_Tc : ∀ c, (Tc c).relIndex T ≠ 0
  exh : ∀ x ∈ Nf, ∃ k : ℕ, z ^ k * x * (z ^ k)⁻¹ ∈ N
  exists_pow_mul_inv_mem : ∀ a ∈ P, ∃ k : ℕ, z ^ k * a⁻¹ ∈ P
  gen : ∀ t ∈ Tf, ∃ s ∈ T, ∃ a ∈ P, ∃ b ∈ P, t = s * a * b⁻¹
namespace Iwa
def triv (G : Type) [CommGroup G] : Iwa G where
  Nf := ⊥
  Tf := ⊤
  N := ⊥
  T := ⊤
  Tc _ := ⊤
  Nm _ := ⊥
  P := ⊥
  z := 1
  N_le := le_rfl
  T_le := le_rfl
  P_le _ _ := trivial
  z_mem := Submonoid.one_mem _
  Tc_le _ := le_rfl
  Tc_anti _ _ _ := le_rfl
  Nm_anti _ _ _ := le_rfl
  comm s _ t _ := mul_comm s t
  Tf_Nf t _ x hx := by simpa using hx
  T_N t _ x hx := by simpa using hx
  T_Nm _ t _ x hx := by simpa using hx
  P_N t _ x hx := by simpa using hx
  P_Nm _ t _ x hx := by
    have : x = 1 := by simpa using hx
    simp [this]
  z_Nm _ x hx := by simpa using hx
  swap _ y hy x hx := ⟨x, hx, 1, trivial, y, hy, by rw [mul_one, mul_comm]⟩
  uniq x hx t _ y hy h := by
    have h1 : x = 1 := by simpa using hx
    have h2 : y = 1 := by simpa using hy
    simpa [h1, h2] using h
  fin_N _ _ := by simp
  fin_Nm _ := by simp
  fin_Tc _ := by simp
  exh x hx := ⟨0, by simpa using hx⟩
  exists_pow_mul_inv_mem a ha := ⟨0, by
    have : a = 1 := by simpa using ha
    simp [this]⟩
  gen t _ := ⟨t, trivial, 1, Submonoid.one_mem _, 1, Submonoid.one_mem _, by simp⟩
variable {G : Type} [Group G] (I : Iwa G)
def Iw (c : ℕ) : Subgroup G := I.N ⊔ I.T ⊔ I.Nm c
def I1 (c : ℕ) : Subgroup G := I.N ⊔ I.Tc c ⊔ I.Nm c
def Nconj (a : G) : Subgroup G := I.N.map (MulAut.conj a).toMonoidHom
variable {A M : Type} [CommRing A] [AddCommGroup M] [Module A M]
def uOp (π : Representation A G M) (a : G) : Module.End A M :=
  ∑ᶠ q : I.N ⧸ (I.Nconj a).subgroupOf I.N, π ((q.out : I.N) * a)
def jacKer (π : Representation A G M) : Submodule A M :=
  Submodule.span A {w | ∃ x ∈ I.Nf, ∃ v, w = π x v - v}
def Smooth (π : Representation A G M) : Prop :=
  ∀ v, ∃ c : ℕ, v ∈ fixd π (I.Nconj (I.z ^ c)) ∧ v ∈ fixd π (I.Tc c) ∧ v ∈ fixd π (I.Nm c)
def eig (π : Representation A G M) (c : ℕ) (φ : I.T →* Aˣ) : Submodule A M where
  carrier := {v | v ∈ fixd π I.N ∧ v ∈ fixd π (I.Nm c) ∧ ∀ t : I.T, π t v = (((φ t)⁻¹ : Aˣ) : A) • v}
  add_mem' ha hb := ⟨add_mem ha.1 hb.1, add_mem ha.2.1 hb.2.1, fun t => by rw [map_add, ha.2.2, hb.2.2, smul_add]⟩
  zero_mem' := ⟨zero_mem _, zero_mem _, fun t => by simp⟩
  smul_mem' c v hv := ⟨Submodule.smul_mem _ c hv.1, Submodule.smul_mem _ c hv.2.1, fun t => by
    rw [map_smul, hv.2.2, smul_comm]⟩
def ContChar [IsLocalRing A] (θ : I.T →* Aˣ) : Prop :=
  ∀ k : ℕ, ∃ c, ∀ t : I.T, (t : G) ∈ I.Tc c → (θ t : A) - 1 ∈ maximalIdeal A ^ k
end Iwa
class IsCNL (A : Type) [CommRing A] : Prop extends IsLocalRing A, IsNoetherianRing A where
  complete : IsAdicComplete (maximalIdeal A) A
  finite : Finite (ResidueField A)
attribute [instance] IsCNL.complete IsCNL.finite
instance (p : ℕ) [Fact p.Prime] : IsCNL ℤ_[p] where
  complete := inferInstance
  finite := Finite.of_equiv _ (PadicInt.residueField (p := p)).symm.toEquiv
structure Frame (Γ Ga Gp : Type) [Group Γ] [Group Ga] [Group Gp] where
  I : Iwa Gp
  glob : Γ →* Ga × Gp
  Ub : Subgroup Ga
namespace Frame
variable {Γ Ga Gp : Type} [Group Γ] [Group Ga] [Group Gp] (X : Frame Γ Ga Gp)
abbrev Fn (_X : Frame Γ Ga Gp) (A : Type) (m : ℕ) : Type := Ga × Gp → Fin m → A
def FinLevel (U : Subgroup X.Ub) : Prop :=
  ∃ s : Finset (Ga × Gp), ∀ g, ∃ γ, ∃ x ∈ s, ∃ u ∈ U, ∃ b ∈ X.I.Iw 0, g = X.glob γ * x * ((u : Ga), b)
def Neat (U : Subgroup X.Ub) : Prop :=
  ∀ g γ, ∀ u ∈ U, ∀ b ∈ X.I.Iw 0, X.glob γ * g = g * ((u : Ga), b) → u = 1 ∧ b = 1
section Padic
variable {A : Type} [CommRing A] {m : ℕ} (τ : X.Ub →* GL (Fin m) A) (θ : X.I.T →* Aˣ)
def Free (U : Subgroup X.Ub) : Prop :=
  ∀ g γ, ∀ u ∈ U, ∀ b ∈ X.I.Iw 0, X.glob γ * g = g * ((u : Ga), b) →
    b ∈ Subgroup.center Gp ∧ ∃ hb : b ∈ X.I.T, (θ ⟨b, hb⟩ : A) • (τ u : Matrix (Fin m) (Fin m) A) = 1
variable (A m) in

def rp : Representation A Gp (X.Fn A m) := (rtr A (Ga × Gp) (Fin m → A)).comp (MonoidHom.inr Ga Gp)
def ra : Representation A X.Ub (X.Fn A m) where
  toFun u :=
    { toFun := fun f g => (τ u : Matrix (Fin m) (Fin m) A) *ᵥ f (g * ((u : Ga), 1))
      map_add' := fun f f' => by ext g i; simp [mulVec_add]
      map_smul' := fun c f => by ext g i; simp [mulVec_smul] }
  map_one' := by ext f g i; simp [← Prod.one_eq_mk]
  map_mul' u u' := by ext f g i; simp [mul_assoc]
variable (A m) in

def U (a : Gp) : Module.End A (X.Fn A m) := X.I.uOp (X.rp A m) a
variable [IsLocalRing A]
variable (m) in

def Amb : Submodule A (X.Fn A m) where
  carrier := {f | (∀ γ g, f (X.glob γ * g) = f g) ∧ f ∈ fixd (X.rp A m) X.I.N ∧
    (∀ t : X.I.T, X.rp A m t f = (((θ t)⁻¹ : Aˣ) : A) • f) ∧
    ∀ k : ℕ, ∃ c, ∀ y ∈ X.I.Nm c, ∀ g i, f (g * (1, y)) i - f g i ∈ maximalIdeal A ^ k}
  add_mem' {f f'} h h' := ⟨fun γ g => by simp [h.1, h'.1], add_mem h.2.1 h'.2.1,
    fun t => by rw [map_add, h.2.2.1, h'.2.2.1, smul_add], fun k => by
      obtain ⟨c, hc⟩ := h.2.2.2 k
      obtain ⟨c', hc'⟩ := h'.2.2.2 k
      refine ⟨max c c', fun y hy g i => ?_⟩
      have := add_mem (hc y (X.I.Nm_anti (le_max_left _ _) hy) g i) (hc' y (X.I.Nm_anti (le_max_right _ _) hy) g i)
      convert this using 1
      simp only [Pi.add_apply]
      ring⟩
  zero_mem' := ⟨fun _ _ => rfl, zero_mem _, fun t => by simp, fun k => ⟨0, fun _ _ _ _ => by simp⟩⟩
  smul_mem' a f h := ⟨fun γ g => by simp [h.1], Submodule.smul_mem _ a h.2.1,
    fun t => by rw [map_smul, h.2.2.1, smul_comm], fun k => by
      obtain ⟨c, hc⟩ := h.2.2.2 k
      refine ⟨c, fun y hy g i => ?_⟩
      have := Ideal.mul_mem_left _ a (hc y hy g i)
      convert this using 1
      simp only [Pi.smul_apply, smul_eq_mul]
      ring⟩
def Sp (U : Subgroup X.Ub) : Submodule A (X.Fn A m) := X.Amb m θ ⊓ fixd (X.ra τ) U
variable (A m) in

def valIn (k : ℕ) : Submodule A (X.Fn A m) :=
  Submodule.pi Set.univ fun _ => Submodule.pi Set.univ fun _ => maximalIdeal A ^ k
def Ord (U : Subgroup X.Ub) : Submodule A (X.Fn A m) :=
  X.Sp τ θ U ⊓ ⨅ k : ℕ, ⨆ n : ℕ, (X.valIn A m k).comap (X.U A m X.I.z ^ (n + 1) - 1)
end Padic
def mapFn {A B : Type} [CommRing A] [CommRing B] [Algebra A B] {m : ℕ} : X.Fn A m →ₗ[A] X.Fn B m where
  toFun f g i := algebraMap A B (f g i)
  map_add' f f' := by ext g i; simp
  map_smul' c f := by ext g i; simp [Algebra.smul_def]
end Frame
section Loc
variable {A M ι : Type} [CommRing A] [IsLocalRing A] [AddCommGroup M] [Module A M]
def locPart (Y : Submodule A M) (op : ι → Module.End A M) (a : ι → A) : Submodule A M :=
  Y ⊓ ⨅ (i : ι) (k : ℕ), ⨆ n : ℕ, (maximalIdeal A ^ k • Y).comap ((op i - algebraMap A _ (a i)) ^ n)
omit [IsLocalRing A] in

def Restr {Y : Submodule A M} (t : Module.End A Y) (φ : Module.End A M) : Prop := ∀ y : Y, (t y : M) = φ y
omit [IsLocalRing A] in

def heckeAlg (Y : Submodule A M) (op : ι → Module.End A M) : Subalgebra A (Module.End A Y) :=
  Algebra.adjoin A {t | ∃ i, Restr t (op i)}
omit [IsLocalRing A] in

def CommOn (Y : Submodule A M) (op : ι → Module.End A M) : Prop :=
  (∀ i, ∀ y ∈ Y, op i y ∈ Y) ∧ ∀ i j, ∀ y ∈ Y, op i (op j y) = op j (op i y)
end Loc
section Classical
def IsIntUnit (O : Type) {Ω : Type} [CommRing O] [Field Ω] [Algebra O Ω] (x : Ω) : Prop :=
  x ≠ 0 ∧ IsIntegral O x ∧ IsIntegral O x⁻¹
structure WtRep {G : Type} [Group G] (I : Iwa G) (O Ω : Type) [CommRing O] [IsLocalRing O] [Field Ω] [Algebra O Ω] where
  d : ℕ
  ξ : G →* GL (Fin (d + 1)) Ω
  χ : I.Tf →* Ωˣ
  c0 : ℕ
  int_N : ∀ x ∈ I.N, ∀ i j, ξ x i j ∈ (algebraMap O Ω).range
  integral_torusCharacter : ∀ x ∈ I.T, ∀ i j, ξ x i j ∈ (algebraMap O Ω).range
  int_Nm : ∀ x ∈ I.Nm c0, ∀ i j, ξ x i j ∈ (algebraMap O Ω).range
  int_P : ∀ a (ha : a ∈ I.P) i j, ((χ ⟨a, I.P_le a ha⟩)⁻¹ : Ωˣ) * ξ a i j ∈ (algebraMap O Ω).range
  row_N : ∀ x ∈ I.Nf, ∀ j, ξ x 0 j = if j = 0 then 1 else 0
  torusAction : ∀ (t : I.Tf) j, ξ t 0 j = if j = 0 then (χ t : Ω) else 0
  nilpotent_central_action : ∀ i j, j ≠ 0 → ∃ x ∈ maximalIdeal O,
    ((χ ⟨I.z, I.P_le _ I.z_mem⟩)⁻¹ : Ωˣ) * ξ I.z i j = algebraMap O Ω x
  cont_Nm : ∀ k : ℕ, ∃ c, ∀ y ∈ I.Nm c, ∀ i j, ∃ x ∈ maximalIdeal O ^ k,
    ξ y i j = (if i = j then 1 else 0) + algebraMap O Ω x
  continuous_torusCharacter : ∀ k : ℕ, ∃ c, ∀ t : I.Tf, (t : G) ∈ I.Tc c → ∃ x ∈ maximalIdeal O ^ k, (χ t : Ω) = 1 + algebraMap O Ω x
  central : ∀ t : I.Tf, (t : G) ∈ Subgroup.center G → ∀ i j, ξ t i j = if i = j then (χ t : Ω) else 0
theorem fin1 (i j : Fin (0 + 1)) : i = j := Subsingleton.elim (α := Fin 1) i j
def WtRep.triv {G : Type} [Group G] (I : Iwa G) (O Ω : Type) [CommRing O] [IsLocalRing O] [Field Ω] [Algebra O Ω] :
    WtRep I O Ω where
  d := 0
  ξ := 1
  χ := 1
  c0 := 0
  int_N _ _ i j := ⟨1, by simp [fin1 i j]⟩
  integral_torusCharacter _ _ i j := ⟨1, by simp [fin1 i j]⟩
  int_Nm _ _ i j := ⟨1, by simp [fin1 i j]⟩
  int_P _ _ i j := ⟨1, by simp [fin1 i j]⟩
  row_N _ _ j := by simp [fin1 j 0]
  torusAction _ j := by simp [fin1 j 0]
  nilpotent_central_action _ j hj := absurd (fin1 j 0) hj
  cont_Nm _ := ⟨0, fun _ _ i j => ⟨0, zero_mem _, by simp [fin1 i j]⟩⟩
  continuous_torusCharacter _ := ⟨0, fun _ _ => ⟨0, zero_mem _, by simp⟩⟩
  central _ _ i j := by simp [fin1 i j]
namespace Frame
variable {Γ Ga Gp : Type} [Group Γ] [Group Ga] [Group Gp] (X : Frame Γ Ga Gp) {Ω : Type} [Field Ω] {d m : ℕ}
def AF (ξ : Gp →* GL (Fin d) Ω) : Submodule Ω (X.Fn Ω d) where
  carrier := {F | ∀ γ g, F (X.glob γ * g) = (ξ (X.glob γ).2 : Matrix (Fin d) (Fin d) Ω) *ᵥ F g}
  add_mem' h h' γ g := by simp [h γ g, h' γ g, mulVec_add]
  zero_mem' γ g := by simp
  smul_mem' c F h γ g := by simp [h γ g, mulVec_smul]
variable (Ω d m) in

def rpF : Representation Ω Gp (Fin m → X.Fn Ω d) where
  toFun b := LinearMap.compLeft (X.rp Ω d b) (Fin m)
  map_one' := by ext1 F; simp; rfl
  map_mul' b b' := by ext1 F; simp; rfl
variable (d) in

def raF (τ : X.Ub →* GL (Fin m) Ω) : Representation Ω X.Ub (Fin m → X.Fn Ω d) where
  toFun u :=
    { toFun := fun F i g k => X.ra τ u (fun g j => F j g k) g i
      map_add' := fun F F' => by ext i g k; exact congrFun (congrFun ((X.ra τ u).map_add _ _) g) i
      map_smul' := fun c F => by ext i g k; exact congrFun (congrFun ((X.ra τ u).map_smul c _) g) i }
  map_one' := by
    refine LinearMap.ext fun F => ?_
    ext i g k
    simp
  map_mul' u u' := by
    refine LinearMap.ext fun F => ?_
    ext i g k
    simp
def Cl (τ : X.Ub →* GL (Fin m) Ω) (ξ : Gp →* GL (Fin d) Ω) (U : Subgroup X.Ub) (c : ℕ) (φ : X.I.T →* Ωˣ) :
    Submodule Ω (Fin m → X.Fn Ω d) :=
  Submodule.pi Set.univ (fun _ => X.AF ξ) ⊓ fixd (X.raF d τ) U ⊓ X.I.eig (X.rpF Ω d m) c φ
variable {O : Type} [CommRing O] [IsLocalRing O] [Algebra O Ω] (W : WtRep X.I O Ω)
variable (m) in

def UF (a : X.I.P) : Module.End Ω (Fin m → X.Fn Ω (W.d + 1)) :=
  (((W.χ ⟨a, X.I.P_le a a.2⟩)⁻¹ : Ωˣ) : Ω) • X.I.uOp (X.rpF Ω (W.d + 1) m) a
def ClOrd (τ : X.Ub →* GL (Fin m) Ω) (U : Subgroup X.Ub) (c : ℕ) (φ : X.I.T →* Ωˣ) :
    Submodule Ω (Fin m → X.Fn Ω (W.d + 1)) :=
  ⨆ μ : {μ : Ω // IsIntUnit O μ}, X.Cl τ W.ξ U c φ ⊓ (X.UF m W ⟨X.I.z, X.I.z_mem⟩).maxGenEigenspace μ.1
variable (m) in

def ctrl : (Fin m → X.Fn Ω (W.d + 1)) →ₗ[Ω] X.Fn Ω m where
  toFun F g i := (((W.ξ g.2)⁻¹).val *ᵥ F i g) 0
  map_add' F F' := by ext g i; simp only [Pi.add_apply, mulVec_add]
  map_smul' c F := by ext g i; simp only [Pi.smul_apply, mulVec_smul, RingHom.id_apply]
end Frame
end Classical
end UpperTheory.V.Hi


