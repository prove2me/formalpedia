-- Prove2me | Definitions.Def_Formalism_SharpRestriction_GrowthBounds_DataG
-- name    : Formalism_SharpRestriction_GrowthBounds_DataG
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T18:36:59.430304+00:00
-- url     : https://prove2.me/theorems/000c043e-7e65-4fee-b068-dacf2c52c841
-- title:
--   Data G
-- statement:
--   Definitions and structural lemmas for Data G, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/DataG.lean

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_UnramifiedQuadraticSetting
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
namespace Formalism.MainNotions.G
open Formalism.GradedWeylDivisibility
def deltaL (R K : Type*) [CommRing R] [Field K] [Algebra R K] (k : ℕ) (ν : Fin k → ℕ)
    (g : Matrix (Fin k) (Fin k) K) : Submodule R (MvPolynomial (Fin k × Fin k) K) :=
  Submodule.comap ((rowAct K (n := k) g).toLinearMap.restrictScalars R)
    (Submodule.map (mapAlgHom (Algebra.ofId R K)).toLinearMap (weyl R k k le_rfl ν))
def deltaLTw (R K : Type*) [CommRing R] [Field K] [Algebra R K] (m : ℕ) (lam : Fin (m + 1) → ℤ)
    (g : Matrix (Fin (m + 1)) (Fin (m + 1)) K) : Submodule R (MvPolynomial (Fin (m + 1) × Fin (m + 1)) K) :=
  Submodule.map ((LinearMap.lsmul K (MvPolynomial (Fin (m + 1) × Fin (m + 1)) K)
      (g.det ^ (-(lam (Fin.last m))))).restrictScalars R)
    (deltaL R K (m + 1) (nuOf lam) g)
def Dl0 (O : Type*) {Kf : Type*} [CommRing O] [Field Kf] [Algebra O Kf] (m : ℕ) (lam : Fin (m + 1) → ℤ)
    (Λ : Submodule O (Fin (m + 1) → Kf)) : Submodule O (MvPolynomial (Fin (m + 1) × Fin (m + 1)) Kf) :=
  if Antitone lam then
    ⨅ (g : Matrix (Fin (m + 1)) (Fin (m + 1)) Kf) (_ : IsUnit g.det ∧ Λ = colSpan O g), deltaLTw O Kf m lam g
  else ⊥
def HtenW (O : Type*) {Kf : Type*} [CommRing O] [Field Kf] [Algebra O Kf] {n' m : ℕ}
    (lam0 : Fin n' → Fin (m + 1) → ℤ) (Λ : Fin n' → Submodule O (Fin (m + 1) → Kf)) :
    Submodule O (MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) Kf) :=
  tensorLat O Kf fun s => Dl0 O m (lamAt lam0 s) (Λ s)
structure Places (p : ℕ) (O Kf : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf]
    [Algebra O Kf] where
  w : O
  nV : ℕ
  n' : Fin nV → ℕ
  W : Fin nV → Type
  Qq : Fin nV → Type
  [ringW : ∀ v, CommRing (W v)]
  [domW : ∀ v, IsDomain (W v)]
  [dvrW : ∀ v, IsDiscreteValuationRing (W v)]
  [fieldQ : ∀ v, Field (Qq v)]
  [algWQ : ∀ v, Algebra (W v) (Qq v)]
  ι : ∀ v, Qq v →+* Kf
  σ : ∀ v, Qq v ≃+* Qq v
  j : ∀ v, W v →+* O
  setting : ∀ v, HidaSetting p (n' v) (W v) (Qq v) O Kf (ι v) (σ v) (j v) w
  m : ℕ
  r : ℕ
  lam0 : ∀ v, Fin (n' v) → Fin (m + 1) → ℤ

  dom : ∀ v, IsDominant (lam0 v)
attribute [instance] Places.ringW Places.domW Places.dvrW Places.fieldQ Places.algWQ
namespace Places
variable {p : ℕ} {O Kf : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  (P : Places p O Kf)
def Tup : Type := ∀ v, Submodule (P.W v) (Fin (P.m + 1) → P.Qq v)
def IsLatTup (L : P.Tup) : Prop := ∀ v, IsLattice (P.W v) (L v)
abbrev Xsp : Type := MvPolynomial (Σ v : Fin P.nV, Fin (P.n' v) × (Fin (P.m + 1) × Fin (P.m + 1))) Kf
def vEmb (v : Fin P.nV) : MvPolynomial (Fin (P.n' v) × (Fin (P.m + 1) × Fin (P.m + 1))) Kf →ₐ[Kf] P.Xsp :=
  rename fun x => ⟨v, x⟩
def tenV (M : ∀ v, Submodule O (MvPolynomial (Fin (P.n' v) × (Fin (P.m + 1) × Fin (P.m + 1))) Kf)) :
    Submodule O P.Xsp :=
  Submodule.span O {X | ∃ F : ∀ v, MvPolynomial (Fin (P.n' v) × (Fin (P.m + 1) × Fin (P.m + 1))) Kf,
    (∀ v, F v ∈ M v) ∧ X = ∏ v, P.vEmb v (F v)}
def Htup (L : P.Tup) : Submodule O P.Xsp :=
  P.tenV fun v => Hten O (P.lam0 v) fun s => extO O (P.ι v) (P.σ v) s.val (L v)
def HtupW (L : P.Tup) : Submodule O P.Xsp :=
  P.tenV fun v => HtenW O (P.lam0 v) fun s => extO O (P.ι v) (P.σ v) s.val (L v)
def sys (Φ : ∀ v, Submodule (P.W v) (Fin (P.m + 1) → P.Qq v) →
    Submodule O (MvPolynomial (Fin (P.n' v) × (Fin (P.m + 1) × Fin (P.m + 1))) Kf)) (L : P.Tup) :
    Submodule O P.Xsp :=
  P.tenV fun v => Φ v (L v)
def Vtup : Submodule Kf P.Xsp :=
  Submodule.span Kf {X | ∃ F : ∀ v, MvPolynomial (Fin (P.n' v) × (Fin (P.m + 1) × Fin (P.m + 1))) Kf,
    (∀ v, F v ∈ Vsp Kf (P.lam0 v)) ∧ X = ∏ v, P.vEmb v (F v)}
def ArV (v : Fin P.nV) : ℤ := Ar P.r (P.lam0 v)
def gPos (v : Fin P.nV) (s : Fin (P.n' v)) (A : Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) (P.Qq v)) :
    Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) Kf :=
  fun a b => P.ι v ((P.σ v ^ s.val) (A a b))
def subst (G : ∀ v, Fin (P.n' v) → Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) Kf) : P.Xsp →ₐ[Kf] P.Xsp :=
  aeval fun x => ∑ b : Fin (P.m + 1), C (G x.1 x.2.1 x.2.2.1 b) * X ⟨x.1, (x.2.1, (b, x.2.2.2))⟩
def natAct (A : ∀ v, GL (Fin (P.m + 1)) (P.Qq v)) : P.Xsp →ₗ[Kf] P.Xsp :=
  (∏ v, ∏ s : Fin (P.n' v), (P.gPos v s (A v : Matrix _ _ _)).det ^ (-(lamAt (P.lam0 v) s (Fin.last P.m)))) •
    (P.subst fun v s => P.gPos v s ((A v)⁻¹ : GL (Fin (P.m + 1)) (P.Qq v))).toLinearMap
end Places
structure Level {p : ℕ} {O Kf : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf]
    [Algebra O Kf] (P : Places p O Kf) where
  Γ : Type
  [grp : Group Γ]
  act : ∀ v, Γ →* GL (Fin (P.m + 1)) (P.Qq v)
  χ : Γ →* Oˣ
attribute [instance] Level.grp
namespace Level
variable {p : ℕ} {O Kf : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  {P : Places p O Kf} (C : Level P)
def smul (γ : C.Γ) (L : P.Tup) : P.Tup :=
  fun v => (L v).map ((Matrix.mulVecLin ((C.act v γ : GL (Fin (P.m + 1)) (P.Qq v)) :
    Matrix (Fin (P.m + 1)) (Fin (P.m + 1)) (P.Qq v))).restrictScalars (P.W v))
def actX (γ : C.Γ) : P.Xsp →ₗ[Kf] P.Xsp := P.natAct fun v => C.act v γ
def ActH : Prop := ∀ (γ : C.Γ) (L : P.Tup), P.IsLatTup L →
  (P.Htup L).map ((C.actX γ).restrictScalars O) = P.Htup (C.smul γ L)
def ActHW : Prop := ∀ (γ : C.Γ) (L : P.Tup), P.IsLatTup L →
  (P.HtupW L).map ((C.actX γ).restrictScalars O) = P.HtupW (C.smul γ L)
def funMod (Hv : P.Tup → Submodule O P.Xsp) : Submodule O (P.Tup → P.Xsp) :=
  (⨅ (L : P.Tup) (_ : P.IsLatTup L), (Hv L).comap (LinearMap.proj L)) ⊓
  (⨅ (L : P.Tup) (_ : ¬ P.IsLatTup L), LinearMap.ker (LinearMap.proj (R := O) (φ := fun _ : P.Tup => P.Xsp) L)) ⊓
  ⨅ (γ : C.Γ) (L : P.Tup), LinearMap.ker
    (LinearMap.proj (R := O) (φ := fun _ : P.Tup => P.Xsp) (C.smul γ L) -
      ((C.χ γ : O) • ((C.actX γ).restrictScalars O)) ∘ₗ
        LinearMap.proj (R := O) (φ := fun _ : P.Tup => P.Xsp) L)
def Mna : Submodule O (P.Tup → P.Xsp) := C.funMod P.Htup
def M : Submodule O (P.Tup → P.Xsp) := C.funMod P.HtupW
def dna : ℕ := Module.finrank O C.Mna
def d : ℕ := Module.finrank O C.M
def yv (v : Fin P.nV) (F : P.Tup → P.Xsp) : P.Tup → P.Xsp :=
  fun L => ((p : Kf) ^ P.ArV v) •
    ∑ᶠ (L'' : Submodule (P.W v) (Fin (P.m + 1) → P.Qq v)) (_ : IsEdge p (P.n' v) P.r ⟨L'', L v⟩),
      F (Function.update L v L'')
def Sandwich (e : ℕ) : Prop :=
  C.Mna.map (((p : O) ^ e) • LinearMap.id) ≤ C.M ∧ C.M ≤ C.Mna
def TrivStab : Prop := ∀ (γ : C.Γ) (L : P.Tup), P.IsLatTup L → C.smul γ L = L → γ = 1
def FinClasses : Prop :=
  ∃ R : Finset P.Tup, (∀ L ∈ R, P.IsLatTup L) ∧ ∀ L, P.IsLatTup L → ∃ L₀ ∈ R, ∃ γ : C.Γ, L = C.smul γ L₀
end Level
structure GAtP (p : ℕ) where
  O : Type
  Kf : Type
  [ringO : CommRing O]
  [domO : IsDomain O]
  [dvrO : IsDiscreteValuationRing O]
  [fieldK : Field Kf]
  [algOK : Algebra O Kf]
  P : Places p O Kf
  comp : Type
  [finComp : Fintype comp]
  lev : comp → Level P
  e : ℕ
attribute [instance] GAtP.ringO GAtP.domO GAtP.dvrO GAtP.fieldK GAtP.algOK GAtP.finComp
namespace GAtP
variable {p : ℕ} (G : GAtP p)
abbrev Fn : Type := G.comp → G.P.Tup → G.P.Xsp
def funMod (Hv : G.P.Tup → Submodule G.O G.P.Xsp) : Submodule G.O G.Fn :=
  Submodule.pi Set.univ fun i => (G.lev i).funMod Hv
def Mna : Submodule G.O G.Fn := G.funMod G.P.Htup
def M : Submodule G.O G.Fn := G.funMod G.P.HtupW
def d : ℕ := Module.finrank G.O G.M
def dna : ℕ := Module.finrank G.O G.Mna
def yv (v : Fin G.P.nV) (F : G.Fn) : G.Fn := fun i => Level.yv (P := G.P) v (F i)
def Sandwich : Prop :=
  G.Mna.map (((p : G.O) ^ G.e) • LinearMap.id) ≤ G.M ∧ G.M ≤ G.Mna
def TrivStab : Prop := ∀ i, (G.lev i).TrivStab
def FinClasses : Prop := ∀ i, (G.lev i).FinClasses
end GAtP
end Formalism.MainNotions.G


