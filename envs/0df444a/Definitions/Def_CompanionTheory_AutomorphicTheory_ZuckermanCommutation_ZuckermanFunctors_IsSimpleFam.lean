-- Prove2me | Definitions.Def_CompanionTheory_AutomorphicTheory_ZuckermanCommutation_ZuckermanFunctors_IsSimpleFam
-- name    : CompanionTheory_AutomorphicTheory_ZuckermanCommutation_ZuckermanFunctors_IsSimpleFam
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T02:58:48.48384+00:00
-- url     : https://prove2.me/theorems/a2650a13-c4fb-4c7c-8d24-6eedbd5435ad
-- title:
--   Is Simple Fam
-- statement:
--   Definitions and structural lemmas for Is Simple Fam, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/ZuckermanCommutation/ZuckermanFunctors/IsSimpleFam.lean

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_SumIoPrAlt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_SumIoPr
import Definitions.Def_Formalism_PeriodIntegrals_ZuckTensor
import Definitions.Def_Formalism_PeriodIntegrals_DSInfCharCap
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CapelliEigenvalues_HeckeMultiplication
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_PhMeas
import Theorems.Thm_CompanionTheory_D_Upq_Sm_IsSm_add
import Theorems.Thm_CompanionTheory_D_Upq_Sm_IsSm_apply
import Theorems.Thm_CompanionTheory_D_Upq_Sm_IsSm_smul
import Theorems.Thm_CompanionTheory_D_Upq_Sm_IsSm_zero
import Theorems.Thm_CompanionTheory_D_Upq_Sm_SmOn_add
import Theorems.Thm_CompanionTheory_D_Upq_Sm_ds_add
import Theorems.Thm_CompanionTheory_D_Upq_Sm_ds_smul
import Theorems.Thm_CompanionTheory_D_Upq_Sm_ex_mem_of_lie
import Theorems.Thm_PI_UnitaryGroupMassFormula_CapelliEig_unitary_Hecke_group

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped InnerProductSpace Kronecker
noncomputable section
namespace CompanionTheory.Zuck
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData CompanionTheory.D.Upq.Sm
open PI.UpqRep (IsURepOn InLieHpk dsigW IsHCParam)
section Lin
universe u
variable {O : Type u} (N : O → Type) [∀ o, AddCommGroup (N o)] [∀ o, Module ℂ (N o)]
structure IsLinCat (Hom : ∀ a b, (N a →ₗ[ℂ] N b) → Prop) : Prop where
  zero : ∀ a b, Hom a b 0
  add : ∀ a b f g, Hom a b f → Hom a b g → Hom a b (f + g)
  smul : ∀ a b (c : ℂ) f, Hom a b f → Hom a b (c • f)
  id : ∀ a, Hom a a LinearMap.id
  comp : ∀ a b c f g, Hom a b f → Hom b c g → Hom a c (g ∘ₗ f)
variable {N}
structure IsDec (Hom : ∀ a b, (N a →ₗ[ℂ] N b) → Prop) {κ : Type} [Fintype κ] (X : O) (T : κ → O)
    (io : ∀ k, N (T k) →ₗ[ℂ] N X) (pr : ∀ k, N X →ₗ[ℂ] N (T k)) : Prop where
  io_hom : ∀ k, Hom (T k) X (io k)
  pr_hom : ∀ k, Hom X (T k) (pr k)
  sum : ∑ k, io k ∘ₗ pr k = LinearMap.id
  pr_io : ∀ k, pr k ∘ₗ io k = LinearMap.id
  pr_io_ne : ∀ k k', k ≠ k' → pr k ∘ₗ io k' = 0
def IsSimpleFam (Hom : ∀ a b, (N a →ₗ[ℂ] N b) → Prop) {S : Type} (T : S → O) : Prop :=
  (∀ s, Nontrivial (N (T s))) ∧ (∀ s f, Hom (T s) (T s) f → ∃ c : ℂ, f = c • LinearMap.id) ∧
    ∀ s t, s ≠ t → ∀ f, Hom (T s) (T t) f → f = 0
def JInj (Hom : ∀ a b, (N a →ₗ[ℂ] N b) → Prop) {S : Type} (X : O) (T : S → O) : Prop :=
  ∀ x : N X, (∀ s p, Hom X (T s) p → p x = 0) → x = 0
def AtMostOne (Hom : ∀ a b, (N a →ₗ[ℂ] N b) → Prop) (a b : O) : Prop :=
  ∀ f g, Hom a b f → Hom a b g → ∃ α β : ℂ, (α ≠ 0 ∨ β ≠ 0) ∧ α • f + β • g = 0
def IsIso (Hom : ∀ a b, (N a →ₗ[ℂ] N b) → Prop) (a b : O) : Prop :=
  ∃ f g, Hom a b f ∧ Hom b a g ∧ g ∘ₗ f = LinearMap.id ∧ f ∘ₗ g = LinearMap.id
end Lin
def DecOfInj : Prop :=
  ∀ (O : Type 1) (N : O → Type) [∀ o, AddCommGroup (N o)] [∀ o, Module ℂ (N o)]
    (Hom : ∀ a b, (N a →ₗ[ℂ] N b) → Prop), IsLinCat N Hom →
    ∀ (S : Type) [Fintype S] (X : O) (T : S → O), IsSimpleFam Hom T → JInj Hom X T →
      (∀ s, AtMostOne Hom X (T s)) → (∀ s, ∃ i, Hom (T s) X i ∧ i ≠ 0) → ∃ io pr, IsDec Hom X T io pr
def DecOfTrace : Prop :=
  ∀ (O : Type 1) (N : O → Type) [∀ o, AddCommGroup (N o)] [∀ o, Module ℂ (N o)]
    (Hom : ∀ a b, (N a →ₗ[ℂ] N b) → Prop), IsLinCat N Hom →
    ∀ (P : Type) [DecidableEq P] (T : P → O), IsSimpleFam Hom T →
    ∀ (κ : Type) [Fintype κ] (par : κ → P) (X Z : O)
      (io₁ io₂ : ∀ k, N (T (par k)) →ₗ[ℂ] N X) (pr₁ pr₂ : ∀ k, N X →ₗ[ℂ] N (T (par k))),
      IsDec Hom X (fun k => T (par k)) io₁ pr₁ → IsDec Hom X (fun k => T (par k)) io₂ pr₂ →
    ∀ (Φ Φ₁ Φ₂ : Module.End ℂ (N X)) (a b : κ → ℂ) (cs : P → ℂ) (α β : ℂ),
      (∀ k, Φ₁ ∘ₗ io₁ k = a k • io₁ k) → (∀ k, Φ₂ ∘ₗ io₂ k = b k • io₂ k) →
      (∀ ν i, Hom (T ν) X i → Φ ∘ₗ i = cs ν • i) →
    ∀ (j : N Z →ₗ[ℂ] N X) (q : N X →ₗ[ℂ] N Z), Hom Z X j → Hom X Z q → q ∘ₗ j = LinearMap.id → β ≠ 0 →
      Φ = Φ₁ + Φ₂ + α • LinearMap.id - β • (j ∘ₗ q) →
    ∀ (I : Type) [Fintype I] (e : I → P), Function.Injective e →
      (∀ i, ∑ k ∈ univ.filter (fun k => par k = e i), (a k + b k + α - cs (e i)) = β) →
      (∀ ν, (∀ i, e i ≠ ν) → ∑ k ∈ univ.filter (fun k => par k = ν), (a k + b k + α - cs ν) = 0) →
      ∃ io pr, IsDec Hom Z (fun i => T (e i)) io pr
structure FRep (k r : ℕ) : Type 1 where
  ι : Type
  [fin : Fintype ι]
  [dec : DecidableEq ι]
  ρ : Mx k r → Matrix ι ι ℂ
  deg : ℕ
attribute [instance] FRep.fin FRep.dec
variable {k r : ℕ}
structure FRep.OK (F : FRep k r) : Prop where
  one : F.ρ 1 = 1
  mul : ∀ g ∈ GG k r, ∀ h ∈ GG k r, F.ρ (g * h) = F.ρ g * F.ρ h
  smooth : ∀ c d, PI.UpqRep.SmoothOnH (PI.UpqRep.Hpk k r) fun g => F.ρ g c d
  growth : ∃ C : ℝ, ∀ g ∈ GG k r, ∀ c d, ‖F.ρ g c d‖ ≤ C * B.gN g ^ F.deg
abbrev triv (k r : ℕ) : FRep k r := { ι := Unit, ρ := fun _ => 1, deg := 0 }
abbrev vr (k r : ℕ) (b : Bool) : FRep k r :=
  { ι := Fin (2 * r + k + 1), ρ := fun g => if b then dualM g else g, deg := 1 }
abbrev wedge (k r l : ℕ) : FRep k r := { ι := Sub (2 * r + k + 1) l, ρ := cmp l, deg := l }
abbrev FRep.tens (F F' : FRep k r) : FRep k r :=
  { ι := F.ι × F'.ι, ρ := fun g => F.ρ g ⊗ₖ F'.ρ g, deg := F.deg + F'.deg }
structure URep (k r : ℕ) : Type 1 where
  R : Rep k r
  rep : IsURepOn (GG k r) R.σ
theorem URep.repOn (U : URep k r) : RepOn (GG k r) U.R.σ where
  one_mem := by show (1 : Mx k r)ᴴ * _ * 1 = _; simp
  mul_mem := fun a ha b hb => (PI.UnitaryGroupMassFormula.CapelliEig.unitary_Hecke_group k r a ha).2.2 b hb
  map_one := U.rep.1.1
  map_mul := U.rep.1.2
open Classical in

def URep.sig (U : URep k r) (g : Mx k r) : Module.End ℂ U.R.smSub :=
  if hg : g ∈ GG k r then
    ((U.R.σ g : U.R.H →ₗ[ℂ] U.R.H).restrict fun v hv => IsSm.apply U.repOn (w := v) hv hg)
  else 0
open Classical in

def URep.dsig (U : URep k r) (X : Mx k r) : Module.End ℂ U.R.smSub :=
  if hX : InLieHpk k r X then
    { toFun := fun v => ⟨ds U.R.σ X v, IsSm.dsW U.repOn (W := [X]) v.2
        (fun Y hY t => by rw [List.mem_singleton.1 hY]; exact ex_mem_of_lie hX t)⟩
      map_add' := fun v w => Subtype.ext (ds_add U.repOn (ex_mem_of_lie hX) v.2 w.2)
      map_smul' := fun c v => Subtype.ext (ds_smul U.repOn (ex_mem_of_lie hX) v.2 c) }
  else 0
abbrev Obj (k r : ℕ) : Type 1 := FRep k r × URep k r
abbrev M (X : Obj k r) : Type := X.1.ι → X.2.R.smSub
def mAct {ι ι' : Type} [Fintype ι] {V : Type} [AddCommGroup V] [Module ℂ V] (A : Matrix ι' ι ℂ) :
    (ι → V) →ₗ[ℂ] (ι' → V) :=
  LinearMap.pi fun c => ∑ d, A c d • LinearMap.proj d
def dOp (ι : Type) {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] (T : V →ₗ[ℂ] V') :
    (ι → V) →ₗ[ℂ] (ι → V') := T.compLeft ι
def act (X : Obj k r) (g : Mx k r) : Module.End ℂ (M X) := mAct (X.1.ρ g) ∘ₗ dOp X.1.ι (X.2.sig g)
def sn (X : Obj k r) (W : List (Mx k r)) (x : M X) : ℝ :=
  ∑ c, ‖dsigW (k := k) (r := r) X.2.R.σ W (x c : X.2.R.H)‖
def LieWd (k r : ℕ) (W : List (Mx k r)) : Prop := ∀ Y ∈ W, InLieHpk k r Y
structure IsHom (X Y : Obj k r) (f : M X →ₗ[ℂ] M Y) : Prop where
  cont : ∀ W, LieWd k r W → ∃ (C : ℝ) (Ws : List (List (Mx k r))), (∀ W' ∈ Ws, LieWd k r W') ∧
    ∀ x, sn Y W (f x) ≤ C * (Ws.map fun W' => sn X W' x).sum
  equiv : ∀ g ∈ GG k r, f ∘ₗ act X g = act Y g ∘ₗ f
def reH (k r : ℕ) (Y : Mx k r) : Mx k r := (1 / 2 : ℂ) • (Y + -(Formalism.QuantumDeterminants.Hpk k r * Yᴴ * Formalism.QuantumDeterminants.Hpk k r))
def imH (k r : ℕ) (Y : Mx k r) : Mx k r :=
  (1 / (2 * Complex.I)) • (Y - -(Formalism.QuantumDeterminants.Hpk k r * Yᴴ * Formalism.QuantumDeterminants.Hpk k r))
def FRep.dR (F : FRep k r) (X : Mx k r) : Matrix F.ι F.ι ℂ :=
  fun c d => deriv (fun t : ℝ => F.ρ (NormedSpace.exp ((t : ℂ) • X)) c d) 0
def FRep.dC (F : FRep k r) (Y : Mx k r) : Matrix F.ι F.ι ℂ := F.dR (reH k r Y) + Complex.I • F.dR (imH k r Y)
def URep.dC (U : URep k r) (Y : Mx k r) : Module.End ℂ U.R.smSub :=
  U.dsig (reH k r Y) + Complex.I • U.dsig (imH k r Y)
def L (X : Obj k r) (Y : Mx k r) : Module.End ℂ (M X) := dOp X.1.ι (X.2.dC Y) + mAct (X.1.dC Y)
def cas (X : Obj k r) : Module.End ℂ (M X) :=
  ∑ a, ∑ b, L X (Matrix.single a b 1) * L X (Matrix.single b a 1)
abbrev one (U : URep k r) : Obj k r := (triv k r, U)
def on1 {ι ι' κ V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
    (f : (ι → V) →ₗ[ℂ] (ι' → V')) : (ι × κ → V) →ₗ[ℂ] (ι' × κ → V') :=
  LinearMap.pi fun p => LinearMap.proj p.1 ∘ₗ f ∘ₗ LinearMap.funLeft ℂ V fun c => (c, p.2)
def on2 {ι κ κ' V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
    (f : (κ → V) →ₗ[ℂ] (κ' → V')) : (ι × κ → V) →ₗ[ℂ] (ι × κ' → V') :=
  LinearMap.pi fun p => LinearMap.proj p.2 ∘ₗ f ∘ₗ LinearMap.funLeft ℂ V fun d => (p.1, d)
def cas1 (F F' : FRep k r) (U : URep k r) : Module.End ℂ (M (F.tens F', U)) := on1 (cas (F, U))
def cas2 (F F' : FRep k r) (U : URep k r) : Module.End ℂ (M (F.tens F', U)) := on2 (cas (F', U))
def casR (X : Obj k r) : Module.End ℂ (M X) :=
  dOp X.1.ι (∑ a, ∑ b, X.2.dC (Matrix.single a b 1) * X.2.dC (Matrix.single b a 1))
def qMat (F F' : FRep k r) : Matrix (F.ι × F'.ι) (F.ι × F'.ι) ℂ :=
  ∑ a, ∑ b, F.dC (Matrix.single a b 1) ⊗ₖ F'.dC (Matrix.single b a 1)
def jW (n m : ℕ) : Matrix (Sub n m × Fin n) (Sub n (m + 1)) ℂ :=
  fun p I => if p.2 ∉ p.1.1 ∧ I.1 = insert p.2 p.1.1 then (-1) ^ (p.1.1.filter fun a => a < p.2).card else 0
def shift {n : ℕ} (b : Bool) (μ : Fin n → ℝ) (s : Fin n) : Fin n → ℝ :=
  if b then μ - Pi.single s 1 else μ + Pi.single s 1
def CoefIn (X : Obj k r) {S : Type} (T : S → URep k r) : Prop :=
  ∀ v w, X.2.R.KFin v → X.2.R.KFin w → ∀ c d, ∃ (I : Type) (_ : Fintype I) (s : I → S) (y y' : ∀ i, (T (s i)).R.H),
    ∀ g ∈ GG k r, ⟪w, X.2.R.σ g v⟫_ℂ * X.1.ρ g c d = ∑ i, ⟪y' i, (T (s i)).R.σ g (y i)⟫_ℂ
def CoefOf (X : Obj k r) (T : URep k r) : Prop :=
  ∃ y : T.R.H, y ≠ 0 ∧ ∃ (I : Type) (_ : Fintype I) (v w : I → X.2.R.H) (c d : I → X.1.ι),
    (∀ i, X.2.R.KFin (v i) ∧ X.2.R.KFin (w i)) ∧
    ∀ g ∈ GG k r, ⟪y, T.R.σ g y⟫_ℂ = ∑ i, ⟪w i, X.2.R.σ g (v i)⟫_ℂ * X.1.ρ g (c i) (d i)
def Decay (U : URep k r) (m : ℕ) : Prop :=
  ∃ (C : ℝ) (Ws : List (List (Mx k r))), (∀ W ∈ Ws, LieWd k r W) ∧ ∀ u ∈ U.R.sm, ∀ v ∈ U.R.sm, ∀ g ∈ GG k r,
    B.gN g ^ m * ‖⟪v, U.R.σ g u⟫_ℂ‖ ≤ C * (Ws.map fun W => ‖dsigW (k := k) (r := r) U.R.σ W u‖).sum *
      (Ws.map fun W => ‖dsigW (k := k) (r := r) U.R.σ W v‖).sum
def URep.DS (U : URep k r) : Prop := ∃ ε μ, U.R.IsDS ε μ
def HomCat : Prop := ∀ k r : ℕ, IsLinCat (O := Obj k r) M IsHom
def OKTriv : Prop := ∀ k r : ℕ, (triv k r).OK
def OKVr : Prop := ∀ (k r : ℕ) (b : Bool), (vr k r b).OK
def OKWedge : Prop := ∀ k r l : ℕ, (wedge k r l).OK
def OKTens : Prop := ∀ (k r : ℕ) (F F' : FRep k r), F.OK → F'.OK → (F.tens F').OK
def MatHom : Prop :=
  ∀ (k r : ℕ) (F F' : FRep k r) (U : URep k r) (A : Matrix F'.ι F.ι ℂ),
    (∀ g ∈ GG k r, A * F.ρ g = F'.ρ g * A) → IsHom (F, U) (F', U) (mAct A)
def TensHom : Prop :=
  ∀ (k r : ℕ) (F F' E : FRep k r) (U U' : URep k r) (f : M (F, U) →ₗ[ℂ] M (F', U')), IsHom (F, U) (F', U') f →
    IsHom (F.tens E, U) (F'.tens E, U') (on1 f) ∧ IsHom (E.tens F, U) (E.tens F', U') (on2 f)
def UIso : Prop :=
  ∀ (k r : ℕ) (F : FRep k r) (U U' : URep k r),
    (∃ e : U.R.H ≃ₗᵢ[ℂ] U'.R.H, ∀ g ∈ GG k r, ∀ x, e (U.R.σ g x) = U'.R.σ g (e x)) →
    IsIso (N := M) IsHom (F, U) (F, U')
def HomLie : Prop :=
  ∀ (k r : ℕ) (X Y : Obj k r) (f : M X →ₗ[ℂ] M Y), X.1.OK → Y.1.OK → IsHom X Y f →
    ∀ Z : Mx k r, f ∘ₗ L X Z = L Y Z ∘ₗ f
def CasSplit : Prop :=
  ∀ (k r : ℕ) (F F' : FRep k r) (U : URep k r), F.OK → F'.OK →
    cas (F.tens F', U) = cas1 F F' U + cas2 F F' U - casR (F.tens F', U) + (2 : ℂ) • mAct (qMat F F')
def CasDS : Prop :=
  PI.DSInfCharCap.DSInfCharCap → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (μ : Fin (2 * r + k + 1) → ℝ)
    (U : URep k r), 1 ≤ k → U.R.IsDS ε μ → ∀ F : FRep k r,
      casR (F, U) = (casG μ : ℂ) • LinearMap.id ∧ cas (one U) = (casG μ : ℂ) • LinearMap.id
def StdD : Prop :=
  ∀ (k r : ℕ) (Y : Mx k r), (vr k r false).dC Y = Y ∧ (vr k r true).dC Y = -Yᵀ
def WedgeInt : Prop :=
  ∀ (n m : ℕ), (∀ g : Matrix (Fin n) (Fin n) ℂ, jW n m * cmp (m + 1) g = (cmp m g ⊗ₖ g) * jW n m ∧
      (jW n m)ᵀ * (cmp m g ⊗ₖ g) = cmp (m + 1) g * (jW n m)ᵀ) ∧
    (jW n m)ᵀ * jW n m = ((m : ℂ) + 1) • (1 : Matrix (Sub n (m + 1)) (Sub n (m + 1)) ℂ)
def WedgeQ : Prop :=
  ∀ k r m : ℕ, qMat (wedge k r m) (vr k r false) = 1 - jW (2 * r + k + 1) m * (jW (2 * r + k + 1) m)ᵀ
def Schur : Prop :=
  PI.DSInfCharCap.DSInfCharCap → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (S : Type)
    (μ : S → Fin (2 * r + k + 1) → ℝ) (T : S → URep k r), Function.Injective μ → (∀ s, (T s).R.IsDS ε (μ s)) →
    IsSimpleFam (N := M) IsHom fun s => one (T s)
def KerZero : Prop :=
  ∀ (k r : ℕ) (T : URep k r) (X : Obj k r) (i : M (one T) →ₗ[ℂ] M X), T.DS → IsHom (one T) X i →
    ∀ y, y ≠ 0 → i y = 0 → i = 0
def Adj : Prop :=
  ∀ (k r : ℕ) (b : Bool) (U U' : URep k r),
    ∃ e : (M (vr k r b, U) →ₗ[ℂ] M (one U')) ≃ₗ[ℂ] (M (one U) →ₗ[ℂ] M (vr k r (!b), U')),
      ∀ p, IsHom (vr k r b, U) (one U') p ↔ IsHom (one U) (vr k r (!b), U') (e p)
def MultOne : Prop :=
  ∀ (k r : ℕ) (b : Bool) (B T : URep k r) (S : Type) (Bt : S → URep k r) (cB cT : ℂ) (ct : S → ℂ),
    (∀ F : FRep k r, casR (F, B) = cB • LinearMap.id) → cas (one B) = cB • LinearMap.id →
    cas (one T) = cT • LinearMap.id → (∀ t, cas (one (Bt t)) = ct t • LinearMap.id) → (∀ t, ct t ≠ 2 * cB - cT) →
    JInj (N := M) IsHom (vr k r (!b), B) (fun t => one (Bt t)) →
    (∀ f, IsHom (one B) (one B) f → ∃ c : ℂ, f = c • LinearMap.id) → T.DS →
    (∃ κ, IsHom (one B) (vr k r (!b), T) κ ∧ κ ≠ 0) → AtMostOne (N := M) IsHom (one T) (vr k r b, B)
def Lift : Prop :=
  ∀ (k r : ℕ) (X : Obj k r) (T : URep k r) (f : M X →ₗ[ℂ] T.R.H), X.1.OK →
    (∃ (C : ℝ) (Ws : List (List (Mx k r))), (∀ W ∈ Ws, LieWd k r W) ∧ ∀ x, ‖f x‖ ≤ C * (Ws.map fun W => sn X W x).sum) →
    (∀ g ∈ GG k r, ∀ x, f (act X g x) = T.R.σ g (f x)) →
    ∃ p, IsHom X (one T) p ∧ ∀ x, (p x () : T.R.H) = f x
def InjStep : Prop :=
  ∀ (k r : ℕ) (X : Obj k r) (S : Type) (T : S → URep k r) (m : ℕ), X.1.OK → X.2.DS → (∀ s, (T s).DS) →
    Decay X.2 m → X.1.deg + (2 * r + k + 1) ^ 2 + 1 ≤ m → CoefIn X T → JInj (N := M) IsHom X fun s => one (T s)
def OccStep : Prop :=
  ∀ (k r : ℕ) (X : Obj k r) (T : URep k r) (m : ℕ), X.1.OK → X.2.DS → T.DS →
    Decay X.2 m → X.1.deg + (2 * r + k + 1) ^ 2 + 1 ≤ m → CoefOf X T → ∃ p, IsHom X (one T) p ∧ p ≠ 0
def ZG (t : ∀ n : ℕ, (Fin n → Bool) → ℝ) : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (μ : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)),
    IsHCParam μ → PI.UpqRep.IsDS ε μ σ → ∀ h : ℝ, PI.ZuckTensor.GapAtLeast ε μ h → t n ε + 1 < h →
      (∃ X : PI.ZuckTensor.TensorDS n ε μ H σ, ∀ s, s ∈ X.Sm ↔ IsHCParam (μ + Pi.single s 1)) ∧
      ∃ X : PI.ZuckTensor.TensorDSd n ε μ H σ, ∀ s, s ∈ X.Sm ↔ IsHCParam (μ - Pi.single s 1)
def ZuckH : Prop :=
  ∀ t, ZG t → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (μ : Fin (2 * r + k + 1) → ℝ) (U : URep k r) (b : Bool)
    (h : ℝ), U.R.IsDS ε μ → PI.ZuckTensor.GapAtLeast ε μ h → t _ ε + 1 < h →
    ∃ T : {s // IsHCParam (shift b μ s)} → URep k r, (∀ s, (T s).R.IsDS ε (shift b μ s)) ∧
      CoefIn (vr k r b, U) T ∧ ∀ s, CoefOf (vr k r b, U) (T s)
def DecTens : Prop :=
  ∀ (k r : ℕ) (F F' : FRep k r) (U : URep k r), F.OK → F'.OK →
    (∀ (A B : Type) [Fintype A] [Fintype B] (T : A → URep k r) (S : A × B → URep k r) (c : A → ℂ),
      (∃ io pr, IsDec (N := M) IsHom (F, U) (fun a => one (T a)) io pr) →
      (∀ a, ∃ io pr, IsDec (N := M) IsHom (F', T a) (fun b => one (S (a, b))) io pr) →
      (∀ a, cas (one (T a)) = c a • LinearMap.id) →
      ∃ io pr, IsDec (N := M) IsHom (F.tens F', U) (fun p => one (S p)) io pr ∧
        ∀ p, cas1 F F' U ∘ₗ io p = c p.1 • io p) ∧
    ∀ (A B : Type) [Fintype A] [Fintype B] (T : B → URep k r) (S : A × B → URep k r) (c : B → ℂ),
      (∃ io pr, IsDec (N := M) IsHom (F', U) (fun b => one (T b)) io pr) →
      (∀ b, ∃ io pr, IsDec (N := M) IsHom (F, T b) (fun a => one (S (a, b))) io pr) →
      (∀ b, cas (one (T b)) = c b • LinearMap.id) →
      ∃ io pr, IsDec (N := M) IsHom (F.tens F', U) (fun p => one (S p)) io pr ∧
        ∀ p, cas2 F F' U ∘ₗ io p = c p.2 • io p
def ToRaw : Prop :=
  ∀ (k r : ℕ) (F : FRep k r) (U : URep k r) (κ : Type) [Fintype κ] [DecidableEq κ] (T : κ → URep k r),
    (∃ io pr, IsDec (N := M) IsHom (F, U) (fun a => one (T a)) io pr) →
    ∃ io pr, TensRaw F.ρ U.R (fun a => (T a).R) io pr
def Count : Prop :=
  ∀ (n m : ℕ) (μ : Fin n → ℝ), (∀ a c, a < c → 2 ≤ μ a - μ c) →
    let par : Sub n m × Fin n → Fin n → ℝ := fun p => addSet μ p.1.1 + Pi.single p.2 1
    let w : Sub n m × Fin n → (Fin n → ℝ) → ℂ := fun p ν =>
      (casG (addSet μ p.1.1) : ℂ) + (casG (μ + Pi.single p.2 1) : ℂ) + (2 - (casG μ : ℂ)) - (casG ν : ℂ)
    (∀ I : Sub n (m + 1), ∑ p ∈ univ.filter (fun p => par p = addSet μ I.1), w p (addSet μ I.1) = 2 * ((m : ℂ) + 1)) ∧
    ∀ ν, (∀ I : Sub n (m + 1), addSet μ I.1 ≠ ν) → ∑ p ∈ univ.filter (fun p => par p = ν), w p ν = 0
end CompanionTheory.Zuck
end


