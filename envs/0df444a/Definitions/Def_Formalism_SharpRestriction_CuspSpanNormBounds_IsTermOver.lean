-- Prove2me | Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_IsTermOver
-- name    : Formalism_SharpRestriction_CuspSpanNormBounds_IsTermOver
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:16:41.47749+00:00
-- url     : https://prove2.me/theorems/d85a3a8e-0ad5-4156-a27f-bb9b22b2e291
-- title:
--   Is Term Over
-- statement:
--   Definitions and structural lemmas for Is Term Over, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/IsTermOver.lean

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_LinQRawRange
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ValuativeRel ComplexConjugate
namespace Formalism.MainNotions.S.LocNG
open Formalism.MainNotions.S.Loc
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V]
def img (g : V ≃ₗ[E] V) (Λ : Submodule M.L.O V) : Submodule M.L.O V :=
  Λ.map ((g : V →ₗ[E] V).restrictScalars M.L.O)
def IsUnitary (H : HermSp M V) (g : V ≃ₗ[E] V) : Prop := ∀ x y, H.h (g x) (g y) = H.h x y
def volRel {G : Type*} [Group G] (K K0 : Subgroup G) : ℝ :=
  (K0.relIndex K : ℝ) / (K.relIndex K0 : ℝ)
def IsTransv {α : Type*} (rel : α → α → Prop) (S R : Set α) : Prop :=
  R ⊆ S ∧ (∀ x ∈ S, ∃ y ∈ R, rel y x) ∧ ∀ y ∈ R, ∀ y' ∈ R, rel y y' → y = y'
def theta (M : Model F E) : F :=
  match M.split with
  | none => 1
  | some g => (g.q : F)
def qF (F : Type) [Field F] [ValuativeRel F] : ℕ := Nat.card 𝓀[F]
def IsUnitO (M : Model F E) (x : E) : Prop := x ∈ M.L.O ∧ ∃ y ∈ M.L.O, x * y = 1
structure FrameD (H : HermSp M V) (r : ℕ) where
  f : Fin (r + 1) → V
  es : Fin r → V
  T : F
  h_iso : ∀ a b : Fin (r + 1), (a ≠ Fin.last r ∨ b ≠ Fin.last r) → H.h (f a) (f b) = 0
  h_zz : H.h (f (Fin.last r)) (f (Fin.last r)) = -(algebraMap F E T)
  h_ss : ∀ i j, H.h (es i) (es j) = 0
  h_es : ∀ i j : Fin r, H.h (f i.castSucc) (es j) = if i = j then 1 else 0
  h_sz : ∀ i, H.h (es i) (f (Fin.last r)) = 0
namespace FrameD
variable {H : HermSp M V} {r : ℕ} (Fr : FrameD H r)
def e (a : Fin r) : V := Fr.f a.castSucc
def z : V := Fr.f (Fin.last r)
def Fj (j : ℕ) : Submodule E V := Submodule.span E (Fr.e '' {a | a.val < j})
def prF (v : V) : V := v - ∑ a, H.h v (Fr.es a) • Fr.e a - ∑ a, H.h v (Fr.e a) • Fr.es a
def NSet : Set (V ≃ₗ[E] V) :=
  {g | IsUnitary H g ∧ (∀ j, j ≤ r → ∀ v ∈ Fr.Fj j, g v - v ∈ Fr.Fj (j - 1)) ∧
    ∀ v ∈ H.perp (H.X Fr.f), g v - v ∈ H.X Fr.f}
def N : Subgroup (V ≃ₗ[E] V) := Subgroup.closure Fr.NSet
def coefSum (x : Fin (r + 1) → V) : E := ∑ a : Fin r, H.h (x a.succ) (Fr.es a)
def psiOf (θ : F) (x : Fin (r + 1) → V) : ℂ := M.L.psi0 (algebraMap F E θ⁻¹ * Fr.coefSum x)
def psiN (θ : F) (g : V ≃ₗ[E] V) : ℂ := Fr.psiOf θ (fun b => g (Fr.f b))
def IsInner (L : Submodule M.L.O (H.Wb Fr.f)) : Prop :=
  L.FG ∧
  (∀ x : ↥(H.perp (H.X Fr.f)),
    H.mkW Fr.f x ∈ L ↔ ∀ y : ↥(H.perp (H.X Fr.f)), H.mkW Fr.f y ∈ L → H.h x y ∈ M.L.O) ∧
  ∃ xz : ↥(H.perp (H.X Fr.f)), (xz : V) = Fr.z ∧ H.mkW Fr.f xz ∈ L ∧
    ∀ (c : M.L.O) (y : ↥(H.perp (H.X Fr.f))), H.mkW Fr.f y ∈ L →
      H.mkW Fr.f xz = (c : E) • H.mkW Fr.f y → IsUnit c
def LamStd (L : Submodule M.L.O (H.Wb Fr.f)) : Submodule M.L.O V :=
  Submodule.span M.L.O {v | (∀ a, H.h v (Fr.es a) ∈ M.L.O) ∧ (∀ a, H.h v (Fr.e a) ∈ M.L.O) ∧
    ∃ w : ↥(H.perp (H.X Fr.f)), (w : V) = Fr.prF v ∧ H.mkW Fr.f w ∈ L}
end FrameD
structure FPair (H : HermSp M V) (r : ℕ) where
  A : FrameD H r
  B : FrameD H r
namespace FPair
variable {H : HermSp M V} {r : ℕ} (P : FPair H r)
def Dm (l : ℕ) : E := H.Dl P.A.f P.B.f l
def Gv : E := H.Gdet P.A.f P.B.f P.A.T P.B.T
def St : Subgroup (V ≃ₗ[E] V) := P.A.N ⊓ P.B.N
def IsPoint : Prop :=
  ∃ w : Loc.Pt E (r + 1), ∀ a b : Fin (r + 1), (-1) ^ (r - b.val) * H.Zhat P.A.f P.B.f a b = w.mat a b
def NormsOK : Prop :=
  P.A.T ∈ 𝒪[F] ∧ P.A.T ≠ 0 ∧ P.B.T ∈ 𝒪[F] ∧ P.B.T ≠ 0 ∧
    ∀ g, M.split = some g →
      (∃ u v : 𝒪[F], (u : F) * P.A.T = 1 ∧ (v : F) * P.B.T = 1) ∧
      ∃ c : 𝒪[F], P.A.T - P.B.T = (g.q : F) ^ 2 * c
def RelG (θ : F) : Prop :=
  H.Xp P.A.f ⊓ H.Xp P.B.f = ⊥ ∧ IsUnit (P.Dm (r + 1)) ∧ P.Gv ≠ 0 ∧
    (∀ l, l ≤ r + 1 → P.Dm l = 0 ∨ IsUnit (P.Dm l)) ∧
    (∀ g ∈ P.St, P.A.psiN θ g = P.B.psiN θ g) ∧ P.IsPoint ∧ P.NormsOK
def UW0 : Subgroup (V ≃ₗ[E] V) :=
  Subgroup.closure {g | IsUnitary H g ∧ ∀ b, g (P.A.f b) = P.A.f b ∧ g (P.B.f b) = P.B.f b}
def K0 : Subgroup (V ≃ₗ[E] V) :=
  Subgroup.closure {s | s ∈ P.St ∧ ∀ (a : Fin r) (b : Fin (r + 1)),
    H.h (s (P.A.f b)) (P.A.es a) ∈ M.L.O ∧ H.h (s (P.B.f b)) (P.B.es a) ∈ M.L.O}
def ends : Finset ℕ :=
  haveI := Classical.decPred (fun l : ℕ => 1 ≤ l ∧ IsUnit (P.Dm l))
  (Finset.range (r + 2)).filter (fun l => 1 ≤ l ∧ IsUnit (P.Dm l))
def MMgen : Fin (r + 1) ⊕ Fin (r + 1) → V :=
  H.MMfam ⟨0, P.A.f, P.B.f, P.A.T, P.B.T⟩
def Hp : ℝ :=
  (M.modK (algebraMap F E (theta M)) * M.modK (H.gram P.MMgen).det *
    ∏ l ∈ P.ends, M.modK (P.Dm l * M.L.cj (P.Dm l))) ^ (-(1 / 2 : ℝ))
def PrimeTo : Prop :=
  M.split = none ∧ IsUnitO M P.Gv ∧ ∀ l ∈ P.ends, IsUnitO M (P.Dm l)
end FPair
variable {H : HermSp M V} {r : ℕ}
structure Datum (P : FPair H r) where
  L : Submodule M.L.O (H.Wb P.A.f)
  L' : Submodule M.L.O (H.Wb P.B.f)
  hL : P.A.IsInner L
  hL' : P.B.IsInner L'
  io : Set (H.Wb P.B.f × H.Wb P.A.f)
  io_L : M.split = none → io = ∅
namespace Datum
variable {P : FPair H r}
def Moves (g : V ≃ₗ[E] V) (d d' : Datum P) : Prop :=
  (∀ x y : ↥(H.perp (H.X P.A.f)), (y : V) = g x → (H.mkW P.A.f x ∈ d.L ↔ H.mkW P.A.f y ∈ d'.L)) ∧
  (∀ x y : ↥(H.perp (H.X P.B.f)), (y : V) = g x → (H.mkW P.B.f x ∈ d.L' ↔ H.mkW P.B.f y ∈ d'.L')) ∧
  ∀ (x' y' : ↥(H.perp (H.X P.B.f))) (x y : ↥(H.perp (H.X P.A.f))), (y' : V) = g x' → (y : V) = g x →
    ((H.mkW P.B.f x', H.mkW P.A.f x) ∈ d.io ↔ (H.mkW P.B.f y', H.mkW P.A.f y) ∈ d'.io)
def Rel (d d' : Datum P) : Prop := ∃ g ∈ P.UW0, Moves g d d'
def Stab (d : Datum P) : Subgroup (V ≃ₗ[E] V) := Subgroup.closure {g | g ∈ P.UW0 ∧ Moves g d d}
def wt (d0 d : Datum P) : ℝ := 1 / volRel (Stab d) (Stab d0)
end Datum
def IsTermOver (P : FPair H r) (d : Datum P) (t : Term V M r) : Prop :=
  t.T = P.A.T ∧ t.T' = P.B.T ∧
  (∃ n ∈ P.A.N, t.f = (fun b => n (P.A.f b)) ∧ t.abelian₂ = img n (P.A.LamStd d.L)) ∧
  (∃ n' ∈ P.B.N, t.f' = (fun b => n' (P.B.f b)) ∧ t.abelian₂ = img n' (P.B.LamStd d.L')) ∧
  ∀ g, M.split = some g → H.Admissible g t ∧
    H.iotaGraph g ⟨t.abelian₂, P.A.f, P.B.f, t.T, t.T'⟩ = d.io
def TRel (P : FPair H r) (t t' : Term V M r) : Prop :=
  ∃ s ∈ P.St, t'.abelian₂ = img s t.abelian₂
def om (P : FPair H r) (t : Term V M r) : ℂ :=
  P.A.psiOf (theta M) t.f * (P.B.psiOf (theta M) t.f')⁻¹
def Aut (Λ : Submodule M.L.O V) : Subgroup (V ≃ₗ[E] V) := Subgroup.closure {g | img g Λ = Λ}
def mu (P : FPair H r) (t : Term V M r) : ℝ := 1 / volRel (P.St ⊓ Aut t.abelian₂) P.K0
def BBne (t : Term V M r) : Prop :=
  ∃ v ∈ t.abelian₂, v ∈ Submodule.span E (Set.range (H.MMfam t)) ∧
    v ∉ Submodule.span M.L.O (Set.range (H.MMfam t))
structure Reps (P : FPair H r) where
  RD : Set (Datum P)
  RT : Datum P → Set (Term V M r)
  hRD : IsTransv Datum.Rel Set.univ RD
  hRT : ∀ d, IsTransv (TRel P) {t | IsTermOver P d t} (RT d)
variable {P : FPair H r}
def amp (R : Reps P) (d : Datum P) (S : Term V M r → Prop) : ℂ :=
  ∑' t : {t // t ∈ R.RT d ∧ S t}, (mu P t.1 : ℂ) * om P t.1
def sumSq (R : Reps P) (d0 : Datum P) (S : Term V M r → Prop) : ENNReal :=
  ∑' d : R.RD, ENNReal.ofReal (Datum.wt d0 d.1) * ((‖amp R d.1 S‖₊ : ENNReal) ^ 2)
def nn (R : Reps P) (d0 : Datum P) : ENNReal :=
  ∑' d : R.RD, ENNReal.ofReal (Datum.wt d0 d.1) * ∑' t : R.RT d.1, ENNReal.ofReal (mu P t.1)
def NGAt (k : ℕ) (P : FPair H r) (C : ℝ) : Prop :=
  ∀ (R : Reps P) (d0 : Datum P),
    sumSq R d0 (BBne (H := H)) ≤ ENNReal.ofReal (P.Hp ^ (C * ((r : ℝ) + 1) ^ 2) *
        (qF F : ℝ) ^ (-((k : ℝ) - 2 * r - 5))) * nn R d0 ∧
    sumSq R d0 (fun t => ¬ BBne (H := H) t) ≤ ENNReal.ofReal (P.Hp ^ (C * ((r : ℝ) + 1) ^ 2)) * nn R d0 ∧
    sumSq R d0 (fun _ => True) ≤ ENNReal.ofReal (P.Hp ^ (C * ((r : ℝ) + 1) ^ 2)) * nn R d0 ∧
    (P.PrimeTo → P.Hp = 1 ∧ sumSq R d0 (fun t => ¬ BBne (H := H) t) = nn R d0 ∧
      sumSq R d0 (fun _ => True) = nn R d0)
end Formalism.MainNotions.S.LocNG
end


