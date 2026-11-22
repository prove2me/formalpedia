-- Prove2me | Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_LinQRawRange
-- name    : Formalism_SharpRestriction_CuspSpanNormBounds_LinQRawRange
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:01:00.735793+00:00
-- url     : https://prove2.me/theorems/e4bc1b33-d1b1-41fc-b92b-09824afeb6ca
-- title:
--   Lin QRaw Range
-- statement:
--   Definitions and structural lemmas for Lin QRaw Range, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/LinQRawRange.lean

import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks


set_option autoImplicit false
noncomputable section
open ValuativeRel
namespace Formalism.MainNotions.S.Loc
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
structure HermSp (M : Model F E) (V : Type) [AddCommGroup V] [Module E V] where
  h : V → V → E
  h_add_left : ∀ x x' y, h (x + x') y = h x y + h x' y
  h_smul_left : ∀ (a : E) x y, h (a • x) y = a * h x y
  h_herm : ∀ x y, h y x = M.L.cj (h x y)
  nondeg : ∀ x, (∀ y, h x y = 0) → x = 0
  free : Module.Free E V
  fin : Module.Finite E V
namespace HermSp
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V)
lemma h_zero_left (y : V) : H.h 0 y = 0 := by
  have h := H.h_add_left 0 0 y
  rw [add_zero] at h
  linear_combination -h
def perp (S : Submodule E V) : Submodule E V where
  carrier := {v | ∀ x ∈ S, H.h v x = 0}
  add_mem' {a b} ha hb x hx := by
    simp only [Set.mem_ofPred_eq] at ha hb
    rw [H.h_add_left, ha x hx, hb x hx, add_zero]
  zero_mem' x _ := H.h_zero_left x
  smul_mem' c v hv x hx := by
    simp only [Set.mem_ofPred_eq] at hv
    rw [H.h_smul_left, hv x hx, mul_zero]
def smulLat (_H : HermSp M V) (c : E) (abelian₂ : Submodule M.L.O V) : Submodule M.L.O V :=
  Submodule.span M.L.O ((fun v => c • v) '' (abelian₂ : Set V))
def IsSelfDual (abelian₂ : Submodule M.L.O V) : Prop :=
  abelian₂.FG ∧ Submodule.span E (abelian₂ : Set V) = ⊤ ∧ ∀ x : V, x ∈ abelian₂ ↔ ∀ y ∈ abelian₂, H.h x y ∈ M.L.O
def Prim (_H : HermSp M V) (abelian₂ : Submodule M.L.O V) {ι : Type} (v : ι → V) : Prop :=
  (∀ a, v a ∈ abelian₂) ∧ LinearIndependent E v ∧
    ∀ x ∈ abelian₂, x ∈ Submodule.span E (Set.range v) → x ∈ Submodule.span M.L.O (Set.range v)
def IsFrame (abelian₂ : Submodule M.L.O V) (r : ℕ) (f : Fin (r + 1) → V) (T : F) : Prop :=
  H.Prim abelian₂ f ∧ (∀ a b : Fin (r + 1), (a ≠ Fin.last r ∨ b ≠ Fin.last r) → H.h (f a) (f b) = 0) ∧
    H.h (f (Fin.last r)) (f (Fin.last r)) = - algebraMap F E T ∧ T ∈ 𝒪[F] ∧ T ≠ 0
def Zhat {r : ℕ} (f f' : Fin (r + 1) → V) : Matrix (Fin (r + 1)) (Fin (r + 1)) E :=
  Matrix.of fun a b => H.h (f' b) (f a)
def Dl {r : ℕ} (f f' : Fin (r + 1) → V) (l : ℕ) : E :=
  if hl : l ≤ r + 1 then ((H.Zhat f f').submatrix (Fin.castLE hl) (Fin.castLE hl)).det else 0
def normE (_H : HermSp M V) (x : E) : E := x * M.L.cj x
def Gdet {r : ℕ} (f f' : Fin (r + 1) → V) (T T' : F) : E :=
  H.normE (H.Dl f f' (r + 1)) - algebraMap F E (T * T') * H.normE (H.Dl f f' r)
def X (_H : HermSp M V) {r : ℕ} (f : Fin (r + 1) → V) : Submodule E V :=
  Submodule.span E (Set.range fun a : Fin r => f a.castSucc)
def Xp (_H : HermSp M V) {r : ℕ} (f : Fin (r + 1) → V) : Submodule E V := Submodule.span E (Set.range f)
def W0 {r : ℕ} (f f' : Fin (r + 1) → V) : Submodule E V := H.perp (H.Xp f ⊔ H.Xp f')
abbrev Wb {r : ℕ} (f : Fin (r + 1) → V) : Type :=
  ↥(H.perp (H.X f)) ⧸ (H.X f).comap (H.perp (H.X f)).subtype
def mkW {r : ℕ} (f : Fin (r + 1) → V) : ↥(H.perp (H.X f)) →ₗ[E] H.Wb f := Submodule.mkQ _
def Lset (abelian₂ : Submodule M.L.O V) {r : ℕ} (f : Fin (r + 1) → V) : Set (H.Wb f) :=
  {w | ∃ x : ↥(H.perp (H.X f)), (x : V) ∈ abelian₂ ∧ H.mkW f x = w}
def om' {r : ℕ} (f f' : Fin (r + 1) → V) : V :=
  ∑ b, (H.Zhat f f').adjugate b (Fin.last r) • f' b
def om {r : ℕ} (f f' : Fin (r + 1) → V) : V :=
  ∑ a, M.L.cj ((H.Zhat f f').adjugate (Fin.last r) a) • f a
def NGrp (abelian₂ : Submodule M.L.O V) {r : ℕ} (f : Fin (r + 1) → V) : Set (V ≃ₗ[E] V) :=
  {n | (∀ x y, H.h (n x) (n y) = H.h x y) ∧ (n : V → V) '' (abelian₂ : Set V) = abelian₂ ∧
    (∀ a : Fin r, n (f a.castSucc) - f a.castSucc ∈
      Submodule.span E ((fun b : Fin r => f b.castSucc) '' {b | b < a})) ∧
    ∀ v ∈ H.perp (H.X f), n v - v ∈ H.X f}
end HermSp
structure Term (V : Type) [AddCommGroup V] [Module E V] (M : Model F E) (r : ℕ) where
  abelian₂ : Submodule M.L.O V
  f : Fin (r + 1) → V
  f' : Fin (r + 1) → V
  T : F
  T' : F
namespace HermSp
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V)
def Admissible (g : SplitG M.L) {r : ℕ} (t : Term V M r) : Prop :=
  ∀ b, t.f' b - t.f b ∈ H.smulLat (algebraMap F E (g.q : F)) t.abelian₂
def MMfam (_H : HermSp M V) {r : ℕ} (t : Term V M r) : Fin (r + 1) ⊕ Fin (r + 1) → V :=
  match M.split with
  | none => Sum.elim t.f t.f'
  | some g => Sum.elim t.f (fun a => algebraMap F E ((g.q : F)⁻¹) • (t.f' a - t.f a))
def IsTerm {r : ℕ} (t : Term V M r) : Prop :=
  H.IsSelfDual t.abelian₂ ∧ H.IsFrame t.abelian₂ r t.f t.T ∧ H.IsFrame t.abelian₂ r t.f' t.T' ∧
    IsUnit (H.Dl t.f t.f' (r + 1)) ∧ H.Gdet t.f t.f' t.T t.T' ≠ 0 ∧
    ∀ g, M.split = some g →
      (∃ u v : 𝒪[F], (u : F) * t.T = 1 ∧ (v : F) * t.T' = 1) ∧
      (∃ c : 𝒪[F], t.T - t.T' = (g.q : F) ^ 2 * c) ∧ H.Admissible g t
def IsGeneric {r : ℕ} (t : Term V M r) : Prop := H.IsTerm t ∧ H.Prim t.abelian₂ (H.MMfam t)
def ZZplusOf (M : Model F E) {r : ℕ} (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : F) :
    Matrix (Fin (r + 1)) (Fin (r + 1)) E :=
  match M.split with
  | none => Zh
  | some g => Matrix.of fun a b =>
      g.e.symm ((g.e (Zh a b)).1 / (g.q : F), -((g.e (Zh b a)).2 / (g.q : F))) -
      (if a = Fin.last r ∧ b = Fin.last r then g.e.symm (-T / (g.q : F), T' / (g.q : F)) else 0)
def ZZplus {r : ℕ} (t : Term V M r) : Matrix (Fin (r + 1)) (Fin (r + 1)) E :=
  ZZplusOf M (H.Zhat t.f t.f') t.T t.T'
def iotaGraph (g : SplitG M.L) {r : ℕ} (t : Term V M r) : Set (H.Wb t.f' × H.Wb t.f) :=
  {p | ∃ (x' : ↥(H.perp (H.X t.f'))) (x : ↥(H.perp (H.X t.f))), (x' : V) ∈ t.abelian₂ ∧ (x : V) ∈ t.abelian₂ ∧
    (x : V) - x' ∈ H.smulLat (algebraMap F E (g.q : F)) t.abelian₂ ∧ p = (H.mkW t.f' x', H.mkW t.f x)}
def IsIsomW {r : ℕ} {f₁ f₂ : Fin (r + 1) → V} (φ : H.Wb f₁ ≃ₗ[E] H.Wb f₂) : Prop :=
  ∀ (x y : ↥(H.perp (H.X f₁))) (x₂ y₂ : ↥(H.perp (H.X f₂))),
    φ (H.mkW f₁ x) = H.mkW f₂ x₂ → φ (H.mkW f₁ y) = H.mkW f₂ y₂ → H.h x₂ y₂ = H.h x y
def SendsTo {r : ℕ} {f₁ f₂ : Fin (r + 1) → V} (φ : H.Wb f₁ →ₗ[E] H.Wb f₂) (c₁ c₂ : E)
    (v₁ v₂ : V) : Prop :=
  ∀ (x : ↥(H.perp (H.X f₁))) (x₂ : ↥(H.perp (H.X f₂))), (x : V) = v₁ → (x₂ : V) = v₂ →
    c₁ • φ (H.mkW f₁ x) = c₂ • H.mkW f₂ x₂
def Ident {r : ℕ} (t₁ t₂ : Term V M r) (φ : H.Wb t₁.f ≃ₗ[E] H.Wb t₂.f)
    (φ' : H.Wb t₁.f' ≃ₗ[E] H.Wb t₂.f') : Prop :=
  H.IsIsomW φ ∧ H.IsIsomW φ' ∧
  (∀ w ∈ H.W0 t₁.f t₁.f', ∃ w₂ ∈ H.W0 t₂.f t₂.f',
    H.SendsTo φ.toLinearMap 1 1 w w₂ ∧ H.SendsTo φ'.toLinearMap 1 1 w w₂) ∧
  H.SendsTo φ.toLinearMap (H.Dl t₂.f t₂.f' (r + 1)) (H.Dl t₁.f t₁.f' (r + 1))
    (H.om' t₁.f t₁.f') (H.om' t₂.f t₂.f') ∧
  H.SendsTo φ'.toLinearMap (M.L.cj (H.Dl t₂.f t₂.f' (r + 1))) (M.L.cj (H.Dl t₁.f t₁.f' (r + 1)))
    (H.om t₁.f t₁.f') (H.om t₂.f t₂.f') ∧
  H.Dl t₁.f t₁.f' r * H.Dl t₂.f t₂.f' (r + 1) = H.Dl t₂.f t₂.f' r * H.Dl t₁.f t₁.f' (r + 1)
def Respects {r : ℕ} (t₁ t₂ : Term V M r) (φ : H.Wb t₁.f ≃ₗ[E] H.Wb t₂.f)
    (φ' : H.Wb t₁.f' ≃ₗ[E] H.Wb t₂.f') : Prop :=
  φ '' H.Lset t₁.abelian₂ t₁.f = H.Lset t₂.abelian₂ t₂.f ∧
  H.SendsTo φ.toLinearMap 1 1 (t₁.f (Fin.last r)) (t₂.f (Fin.last r)) ∧
  φ' '' H.Lset t₁.abelian₂ t₁.f' = H.Lset t₂.abelian₂ t₂.f' ∧
  H.SendsTo φ'.toLinearMap 1 1 (t₁.f' (Fin.last r)) (t₂.f' (Fin.last r)) ∧
  ∀ g, M.split = some g → Prod.map φ' φ '' H.iotaGraph g t₁ = H.iotaGraph g t₂
def IsScalarPair {r : ℕ} (t₁ t₂ : Term V M r) : Prop :=
  ∃ φ φ', H.Ident t₁ t₂ φ φ' ∧ H.Respects t₁ t₂ φ φ'
def dens (ϖ : 𝒪[F]) (abelian₂ : Submodule M.L.O V) {ι : Type} [Fintype ι] (G₀ : Matrix ι ι E) : ℝ :=
  (Nat.card (Set.range fun v : {v : ι → V // H.Prim abelian₂ v ∧ ∀ a b,
      H.h (v b) (v a) - G₀ a b ∈ Submodule.span M.L.O {algebraMap F E (ϖ : F)}} =>
      fun a => Submodule.Quotient.mk (p := H.smulLat (algebraMap F E (ϖ : F)) abelian₂) (v.1 a)) : ℝ) /
    (Nat.card 𝓀[F] : ℝ) ^ ((2 * Module.finrank E V * Fintype.card ι : ℤ) - (Fintype.card ι : ℤ) ^ 2)
def gram {ι : Type} (v : ι → V) : Matrix ι ι E := Matrix.of fun a b => H.h (v b) (v a)
end HermSp
namespace Model
variable (M : Model F E)
def linQRaw {m : ℕ} (ZZ : M.Mat m) (row : Fin m → M.R) : (Fin m → M.R) →ₗ[M.R] E ⧸ M.Rsub :=
  M.Rsub.mkQ ∘ₗ
    ((Matrix.of fun (_ : Fin 1) (j : Fin m) => ((row j : M.R) : E)).mulVecLin.restrictScalars M.R |>.comp
      ((ZZ.Z.map M.R.subtype)⁻¹.mulVecLin.restrictScalars M.R) |> (LinearMap.proj (0 : Fin 1)).comp) ∘ₗ
    (LinearMap.compLeft (Algebra.linearMap M.R E) (Fin m))
lemma linQRaw_range {m : ℕ} (ZZ : M.Mat m) (row : Fin m → M.R) :
    LinearMap.range ZZ.Z.mulVecLin ≤ LinearMap.ker (M.linQRaw ZZ row) := by
  rintro _ ⟨w, rfl⟩
  rw [LinearMap.mem_ker]
  have hinv : (ZZ.Z.map M.R.subtype)⁻¹ * ZZ.Z.map M.R.subtype = 1 :=
    Matrix.nonsing_inv_mul _ ZZ.unit
  have hv : (fun i => ((ZZ.Z.mulVecLin w i : M.R) : E)) =
      (ZZ.Z.map M.R.subtype).mulVec (fun i => (w i : E)) := by
    funext i
    exact RingHom.map_mulVec M.R.subtype ZZ.Z w i
  have key : (ZZ.Z.map M.R.subtype)⁻¹.mulVec (fun i => ((ZZ.Z.mulVecLin w i : M.R) : E)) =
      fun i => (w i : E) := by
    rw [hv, Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
  simp only [linQRaw, LinearMap.coe_comp, Function.comp_apply,
    LinearMap.coe_restrictScalars, Matrix.mulVecLin_apply, LinearMap.proj_apply]
  change Submodule.mkQ M.Rsub _ = 0
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  have key' : (ZZ.Z.map M.R.subtype)⁻¹.mulVec
      ((Algebra.linearMap M.R E).compLeft (Fin m) (ZZ.Z.mulVec w)) = fun i => (w i : E) := key
  rw [key']
  refine ⟨∑ j, row j * w j, ?_⟩
  simp [Matrix.mulVec, dotProduct]
  rfl
def linQ {m : ℕ} (ZZ : M.Mat m) (row : Fin m → M.R) : M.Cok ZZ →ₗ[M.R] E ⧸ M.Rsub :=
  Submodule.liftQ _ (M.linQRaw ZZ row) (M.linQRaw_range ZZ row)
def nIsoBA {m : ℕ} (Z₁ Z₂ : M.Mat m) (be₁ be₂ al₁ al₂ : Fin m → M.R) : ℕ :=
  Nat.card {φ : M.Cok Z₁ ≃ₗ[M.R] M.Cok Z₂ //
    φ (Submodule.Quotient.mk be₁) = Submodule.Quotient.mk be₂ ∧
      ∀ v, M.linQ Z₂ al₂ (φ v) = M.linQ Z₁ al₁ v}
end Model
end Formalism.MainNotions.S.Loc
end


