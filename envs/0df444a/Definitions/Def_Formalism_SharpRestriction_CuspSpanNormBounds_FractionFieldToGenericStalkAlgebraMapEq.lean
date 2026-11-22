-- Prove2me | Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
-- name    : Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T16:48:19.884804+00:00
-- url     : https://prove2.me/theorems/12a67047-98ae-474e-8c78-e59c94314e37
-- title:
--   Fraction Field To Generic Stalk Algebra Map Eq
-- statement:
--   Definitions and structural lemmas for Fraction Field To Generic Stalk Algebra Map Eq, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/FractionFieldToGenericStalkAlgebraMapEq.lean

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_Point
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ValuativeRel MeasureTheory ComplexConjugate
namespace Formalism.MainNotions.S.Loc
structure LocE (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    (E : Type) [CommRing E] [Algebra F E] [TopologicalSpace E] where
  cj : E ≃ₐ[F] E
  cj_cj : ∀ x, cj (cj x) = x
  cj_fix : ∀ x, cj x = x ↔ ∃ a : F, algebraMap F E a = x
  free : Module.Free F E
  rank : Module.finrank F E = 2
  reduced : IsReduced E
  top : IsModuleTopology F E
  O : Subring E
  O_def : ∀ x : E, x ∈ O ↔ IsIntegral 𝒪[F] x
  unram : ∀ ϖ : 𝒪[F], Irreducible ϖ → ∀ x ∈ O,
    x * x ∈ Submodule.span O {algebraMap F E ϖ} → x ∈ Submodule.span O {algebraMap F E ϖ}
  psi0 : AddChar E ℂ
  local_additive_char_continuous : Continuous psi0
  local_additive_char_conj : ∀ y, psi0 (cj y) = psi0 y
  additive_character_dual_ring : ∀ x : E, (∀ y ∈ O, psi0 (x * y) = 1) ↔ x ∈ O
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
structure SplitG (L : LocE F E) where
  e : E ≃ₐ[F] F × F
  e_cj : ∀ x, e (L.cj x) = (e x).swap
  q : 𝒪[F]
  q_irr : Irreducible q
  psiF : AddChar F ℂ
  psiF_cont : Continuous psiF
  psiF_o : ∀ y ∈ 𝒪[F], psiF y = 1
  psiF_cond : ∃ y : 𝒪[F], psiF ((y : F) / (q : F)) ≠ 1
  fractionFieldToGenericStalk_algebraMap_eq : ∀ x, L.psi0 x = psiF ((e x).1 + (e x).2)
structure Model (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    (E : Type) [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] where
  L : LocE F E
  split : Option (SplitG L)
  mu : Measure E
namespace Model
variable [MeasurableSpace E]
def R (M : Model F E) : Subring E :=
  match M.split with
  | none => M.L.O
  | some g =>
    let S : Subring (𝒪[F] × 𝒪[F]) :=
      RingHom.eqLocus ((Ideal.Quotient.mk (Ideal.span {g.q})).comp (RingHom.fst _ _))
        ((Ideal.Quotient.mk (Ideal.span {g.q})).comp (RingHom.snd _ _))
    (S.map ((𝒪[F]).subtype.prodMap (𝒪[F]).subtype)).comap g.e.toRingEquiv.toRingHom
def trR (M : Model F E) (g : SplitG M.L) : E →+ F where
  toFun x := ((g.e x).1 - (g.e x).2) / (g.q : F)
  map_zero' := by simp
  map_add' x y := by simp only [map_add, Prod.fst_add, Prod.snd_add]; ring
def psiR (M : Model F E) : AddChar E ℂ :=
  match M.split with
  | none => M.L.psi0
  | some g => g.psiF.compAddMonoidHom (M.trR g)
structure HaarOK (M : Model F E) : Prop where
  haar : M.mu.IsAddHaarMeasure
  sf : SigmaFinite M.mu
  volR : M.mu (M.R : Set E) = 1
structure OK (M : Model F E) : Prop where
  loc : IsNonarchimedeanLocalField F
  char0 : CharZero F
  borel : BorelSpace E
  haar : M.HaarOK
def Rsub (M : Model F E) : Submodule M.R E := LinearMap.range (Algebra.linearMap M.R E)
def modK (M : Model F E) (x : E) : ℝ := (M.mu ((fun y => x * y) '' (M.R : Set E))).toReal
structure Mat (M : Model F E) (m : ℕ) where
  Z : Matrix (Fin m) (Fin m) M.R
  unit : IsUnit (Z.map M.R.subtype).det
abbrev Cok (M : Model F E) {m : ℕ} (ZZ : M.Mat m) : Type :=
  (Fin m → M.R) ⧸ LinearMap.range ZZ.Z.mulVecLin
def eCls (M : Model F E) {m : ℕ} (ZZ : M.Mat (m + 1)) : M.Cok ZZ :=
  Submodule.Quotient.mk (Pi.single (Fin.last m) 1)
def lamRaw (M : Model F E) {m : ℕ} (ZZ : M.Mat (m + 1)) :
    (Fin (m + 1) → M.R) →ₗ[M.R] E ⧸ M.Rsub :=
  M.Rsub.mkQ ∘ₗ (LinearMap.proj (Fin.last m)) ∘ₗ
    ((ZZ.Z.map M.R.subtype)⁻¹.mulVecLin.restrictScalars M.R) ∘ₗ
    (LinearMap.compLeft (Algebra.linearMap M.R E) (Fin (m + 1)))
lemma lamRaw_range (M : Model F E) {m : ℕ} (ZZ : M.Mat (m + 1)) :
    LinearMap.range ZZ.Z.mulVecLin ≤ LinearMap.ker (M.lamRaw ZZ) := by
  rintro _ ⟨w, rfl⟩
  rw [LinearMap.mem_ker]
  have hmap : (fun i => Algebra.linearMap M.R E (ZZ.Z.mulVecLin w i)) =
      Matrix.mulVec (ZZ.Z.map M.R.subtype) (fun i => Algebra.linearMap M.R E (w i)) := by
    funext i
    simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Matrix.map_apply, Algebra.linearMap_apply]
    push_cast
    rfl
  have hinv : ∀ v : Fin (m + 1) → E,
      Matrix.mulVec (ZZ.Z.map M.R.subtype)⁻¹ (Matrix.mulVec (ZZ.Z.map M.R.subtype) v) = v := by
    intro v
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ ZZ.unit, Matrix.one_mulVec]
  show M.Rsub.mkQ ((Matrix.mulVec (ZZ.Z.map M.R.subtype)⁻¹
    (fun i => Algebra.linearMap M.R E (ZZ.Z.mulVecLin w i))) (Fin.last m)) = 0
  rw [hmap, hinv, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact ⟨w (Fin.last m), rfl⟩
def lam (M : Model F E) {m : ℕ} (ZZ : M.Mat (m + 1)) : M.Cok ZZ →ₗ[M.R] E ⧸ M.Rsub :=
  Submodule.liftQ _ (M.lamRaw ZZ) (M.lamRaw_range ZZ)
def Iso (M : Model F E) {m : ℕ} (ZZ ZZ' : M.Mat (m + 1)) : Type :=
  {φ : M.Cok ZZ ≃ₗ[M.R] M.Cok ZZ' //
    φ (M.eCls ZZ) = M.eCls ZZ' ∧ ∀ v, M.lam ZZ' (φ v) = M.lam ZZ v}
def nIso (M : Model F E) {m : ℕ} (ZZ ZZ' : M.Mat (m + 1)) : ℕ := Nat.card (M.Iso ZZ ZZ')
def isoSetoid (M : Model F E) (m : ℕ) : Setoid (M.Mat (m + 1)) where
  r ZZ ZZ' := Nonempty (M.Iso ZZ ZZ')
  iseqv := by
    refine ⟨fun ZZ => ⟨⟨LinearEquiv.refl _ _, rfl, fun _ => rfl⟩⟩, ?_, ?_⟩
    · rintro ZZ ZZ' ⟨φ, he, hl⟩
      refine ⟨⟨φ.symm, ?_, fun v => ?_⟩⟩
      · rw [← he]; simp
      · rw [← hl (φ.symm v)]; simp
    · rintro ZZ ZZ' ZZ'' ⟨φ, he, hl⟩ ⟨ψ, he', hl'⟩
      refine ⟨⟨φ.trans ψ, ?_, fun v => ?_⟩⟩
      · simp [he, he']
      · simp [hl, hl']
def Cls (M : Model F E) (m : ℕ) : Type := Quotient (M.isoSetoid m)
def nAut (M : Model F E) {m : ℕ} (c : M.Cls m) : ℕ :=
  M.nIso (Quotient.out c) (Quotient.out c)
end Model
def ptEntryL : List (Eˣ × ℕ+) → ℕ → ℕ → E
  | [], _, _ => 0
  | (t, s) :: bs, a, b =>
    if a < s ∧ b < s then (if a + b + 1 = (s : ℕ) then (t : E) else 0)
    else if (s : ℕ) ≤ a ∧ (s : ℕ) ≤ b then ptEntryL bs (a - s) (b - s) else 0
def sameBlock : List (Eˣ × ℕ+) → ℕ → ℕ → Bool
  | [], _, _ => false
  | (_, s) :: bs, a, b =>
    (decide (a < s ∧ b < s)) ||
      (decide ((s : ℕ) ≤ a ∧ (s : ℕ) ≤ b) && sameBlock bs (a - s) (b - s))
structure Pt (E : Type) [CommRing E] (n : ℕ) where
  blocks : List (Eˣ × ℕ+)
  size : (blocks.map (fun b => (b.2 : ℕ))).sum = n
namespace Pt
def mat {n : ℕ} (w : Pt E n) : Matrix (Fin n) (Fin n) E := fun a b => ptEntryL w.blocks a b
def snoc {n : ℕ} (h : Pt E n) (t : Eˣ) (s : ℕ+) : Pt E (n + s) where
  blocks := h.blocks ++ [(t, s)]
  size := by simp [h.size]
end Pt
abbrev IL (n : ℕ) : Type := {p : Fin n × Fin n // p.2 < p.1}
abbrev IN {n : ℕ} (w : Pt E n) : Type :=
  {p : Fin n × Fin n // p.1 < p.2 ∧ sameBlock w.blocks p.1 p.2 = false}
def uLow {n : ℕ} (x : IL n → E) : Matrix (Fin n) (Fin n) E :=
  fun a b => if a = b then 1 else if h : b < a then x ⟨(a, b), h⟩ else 0
def uUp {n : ℕ} (w : Pt E n) (y : IN w → E) : Matrix (Fin n) (Fin n) E :=
  fun a b => if a = b then 1 else
    if h : a < b ∧ sameBlock w.blocks a b = false then y ⟨(a, b), h⟩ else 0
def simpleLow {n : ℕ} (A : Matrix (Fin n) (Fin n) E) : E :=
  ∑ a : Fin n, ∑ b : Fin n, if (a : ℕ) = b + 1 then A a b else 0
def simpleUp {n : ℕ} (A : Matrix (Fin n) (Fin n) E) : E :=
  ∑ a : Fin n, ∑ b : Fin n, if (b : ℕ) = a + 1 then A a b else 0
namespace Model
variable [MeasurableSpace E]
open scoped Classical in

def bbIntegrand (M : Model F E) {m : ℕ} (w : Pt E (m + 1)) (c : M.Cls m)
    (xy : (IL (m + 1) → E) × (IN w → E)) : ℂ :=
  let Z : Matrix (Fin (m + 1)) (Fin (m + 1)) E := uLow xy.1 * w.mat * uUp w xy.2
  if h : (∀ a b, Z a b ∈ M.R) ∧ IsUnit Z.det then
    (M.nIso ⟨Matrix.of fun a b => ⟨Z a b, h.1 a b⟩, by
        have : (Matrix.of fun a b => (⟨Z a b, h.1 a b⟩ : M.R)).map M.R.subtype = Z :=
          rfl
        rw [this]; exact h.2⟩ (Quotient.out c) : ℂ) *
      M.psiR (simpleLow (uLow xy.1) + simpleUp (uUp w xy.2))
  else 0
def BB (M : Model F E) {m : ℕ} (w : Pt E (m + 1)) (c : M.Cls m) : ℂ :=
  ∫ xy, M.bbIntegrand w c xy ∂((Measure.pi fun _ : IL (m + 1) => M.mu).prod
    (Measure.pi fun _ : IN w => M.mu))
def Kk (M : Model F E) : (i : ℕ) → Pt E i → Pt E i → ℂ
  | 0, _, _ => 1
  | m + 1, w, w' => ∑' c : M.Cls m, M.BB w c * conj (M.BB w' c) / (M.nAut c : ℂ)
def N0 (M : Model F E) {m : ℕ} (h h' : Pt E m) : ℂ := M.Kk m h h'
def Ns (M : Model F E) {m : ℕ} (s : ℕ+) (t t' : Eˣ) (h h' : Pt E m) : ℂ :=
  ((M.modK ((t : E) * t') ^ ((s : ℕ) * ((s : ℕ) - 1) / 2) : ℝ) : ℂ) *
    M.Kk (m + s) (h.snoc t s) (h'.snoc t' s)
def detMod (M : Model F E) {m : ℕ} (h : Pt E m) : ℝ := M.modK h.mat.det
def InGLR (M : Model F E) {m : ℕ} (h : Pt E m) : Prop :=
  (∀ a b, h.mat a b ∈ M.R) ∧ ∃ u ∈ M.R, h.mat.det * u = 1
end Model
end Formalism.MainNotions.S.Loc
end
noncomputable section
open ComplexConjugate
namespace Formalism.MainNotions.S.Loc
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
namespace Model
open scoped Classical in

def CuspSpanExtension (M : Model F E) {m : ℕ} (c : E) (h h' : Pt E m) : ℂ :=
  if hc : ∃ n : Fin 3, IsUnit (c + ((n : ℕ) : E)) then
    M.Ns 1 hc.choose_spec.unit hc.choose_spec.unit h h'
  else 0
end Model
namespace Pt
def cast {n n' : ℕ} (e : n = n') (w : Pt E n) : Pt E n' := ⟨w.blocks, w.size.trans e⟩
end Pt
def ofPoint {n : ℕ} (p : Formalism.MainNotions.S.Point E n) (hu : ∀ b ∈ p.1, IsUnit b.1) : Pt E n where
  blocks := p.1.attach.map fun b => ((hu b.1 b.2).unit, ⟨b.1.2, by have := (p.2.1 b.1 b.2).2; omega⟩)
  size := by
    refine Eq.trans ?_ p.2.2
    congr 1
    rw [List.map_map]
    conv_rhs => rw [← List.attach_map_subtype_val p.1]
    rw [List.map_map]
    rfl
end Formalism.MainNotions.S.Loc
end


