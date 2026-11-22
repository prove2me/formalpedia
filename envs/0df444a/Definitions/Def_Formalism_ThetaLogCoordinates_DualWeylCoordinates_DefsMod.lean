-- Prove2me | Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DefsMod
-- name    : Formalism_ThetaLogCoordinates_DualWeylCoordinates_DefsMod
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:17:32.014079+00:00
-- url     : https://prove2.me/theorems/f01815e1-cf38-480c-ba8c-52adffd249e6
-- title:
--   Defs Mod
-- statement:
--   Definitions and structural lemmas for Defs Mod, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/DualWeylCoordinates/DefsMod.lean

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DefsObj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
namespace Formalism.InvariantFactorPaths.ColumnFamilies
lemma genMat_map_eval {n : ℕ} {R : Type} [CommRing R] (f : ℤ →+* R) (g : Matrix (Fin n) (Fin n) R) :
    (MvPolynomial.eval₂Hom f (fun ab : Fin n × Fin n => g ab.1 ab.2)).mapMatrix (genMat ℤ n) = g := by
  ext a b
  simp [genMat]
def evGL {n : ℕ} {R : Type} [CommRing R] (g : GL (Fin n) R) : GLCoord ℤ n →+* R :=
  IsLocalization.Away.lift (genMat ℤ n).det
    (g := MvPolynomial.eval₂Hom (Int.castRingHom R) (fun ab : Fin n × Fin n => g.val ab.1 ab.2))
    (by rw [RingHom.map_det, genMat_map_eval]; exact Matrix.isUnits_det_units g)
lemma genMat_map_coord {n : ℕ} (F : Type) [CommRing F] :
    (MvPolynomial.map (Int.castRingHom F)).mapMatrix (genMat ℤ n) = genMat F n := by
  ext a b
  simp [genMat]
def mapCoord {n : ℕ} (F : Type) [CommRing F] : GLCoord ℤ n →+* GLCoord F n :=
  IsLocalization.Away.lift (genMat ℤ n).det
    (g := (algebraMap (MvPolynomial (Fin n × Fin n) F) (GLCoord F n)).comp (MvPolynomial.map (Int.castRingHom F)))
    (by rw [RingHom.comp_apply, RingHom.map_det, genMat_map_coord]
        exact IsLocalization.Away.algebraMap_isUnit _)
structure GLMod (n : ℕ) where
  ι : Type
  [fi : Fintype ι]
  [de : DecidableEq ι]
  A : Matrix ι ι (GLCoord ℤ n)
  mul : ∀ (R : Type) [CommRing R] (g h : GL (Fin n) R), A.map (evGL (g * h)) = A.map (evGL g) * A.map (evGL h)
  one : ∀ (R : Type) [CommRing R], A.map (evGL (1 : GL (Fin n) R)) = 1
attribute [instance] GLMod.fi GLMod.de
def TCols {n : ℕ} [NeZero n] (mu : Fin n → ℤ) : Finset ℤ := Finset.Ioc (mu (lastIdx n)) (mu 0)
abbrev TIdx {n : ℕ} [NeZero n] (mu : Fin n → ℤ) :=
  (c : ↥(TCols mu)) → {J : Finset (Fin n) // J.card = colH mu c}
lemma colH_le {n : ℕ} (mu : Fin n → ℤ) (c : ℤ) : colH mu c ≤ n :=
  le_of_le_of_eq (Finset.card_filter_le _ _) (by simp)
def canT {n : ℕ} [NeZero n] (mu : Fin n → ℤ) : TIdx mu :=
  fun c => ⟨(univ : Finset (Fin (colH mu c))).map (Fin.castLEEmb (colH_le mu c)), by simp⟩
def minorC {n h : ℕ} (J I : Finset (Fin n)) (hJ : J.card = h) (hI : I.card = h) : GLCoord ℤ n :=
  algebraMap _ (GLCoord ℤ n)
    (Matrix.det (Matrix.of fun a b : Fin h => genMat ℤ n (J.orderEmbOfFin hJ a) (I.orderEmbOfFin hI b)))
def detU (n : ℕ) : (GLCoord ℤ n)ˣ := (IsLocalization.Away.algebraMap_isUnit (genMat ℤ n).det).unit
def TMat {n : ℕ} [NeZero n] (mu : Fin n → ℤ) : Matrix (TIdx mu) (TIdx mu) (GLCoord ℤ n) :=
  fun J I => ((detU n ^ mu (lastIdx n) : (GLCoord ℤ n)ˣ) : GLCoord ℤ n) *
    ∏ c : ↥(TCols mu), minorC (J c).1 (I c).1 (J c).2 (I c).2
def brk {n : ℕ} [NeZero n] (mu : Fin n → ℤ) (I : TIdx mu) : GLCoord ℤ n := TMat mu (canT mu) I
def StdT {n : ℕ} [NeZero n] {mu : Fin n → ℤ} (I : TIdx mu) : Prop :=
  ∀ (c : ↥(TCols mu)) (hc : (c : ℤ) + 1 ∈ TCols mu) (t : Fin n),
    ((I ⟨(c : ℤ) + 1, hc⟩).1.filter (· ≤ t)).card ≤ ((I c).1.filter (· ≤ t)).card
def dMu {n : ℕ} [NeZero n] (mu : Fin n → ℤ) : ℕ := Nat.card {I : TIdx mu // StdT I}
def SMu {n : ℕ} [NeZero n] (mu : Fin n → ℤ) : Submodule ℤ (GLCoord ℤ n) :=
  Submodule.span ℤ (Set.range (brk mu))
def torusPt (n : ℕ) : GL (Fin n) (AddMonoidAlgebra ℤ (Fin n → ℤ)) where
  val := Matrix.diagonal fun a => AddMonoidAlgebra.single (Pi.single a 1) 1
  inv := Matrix.diagonal fun a => AddMonoidAlgebra.single (Pi.single a (-1)) 1
  val_inv := by
    rw [Matrix.diagonal_mul_diagonal]; convert Matrix.diagonal_one using 2
    funext a; rw [AddMonoidAlgebra.single_mul_single, ← Pi.single_add]; simp [AddMonoidAlgebra.one_def]
  inv_val := by
    rw [Matrix.diagonal_mul_diagonal]; convert Matrix.diagonal_one using 2
    funext a; rw [AddMonoidAlgebra.single_mul_single, ← Pi.single_add]; simp [AddMonoidAlgebra.one_def]
def prMu {n : ℕ} (M : GLMod n) (mu : Fin n → ℤ) : Matrix M.ι M.ι ℤ :=
  fun i j => (evGL (torusPt n) (M.A i j)).coeff mu
def IsHighest {n : ℕ} (M : GLMod n) (R : Type) [CommRing R] (mu : Fin n → ℤ) (x : M.ι → R) : Prop :=
  Matrix.mulVec ((prMu M mu).map (Int.castRingHom R)) x = x ∧
  ∀ (R' : Type) [CommRing R'] [Algebra R R'] (u : GL (Fin n) R'), (∀ a, u.val a a = 1) →
    (∀ a b, b < a → u.val a b = 0) → Matrix.mulVec (M.A.map (evGL u)) (fun i => algebraMap R R' (x i)) = fun i => algebraMap R R' (x i)
def typeSum {n : ℕ} (M : GLMod n) (pi : Set (Fin n → ℤ)) : Submodule ℚ (M.ι → ℚ) :=
  Submodule.span ℚ {y | ∃ mu ∈ pi, ∃ v, IsHighest M ℚ mu v ∧ ∃ g : GL (Fin n) ℚ, y = Matrix.mulVec (M.A.map (evGL g)) v}
def DomLE {n : ℕ} (nu mu : Fin n → ℤ) : Prop :=
  (∀ a : Fin n, ∑ b ∈ univ.filter (· ≤ a), nu b ≤ ∑ b ∈ univ.filter (· ≤ a), mu b) ∧ ∑ b, nu b = ∑ b, mu b
def DomLowerSet {n : ℕ} (pi : Set (Fin n → ℤ)) : Prop :=
  (∀ mu ∈ pi, Dominant mu) ∧ ∀ mu ∈ pi, ∀ nu, Dominant nu → DomLE nu mu → nu ∈ pi
structure ColFam {n : ℕ} [NeZero n] (M : GLMod n) where
  J : Type
  [fJ : Fintype J]
  [dJ : DecidableEq J]
  mu : J → Fin n → ℤ
  dom : ∀ j, Dominant (mu j)
  ph : (j : J) → Matrix M.ι (TIdx (mu j)) ℤ
  equiv : ∀ j, M.A * (ph j).map (Int.castRingHom _) = (ph j).map (Int.castRingHom _) * TMat (mu j)
  indepP : ∀ (p : ℕ), p.Prime → ∀ nu : Fin n → ℤ,
    LinearIndependent (ZMod p) (fun j : {j : J // mu j = nu} => fun i => ((ph j.1 i (canT (mu j.1)) : ℤ) : ZMod p))
  indepQ : ∀ nu : Fin n → ℤ,
    LinearIndependent ℚ (fun j : {j : J // mu j = nu} => fun i => ((ph j.1 i (canT (mu j.1)) : ℤ) : ℚ))
  rank : Fintype.card M.ι = ∑ j, dMu (mu j)
attribute [instance] ColFam.fJ ColFam.dJ
def ColFam.vec {n : ℕ} [NeZero n] {M : GLMod n} (CF : ColFam M) (j : CF.J) (I : TIdx (CF.mu j)) : M.ι → ℤ :=
  fun i => CF.ph j i I
def ColFam.Mpi {n : ℕ} [NeZero n] {M : GLMod n} (CF : ColFam M) (pi : Set (Fin n → ℤ)) : Submodule ℤ (M.ι → ℤ) :=
  Submodule.span ℤ {x | ∃ j, CF.mu j ∈ pi ∧ ∃ I : TIdx (CF.mu j), x = CF.vec j I}
def ColFam.MM {n : ℕ} [NeZero n] {M : GLMod n} (CF : ColFam M) (mu : Fin n → ℤ) : Submodule ℤ (M.ι → ℤ) :=
  Submodule.span ℤ {x | ∃ j, CF.mu j = mu ∧ x = CF.vec j (canT (CF.mu j))}
abbrev SymIdx (n b : ℕ) := {α : Fin n → Fin (b + 1) // ∑ a, (α a : ℕ) = b}
def symMono {n b : ℕ} (α : SymIdx n b) : Fin n →₀ ℕ := Finsupp.equivFunOnFinite.symm fun a => (α.1 a : ℕ)
def SymMat (n b : ℕ) : Matrix (SymIdx n b) (SymIdx n b) (GLCoord ℤ n) :=
  fun α β => MvPolynomial.coeff (symMono α)
    (∏ m : Fin n, (∑ a : Fin n, MvPolynomial.C (algebraMap _ (GLCoord ℤ n) (genMat ℤ n a m)) * X a) ^ (β.1 m : ℕ))
def ginvC (n : ℕ) (a b : Fin n) : GLCoord ℤ n :=
  (((detU n)⁻¹ : (GLCoord ℤ n)ˣ) : GLCoord ℤ n) * algebraMap _ (GLCoord ℤ n) ((genMat ℤ n).adjugate a b)
def SymDMat (n b : ℕ) : Matrix (SymIdx n b) (SymIdx n b) (GLCoord ℤ n) :=
  fun α β => MvPolynomial.coeff (symMono α)
    (∏ m : Fin n, (∑ a : Fin n, MvPolynomial.C (ginvC n m a) * X a) ^ (β.1 m : ℕ))
abbrev LamIdx (n b : ℕ) := {J : Finset (Fin n) // J.card = b}
def LamMat (n b : ℕ) : Matrix (LamIdx n b) (LamIdx n b) (GLCoord ℤ n) :=
  fun J I => minorC J.1 I.1 J.2 I.2
def IsTensor {n : ℕ} (M M' : GLMod n) {κ : Type} (B : Matrix κ κ (GLCoord ℤ n)) (e : M'.ι ≃ M.ι × κ) : Prop :=
  ∀ i j, M'.A i j = M.A (e i).1 (e j).1 * B (e i).2 (e j).2
def IsSMu {n : ℕ} [NeZero n] (M : GLMod n) (mu : Fin n → ℤ) (β : M.ι → GLCoord ℤ n) : Prop :=
  LinearIndependent ℤ β ∧ Submodule.span ℤ (Set.range β) = SMu mu ∧
  ∀ (R : Type) [CommRing R] (x g : GL (Fin n) R) (i : M.ι),
    evGL (x * g) (β i) = ∑ j, evGL g (M.A j i) * evGL x (β j)
def Interl {m : ℕ} (lam : Fin (m + 1) → ℤ) (nu : Fin m → ℤ) : Prop :=
  ∀ a : Fin m, nu a ≤ lam a.castSucc ∧ lam a.succ ≤ nu a
def IsBlock {m : ℕ} {R : Type} [CommRing R] (h : GL (Fin (m + 1)) R) (g1 : GL (Fin m) R) (t : Rˣ) : Prop :=
  (∀ a b : Fin m, h.val a.castSucc b.castSucc = g1.val a b) ∧ h.val (Fin.last m) (Fin.last m) = t ∧
  ∀ a : Fin m, h.val a.castSucc (Fin.last m) = 0 ∧ h.val (Fin.last m) a.castSucc = 0
lemma genMat_map_evalR {n : ℕ} {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R']
    (g : Matrix (Fin n) (Fin n) R') :
    (MvPolynomial.eval₂Hom (algebraMap R R') (fun ab : Fin n × Fin n => g ab.1 ab.2)).mapMatrix (genMat R n) = g := by
  ext a b
  simp [genMat]
def evGLR {n : ℕ} {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] (g : GL (Fin n) R') : GLCoord R n →+* R' :=
  IsLocalization.Away.lift (genMat R n).det
    (g := MvPolynomial.eval₂Hom (algebraMap R R') (fun ab : Fin n × Fin n => g.val ab.1 ab.2))
    (by rw [RingHom.map_det, genMat_map_evalR]; exact Matrix.isUnits_det_units g)
def inducedSections {n : ℕ} (R : Type) [CommRing R] (mu : Fin n → ℤ) : Set (GLCoord R n) :=
  {f | ∀ (R' : Type) [CommRing R'] [Algebra R R'] (b g : GL (Fin n) R'), (∀ a c : Fin n, a < c → b.val a c = 0) →
    evGLR (b * g) f * ∏ a, b.val a a ^ (-(mu a)).toNat = (∏ a, b.val a a ^ (mu a).toNat) * evGLR g f}
def rowLetters (n : ℕ) : Letters (Fin n) := ⟨fun _ => true⟩
def brkPol {n : ℕ} [NeZero n] (mu : Fin n → ℤ) (I : TIdx mu) : MvPolynomial (Fin n × Fin n) ℤ :=
  (genMat ℤ n).det ^ (mu (lastIdx n)).toNat *
    ∏ c : ↥(TCols mu), Matrix.det (Matrix.of fun a b : Fin (colH mu c) =>
      genMat ℤ n ((canT mu c).1.orderEmbOfFin (canT mu c).2 a) ((I c).1.orderEmbOfFin (I c).2 b))
end Formalism.InvariantFactorPaths.ColumnFamilies


