-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_BetaSesquilinearity
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-24T14:07:08.273458+00:00
-- url     : https://prove2.me/theorems/44d9f4b8-3a51-455c-836d-7cf498cf020d
-- title:
--   Beta Sesquilinearity
-- statement:
--   Definitions and structural lemmas for Beta Sesquilinearity, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/BetaSesquilinearity.lean

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal
noncomputable section
namespace Formalism.FourierDecayAlt.P.BetaSesquilinearity
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
open scoped ContDiff
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
def crv (x : Bool × Mat k r) (g : Mat k r) (t : ℝ) : Mat k r :=
  if x.1 then NormedSpace.exp (-((t : ℂ) • x.2)) * g else g * NormedSpace.exp ((t : ℂ) • x.2)
def dirv (x : Bool × Mat k r) (g : Mat k r) : Mat k r := if x.1 then -x.2 * g else g * x.2
def Dx (x : Bool × Mat k r) (f : Mat k r → E) : Mat k r → E := if x.1 then LdV x.2 f else RdV x.2 f
def Dw (w : List (Bool × Mat k r)) (f : Mat k r → E) : Mat k r → E := w.foldr Dx f
lemma Dx_eq (x : Bool × Mat k r) (f : Mat k r → E) (g : Mat k r) :
    Dx x f g = deriv (fun t : ℝ => f (crv x g t)) 0 := by
  rcases x with ⟨_ | _, X⟩ <;> rfl
lemma Dx_zero (x : Bool × Mat k r) : Dx x (fun _ => (0 : E)) = fun _ => 0 := by
  funext g
  rw [Dx_eq]
  simp
lemma Dw_zero (w : List (Bool × Mat k r)) : Dw w (fun _ => (0 : E)) = fun _ => 0 := by
  induction w with
  | nil => rfl
  | cons x w ih =>
    show Dx x (Dw w (fun _ => (0 : E))) = _
    rw [ih, Dx_zero]
lemma Dw_append (w w' : List (Bool × Mat k r)) (f : Mat k r → E) :
    Dw (w ++ w') f = Dw w (Dw w' f) := by
  show (w ++ w').foldr Dx f = w.foldr Dx (w'.foldr Dx f)
  rw [List.foldr_append]
def dirL (x : Bool × Mat k r) : Mat k r →L[ℝ] Mat k r :=
  if x.1 then LinearMap.toContinuousLinearMap (LinearMap.mulLeft ℝ (-x.2)) else mulRightRealCLM x.2
end Formalism.FourierDecayAlt.P.BetaSesquilinearity
namespace Formalism.FourierDecayAlt.P.BetaSesquilinearity
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
open scoped ContDiff
section Frob
attribute [local instance] Matrix.frobeniusSeminormedAddCommGroup Matrix.frobeniusNormedAddCommGroup
  Matrix.frobeniusNormedSpace Matrix.frobeniusNormedRing
end Frob
end Formalism.FourierDecayAlt.P.BetaSesquilinearity
namespace Formalism.FourierDecayAlt.P.BetaSesquilinearity
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
open scoped ContDiff
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℂ E']
lemma CkOn_zero {m : ℕ∞} {UU : Set (Mat k r)} : CkOn m UU (fun _ => (0 : E)) := fun _ _ =>
  ⟨Set.univ, fun _ => 0, isOpen_univ, Set.mem_univ _, contDiffOn_const, fun _ _ _ => rfl⟩
def ap (a : Mat k r → (E →L[ℂ] E')) (Φ : Mat k r → E) : Mat k r → E' := fun g => a g (Φ g)
structure Pr (O UU : Set (Mat k r)) (m : ℕ∞) (a : Mat k r → (E →L[ℂ] E')) (Φ : Mat k r → E) : Prop where
  ha : CkOn m UU a
  hΦ : CkOn m (GV k r) Φ
  hz : ∀ g ∈ GV k r, g ∈ O → Φ g = 0
variable {O UU : Set (Mat k r)} {a : Mat k r → (E →L[ℂ] E')} {Φ : Mat k r → E}
def wL (u : List (Mat k r)) : List (Bool × Mat k r) := u.map (Prod.mk true)
def wR (v : List (Mat k r)) : List (Bool × Mat k r) := v.map (Prod.mk false)
lemma Dw_wR (v : List (Mat k r)) (f : Mat k r → E) : Dw (wR v) f = Rw v f := by
  induction v with
  | nil => rfl
  | cons X v ih =>
    show Dx (false, X) (Dw (wR v) f) = RdV X (Rw v f)
    rw [ih]
    rfl
lemma Dw_wL (u : List (Mat k r)) (f : Mat k r → E) : Dw (wL u) f = u.foldr LdV f := by
  induction u with
  | nil => rfl
  | cons X u ih =>
    show Dx (true, X) (Dw (wL u) f) = LdV X (u.foldr LdV f)
    rw [ih]
    rfl
lemma dLR_eq (u v : List (Mat k r)) (f : Mat k r → E) : dLR u v f = Dw (wL u ++ wR v) f := by
  show u.foldr LdV (Rw v f) = _
  rw [Dw_append, Dw_wR, Dw_wL]
def nz (X : Mat k r) : ℝ := max 1 ‖X‖
def nrm (X : Mat k r) : Mat k r := (((nz X)⁻¹ : ℝ) : ℂ) • X
end Formalism.FourierDecayAlt.P.BetaSesquilinearity
namespace Formalism.FourierDecayAlt.P.BetaSesquilinearity
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
open scoped ContDiff
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℂ E']
lemma CCle_zero {A : ℝ} {m : ℕ} : CCle A m (fun _ : Mat k r => (0 : E)) 0 := ⟨CkOn_zero, fun u v _ _ _ g _ => by rw [dLR_eq, Dw_zero]; simp⟩
def trn (L : E →L[ℂ] E') (a b : Mat k r) (f : Mat k r → E) : Mat k r → E' := fun g => L (f (a * g * b))
def abL (a b : Mat k r) : Mat k r →L[ℝ] Mat k r :=
  (mulRightRealCLM b).comp (LinearMap.toContinuousLinearMap (LinearMap.mulLeft ℝ a))
end Formalism.FourierDecayAlt.P.BetaSesquilinearity
namespace Formalism.FourierDecayAlt.P.BetaSesquilinearity
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
section weaken
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
end weaken
end Formalism.FourierDecayAlt.P.BetaSesquilinearity
namespace Formalism.FourierDecayAlt.P.BetaSesquilinearity
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
open scoped ContDiff
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
section gen
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
end gen
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
def Lp (D : RealPlaceData k r Wp Wq) (p : SS k r) : (Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp) :=
  (ContinuousLinearMap.compL ℂ Wq Wp Wp (D.π (Matrix.of p.1.1))).comp
    ((ContinuousLinearMap.compL ℂ Wq Wq Wp).flip (D.π' (Matrix.of p.2.1)⁻¹))
end Formalism.FourierDecayAlt.P.BetaSesquilinearity
namespace Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity
open scoped ContDiff
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
end Formalism.FourierDecayAlt.P
namespace Formalism.FourierDecayAlt.P.BetaSesquilinearity
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
def wt (D : RealPlaceData k r Wp Wq) (q : (Fin r → ℂ) × ℂ) : ℝ := bcWeight k r (Tz k r D.z) (Tz k r D.z') q
def μQ (D : RealPlaceData k r Wp Wq) : Measure ((Fin r → ℂ) × ℂ) :=
  (volume.restrict (Qset D)).withDensity fun q => ENNReal.ofReal (wt D q)
def Jv (D : RealPlaceData k r Wp Wq) (τ : ℝ × ℝ) (F : Mat k r → (Wq →L[ℂ] Wp)) (q : (Fin r → ℂ) × ℂ) :
    PiLp 2 (fun _ : Fin (Module.finrank ℂ Wq) => Wp) := hsVec (Jtau D τ F (gq D q))
section steps
variable {D : RealPlaceData k r Wp Wq} {A : ℝ}
end steps
section sesq
variable {D : RealPlaceData k r Wp Wq} {A : ℝ}
end sesq
section zero
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
lemma inCC_zero (A : ℝ) (m : ℕ) : InCC A m (0 : Mat k r → E) := ⟨0, CCle_zero⟩
end zero
def CCs (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (hL : CCLin) (A : ℝ) (m : ℕ) :
    Submodule ℂ (Mat k r → (Wq →L[ℂ] Wp)) where
  carrier := {F | InCC A m F}
  add_mem' := by
    rintro a b ⟨c, hc⟩ ⟨c', hc'⟩
    exact ⟨_, (hL k r _ A m a b c c' 0 hc hc').1⟩
  zero_mem' := inCC_zero A m
  smul_mem' := by
    rintro a x ⟨c, hc⟩
    exact ⟨_, (hL k r _ A m x x c c a hc hc).2⟩
section core
variable {D : RealPlaceData k r Wp Wq} {A : ℝ}
end core
end Formalism.FourierDecayAlt.P.BetaSesquilinearity
namespace Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity
end Formalism.FourierDecayAlt.P


