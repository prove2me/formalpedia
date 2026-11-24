-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HasDerivAtInvpow
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_HasDerivAtInvpow
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-24T18:18:56.74764+00:00
-- url     : https://prove2.me/theorems/4ac05f62-a73f-4569-830d-343e95b1fc37
-- title:
--   Has Deriv At Invpow
-- statement:
--   Definitions and structural lemmas for Has Deriv At Invpow, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/HasDerivAtInvpow.lean

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HsVecApply
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BudgetClassEstimate
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentComposition_HasDerivAtInvpow
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentComposition_DegPderivMul
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentComposition_Expand
import Theorems.Thm_Formalism_QuantumDeterminants_Zhat_eq
import Theorems.Thm_PI_UnitaryGroupMassFormula_UsCompose_deg_CX
import Theorems.Thm_PI_UnitaryGroupMassFormula_UsCompose_deg_cmul
import Theorems.Thm_PI_UnitaryGroupMassFormula_UsCompose_deg_det

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MvPolynomial
open scoped ComplexConjugate ContDiff Topology
noncomputable section
namespace Formalism.FourierDecayAlt.P.MinorPolynomials
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity PI.UnitaryGroupMassFormula.UsCompose
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
lemma exists_zhat_eq_eval_poly_deg_le_one (z z' : Fin (2 * r + k + 1) → ℂ) :
    ∃ P : Fin (r + 1) → Fin (r + 1) → MvPolynomial (Vr (2 * r + k + 1)) ℂ,
      (∀ a b, (P a b).totalDegree ≤ 1) ∧
        ∀ (g : Mat k r) a b, eval (vars g) (P a b) = Zhat k r z z' g a b := by
  refine ⟨fun a b => ∑ i, ∑ j, C (((Fm k r z)ᴴ * Hpk k r) a i * Fm k r z' j b) *
    MvPolynomial.X (Sum.inl (i, j)), ?_, ?_⟩
  · intro a b
    refine (MvPolynomial.totalDegree_finset_sum _ _).trans (Finset.sup_le fun i _ => ?_)
    refine (MvPolynomial.totalDegree_finset_sum _ _).trans (Finset.sup_le fun j _ => ?_)
    exact deg_CX _ _
  · intro g a b
    rw [Zhat_eq]
    simp only [map_sum, map_mul, eval_C, eval_X, PI.UnitaryGroupMassFormula.UsCompose.vars, Sum.elim_inl, Matrix.mul_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
    exact Finset.sum_congr rfl fun x _ => by ring
lemma exists_star_zhat_eq_eval_poly_deg_le_one (z z' : Fin (2 * r + k + 1) → ℂ) :
    ∃ P : Fin (r + 1) → Fin (r + 1) → MvPolynomial (Vr (2 * r + k + 1)) ℂ,
      (∀ a b, (P a b).totalDegree ≤ 1) ∧
        ∀ (g : Mat k r) a b, eval (vars g) (P a b) = star (Zhat k r z z' g a b) := by
  refine ⟨fun a b => ∑ i, ∑ j, C (star (((Fm k r z)ᴴ * Hpk k r) a i * Fm k r z' j b)) *
    MvPolynomial.X (Sum.inr (i, j)), ?_, ?_⟩
  · intro a b
    refine (MvPolynomial.totalDegree_finset_sum _ _).trans (Finset.sup_le fun i _ => ?_)
    refine (MvPolynomial.totalDegree_finset_sum _ _).trans (Finset.sup_le fun j _ => ?_)
    exact deg_CX _ _
  · intro g a b
    rw [Zhat_eq]
    simp only [map_sum, map_mul, eval_C, eval_X, PI.UnitaryGroupMassFormula.UsCompose.vars, Sum.elim_inr, Matrix.mul_apply, Finset.sum_mul,
      star_sum, star_mul']
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
    exact Finset.sum_congr rfl fun x _ => by ring
lemma exists_det_submatrix_poly_deg_le_of_entries_deg_le_one {m : ℕ} (f : Mat k r → Matrix (Fin m) (Fin m) ℂ)
    (P : Fin m → Fin m → MvPolynomial (Vr (2 * r + k + 1)) ℂ) (hP : ∀ a b, (P a b).totalDegree ≤ 1)
    (hf : ∀ g a b, eval (vars g) (P a b) = f g a b) (n : ℕ) (e : Fin n → Fin m) :
    ∃ q : MvPolynomial (Vr (2 * r + k + 1)) ℂ, q.totalDegree ≤ n ∧
      ∀ g, ((f g).submatrix e e).det = eval (vars g) q := by
  refine ⟨(Matrix.of fun a b => P (e a) (e b)).det, deg_det _ (fun a b => hP _ _), fun g => ?_⟩
  rw [RingHom.map_det]
  congr 1
  ext a b
  simp [RingHom.mapMatrix_apply, hf]
lemma exists_dmin_eq_eval_poly_deg_le (z z' : Fin (2 * r + k + 1) → ℂ) (l : Fin (r + 2)) :
    ∃ q : MvPolynomial (Vr (2 * r + k + 1)) ℂ, q.totalDegree ≤ l.val ∧
      ∀ g : Mat k r, Dmin k r z z' g l = eval (vars g) q := by
  obtain ⟨P, hP, hPe⟩ := exists_zhat_eq_eval_poly_deg_le_one (k := k) (r := r) z z'
  obtain ⟨q, hq, hqe⟩ := exists_det_submatrix_poly_deg_le_of_entries_deg_le_one (fun g => Zhat k r z z' g) P hP hPe l.val
    (Fin.castLE (Nat.le_of_lt_succ l.isLt))
  exact ⟨q, hq, fun g => by rw [Dmin]; exact hqe g⟩
lemma exists_star_dmin_eq_eval_poly_deg_le (z z' : Fin (2 * r + k + 1) → ℂ) (l : Fin (r + 2)) :
    ∃ q : MvPolynomial (Vr (2 * r + k + 1)) ℂ, q.totalDegree ≤ l.val ∧
      ∀ g : Mat k r, star (Dmin k r z z' g l) = eval (vars g) q := by
  obtain ⟨P, hP, hPe⟩ := exists_star_zhat_eq_eval_poly_deg_le_one (k := k) (r := r) z z'
  obtain ⟨q, hq, hqe⟩ := exists_det_submatrix_poly_deg_le_of_entries_deg_le_one (fun g => (Zhat k r z z' g).map (starRingEnd ℂ)) P hP
    (fun g a b => by simp [hPe]) l.val (Fin.castLE (Nat.le_of_lt_succ l.isLt))
  refine ⟨q, hq, fun g => ?_⟩
  rw [← hqe g, Dmin, ← starRingEnd_apply, RingHom.map_det, RingHom.mapMatrix_apply, Matrix.submatrix_map]
lemma dminPoly (z z' : Fin (2 * r + k + 1) → ℂ) (l : Fin (r + 2)) :
    ∃ q : MvPolynomial (Vr (2 * r + k + 1)) ℂ, q.totalDegree ≤ 2 * r + 2 ∧
      ∀ g : Mat k r, Dmin k r z z' g l = eval (vars g) q := by
  obtain ⟨q, hq, hqe⟩ := exists_dmin_eq_eval_poly_deg_le (k := k) z z' l
  exact ⟨q, hq.trans (by have := l.isLt; omega), hqe⟩
lemma dminStarPoly (z z' : Fin (2 * r + k + 1) → ℂ) (l : Fin (r + 2)) :
    ∃ q : MvPolynomial (Vr (2 * r + k + 1)) ℂ, q.totalDegree ≤ 2 * r + 2 ∧
      ∀ g : Mat k r, star (Dmin k r z z' g l) = eval (vars g) q := by
  obtain ⟨q, hq, hqe⟩ := exists_star_dmin_eq_eval_poly_deg_le (k := k) z z' l
  exact ⟨q, hq.trans (by have := l.isLt; omega), hqe⟩
lemma gfPoly (z z' : Fin (2 * r + k + 1) → ℂ) :
    ∃ q : MvPolynomial (Vr (2 * r + k + 1)) ℂ, q.totalDegree ≤ 2 * r + 2 ∧
      ∀ g : Mat k r, ((Gf k r z z' g : ℝ) : ℂ) = eval (vars g) q := by
  obtain ⟨qa, ha, hae⟩ := exists_dmin_eq_eval_poly_deg_le (k := k) z z' (Fin.last (r + 1))
  obtain ⟨qab, hab, habe⟩ := exists_star_dmin_eq_eval_poly_deg_le (k := k) z z' (Fin.last (r + 1))
  obtain ⟨qb, hb, hbe⟩ := exists_dmin_eq_eval_poly_deg_le (k := k) z z' ⟨r, by omega⟩
  obtain ⟨qbb, hbb, hbbe⟩ := exists_star_dmin_eq_eval_poly_deg_le (k := k) z z' ⟨r, by omega⟩
  simp only [Fin.val_last] at ha hab hb hbb
  refine ⟨qa * qab - C ((Tz k r z * Tz k r z' : ℝ) : ℂ) * qb * qbb, ?_, fun g => ?_⟩
  · refine (MvPolynomial.totalDegree_sub _ _).trans (max_le ?_ ?_)
    · exact (MvPolynomial.totalDegree_mul _ _).trans (by omega)
    · exact (deg_cmul _ _ _).trans (by omega)
  · simp only [map_sub, map_mul, eval_C]
    rw [← hae g, ← habe g, ← hbe g, ← hbbe g, Gf]
    push_cast
    rw [Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_conj_mul_self]
    simp only [Complex.star_def]
    ring
def qDl (z z' : Fin (2 * r + k + 1) → ℂ) (l : Fin (r + 2)) : MvPolynomial (Vr (2 * r + k + 1)) ℂ :=
  Classical.choose (dminPoly (k := k) z z' l)
def qDbl (z z' : Fin (2 * r + k + 1) → ℂ) (l : Fin (r + 2)) : MvPolynomial (Vr (2 * r + k + 1)) ℂ :=
  Classical.choose (dminStarPoly (k := k) z z' l)
def qGf (z z' : Fin (2 * r + k + 1) → ℂ) : MvPolynomial (Vr (2 * r + k + 1)) ℂ :=
  Classical.choose (gfPoly (k := k) z z')
structure CT (k r nf : ℕ) where
  q : MvPolynomial (Vr (2 * r + k + 1)) ℂ
  a : Fin (r + 2) → ℕ
  b : Fin (r + 2) → ℕ
  c : ℕ
  es : List (Fin nf × List (Mat k r))
section vals
variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
def cvs (D : RealPlaceData k r Wp Wq) {nf : ℕ} (t : CT k r nf) (g : Mat k r) : ℂ :=
  eval (vars g) t.q * C6.monoM D t.a t.b t.c g
def cv (D : RealPlaceData k r Wp Wq) {nf : ℕ} (fib : Fin nf → Mat k r → C6.EndH Wp Wq) (t : CT k r nf) (g : Mat k r) :
    C6.EndH Wp Wq :=
  cvs D t g • C6.Epart fib t.es g
def dscal (D : RealPlaceData k r Wp Wq) {nf : ℕ} (X : Mat k r) (t : CT k r nf) : List (CT k r nf) :=
  [{ t with q := dP X t.q }] ++
  List.ofFn (fun l : Fin (r + 2) => if t.a l = 0 then { t with q := 0 } else
    { t with q := C (-(t.a l : ℂ)) * t.q * dP X (qDl D.z D.z' l), a := t.a + Pi.single l 1 }) ++
  List.ofFn (fun l : Fin (r + 2) => if t.b l = 0 then { t with q := 0 } else
    { t with q := C (-(t.b l : ℂ)) * t.q * dP X (qDbl D.z D.z' l), b := t.b + Pi.single l 1 }) ++
  [if t.c = 0 then { t with q := 0 } else { t with q := C (-(t.c : ℂ)) * t.q * dP X (qGf D.z D.z'), c := t.c + 1 }]
def dfib {nf : ℕ} (X : Mat k r) (t : CT k r nf) : List (CT k r nf) :=
  List.ofFn (fun i : Fin t.es.length => { t with es := t.es.set i ((t.es.get i).1, X :: (t.es.get i).2) })
def dco (D : RealPlaceData k r Wp Wq) {nf : ℕ} (X : Mat k r) (t : CT k r nf) : List (CT k r nf) :=
  dscal D X t ++ dfib X t
end vals
end Formalism.FourierDecayAlt.P.MinorPolynomials


