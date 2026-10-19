-- Prove2me | Definitions.Def_MazurTransfer_Order13FieldPicardCyclotomicNormData
-- name    : MazurTransfer_Order13FieldPicardCyclotomicNormData
-- status  : Definition
-- author  : @Vas
-- created : 2026-10-17T18:00:06.09968+00:00
-- url     : https://prove2.me/theorems/fdf80531-e1fb-4808-9cf4-2bd5f37a37ae
-- title:
--   Literal arithmetic Picard cyclotomic and nineteen norm identities over characteristic-zero fields
-- statement:
--   Over every characteristic-zero field, the actual diamond endomorphism satisfies rho^2-rho+1=0; both composites of the original pi=3+2rho and piConjugate=5-2rho equal nineteen; and both kernels are annihilated by nineteen. All nine complete original theorem types and proofs and the original local scalar algebra provider are retained and compared. Named downstream consumer: geometric arithmetic Picard group action and genuine scheme norm transport.
-- source:
--   Complete original MazurTheorem Order13FieldPicardCyclotomicNorm, using the published original paired general-field arithmetic Picard traces. Official Anthropic FLT arithmetic Pic0 interfaces at 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the literal diamond action on arithmetic Pic0 satisfies
(rho K)^2-(rho K)+1=0 and the two displayed endomorphisms have product nineteen.
Named downstream consumer: arithmetic nineteen descent on the actual
order-thirteen Picard group and its represented relative Picard object.
-/
import Definitions.Def_MazurTransfer_Order13FieldPicardDiamondTraceData

noncomputable section
universe w
namespace MazurTransfer.Order13FieldPicardCyclotomicNorm
open Order13FieldDiamondPicardEndomorphisms Order13FieldPicardDiamondTrace
open GoodCharacteristicGeometryPublicProof.MazurTransfer.Order13GoodCharacteristicCurveModel
variable (K : Type w) [Field K] [CharZero K]
local instance : Fact ((104 : K) ≠ 0) := ⟨by norm_num⟩
local instance : Algebra K (actualCurveFunctionField K) := actualCurveFunctionFieldAlgebra K

theorem rho_cube_apply (c : (ActualPicard K)) : ((rho K) ^ 3) c = -c :=
  eq_neg_of_add_eq_zero_right ((hyperelliptic_trace_zero K) c)

theorem rho_pow_three : (rho K) ^ 3 = -1 := by
  apply AddMonoidHom.ext
  intro c
  exact (rho_cube_apply K) c

theorem rho_fourth_apply (c : (ActualPicard K)) : ((rho K) ^ 4) c = -(rho K) c := by
  rw [show (4 : ℕ) = 3 + 1 by rfl, pow_succ]
  exact (rho_cube_apply K) ((rho K) c)

theorem rho_square_apply (c : (ActualPicard K)) : ((rho K) ^ 2) c = (rho K) c - c := by
  have h := (order_three_trace_zero K) c
  rw [(rho_fourth_apply K)] at h
  apply eq_of_sub_eq_zero
  calc
    ((rho K) ^ 2) c - ((rho K) c - c) = c + ((rho K) ^ 2) c + -(rho K) c := by abel
    _ = 0 := h

theorem rho_cyclotomic : (rho K) ^ 2 - (rho K) + 1 = 0 := by
  apply AddMonoidHom.ext
  intro c
  change ((rho K) ^ 2) c - (rho K) c + c = 0
  rw [(rho_square_apply K)]
  abel

theorem pi_comp_piConjugate_nineteen : (pi K) * (piConjugate K) = 19 := by
  rw [(pi_comp_piConjugate K)]
  apply AddMonoidHom.ext
  intro c
  change (15 : ℕ) • c + (4 : ℕ) • (rho K) c - (4 : ℕ) • ((rho K) ^ 2) c = (19 : ℕ) • c
  rw [(rho_square_apply K)]
  abel

theorem piConjugate_comp_pi_nineteen : (piConjugate K) * (pi K) = 19 :=
  (piConjugate_comp_pi K).trans ((pi_comp_piConjugate K).symm.trans (pi_comp_piConjugate_nineteen K))

theorem nineteen_nsmul_eq_zero_of_pi_eq_zero {c : (ActualPicard K)} (hc : (pi K) c = 0) :
    (19 : ℕ) • c = 0 := by
  have h := congrArg (fun f : AddMonoid.End (ActualPicard K) => f c)
    (piConjugate_comp_pi_nineteen K)
  change (piConjugate K) ((pi K) c) = (19 : ℕ) • c at h
  rw [hc, map_zero] at h
  exact h.symm

theorem nineteen_nsmul_eq_zero_of_piConjugate_eq_zero {c : (ActualPicard K)}
    (hc : (piConjugate K) c = 0) : (19 : ℕ) • c = 0 := by
  have h := congrArg (fun f : AddMonoid.End (ActualPicard K) => f c)
    (pi_comp_piConjugate_nineteen K)
  change (pi K) ((piConjugate K) c) = (19 : ℕ) • c at h
  rw [hc, map_zero] at h
  exact h.symm

end MazurTransfer.Order13FieldPicardCyclotomicNorm
#print axioms MazurTransfer.Order13FieldPicardCyclotomicNorm.rho_cyclotomic
#print axioms MazurTransfer.Order13FieldPicardCyclotomicNorm.pi_comp_piConjugate_nineteen
#print axioms MazurTransfer.Order13FieldPicardCyclotomicNorm.nineteen_nsmul_eq_zero_of_pi_eq_zero


