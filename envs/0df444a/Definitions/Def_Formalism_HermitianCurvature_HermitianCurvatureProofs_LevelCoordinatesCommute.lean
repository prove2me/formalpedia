-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelCoordinatesCommute
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_LevelCoordinatesCommute
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T03:44:31.213702+00:00
-- url     : https://prove2.me/theorems/f2e54d41-27a1-463d-93d2-bc8dc7ac7418
-- title:
--   Level Coordinates Commute
-- statement:
--   Definitions and structural lemmas for Level Coordinates Commute, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LevelCoordinatesCommute.lean

import Definitions.Def_Formalism_HermitianCurvature_StatementNF
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ActualAdjointnessFromHermitian
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeylCellConjTransposeMulApply
import Definitions.Def_Formalism_FormalDegreeBessel_FinalWR
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_Good_comp
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyAt_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_at
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_congr
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_pb_cbi
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx5_end_ext
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_HatData_Good_comp
import Theorems.Thm_Formalism_QuantumDeterminants_commFun
import Theorems.Thm_Formalism_QuantumDeterminants_linOps
import Theorems.Thm_Formalism_QuantumDeterminants_presOps
import Theorems.Thm_Formalism_QuantumDeterminants_weylFun

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Filter Topology
open scoped ContDiff
noncomputable section
namespace Formalism.FourierDecayAlt.P.NFx1.APL
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.NF
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
section Pair
variable {V : Type*} [AddCommGroup V] [Module ℂ V]
theorem mkPair_mul_mkPair (a b c d : Module.End ℂ V) : mkP a b * mkP c d = mkP (a * c) (d * b) := rfl
theorem mkPair_add_mkPair (a b c d : Module.End ℂ V) : mkP a b + mkP c d = mkP (a + c) (b + d) := rfl
theorem mkPair_sub_mkPair (a b c d : Module.End ℂ V) : mkP a b - mkP c d = mkP (a - c) (b - d) := rfl
theorem one_eq_mkPair : (1 : Pr V) = mkP 1 1 := rfl
theorem mkPair_inj (a b c d : Module.End ℂ V) : mkP a b = mkP c d ↔ a = c ∧ b = d := by
  constructor
  · intro h
    exact ⟨congrArg Prod.fst h, congrArg (fun p : Module.End ℂ V × (Module.End ℂ V)ᵐᵒᵖ => MulOpposite.unop p.2) h⟩
  · rintro ⟨rfl, rfl⟩
    rfl
theorem algebraMap_Pr (s : ℂ) :
    algebraMap ℂ (Pr V) s = mkP (algebraMap ℂ (Module.End ℂ V) s) (algebraMap ℂ (Module.End ℂ V) (starRingEnd ℂ s)) := rfl
end Pair
section Ops
variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp]
  [NormedAddCommGroup Wq] [NormedSpace ℂ Wq] {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}
theorem slice_wsm {Φ : Fn k r (Wq →L[ℂ] Wp)} (hΦ : Φ ∈ RadSp k r z z' π π') (g : Mx k r) :
    (fun c' => Φ c' g) ∈ WSm r (Wq →L[ℂ] Wp) := by
  by_cases hg : g ∈ Glev k r (Fin.last r) ∧ 0 < GGl k r z z' g
  · show ContDiffOn ℝ ∞ (fun c' => Φ c' g) (OmX r) ∧ ∀ x, x ∉ OmX r → Φ x g = 0
    refine ⟨fun c hc => ?_, fun c hc => hΦ.1 (c, g) (fun h => hc h.1)⟩
    obtain ⟨U, F, hU, hxU, hF, hΦF⟩ := hΦ.2.1 (c, g) ⟨hc, hg.1, hg.2⟩
    have hcd : ContDiffAt ℝ ∞ (fun c' : Fin r → ℂ => F (c', g)) c :=
      (hF.contDiffAt (hU.mem_nhds hxU)).comp c (contDiffAt_id.prodMk contDiffAt_const)
    have hev : (fun c' => Φ c' g) =ᶠ[𝓝 c] fun c' => F (c', g) := by
      filter_upwards [Qx5.eventually_slice (x := (c, g)) hU hxU] with c' hc'
      exact hΦF (c', g) hc' hg.1
    exact (hcd.congr_of_eventuallyEq hev).contDiffWithinAt
  · rw [Qx5.slice_zero hΦ hg]
    exact (WSm r _).zero_mem
theorem end_ext {A B : Module.End ℂ (RadSp k r z z' π π')}
    (h : ∀ Φ : RadSp k r z z' π π', ((A Φ : RadSp k r z z' π π') : Fn k r (Wq →L[ℂ] Wp)) = (B Φ : Fn k r (Wq →L[ℂ] Wp))) :
    A = B := LinearMap.ext fun Φ => Subtype.ext (h Φ)
variable (X : ActualOps k r z z' π π')
theorem op_coe (l : Fin r) (i : Fin 6) (Φ : RadSp k r z z' π π') :
    ((X.op l i Φ : RadSp k r z z' π π') : Fn k r (Wq →L[ℂ] Wp)) =
      fun c g => opL l i (fun c' => (Φ : Fn k r (Wq →L[ℂ] Wp)) c' g) c := X.op_apply l i Φ
theorem opop_coe (l m : Fin r) (i j : Fin 6) (Φ : RadSp k r z z' π π') :
    (((X.op l i * X.op m j) Φ : RadSp k r z z' π π') : Fn k r (Wq →L[ℂ] Wp)) =
      fun c g => opL l i (opL m j (fun c' => (Φ : Fn k r (Wq →L[ℂ] Wp)) c' g)) c := (op_coe X l i (X.op m j Φ)).trans (by rw [op_coe X m j])
theorem fn_coe (j : Fin 6) (Φ : RadSp k r z z' π π') :
    ((X.fn j Φ : RadSp k r z z' π π') : Fn k r (Wq →L[ℂ] Wp)) =
      fun c g => fnVal k r z z' j g • (Φ : Fn k r (Wq →L[ℂ] Wp)) c g := by
  funext c g
  show _ = fnVal k r z z' j g • (Φ : Fn k r (Wq →L[ℂ] Wp)) c g
  by_cases hx : (c, g) ∈ DomR k r z z'
  · exact X.fn_apply j Φ (c, g) hx
  · obtain ⟨h1, -, -⟩ := (X.fn j Φ).2
    obtain ⟨h2, -, -⟩ := Φ.2
    have e1 : (X.fn j Φ : Fn k r (Wq →L[ℂ] Wp)) c g = 0 := h1 (c, g) hx
    have e2 : (Φ : Fn k r (Wq →L[ℂ] Wp)) c g = 0 := h2 (c, g) hx
    rw [e1, e2, smul_zero]
end Ops
section Ids
variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp]
  [NormedAddCommGroup Wq] [NormedSpace ℂ Wq] {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}
variable (X : ActualOps k r z z' π π')
theorem end_of_slices {A B : Module.End ℂ (RadSp k r z z' π π')}
    (RA RB : ((Fin r → ℂ) → (Wq →L[ℂ] Wp)) → (Fin r → ℂ) → (Wq →L[ℂ] Wp))
    (hA : ∀ Φ : RadSp k r z z' π π', ((A Φ : RadSp k r z z' π π') : Fn k r (Wq →L[ℂ] Wp)) =
      fun c g => RA (fun c' => (Φ : Fn k r (Wq →L[ℂ] Wp)) c' g) c)
    (hB : ∀ Φ : RadSp k r z z' π π', ((B Φ : RadSp k r z z' π π') : Fn k r (Wq →L[ℂ] Wp)) =
      fun c g => RB (fun c' => (Φ : Fn k r (Wq →L[ℂ] Wp)) c' g) c)
    (h : ∀ f ∈ WSm r (Wq →L[ℂ] Wp), RA f = RB f) : A = B := by
  refine end_ext fun Φ => ?_
  rw [hA Φ, hB Φ]
  funext c g
  exact congrFun (h _ (slice_wsm Φ.2 g)) c
theorem coe_add (A B : Module.End ℂ (RadSp k r z z' π π')) (Φ : RadSp k r z z' π π') :
    (((A + B) Φ : RadSp k r z z' π π') : Fn k r (Wq →L[ℂ] Wp)) =
      fun c g => (A Φ : Fn k r (Wq →L[ℂ] Wp)) c g + (B Φ : Fn k r (Wq →L[ℂ] Wp)) c g := rfl
theorem coe_sub (A B : Module.End ℂ (RadSp k r z z' π π')) (Φ : RadSp k r z z' π π') :
    (((A - B) Φ : RadSp k r z z' π π') : Fn k r (Wq →L[ℂ] Wp)) =
      fun c g => (A Φ : Fn k r (Wq →L[ℂ] Wp)) c g - (B Φ : Fn k r (Wq →L[ℂ] Wp)) c g := rfl
theorem weyl_pc (l : Fin r) : X.op l 0 * X.op l 1 = X.op l 1 * X.op l 0 + X.op l 1 := by
  refine end_of_slices (fun f => opL l 0 (opL l 1 f)) (fun f => opL l 1 (opL l 0 f) + opL l 1 f) (fun Φ => opop_coe X l l 0 1 Φ) (fun Φ => ?_) (fun f hf => (weylFun r _ l f hf).2.2.1)
  rw [coe_add, opop_coe X l l 1 0 Φ, op_coe X l 1 Φ] <;> rfl
theorem weyl_pbcb (l : Fin r) : X.op l 3 * X.op l 4 = X.op l 4 * X.op l 3 + X.op l 4 := by
  refine end_of_slices (fun f => opL l 3 (opL l 4 f)) (fun f => opL l 4 (opL l 3 f) + opL l 4 f) (fun Φ => opop_coe X l l 3 4 Φ) (fun Φ => ?_) (fun f hf => (weylFun r _ l f hf).2.2.2.2.2)
  rw [coe_add, opop_coe X l l 4 3 Φ, op_coe X l 4 Φ] <;> rfl
theorem fun_pci (l : Fin r) {f : (Fin r → ℂ) → (Wq →L[ℂ] Wp)} (hf : f ∈ WSm r (Wq →L[ℂ] Wp)) :
    pOp l (ciOp l f) = ciOp l (pOp l f) - ciOp l f := by
  have hg : ciOp l f ∈ WSm r (Wq →L[ℂ] Wp) := presOps r _ l 2 f hf
  have hpg : pOp l (ciOp l f) ∈ WSm r (Wq →L[ℂ] Wp) := presOps r _ l 0 _ hg
  have hcpg : cOp l (pOp l (ciOp l f)) ∈ WSm r (Wq →L[ℂ] Wp) := presOps r _ l 1 _ hpg
  have w1 := (weylFun r _ l _ hg).2.2.1
  have w2 := (weylFun r _ l f hf).1
  have w3 : ciOp l (cOp l (pOp l (ciOp l f))) = pOp l (ciOp l f) := (weylFun r _ l _ hpg).2.1
  have hadd : ciOp l (cOp l (pOp l (ciOp l f)) + f) = ciOp l (cOp l (pOp l (ciOp l f))) + ciOp l f :=
    (linOps r _ l 2 _ f 1 hcpg hf).1
  rw [w2] at w1
  rw [w1, hadd, w3, add_sub_cancel_right]
theorem weyl_pci (l : Fin r) : X.op l 0 * X.op l 2 = X.op l 2 * X.op l 0 - X.op l 2 := by
  refine end_of_slices (fun f => opL l 0 (opL l 2 f)) (fun f => opL l 2 (opL l 0 f) - opL l 2 f) (fun Φ => opop_coe X l l 0 2 Φ) (fun Φ => ?_) (fun f hf => fun_pci l hf)
  rw [coe_sub, opop_coe X l l 2 0 Φ, op_coe X l 2 Φ] <;> rfl
theorem pbOp_cbiOp_eq_cbiOp_pbOp_sub (l : Fin r) {f : (Fin r → ℂ) → (Wq →L[ℂ] Wp)} (hf : f ∈ WSm r (Wq →L[ℂ] Wp)) :
    pbOp l (cbiOp l f) = cbiOp l (pbOp l f) - cbiOp l f := by
  have hg : cbiOp l f ∈ WSm r (Wq →L[ℂ] Wp) := presOps r _ l 5 f hf
  have hpg : pbOp l (cbiOp l f) ∈ WSm r (Wq →L[ℂ] Wp) := presOps r _ l 3 _ hg
  have hcpg : cbOp l (pbOp l (cbiOp l f)) ∈ WSm r (Wq →L[ℂ] Wp) := presOps r _ l 4 _ hpg
  have w1 := (weylFun r _ l _ hg).2.2.2.2.2
  have w2 := (weylFun r _ l f hf).2.2.2.1
  have w3 : cbiOp l (cbOp l (pbOp l (cbiOp l f))) = pbOp l (cbiOp l f) := (weylFun r _ l _ hpg).2.2.2.2.1
  have hadd : cbiOp l (cbOp l (pbOp l (cbiOp l f)) + f) = cbiOp l (cbOp l (pbOp l (cbiOp l f))) + cbiOp l f :=
    (linOps r _ l 5 _ f 1 hcpg hf).1
  rw [w2] at w1
  rw [w1, hadd, w3, add_sub_cancel_right]
theorem weyl_pbcbi (l : Fin r) : X.op l 3 * X.op l 5 = X.op l 5 * X.op l 3 - X.op l 5 := by
  refine end_of_slices (fun f => opL l 3 (opL l 5 f)) (fun f => opL l 5 (opL l 3 f) - opL l 5 f) (fun Φ => opop_coe X l l 3 5 Φ) (fun Φ => ?_) (fun f hf => pbOp_cbiOp_eq_cbiOp_pbOp_sub l hf)
  rw [coe_sub, opop_coe X l l 5 3 Φ, op_coe X l 5 Φ] <;> rfl
theorem comm_ops (l m : Fin r) (i j : Fin 6) (h : l ≠ m ∨ (holoIdx i ↔ ¬ holoIdx j)) :
    X.op l i * X.op m j = X.op m j * X.op l i := end_of_slices (fun f => opL l i (opL m j f)) (fun f => opL m j (opL l i f))
    (fun Φ => opop_coe X l m i j Φ) (fun Φ => opop_coe X m l j i Φ) (fun f hf => commFun r _ l m i j f hf h)
theorem inv_ops (l : Fin r) : X.op l 1 * X.op l 2 = 1 ∧ X.op l 2 * X.op l 1 = 1 ∧
    X.op l 4 * X.op l 5 = 1 ∧ X.op l 5 * X.op l 4 = 1 := ⟨end_of_slices (A := X.op l 1 * X.op l 2) (B := 1) (fun f => opL l 1 (opL l 2 f)) (fun f => f)
      (fun Φ => opop_coe X l l 1 2 Φ) (fun Φ => rfl) (fun f hf => (weylFun r _ l f hf).1),
    end_of_slices (A := X.op l 2 * X.op l 1) (B := 1) (fun f => opL l 2 (opL l 1 f)) (fun f => f)
      (fun Φ => opop_coe X l l 2 1 Φ) (fun Φ => rfl) (fun f hf => (weylFun r _ l f hf).2.1),
    end_of_slices (A := X.op l 4 * X.op l 5) (B := 1) (fun f => opL l 4 (opL l 5 f)) (fun f => f)
      (fun Φ => opop_coe X l l 4 5 Φ) (fun Φ => rfl) (fun f hf => (weylFun r _ l f hf).2.2.2.1),
    end_of_slices (A := X.op l 5 * X.op l 4) (B := 1) (fun f => opL l 5 (opL l 4 f)) (fun f => f)
      (fun Φ => opop_coe X l l 5 4 Φ) (fun Φ => rfl) (fun f hf => (weylFun r _ l f hf).2.2.2.2.1)⟩
theorem op_fn (l : Fin r) (i j : Fin 6) : X.op l i * X.fn j = X.fn j * X.op l i := by
  refine end_ext fun Φ => ?_
  have e1 := op_coe X l i (X.fn j Φ)
  have e2 := fn_coe X j (X.op l i Φ)
  rw [fn_coe X j Φ] at e1
  rw [op_coe X l i Φ] at e2
  refine e1.trans (Eq.trans ?_ e2.symm)
  funext c g
  have := (linOps r _ l i (fun c' => (Φ : Fn k r (Wq →L[ℂ] Wp)) c' g) 0 (fnVal k r z z' j g) (slice_wsm Φ.2 g)
    (WSm r _).zero_mem).2
  exact congrFun this c
def multiplicationOperator (A : Module.End ℂ (RadSp k r z z' π π')) (a : (Fin r → ℂ) → Mx k r → ℂ) : Prop :=
  ∀ Φ : RadSp k r z z' π π', ((A Φ : RadSp k r z z' π π') : Fn k r (Wq →L[ℂ] Wp)) =
    fun c g => a c g • (Φ : Fn k r (Wq →L[ℂ] Wp)) c g
theorem multiplicationOperator.comm {A B : Module.End ℂ (RadSp k r z z' π π')} {a b : (Fin r → ℂ) → Mx k r → ℂ}
    (hA : multiplicationOperator A a) (hB : multiplicationOperator B b) : A * B = B * A := by
  refine end_ext fun Φ => ?_
  have e1 := hA (B Φ)
  have e2 := hB (A Φ)
  rw [hB Φ] at e1
  rw [hA Φ] at e2
  refine e1.trans (Eq.trans ?_ e2.symm)
  funext c g
  exact smul_comm (a c g) (b c g) _
theorem multiplicationOperator.one {A B : Module.End ℂ (RadSp k r z z' π π')} {a b : (Fin r → ℂ) → Mx k r → ℂ}
    (hA : multiplicationOperator A a) (hB : multiplicationOperator B b) (h : ∀ c g, (c, g) ∈ DomR k r z z' → a c g * b c g = 1) : A * B = 1 := by
  refine end_ext fun Φ => ?_
  have e1 := hA (B Φ)
  rw [hB Φ] at e1
  refine e1.trans ?_
  funext c g
  show a c g • b c g • (Φ : Fn k r (Wq →L[ℂ] Wp)) c g = (Φ : Fn k r (Wq →L[ℂ] Wp)) c g
  by_cases hx : (c, g) ∈ DomR k r z z'
  · rw [smul_smul, h c g hx, one_smul]
  · obtain ⟨h0, -, -⟩ := Φ.2
    have e : (Φ : Fn k r (Wq →L[ℂ] Wp)) c g = 0 := h0 (c, g) hx
    rw [e, smul_zero, smul_zero]
theorem mul_fn (j : Fin 6) : multiplicationOperator (X.fn j) (fun _ g => fnVal k r z z' j g) := fun Φ => fn_coe X j Φ
theorem mul_c (l : Fin r) : multiplicationOperator (X.op l 1) (fun c _ => c l) := fun Φ => op_coe X l 1 Φ
theorem mul_ci (l : Fin r) : multiplicationOperator (X.op l 2) (fun c _ => (c l)⁻¹) := fun Φ => op_coe X l 2 Φ
theorem mul_cb (l : Fin r) : multiplicationOperator (X.op l 4) (fun c _ => star (c l)) := fun Φ => op_coe X l 4 Φ
theorem mul_cbi (l : Fin r) : multiplicationOperator (X.op l 5) (fun c _ => (star (c l))⁻¹) := fun Φ => op_coe X l 5 Φ
theorem fn_inv (hT : 0 ≤ Tz k r z * Tz k r z') :
    X.fn 0 * X.fn 1 = 1 ∧ X.fn 1 * X.fn 0 = 1 ∧ X.fn 2 * X.fn 3 = 1 ∧ X.fn 3 * X.fn 2 = 1 ∧
    X.fn 4 * X.fn 5 = 1 ∧ X.fn 5 * X.fn 4 = 1 := by
  have hz : ∀ g, 0 < GGl k r z z' g → zetaL k r z z' (Fin.last r) g ≠ 0 := fun g hg => Qx5.zeta_ne hT hg
  have hzb : ∀ g, 0 < GGl k r z z' g → star (zetaL k r z z' (Fin.last r) g) ≠ 0 :=
    fun g hg => star_ne_zero.2 (hz g hg)
  have hG : ∀ g, 0 < GGl k r z z' g → ((GGl k r z z' g : ℝ) : ℂ) ≠ 0 :=
    fun g hg => Complex.ofReal_ne_zero.2 hg.ne'
  refine ⟨(mul_fn X 0).one (mul_fn X 1) fun c g hx => ?_, (mul_fn X 1).one (mul_fn X 0) fun c g hx => ?_,
    (mul_fn X 2).one (mul_fn X 3) fun c g hx => ?_, (mul_fn X 3).one (mul_fn X 2) fun c g hx => ?_,
    (mul_fn X 4).one (mul_fn X 5) fun c g hx => ?_, (mul_fn X 5).one (mul_fn X 4) fun c g hx => ?_⟩
  · exact mul_inv_cancel₀ (hz g hx.2.2)
  · exact inv_mul_cancel₀ (hz g hx.2.2)
  · exact mul_inv_cancel₀ (hzb g hx.2.2)
  · exact inv_mul_cancel₀ (hzb g hx.2.2)
  · exact mul_inv_cancel₀ (hG g hx.2.2)
  · exact inv_mul_cancel₀ (hG g hx.2.2)
theorem fn_GG : X.fn 4 = X.fn 0 * X.fn 2 - algebraMap ℂ (Module.End ℂ (RadSp k r z z' π π'))
    ((Tz k r z * Tz k r z' : ℝ) : ℂ) := by
  refine end_ext fun Φ => ?_
  rw [coe_sub, Module.End.mul_apply, fn_coe, fn_coe, fn_coe, Module.algebraMap_end_apply]
  funext c g
  show fnVal k r z z' 4 g • (Φ : Fn k r (Wq →L[ℂ] Wp)) c g =
    fnVal k r z z' 0 g • fnVal k r z z' 2 g • (Φ : Fn k r (Wq →L[ℂ] Wp)) c g -
      ((Tz k r z * Tz k r z' : ℝ) : ℂ) • (Φ : Fn k r (Wq →L[ℂ] Wp)) c g
  rw [smul_smul, ← sub_smul]
  congr 1
  simp only [fnVal, GGl, Complex.mul_conj, Complex.ofReal_sub, Complex.ofReal_mul, Complex.star_def]
end Ids
section Pre
variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp]
  [NormedAddCommGroup Wq] [NormedSpace ℂ Wq] {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}
variable (X : ActualOps k r z z' π π')
theorem hol_03 : holoIdx (0 : Fin 6) ↔ ¬ holoIdx (3 : Fin 6) := by
  unfold holoIdx
  decide
theorem hol_04 : holoIdx (0 : Fin 6) ↔ ¬ holoIdx (4 : Fin 6) := by
  unfold holoIdx
  decide
theorem hol_05 : holoIdx (0 : Fin 6) ↔ ¬ holoIdx (5 : Fin 6) := by
  unfold holoIdx
  decide
theorem hol_31 : holoIdx (3 : Fin 6) ↔ ¬ holoIdx (1 : Fin 6) := by
  unfold holoIdx
  decide
theorem hol_32 : holoIdx (3 : Fin 6) ↔ ¬ holoIdx (2 : Fin 6) := by
  unfold holoIdx
  decide
theorem hol_13 : holoIdx (1 : Fin 6) ↔ ¬ holoIdx (3 : Fin 6) := by
  unfold holoIdx
  decide
theorem hol_23 : holoIdx (2 : Fin 6) ↔ ¬ holoIdx (3 : Fin 6) := by
  unfold holoIdx
  decide
theorem hol_40 : holoIdx (4 : Fin 6) ↔ ¬ holoIdx (0 : Fin 6) := by
  unfold holoIdx
  decide
theorem hol_50 : holoIdx (5 : Fin 6) ↔ ¬ holoIdx (0 : Fin 6) := by
  unfold holoIdx
  decide
theorem pair_comm {x y : Pr (RadSp k r z z' π π')}
    (hx : ∃ (A : Module.End ℂ (RadSp k r z z' π π')) (a : (Fin r → ℂ) → Mx k r → ℂ)
      (B : Module.End ℂ (RadSp k r z z' π π')) (b : (Fin r → ℂ) → Mx k r → ℂ),
      multiplicationOperator A a ∧ multiplicationOperator B b ∧ x = mkP A B)
    (hy : ∃ (A : Module.End ℂ (RadSp k r z z' π π')) (a : (Fin r → ℂ) → Mx k r → ℂ)
      (B : Module.End ℂ (RadSp k r z z' π π')) (b : (Fin r → ℂ) → Mx k r → ℂ),
      multiplicationOperator A a ∧ multiplicationOperator B b ∧ y = mkP A B) : x * y = y * x := by
  obtain ⟨A, a, B, b, hA, hB, rfl⟩ := hx
  obtain ⟨C, c, D, d, hC, hD, rfl⟩ := hy
  rw [mkPair_mul_mkPair, mkPair_mul_mkPair, multiplicationOperator.comm hA hC, multiplicationOperator.comm hD hB]
theorem mulPair_of_mem (w : Pr (RadSp k r z z' π π'))
    (hw : w ∈ Set.range (fun l => mkP (X.op l 1) (X.op l 4)) ∪ Set.range (fun l => mkP (X.op l 2) (X.op l 5)) ∪
      Set.range (fun l => mkP (X.op l 4) (X.op l 1)) ∪ Set.range (fun l => mkP (X.op l 5) (X.op l 2)) ∪
      {mkP (X.fn 0) (X.fn 2), mkP (X.fn 1) (X.fn 3), mkP (X.fn 2) (X.fn 0), mkP (X.fn 3) (X.fn 1),
        mkP (X.fn 4) (X.fn 4), mkP (X.fn 5) (X.fn 5)}) :
    ∃ (A : Module.End ℂ (RadSp k r z z' π π')) (a : (Fin r → ℂ) → Mx k r → ℂ)
      (B : Module.End ℂ (RadSp k r z z' π π')) (b : (Fin r → ℂ) → Mx k r → ℂ),
      multiplicationOperator A a ∧ multiplicationOperator B b ∧ w = mkP A B := by
  rcases hw with ((((⟨l, rfl⟩ | ⟨l, rfl⟩) | ⟨l, rfl⟩) | ⟨l, rfl⟩) | hw)
  · exact ⟨_, _, _, _, mul_c X l, mul_cb X l, rfl⟩
  · exact ⟨_, _, _, _, mul_ci X l, mul_cbi X l, rfl⟩
  · exact ⟨_, _, _, _, mul_cb X l, mul_c X l, rfl⟩
  · exact ⟨_, _, _, _, mul_cbi X l, mul_ci X l, rfl⟩
  · rcases hw with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨_, _, _, _, mul_fn X 0, mul_fn X 2, rfl⟩
    · exact ⟨_, _, _, _, mul_fn X 1, mul_fn X 3, rfl⟩
    · exact ⟨_, _, _, _, mul_fn X 2, mul_fn X 0, rfl⟩
    · exact ⟨_, _, _, _, mul_fn X 3, mul_fn X 1, rfl⟩
    · exact ⟨_, _, _, _, mul_fn X 4, mul_fn X 4, rfl⟩
    · exact ⟨_, _, _, _, mul_fn X 5, mul_fn X 5, rfl⟩
theorem f_p_c (l m : Fin r) : mkP (X.op l 0) (-X.op l 3) * mkP (X.op m 1) (X.op m 4) =
    mkP (X.op m 1) (X.op m 4) * mkP (X.op l 0) (-X.op l 3) + (if l = m then mkP (X.op m 1) (X.op m 4) else 0) := by
  rw [mkPair_mul_mkPair, mkPair_mul_mkPair]
  split_ifs with h
  · subst h
    rw [mkPair_add_mkPair, mkPair_inj]
    refine ⟨weyl_pc X l, ?_⟩
    rw [mul_neg, neg_mul, weyl_pbcb X l]
    abel
  · rw [add_zero, mkPair_inj]
    exact ⟨comm_ops X l m 0 1 (Or.inl h), by rw [mul_neg, neg_mul, comm_ops X m l 4 3 (Or.inl (Ne.symm h))]⟩
theorem f_p_ci (l m : Fin r) : mkP (X.op l 0) (-X.op l 3) * mkP (X.op m 2) (X.op m 5) =
    mkP (X.op m 2) (X.op m 5) * mkP (X.op l 0) (-X.op l 3) - (if l = m then mkP (X.op m 2) (X.op m 5) else 0) := by
  rw [mkPair_mul_mkPair, mkPair_mul_mkPair]
  split_ifs with h
  · subst h
    rw [mkPair_sub_mkPair, mkPair_inj]
    refine ⟨weyl_pci X l, ?_⟩
    rw [mul_neg, neg_mul, weyl_pbcbi X l]
    abel
  · rw [sub_zero, mkPair_inj]
    exact ⟨comm_ops X l m 0 2 (Or.inl h), by rw [mul_neg, neg_mul, comm_ops X m l 5 3 (Or.inl (Ne.symm h))]⟩
theorem f_pb_cb (l m : Fin r) : mkP (X.op l 3) (-X.op l 0) * mkP (X.op m 4) (X.op m 1) =
    mkP (X.op m 4) (X.op m 1) * mkP (X.op l 3) (-X.op l 0) + (if l = m then mkP (X.op m 4) (X.op m 1) else 0) := by
  rw [mkPair_mul_mkPair, mkPair_mul_mkPair]
  split_ifs with h
  · subst h
    rw [mkPair_add_mkPair, mkPair_inj]
    refine ⟨weyl_pbcb X l, ?_⟩
    rw [mul_neg, neg_mul, weyl_pc X l]
    abel
  · rw [add_zero, mkPair_inj]
    exact ⟨comm_ops X l m 3 4 (Or.inl h), by rw [mul_neg, neg_mul, comm_ops X m l 1 0 (Or.inl (Ne.symm h))]⟩
theorem f_pb_cbi (l m : Fin r) : mkP (X.op l 3) (-X.op l 0) * mkP (X.op m 5) (X.op m 2) =
    mkP (X.op m 5) (X.op m 2) * mkP (X.op l 3) (-X.op l 0) - (if l = m then mkP (X.op m 5) (X.op m 2) else 0) := by
  rw [mkPair_mul_mkPair, mkPair_mul_mkPair]
  split_ifs with h
  · subst h
    rw [mkPair_sub_mkPair, mkPair_inj]
    refine ⟨weyl_pbcbi X l, ?_⟩
    rw [mul_neg, neg_mul, weyl_pci X l]
    abel
  · rw [sub_zero, mkPair_inj]
    exact ⟨comm_ops X l m 3 5 (Or.inl h), by rw [mul_neg, neg_mul, comm_ops X m l 2 0 (Or.inl (Ne.symm h))]⟩
theorem f_comm (l m : Fin r) (i i' j j' : Fin 6) (h1 : X.op l i * X.op m j = X.op m j * X.op l i)
    (h2 : X.op m j' * X.op l i' = X.op l i' * X.op m j') :
    mkP (X.op l i) (-X.op l i') * mkP (X.op m j) (X.op m j') = mkP (X.op m j) (X.op m j') * mkP (X.op l i) (-X.op l i') := by
  rw [mkPair_mul_mkPair, mkPair_mul_mkPair, mkPair_inj]
  exact ⟨h1, by rw [mul_neg, neg_mul, h2]⟩
theorem f_fn (l : Fin r) (i i' j j' : Fin 6) :
    mkP (X.op l i) (-X.op l i') * mkP (X.fn j) (X.fn j') = mkP (X.fn j) (X.fn j') * mkP (X.op l i) (-X.op l i') := by
  rw [mkPair_mul_mkPair, mkPair_mul_mkPair, mkPair_inj]
  exact ⟨op_fn X l i j, by rw [mul_neg, neg_mul, op_fn X l i' j']⟩
theorem f_pp (l m : Fin r) (i i' : Fin 6) (h1 : ∀ l m : Fin r, l ≠ m → X.op l i * X.op m i = X.op m i * X.op l i)
    (h2 : ∀ l m : Fin r, l ≠ m → X.op l i' * X.op m i' = X.op m i' * X.op l i') :
    mkP (X.op l i) (-X.op l i') * mkP (X.op m i) (-X.op m i') = mkP (X.op m i) (-X.op m i') * mkP (X.op l i) (-X.op l i') := by
  rw [mkPair_mul_mkPair, mkPair_mul_mkPair, mkPair_inj]
  by_cases h : l = m
  · subst h
    exact ⟨rfl, rfl⟩
  · exact ⟨h1 l m h, by rw [neg_mul_neg, neg_mul_neg, h2 m l (Ne.symm h)]⟩
theorem f_ppb (l m : Fin r) : mkP (X.op l 0) (-X.op l 3) * mkP (X.op m 3) (-X.op m 0) =
    mkP (X.op m 3) (-X.op m 0) * mkP (X.op l 0) (-X.op l 3) := by
  rw [mkPair_mul_mkPair, mkPair_mul_mkPair, mkPair_inj]
  exact ⟨comm_ops X l m 0 3 (Or.inr hol_03), by rw [neg_mul_neg, neg_mul_neg, comm_ops X m l 0 3 (Or.inr hol_03)]⟩
theorem f_GG : mkP (X.fn 4) (X.fn 4) = mkP (X.fn 0) (X.fn 2) * mkP (X.fn 2) (X.fn 0) -
    algebraMap ℂ (Pr (RadSp k r z z' π π')) ((Tz k r z * Tz k r z' : ℝ) : ℂ) := by
  rw [mkPair_mul_mkPair, algebraMap_Pr, mkPair_sub_mkPair, Complex.conj_ofReal, ← fn_GG X]
def preOf (X : ActualOps k r z z' π π') (hT : 0 ≤ Tz k r z * Tz k r z') : PreLevel (Pr (RadSp k r z z' π π')) r where
  p := fun l => mkP (X.op l 0) (-X.op l 3)
  pb := fun l => mkP (X.op l 3) (-X.op l 0)
  c := fun l => mkP (X.op l 1) (X.op l 4)
  ci := fun l => mkP (X.op l 2) (X.op l 5)
  cb := fun l => mkP (X.op l 4) (X.op l 1)
  cbi := fun l => mkP (X.op l 5) (X.op l 2)
  ζ := mkP (X.fn 0) (X.fn 2)
  ζi := mkP (X.fn 1) (X.fn 3)
  ζb := mkP (X.fn 2) (X.fn 0)
  ζbi := mkP (X.fn 3) (X.fn 1)
  GG := mkP (X.fn 4) (X.fn 4)
  GGi := mkP (X.fn 5) (X.fn 5)
  TT := ((Tz k r z * Tz k r z' : ℝ) : ℂ)
  fns_comm := fun x hx y hy => pair_comm (mulPair_of_mem X x hx) (mulPair_of_mem X y hy)
  c_ci := fun l => by rw [mkPair_mul_mkPair, one_eq_mkPair, mkPair_inj]; exact ⟨(inv_ops X l).1, (inv_ops X l).2.2.2⟩
  ci_c := fun l => by rw [mkPair_mul_mkPair, one_eq_mkPair, mkPair_inj]; exact ⟨(inv_ops X l).2.1, (inv_ops X l).2.2.1⟩
  cb_cbi := fun l => by rw [mkPair_mul_mkPair, one_eq_mkPair, mkPair_inj]; exact ⟨(inv_ops X l).2.2.1, (inv_ops X l).2.1⟩
  cbi_cb := fun l => by rw [mkPair_mul_mkPair, one_eq_mkPair, mkPair_inj]; exact ⟨(inv_ops X l).2.2.2, (inv_ops X l).1⟩
  ζ_ζi := by rw [mkPair_mul_mkPair, one_eq_mkPair, mkPair_inj]; exact ⟨(fn_inv X hT).1, (fn_inv X hT).2.2.2.1⟩
  ζi_ζ := by rw [mkPair_mul_mkPair, one_eq_mkPair, mkPair_inj]; exact ⟨(fn_inv X hT).2.1, (fn_inv X hT).2.2.1⟩
  ζb_ζbi := by rw [mkPair_mul_mkPair, one_eq_mkPair, mkPair_inj]; exact ⟨(fn_inv X hT).2.2.1, (fn_inv X hT).2.1⟩
  ζbi_ζb := by rw [mkPair_mul_mkPair, one_eq_mkPair, mkPair_inj]; exact ⟨(fn_inv X hT).2.2.2.1, (fn_inv X hT).1⟩
  GG_GGi := by rw [mkPair_mul_mkPair, one_eq_mkPair, mkPair_inj]; exact ⟨(fn_inv X hT).2.2.2.2.1, (fn_inv X hT).2.2.2.2.2⟩
  GGi_GG := by rw [mkPair_mul_mkPair, one_eq_mkPair, mkPair_inj]; exact ⟨(fn_inv X hT).2.2.2.2.2, (fn_inv X hT).2.2.2.2.1⟩
  GG_def := f_GG X
  p_c := f_p_c X
  p_ci := f_p_ci X
  p_cb := fun l m => f_comm X l m 0 3 4 1 (comm_ops X l m 0 4 (Or.inr hol_04)) (comm_ops X m l 1 3 (Or.inr hol_13))
  p_cbi := fun l m => f_comm X l m 0 3 5 2 (comm_ops X l m 0 5 (Or.inr hol_05)) (comm_ops X m l 2 3 (Or.inr hol_23))
  p_ζ := fun l => f_fn X l 0 3 0 2
  p_ζi := fun l => f_fn X l 0 3 1 3
  p_ζb := fun l => f_fn X l 0 3 2 0
  p_ζbi := fun l => f_fn X l 0 3 3 1
  p_GG := fun l => f_fn X l 0 3 4 4
  p_GGi := fun l => f_fn X l 0 3 5 5
  pb_cb := f_pb_cb X
  pb_cbi := f_pb_cbi X
  pb_c := fun l m => f_comm X l m 3 0 1 4 (comm_ops X l m 3 1 (Or.inr hol_31)) (comm_ops X m l 4 0 (Or.inr hol_40))
  pb_ci := fun l m => f_comm X l m 3 0 2 5 (comm_ops X l m 3 2 (Or.inr hol_32)) (comm_ops X m l 5 0 (Or.inr hol_50))
  pb_ζ := fun l => f_fn X l 3 0 0 2
  pb_ζi := fun l => f_fn X l 3 0 1 3
  pb_ζb := fun l => f_fn X l 3 0 2 0
  pb_ζbi := fun l => f_fn X l 3 0 3 1
  pb_GG := fun l => f_fn X l 3 0 4 4
  pb_GGi := fun l => f_fn X l 3 0 5 5
  p_p := fun l m => f_pp X l m 0 3 (fun a b h => comm_ops X a b 0 0 (Or.inl h)) (fun a b h => comm_ops X a b 3 3 (Or.inl h))
  p_pb := f_ppb X
  pb_pb := fun l m => f_pp X l m 3 0 (fun a b h => comm_ops X a b 3 3 (Or.inl h)) (fun a b h => comm_ops X a b 0 0 (Or.inl h))
end Pre
end Formalism.FourierDecayAlt.P.NFx1.APL
open Matrix Finset Filter Topology
open scoped ContDiff
noncomputable section
namespace Formalism.FourierDecayAlt.P.NFx1.TC
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.NF
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
section CD
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {i : Fin (r + 1)}
structure CD (k r : ℕ) (i : Fin (r + 1)) (T : (Mx k r → E) → Mx k r → E) : Prop where
  pres : ∀ (U₀ : Set ((Fin r → ℂ) × Mx k r)) (Φ : Fn k r E), SmoothFam k r i U₀ Φ →
    SmoothFam k r i U₀ (fun c => T (Φ c))
  loc : ∀ D : Set (Mx k r), IsOpen D → ∀ f f₂ : Mx k r → E, (∀ x ∈ Glev k r i ∩ D, f x = f₂ x) →
    ∀ x ∈ Glev k r i ∩ D, T f x = T f₂ x
  comm : ∀ U₀ : Set ((Fin r → ℂ) × Mx k r), IsOpen U₀ → ∀ Φ : Fn k r E, SmoothFam k r i U₀ Φ →
    ∀ x ∈ U₀, x.2 ∈ Glev k r i → ∀ v : Fin r → ℂ,
      fderiv ℝ (fun c' => T (Φ c') x.2) x.1 v = T (fun g => fderiv ℝ (fun c' => Φ c' g) x.1 v) x.2
structure CW (k r : ℕ) (i : Fin (r + 1)) (T : (Mx k r → E) → Mx k r → E) : Prop where
  diff : ∀ U₀ : Set ((Fin r → ℂ) × Mx k r), IsOpen U₀ → ∀ Φ : Fn k r E, SmoothFam k r i U₀ Φ →
    ∀ x ∈ U₀, x.2 ∈ Glev k r i → DifferentiableAt ℝ (fun c' => T (Φ c') x.2) x.1
  comm : ∀ U₀ : Set ((Fin r → ℂ) × Mx k r), IsOpen U₀ → ∀ Φ : Fn k r E, SmoothFam k r i U₀ Φ →
    ∀ x ∈ U₀, x.2 ∈ Glev k r i → ∀ v : Fin r → ℂ,
      fderiv ℝ (fun c' => T (Φ c') x.2) x.1 v = T (fun g => fderiv ℝ (fun c' => Φ c' g) x.1 v) x.2
end CD
section Rad
variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp]
  [NormedAddCommGroup Wq] [NormedSpace ℂ Wq] {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}
variable (X : ActualOps k r z z' π π')
end Rad
end Formalism.FourierDecayAlt.P.NFx1.TC


