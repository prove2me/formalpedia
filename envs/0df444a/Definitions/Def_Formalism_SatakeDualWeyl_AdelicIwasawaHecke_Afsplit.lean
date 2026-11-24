-- Prove2me | Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Afsplit
-- name    : Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Afsplit
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-24T12:18:10.801817+00:00
-- url     : https://prove2.me/theorems/4a5b980e-d6cf-4d34-bc79-dd7683b50a43
-- title:
--   Afsplit
-- statement:
--   Definitions and structural lemmas for Afsplit, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Afsplit.lean

import Definitions.Def_Formalism_SatakeDualWeyl_StatementC
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_AfsplitC
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_RationalPointsLeHolds
import Theorems.Thm_Formalism_UG_P_afsplitU_mem
import Theorems.Thm_Formalism_UG_P_afsplitU_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix TensorProduct NumberField IsDedekindDomain
namespace Formalism.UG.P
open Formalism.UG
section Lat
variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]
end Lat
section Int
variable {F : Type} [Field F] [NumberField F] {E : Type} [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F))
local notation "𝔸" => FiniteAdeleRing (𝓞 F) F
lemma prV_tmul_lemma_12 (a : E) (y : 𝔸) : prV (E := E) v (a ⊗ₜ[F] y) = a ⊗ₜ[F] (y v) := by
  first
    | (simp only [prV, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul,
        AlgHom.id_apply]; done)
    | (simp only [prV, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul,
        AlgHom.id_apply]; rfl)
    | simp [prV, evalV]
lemma IE_tmul_lemma_10 (a : E) (b : v.adicCompletion F) :
    afsplitIE v (a ⊗ₜ[F] b) = a ⊗ₜ[F] afsplitF v b := by
  show LinearMap.lTensor E (afsplitI v) (a ⊗ₜ[F] b) = _
  rw [LinearMap.lTensor_tmul]
  try rfl
lemma eps_eq_lemma_2 : afsplitEps E v = (1 : E) ⊗ₜ[F] afsplitF v 1 := by
  show afsplitIE v ((1 : E) ⊗ₜ[F] (1 : v.adicCompletion F)) = _
  exact IE_tmul_lemma_10 v 1 1
lemma prV_IE_lemma (x : E ⊗[F] v.adicCompletion F) : prV (E := E) v (afsplitIE v x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => rw [IE_tmul_lemma_10, prV_tmul_lemma_12, afsplitF_self]
  | add x y hx hy => rw [map_add, map_add, hx, hy]
lemma IE_prV_lemma_3 (x : E ⊗[F] 𝔸) : afsplitIE v (prV (E := E) v x) = afsplitEps E v * x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a y =>
    rw [prV_tmul_lemma_12, IE_tmul_lemma_10, eps_eq_lemma_2, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    congr 1
    ext w
    congr 1
    rw [show (afsplitF v 1 * y) w = afsplitF v 1 w * y w from by first | rfl | simp]
    by_cases h : w = v
    · subst h
      rw [afsplitF_self, afsplitF_self, one_mul]
    · rw [afsplitF_ne v w h, afsplitF_ne v w h, zero_mul]
  | add x y hx hy => rw [map_add, map_add, hx, hy, mul_add]
lemma prV_eps_lemma_4 : prV (E := E) v (afsplitEps E v) = 1 := by
  rw [show afsplitEps E v = afsplitIE v 1 from rfl, prV_IE_lemma]
variable {n : Type} [Fintype n] [DecidableEq n]
end Int
section Iso
variable {F : Type} [Field F] [NumberField F] {E : Type} [Field E] [NumberField E] [Algebra F E]
  {n : Type} [Fintype n] [DecidableEq n] (σ : E →ₐ[F] E) (J : Matrix n n E)
  (v : HeightOneSpectrum (𝓞 F))
local notation "𝔸" => FiniteAdeleRing (𝓞 F) F
def afsplitKer : Subgroup (GL n (E ⊗[F] 𝔸)) := UPts σ J 𝔸 ⊓ (bc (n := n) (prV (E := E) v)).ker
lemma sig_tmul_lemma_13 {R : Type} [CommRing R] [Algebra F R] (a : E) (y : R) :
    sigR σ R (a ⊗ₜ[F] y) = σ a ⊗ₜ[F] y := by
  simp [sigR]
lemma prV_sig_lemma_8 (x : E ⊗[F] 𝔸) :
    prV (E := E) v (sigR σ 𝔸 x) = sigR σ (v.adicCompletion F) (prV (E := E) v x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a y => simp only [prV_tmul_lemma_12, sig_tmul_lemma_13]
  | add x y hx hy => simp only [map_add, hx, hy]
theorem afsplit_bc_mem (g : GL n (E ⊗[F] 𝔸)) (hg : g ∈ UPts σ J 𝔸) :
    bc (prV (E := E) v) g ∈ UPts σ J (v.adicCompletion F) := by
  have hg' : cT (sigR σ 𝔸) (g : Matrix n n (E ⊗[F] 𝔸)) * J.map (inclE (F := F) 𝔸) *
      (g : Matrix n n (E ⊗[F] 𝔸)) = J.map (inclE (F := F) 𝔸) := hg
  show cT (sigR σ (v.adicCompletion F)) ((g : Matrix n n (E ⊗[F] 𝔸)).map (prV (E := E) v)) *
      J.map (inclE (F := F) (v.adicCompletion F)) * (g : Matrix n n (E ⊗[F] 𝔸)).map (prV (E := E) v) =
      J.map (inclE (F := F) (v.adicCompletion F))
  have hJ : (J.map (inclE (F := F) 𝔸)).map (prV (E := E) v) = J.map (inclE (F := F) (v.adicCompletion F)) := by
    ext i j
    first
      | (simp only [Matrix.map_apply, inclE, Algebra.TensorProduct.includeLeftRingHom_apply, prV_tmul_lemma_12]; rfl)
      | simp [inclE, prV_tmul_lemma_12]
      | simp [inclE, prV, evalV]
  have hc : (cT (sigR σ 𝔸) (g : Matrix n n (E ⊗[F] 𝔸))).map (prV (E := E) v) =
      cT (sigR σ (v.adicCompletion F)) ((g : Matrix n n (E ⊗[F] 𝔸)).map (prV (E := E) v)) := by
    ext i j
    simp only [cT, Matrix.map_apply, Matrix.transpose_apply, prV_sig_lemma_8]
  rw [← hc, ← hJ, ← Matrix.map_mul, ← Matrix.map_mul, hg']
theorem afsplit_coe_bc_prV (g : GL n (E ⊗[F] 𝔸)) (w : HeightOneSpectrum (𝓞 F)) :
    ((bc (prV (E := E) w) g : GL n (E ⊗[F] w.adicCompletion F)) : Matrix n n (E ⊗[F] w.adicCompletion F)) =
      (g : Matrix n n (E ⊗[F] 𝔸)).map (prV (E := E) w) := rfl
lemma C_map_prV_lemma_5 (M : Matrix n n (E ⊗[F] v.adicCompletion F)) (N : Matrix n n (E ⊗[F] 𝔸)) :
    (afsplitC v M N).map (prV (E := E) v) = M := by
  ext i j
  simp only [afsplitC, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, map_add, map_mul,
    map_sub, map_one, prV_IE_lemma, prV_eps_lemma_4, sub_self, zero_mul, add_zero]
theorem afsplit_ker_mem (g : GL n (E ⊗[F] 𝔸)) (hg : g ∈ UPts σ J 𝔸) :
    afsplitU v 1 g ∈ afsplitKer σ J v := by
  refine Subgroup.mem_inf.mpr ⟨afsplitU_mem v σ J 1 g (Subgroup.one_mem _) hg, ?_⟩
  rw [MonoidHom.mem_ker]
  apply Units.ext
  rw [afsplit_coe_bc_prV]
  exact C_map_prV_lemma_5 v (1 : Matrix n n (E ⊗[F] v.adicCompletion F)) (g : Matrix n n (E ⊗[F] 𝔸))
theorem afsplit_ker_map (k : GL n (E ⊗[F] 𝔸)) (hk : k ∈ afsplitKer σ J v) :
    (k : Matrix n n (E ⊗[F] 𝔸)).map (prV (E := E) v) = 1 := by
  have h2 := (Subgroup.mem_inf.mp hk).2
  rw [MonoidHom.mem_ker] at h2
  rw [← afsplit_coe_bc_prV, h2, Units.val_one]
lemma IE_eps_lemma_6 (x : E ⊗[F] v.adicCompletion F) :
    afsplitIE v x = afsplitEps E v * afsplitIE v x := by
  rw [show afsplitEps E v = afsplitIE v 1 from rfl, ← map_mul, one_mul]
lemma eps_idem_lemma_7 : afsplitEps E v * afsplitEps E v = afsplitEps E v := by
  rw [show afsplitEps E v = afsplitIE v 1 from rfl, ← map_mul, one_mul]
theorem afsplit_left (g : GL n (E ⊗[F] 𝔸)) :
    afsplitU v (bc (prV (E := E) v) g) (afsplitU v 1 g) = g := by
  apply Units.ext
  show afsplitC v ((g : Matrix n n (E ⊗[F] 𝔸)).map (prV (E := E) v))
      (afsplitC v (1 : Matrix n n (E ⊗[F] v.adicCompletion F)) (g : Matrix n n (E ⊗[F] 𝔸))) =
      (g : Matrix n n (E ⊗[F] 𝔸))
  ext i j
  simp only [afsplitC, Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, IE_prV_lemma_3]
  linear_combination IE_eps_lemma_6 v ((1 : Matrix n n (E ⊗[F] v.adicCompletion F)) i j) +
    (g : Matrix n n (E ⊗[F] 𝔸)) i j * eps_idem_lemma_7 (E := E) v
theorem afsplit_right1 (h : GL n (E ⊗[F] v.adicCompletion F)) (k : GL n (E ⊗[F] 𝔸)) :
    bc (prV (E := E) v) (afsplitU v h k) = h := by
  apply Units.ext
  rw [afsplit_coe_bc_prV]
  exact C_map_prV_lemma_5 v (h : Matrix n n (E ⊗[F] v.adicCompletion F)) (k : Matrix n n (E ⊗[F] 𝔸))
theorem afsplit_right2 (h : GL n (E ⊗[F] v.adicCompletion F)) (k : GL n (E ⊗[F] 𝔸))
    (hk : k ∈ afsplitKer σ J v) : afsplitU v 1 (afsplitU v h k) = k := by
  have hK := afsplit_ker_map σ J v k hk
  apply Units.ext
  show afsplitC v (1 : Matrix n n (E ⊗[F] v.adicCompletion F))
      (afsplitC v (h : Matrix n n (E ⊗[F] v.adicCompletion F)) (k : Matrix n n (E ⊗[F] 𝔸))) =
      (k : Matrix n n (E ⊗[F] 𝔸))
  ext i j
  have e1 : (1 : Matrix n n (E ⊗[F] v.adicCompletion F)) i j =
      prV (E := E) v ((k : Matrix n n (E ⊗[F] 𝔸)) i j) := by
    rw [← hK, Matrix.map_apply]
  simp only [afsplitC, Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
  rw [e1, IE_prV_lemma_3]
  linear_combination IE_eps_lemma_6 v ((h : Matrix n n (E ⊗[F] v.adicCompletion F)) i j) +
    (k : Matrix n n (E ⊗[F] 𝔸)) i j * eps_idem_lemma_7 (E := E) v
def afsplitE : UPts σ J 𝔸 ≃* (UPts σ J (v.adicCompletion F) × afsplitKer σ J v) where
  toFun g := (⟨bc (prV (E := E) v) g, afsplit_bc_mem σ J v g g.2⟩,
    ⟨afsplitU v 1 g, afsplit_ker_mem σ J v g g.2⟩)
  invFun p := ⟨afsplitU v p.1 p.2, afsplitU_mem v σ J _ _ p.1.2 (Subgroup.mem_inf.mp p.2.2).1⟩
  left_inv g := Subtype.ext (afsplit_left v (g : GL n (E ⊗[F] 𝔸)))
  right_inv p := Prod.ext (Subtype.ext (afsplit_right1 v _ _))
    (Subtype.ext (afsplit_right2 σ J v _ _ p.2.2))
  map_mul' g g' := by
    refine Prod.ext (Subtype.ext (map_mul _ _ _)) (Subtype.ext ?_)
    change afsplitU v 1 ((g : GL n (E ⊗[F] 𝔸)) * (g' : GL n (E ⊗[F] 𝔸))) =
      afsplitU v 1 (g : GL n (E ⊗[F] 𝔸)) * afsplitU v 1 (g' : GL n (E ⊗[F] 𝔸))
    rw [← afsplitU_mul, one_mul]
end Iso
end Formalism.UG.P


