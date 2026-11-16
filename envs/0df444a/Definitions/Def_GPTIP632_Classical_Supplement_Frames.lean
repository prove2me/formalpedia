-- Prove2me | Definitions.Def_GPTIP632_Classical_Supplement_Frames
-- name    : GPTIP632_Classical_Supplement_Frames
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T20:10:28.231088+00:00
-- url     : https://prove2.me/theorems/d813f9d3-488a-4add-b6d6-e93c39554018
-- title:
--   Hermitian coordinate frames and transport of state cones
-- statement:
--   A Hermitian frame is a finite family of Hermitian matrices, linearly independent over the complex numbers, whose real span contains the identity. A real coordinate vector $x$ represents $H(x)=\sum_i x_i\beta_i$. Its cone is $H(x)\succeq0$ and its unit is $\operatorname{Tr}H(x)$. Quantum systems use a full Hermitian basis; classical systems use diagonal matrix units, and classical–quantum systems use their tensor products. Frames themselves need not span a full matrix algebra; the later tree construction specifies the intended full quantum and block diagonal algebras. Kronecker products compose frames. Transport by an invertible real matrix $T$ replaces a cone $C$ by $T^{-1}(C)$ and its unit $u$ by $uT$. The identity-span condition ensures the cone is generating; no quantum restriction is imposed on arbitrary systems of the ambient published Theory.
-- source:
--   Kishor Bharti, Beyond IP = PSPACE and QIP = PSPACE: Interactive Proofs in Arbitrary Physical Theories, STOC 2027 submission #632 (October 2026), source.pdf SHA-256 ebbc45027e7a3b48cbfb1a2deb89e9a7d8374373b23763680b948fda16cf4da7, pp.14, 17–19, 22–23, 28, 32–35 (PDF pp.16, 19–21, 24–25, 30, 34–37), Examples B.3, B.5, B.17–B.23, Definitions D.3–D.4, F.1, §G

import Mathlib
import Definitions.Def_GPTIP632_Classical_Systems

set_option autoImplicit false

/-!
# Systems presented by Hermitian matrices, and transported systems

Kishor Bharti, *Beyond IP = PSPACE and QIP = PSPACE: Interactive Proofs in Arbitrary Physical
Theories*, STOC 2027 submission #632 (October 2026), Example B.3 (p.14, PDF p.16), Example B.18
(p.18, PDF p.20), Example B.23 (p.19, PDF p.21).

A **Hermitian frame** is a family `β_p` (`p ∈ ι`) of Hermitian `D × D` complex matrices, linearly
independent over `ℂ`, whose real span contains the identity. Its system has `V = ι → ℝ`, the cone of
coordinate vectors `x` with `∑_p x_p β_p` positive semidefinite, and the unit effect
`x ↦ Tr ∑_p x_p β_p`. Quantum systems (`β` a real basis of `Herm_d(ℂ)`), classical systems (`β` the
diagonal matrix units) and their composites (Kronecker products of frames) are of this form.

A **transported system** has the cone `{x : T x ∈ V_S⁺}` and unit `u_S ∘ T` for an invertible
matrix `T` (Example B.23: cones and units transported through `id ⊗ L_v^{⊗c}`).
-/

noncomputable section

namespace GPTIP632.Classical.Supplement

open GPTIP632.Classical Matrix
open scoped Kronecker ComplexOrder

/-- A **Hermitian frame**: Hermitian matrices `β_p`, linearly independent over `ℂ`, whose real span
contains the identity matrix. -/
structure HermFrame (ι D : Type) [Fintype ι] [DecidableEq ι] [Fintype D] [DecidableEq D] where
  β : ι → Matrix D D ℂ
  herm : ∀ p, (β p).IsHermitian
  inj : ∀ y : ι → ℂ, ∑ p, y p • β p = 0 → y = 0
  one_mem : ∃ η : ι → ℝ, ∑ p, ((η p : ℝ) : ℂ) • β p = 1

namespace HermFrame

variable {ι D : Type} [Fintype ι] [DecidableEq ι] [Fintype D] [DecidableEq D] (F : HermFrame ι D)

/-- The Hermitian matrix `∑_p x_p β_p` of a real coordinate vector `x`. -/
def hmat (x : ι → ℝ) : Matrix D D ℂ := ∑ p, ((x p : ℝ) : ℂ) • F.β p

lemma hmat_herm (x : ι → ℝ) : (F.hmat x).IsHermitian := by
  unfold hmat IsHermitian
  rw [conjTranspose_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [conjTranspose_smul, (F.herm p).eq, Complex.star_def, Complex.conj_ofReal]

lemma hmat_add (x y : ι → ℝ) : F.hmat (x + y) = F.hmat x + F.hmat y := by
  simp [hmat, add_smul, Finset.sum_add_distrib]

lemma hmat_smul (c : ℝ) (x : ι → ℝ) : F.hmat (c • x) = (c : ℂ) • F.hmat x := by
  simp only [hmat, Finset.smul_sum, smul_smul, Pi.smul_apply, smul_eq_mul, Complex.ofReal_mul]

lemma hmat_zero : F.hmat 0 = 0 := by simp [hmat]

lemma hmat_neg (x : ι → ℝ) : F.hmat (-x) = -F.hmat x := by
  simp [hmat, Finset.sum_neg_distrib]

lemma hmat_sub (x y : ι → ℝ) : F.hmat (x - y) = F.hmat x - F.hmat y := by
  simp [hmat, sub_smul, Finset.sum_sub_distrib]

lemma hmat_inj {x : ι → ℝ} (h : F.hmat x = 0) : x = 0 := by
  have := F.inj (fun p => ((x p : ℝ) : ℂ)) h
  funext p
  have hp := congrFun this p
  simpa using hp

lemma continuous_hmat : Continuous F.hmat := by
  unfold hmat
  fun_prop

/-- The cone of the frame: coordinate vectors whose matrix is positive semidefinite. -/
def cone : Set (ι → ℝ) := {x | (F.hmat x).PosSemidef}

/-- The unit effect: `u_p = Re Tr β_p`, so `u(x) = Tr ∑_p x_p β_p`. -/
def unit : ι → ℝ := fun p => ((F.β p).trace).re

lemma pair_unit (x : ι → ℝ) : pair F.unit x = ((F.hmat x).trace).re := by
  simp [pair, unit, hmat, trace_sum, trace_smul, mul_comm]

open scoped ComplexOrder in
lemma cone_closed : IsClosed F.cone := by
  have : F.cone = ⋂ v : D → ℂ, {x | 0 ≤ star v ⬝ᵥ (F.hmat x *ᵥ v)} := by
    ext x
    simp only [cone, Set.mem_ofPred_eq, Set.mem_iInter]
    rw [posSemidef_iff_dotProduct_mulVec]
    exact ⟨fun h => h.2, fun h => ⟨F.hmat_herm x, h⟩⟩
  rw [this]
  refine isClosed_iInter fun v => ?_
  have hc : Continuous fun x : ι → ℝ => star v ⬝ᵥ (F.hmat x *ᵥ v) := by
    have := F.continuous_hmat
    fun_prop
  have := Complex.orderClosedTopology
  exact isClosed_le continuous_const hc

open scoped ComplexOrder in
lemma psd_neg_eq_zero {A : Matrix D D ℂ} (h1 : A.PosSemidef) (h2 : (-A).PosSemidef) : A = 0 := by
  have hq : ∀ v : D → ℂ, star v ⬝ᵥ (A *ᵥ v) = 0 := by
    intro v
    have a := h1.dotProduct_mulVec_nonneg v
    have b := h2.dotProduct_mulVec_nonneg v
    rw [neg_mulVec, dotProduct_neg] at b
    exact le_antisymm (neg_nonneg.mp b) a
  have hz : ∀ v : D → ℂ, A *ᵥ v = 0 := fun v => (h1.dotProduct_mulVec_zero_iff v).mp (hq v)
  ext i j
  have := congrFun (hz (Pi.single j 1)) i
  simpa [mulVec_single] using this

open scoped Matrix.Norms.L2Operator MatrixOrder in
lemma exists_shift_psd {A : Matrix D D ℂ} (hA : A.IsHermitian) :
    ∃ c : ℝ, 0 ≤ c ∧ (A + (c : ℂ) • (1 : Matrix D D ℂ)).PosSemidef := by
  have hsa : IsSelfAdjoint A := hA
  refine ⟨‖A‖, norm_nonneg _, ?_⟩
  have h := hsa.neg_algebraMap_norm_le_self
  rw [← nonneg_iff_posSemidef]
  have : (0 : Matrix D D ℂ) ≤ A + algebraMap ℝ (Matrix D D ℂ) ‖A‖ := by
    have := sub_nonneg.mpr h
    simpa [sub_neg_eq_add, add_comm] using this
  convert this using 2
  rw [Algebra.algebraMap_eq_smul_one]
  simp

open scoped ComplexOrder in
/-- The system of a Hermitian frame (Definition B.1). -/
def toSystem : System where
  ι := ι
  cone := F.cone
  unit := F.unit
  cone_closed := F.cone_closed
  cone_zero := by simp [cone, hmat_zero, PosSemidef.zero]
  cone_add := fun x hx y hy => by
    simp only [cone, Set.mem_ofPred_eq, hmat_add] at *
    exact hx.add hy
  cone_smul := fun c hc x hx => by
    simp only [cone, Set.mem_ofPred_eq, hmat_smul] at *
    exact hx.smul (by exact_mod_cast hc)
  cone_pointed := fun x hx hnx => by
    simp only [cone, Set.mem_ofPred_eq, hmat_neg] at hx hnx
    exact F.hmat_inj (psd_neg_eq_zero hx hnx)
  cone_generating := fun v => by
    obtain ⟨η, hη⟩ := F.one_mem
    obtain ⟨c, hc, hpsd⟩ := exists_shift_psd (F.hmat_herm v)
    refine ⟨v + c • η, ?_, c • η, ?_, by abel⟩
    · simp only [cone, Set.mem_ofPred_eq, hmat_add, hmat_smul]
      have : F.hmat η = 1 := hη
      rw [this]; exact hpsd
    · simp only [cone, Set.mem_ofPred_eq, hmat_smul]
      have : F.hmat η = 1 := hη
      rw [this]; exact PosSemidef.one.smul (by exact_mod_cast hc)
  unit_pos := fun x hx hne => by
    simp only [cone, Set.mem_ofPred_eq] at hx
    rw [pair_unit]
    have h0 : 0 ≤ (F.hmat x).trace := hx.trace_nonneg
    have hne' : (F.hmat x).trace ≠ 0 := by
      rw [Ne, hx.trace_eq_zero_iff]
      intro h; exact hne (F.hmat_inj h)
    have := Complex.nonneg_iff.mp h0
    rcases lt_or_eq_of_le this.1 with h | h
    · exact h
    · exact absurd (Complex.ext h.symm this.2.symm) hne'

/-- The Kronecker product of two frames (the composite of local tomography, (T1)). -/
def kron {ι' D' : Type} [Fintype ι'] [DecidableEq ι'] [Fintype D'] [DecidableEq D']
    (G : HermFrame ι' D') : HermFrame (ι × ι') (D × D') where
  β := fun p => F.β p.1 ⊗ₖ G.β p.2
  herm := fun p => by
    unfold IsHermitian
    rw [conjTranspose_kronecker, (F.herm p.1).eq, (G.herm p.2).eq]
  inj := fun y hy => by
    -- entrywise: for fixed `(a, b)`, `∑_q (∑_p y_{pq} β_p a b) γ_q = 0`
    have h1 : ∀ a b, (fun q => ∑ p, y (p, q) * F.β p a b) = 0 := by
      intro a b
      apply G.inj
      ext a' b'
      have := congrFun (congrFun hy (a, a')) (b, b')
      simp only [Matrix.sum_apply, Matrix.smul_apply, kroneckerMap_apply, smul_eq_mul, Matrix.zero_apply,
        Fintype.sum_prod_type] at this
      simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply, Finset.sum_mul]
      rw [Finset.sum_comm]
      simpa [mul_assoc] using this
    have h2 : ∀ q, (fun p => y (p, q)) = 0 := by
      intro q
      apply F.inj
      ext a b
      have := congrFun (h1 a b) q
      simpa [Matrix.sum_apply, Matrix.smul_apply] using this
    funext ⟨p, q⟩
    exact congrFun (h2 q) p
  one_mem := by
    obtain ⟨η, hη⟩ := F.one_mem
    obtain ⟨η', hη'⟩ := G.one_mem
    refine ⟨fun p => η p.1 * η' p.2, ?_⟩
    have : (1 : Matrix (D × D') (D × D') ℂ) = (1 : Matrix D D ℂ) ⊗ₖ (1 : Matrix D' D' ℂ) :=
      one_kronecker_one.symm
    rw [this, ← hη, ← hη']
    ext ⟨a, a'⟩ ⟨b, b'⟩
    simp only [Matrix.sum_apply, Matrix.smul_apply, kroneckerMap_apply, smul_eq_mul, Fintype.sum_prod_type,
      Complex.ofReal_mul]
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    ring

end HermFrame

/-- The **transport** of a system `S` through an invertible matrix `T` (with inverse `Tinv`): the
cone `{x : T x ∈ V_S⁺}` and the unit effect `u_S ∘ T` (Example B.23, p.19). -/
def System.transport (S : System) (T Tinv : Matrix S.ι S.ι ℝ) (h₁ : Tinv * T = 1)
    (h₂ : T * Tinv = 1) : System where
  ι := S.ι
  cone := {x | T *ᵥ x ∈ S.cone}
  unit := S.unit ᵥ* T
  cone_closed := S.cone_closed.preimage (Continuous.matrix_mulVec continuous_const continuous_id)
  cone_zero := by simp [S.cone_zero]
  cone_add := fun x hx y hy => by
    simp only [Set.mem_ofPred_eq, mulVec_add] at *
    exact S.cone_add _ hx _ hy
  cone_smul := fun c hc x hx => by
    simp only [Set.mem_ofPred_eq, mulVec_smul] at *
    exact S.cone_smul c hc _ hx
  cone_pointed := fun x hx hnx => by
    simp only [Set.mem_ofPred_eq, mulVec_neg] at hx hnx
    have h0 := S.cone_pointed _ hx hnx
    have : Tinv *ᵥ (T *ᵥ x) = x := by rw [mulVec_mulVec, h₁, one_mulVec]
    rw [← this, h0, mulVec_zero]
  cone_generating := fun v => by
    obtain ⟨a, ha, b, hb, hab⟩ := S.cone_generating (T *ᵥ v)
    refine ⟨Tinv *ᵥ a, ?_, Tinv *ᵥ b, ?_, ?_⟩
    · simpa [mulVec_mulVec, h₂] using ha
    · simpa [mulVec_mulVec, h₂] using hb
    · rw [← mulVec_sub, ← hab, mulVec_mulVec, h₁, one_mulVec]
  unit_pos := fun x hx hne => by
    simp only [Set.mem_ofPred_eq] at hx
    have hne' : T *ᵥ x ≠ 0 := by
      intro h
      apply hne
      have : Tinv *ᵥ (T *ᵥ x) = x := by rw [mulVec_mulVec, h₁, one_mulVec]
      rw [← this, h, mulVec_zero]
    have := S.unit_pos _ hx hne'
    have e : pair (S.unit ᵥ* T) x = pair S.unit (T *ᵥ x) := by
      unfold pair
      have := (dotProduct_mulVec S.unit T x).symm
      simpa [dotProduct] using this
    rw [e]; exact this

end GPTIP632.Classical.Supplement

end


