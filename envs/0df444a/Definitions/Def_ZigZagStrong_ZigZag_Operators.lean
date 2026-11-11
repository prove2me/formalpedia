-- Prove2me | Definitions.Def_ZigZagStrong_ZigZag_Operators
-- name    : ZigZagStrong_ZigZag_Operators
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T03:59:29.509202+00:00
-- url     : https://prove2.me/theorems/21dc85fd-fbc9-47f9-b079-b135f7fd4273
-- title:
--   Hilbert-space rotation, zig-zag adjacency and actual spectral compressions
-- statement:
--   Let $S$ be an enumerated finite symmetric generating set of a group $\Gamma$, with port inversion $s\mapsto s^{-1}$, and let $\pi$ act on a set $V$. The permutation operator on $\ell^2(V)$ is pullback by the inverse permutation. Rotation is defined coordinatewise on the Hilbert direct sum over ports. The adjacency is
--   $$Z_\pi=(A_H\otimes I)\dot G_\pi(A_H\otimes I).$$
--   For finite $V$, the trivial and new operators are compressions through the actual isometric embeddings of cloud-constant vectors and of one copy of $1^\perp$ per port. The constant embedding divides the all-ones vector by $\sqrt{|V|}$. These are operators built from the sampled action; their spectra are not supplied as data. The elementary matrix $E_{i,j}$ sends $e_i$ to $e_j$, matching the source's column-first convention.
-- source:
--   Gal Maor, Alon Dogon, STOC 2027 submission #371 (October 2026), Definitions 2.1, 3.1–3.4 and Eq. (6), pp. 7, 10–11.

import Definitions.Def_ZigZagStrong_ZigZag_Gadget
import Definitions.Def_StrongConv

set_option autoImplicit false
noncomputable section

namespace ZigZagStrong.ZigZag
open scoped BigOperators InnerProductSpace

abbrev L2 (V : Type*) := lp (fun _ : V => ℂ) 2
abbrev Clouds (d : ℕ) (E : Type*) [NormedAddCommGroup E] := PiLp 2 (fun _ : Fin d => E)

/-- The permutation operator on the actual square-summable functions, including infinite V. -/
def permL2 {V : Type*} (e : Equiv.Perm V) : L2 V →L[ℂ] L2 V :=
  LinearMap.mkContinuous
    { toFun := fun f => ⟨fun x => f (e.symm x), by
        have hf := lp.memℓp f
        rw [memℓp_gen_iff (by norm_num)] at hf
        change Memℓp (fun x : V => f (e.symm x)) 2
        rw [memℓp_gen_iff (by norm_num)]
        exact e.symm.summable_iff.mpr hf⟩
      map_add' := fun f g => by ext x; rfl
      map_smul' := fun z f => by ext x; rfl }
    1 (by
      intro f
      rw [one_mul]
      apply le_of_eq
      simp only [LinearMap.coe_mk, AddHom.coe_mk]
      rw [lp.norm_eq_tsum_rpow (by norm_num), lp.norm_eq_tsum_rpow (by norm_num)]
      congr 1
      exact e.symm.tsum_eq (fun x => ‖f x‖ ^ (2 : ENNReal).toReal))

def regularL2 {Γ : Type*} [Group Γ] (g : Γ) : L2 Γ →L[ℂ] L2 Γ :=
  permL2 (Equiv.mulLeft g)

/-- A specified finite symmetric generating set, enumerated without repetition. -/
structure Generators (Γ : Type*) [Group Γ] (d : ℕ) where
  gen : Fin d → Γ
  injective : Function.Injective gen
  generates : Subgroup.closure (Set.range gen) = ⊤
  flip : Equiv.Perm (Fin d)
  flip_inv : ∀ i, gen (flip i) = (gen i)⁻¹
  flip_sq : Function.Involutive flip

section Hilbert
variable {d c : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- Rotation, defined coordinate by coordinate rather than by its tensor expansion. -/
def rotation (bar : Equiv.Perm (Fin d)) (U : Fin d → E →L[ℂ] E) :
    Clouds d E →L[ℂ] Clouds d E :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin d => E)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun i => (U (bar.symm i)).comp (PiLp.proj 2 (fun _ : Fin d => E) (bar.symm i))))

/-- Eq. (6), on the actual Hilbert direct sum. -/
def zigzag (H : Gadget d c) (bar : Equiv.Perm (Fin d)) (U : Fin d → E →L[ℂ] E) :
    Clouds d E →L[ℂ] Clouds d E :=
  (StrongConv.tensorOp H.mat (ContinuousLinearMap.id ℂ E)).comp
    ((rotation bar U).comp (StrongConv.tensorOp H.mat (ContinuousLinearMap.id ℂ E)))

/-- E_{i,j} sends e_i to e_j; this is the source's column-first convention. -/
def elementary (i j : Fin d) : Matrix (Fin d) (Fin d) ℂ :=
  fun a b => if a = j ∧ b = i then 1 else 0

end Hilbert

section Finite
variable {d c n : ℕ}

/-- Pointwise amplification of a continuous linear map. -/
def amplify {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace ℂ E] [NormedSpace ℂ F] (d : ℕ) (T : E →L[ℂ] F) :
    Clouds d E →L[ℂ] Clouds d F :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin d => F)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun i => T.comp (PiLp.proj 2 (fun _ : Fin d => E) i)))

/-- Inclusion of the genuine constants-perpendicular cloud subspace. -/
def newEmbedding (d n : ℕ) :
    Clouds d (StrongConv.OnesPerp n) →L[ℂ] Clouds d (EuclideanSpace ℂ (Fin n)) :=
  amplify d (StrongConv.OnesPerp n).subtypeL

/-- Compression to the actual invariant subspace; no spectral conclusion enters the definition. -/
def newAdj (H : Gadget d c) (bar : Equiv.Perm (Fin d)) (σ : Fin d → Equiv.Perm (Fin n)) :=
  (ContinuousLinearMap.adjoint (newEmbedding d n)).comp
    ((zigzag H bar (fun i => StrongConv.permOp (σ i))).comp (newEmbedding d n))

/-- The isometric constant-vector embedding for n>0. The zero-size case is never used. -/
def constantEmbedding (d n : ℕ) : EuclideanSpace ℂ (Fin d) →L[ℂ]
    Clouds d (EuclideanSpace ℂ (Fin n)) :=
  amplify d ((ContinuousLinearMap.id ℂ ℂ).smulRight
    (((Real.sqrt (n : ℝ))⁻¹ : ℂ) • StrongConv.onesVec n))

def trivialAdj (H : Gadget d c) (bar : Equiv.Perm (Fin d)) (σ : Fin d → Equiv.Perm (Fin n)) :=
  (ContinuousLinearMap.adjoint (constantEmbedding d n)).comp
    ((zigzag H bar (fun i => StrongConv.permOp (σ i))).comp (constantEmbedding d n))

end Finite
end ZigZagStrong.ZigZag


