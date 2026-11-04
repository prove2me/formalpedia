-- Prove2me | Definitions.Def_FreeGroupFactorProof06
-- name    : FreeGroupFactorProof06
-- status  : Definition
-- author  : @wurtle
-- created : 2026-11-04T00:51:34.47719+00:00
-- url     : https://prove2.me/theorems/ec9afc90-45cd-43d4-b07b-174e31b6d07b
-- title:
--   Free group factors: supporting development, part 6 of 12
-- statement:
--   Part 6 of the supporting Lean development for the isomorphism of all interpolated free group factors. It contains the definitions (operators on free Fock spaces, Gaussian systems, weighted corner models, stabilization and amplification constructions, and the free-group word maps) that the statements of the published child theorems and of the main theorem's proof refer to, in source order, together with the proved lemmas their bodies rely on. No result is assumed.
--
--   **Formalization Note** Definitions of this development carry proof fields and `Classical.choose` terms, so their dependencies must be proved here rather than imported from theorems. The code is OpenAI's, carved from `lean/OAI/Analysis/FreeGroupFactor` and `lean/OAI/Analysis/InterpolatedFactors` in openai/math at `adc7f12` and ported to Lean 4.33.1 and Mathlib `0df444a`.
-- source:
--   OpenAI, An isomorphism of the free group factors, September 23, 2026, https://github.com/openai/math (paper: preprints/An-isomorphism-of-the-free-group-factors-September-23-2026/An-isomorphism-of-the-free-group-factors-September-23-2026.pdf; Lean: lean/OAI/Analysis/FreeGroupFactor and lean/OAI/Analysis/InterpolatedFactors, Apache License 2.0)

import Mathlib
import Definitions.Def_FreeGroupFactorProof05

set_option linter.all false

section
namespace OAI

noncomputable section

universe u_1 u_2 u_3 u_4 u_5 u_6

namespace FreeGroupFactorMain.WeightedFock
open FreeFock
variable {ι : Type u_1} [DecidableEq ι]

theorem normalizedResidual_filled_covariance (u v : ℝ) (hu : u≠0) (hv : v≠0)
    (i j : ι) (hji : j≠i) (r s r' s' : Option Bool)
    (hrs : ¬(r=none ∧ s=none)) (hrs' : ¬(r'=none ∧ s'=none))
    (T : filledEdgeAlgebra u v i j) :
    star (normalizedResidual u v i j r s)*(T : Operator ι)*normalizedResidual u v i j r' s'=
      if r=r' ∧ s=s' then
        pVacuumTrace u v ((T : Operator ι)*residualSupport u v i r) • residualSupport u v i s else 0 := by
  simp only [normalizedResidual,star_smul,Complex.star_def,map_inv₀,Complex.conj_ofReal,
    smul_mul_assoc,mul_smul_comm]
  rw [residualCreation_filled_covariance u v hu hv i j hji r s r' s' hrs hrs']
  split_ifs <;> simp only [smul_zero (M := ℂ) (A := Operator ι),smul_smul,pVacuumTrace,mul_assoc]

end FreeGroupFactorMain.WeightedFock

section
namespace FreeGroupFactorMain.GaussianExtension
variable {E : Type u_2} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable (B : StarSubalgebra ℂ (E →L[ℂ] E)) (D : E →L[ℂ] E)
variable (κ : B → B) (hκ : ∀ a : B,star D*(a : E →L[ℂ] E)*D=(κ a : E →L[ℂ] E))
include hκ in
theorem orthogonality_extension (L R : E →L[ℂ] E)
    (hLD : ∀ a : B,star L*(a : E →L[ℂ] E)*D=0)
    (hDR : ∀ a : B,star D*(a : E →L[ℂ] E)*R=0)
    (hLR : ∀ a : B,star L*(a : E →L[ℂ] E)*R=0)
    (T : E →L[ℂ] E)
    (hT : T∈StarSubalgebra.centralizer ℂ
      (StarSubalgebra.centralizer ℂ (insert (D+star D) (B : Set (E →L[ℂ] E))) : Set (E →L[ℂ] E))) :
    star L*T*R=0 := by
  have hh := covariance_extension B D κ hκ L R 0 0 0
    (fun _ => by simp only [map_zero]) (fun _ => by simp only [map_zero]) hLD hDR
    (fun a => by simpa only [smul_zero (M := ℂ) (A := E →L[ℂ] E)] using hLR a) T hT
  simpa only [smul_zero (M := ℂ) (A := E →L[ℂ] E)] using hh
end FreeGroupFactorMain.GaussianExtension

namespace FreeGroupFactorMain.GaussianOrthogonal
variable {A : Type u_3} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]
def Relation (B : StarSubalgebra ℂ A) (L R : A) := ∀ a : B,star L*(a:A)*R=0
variable {B : StarSubalgebra ℂ A} {L R : A}
theorem symm (h : Relation B L R) : Relation B R L := by
  intro a
  have hh := congrArg star (h (star a))
  simpa only [star_mul,star_star,star_zero,StarMemClass.coe_star,mul_assoc] using hh

theorem sandwich_left (h : Relation B L R) (a b : B) : Relation B ((a:A)*L*(b:A)) R := by
  intro T
  calc
    _ = star (b:A)*(star L*((star a*T:B):A)*R) := by
      simp only [star_mul,StarMemClass.coe_star,MulMemClass.coe_mul,mul_assoc]
    _ = 0 := by rw [h (star a*T),mul_zero]

theorem sandwich_right (h : Relation B L R) (a b : B) : Relation B L ((a:A)*R*(b:A)) :=
  symm (sandwich_left (symm h) a b)
end FreeGroupFactorMain.GaussianOrthogonal
namespace FreeGroupFactorMain.WeightedFock
open FreeFock GaussianOrthogonal
variable {ι : Type u_4} [DecidableEq ι]

theorem fresh_C_edge_orthogonal (u v : ℝ) (i n m : ι) (hni : n≠i) (hmi : m≠i) (hnm : n≠m) :
    Relation (edgeAlgebra u v i) (C u v n) (C u v m) := by
  intro a
  have hh := fresh_C_contraction u v {i} n m hni hmi
    ⟨a,edgeAlgebra_le_old u v {i} i (Set.mem_singleton i) a.property⟩
  simpa only [ite_eq_right hnm] using hh

theorem splitBlock_weightedDefect (u v : ℝ) (i j : ι) (hji : j≠i)
    (r s : Bool) (hrs : ¬(r=true ∧ s=true)) :
    Relation (edgeAlgebra u v i) (splitBlock u v i j r s) (weightedDefectCreation u v i j) :=
  GaussianSplit.block_D (edgeAlgebra u v i) (C u v j) (vacuum u v)
    (fresh_C_edge_contraction u v i j hji) (defectAsEdge u v i) (defectAsEdge_projection u v i)
    (defectAsEdge_central u v i) r s hrs

theorem fresh_diagonal_filled (u v : ℝ) (i j n k : ι) (hji : j≠i)
    (hni : n≠i) (hnj : n≠j) (hnk : n≠k) (hjk : j≠k) (r : Bool) :
    Relation (filledEdgeAlgebra u v i j) (C u v n) (edgeCreation k r r) := by
  intro T
  exact GaussianExtension.orthogonality_extension (edgeAlgebra u v i) (weightedDefectCreation u v i j)
    (defectCovariance u v i) (weightedDefect_contraction u v i j hji) (C u v n) (edgeCreation k r r)
    (fresh_C_weightedDefect u v i j n hji hni hnj)
    (symm (fun a => diagonal_weightedDefect u v i j k hji hjk a r))
    (fun a => fresh_C_diagonal_edge u v i n k hni hnk a r) T T.property

theorem fresh_split_filled (u v : ℝ) (i j n : ι) (hji : j≠i)
    (hni : n≠i) (hnj : n≠j) (r s : Bool) (hrs : ¬(r=true ∧ s=true)) :
    Relation (filledEdgeAlgebra u v i j) (C u v n) (splitBlock u v i j r s) := by
  intro T
  exact GaussianExtension.orthogonality_extension (edgeAlgebra u v i) (weightedDefectCreation u v i j)
    (defectCovariance u v i) (weightedDefect_contraction u v i j hji) (C u v n) (splitBlock u v i j r s)
    (fresh_C_weightedDefect u v i j n hji hni hnj)
    (symm (splitBlock_weightedDefect u v i j hji r s hrs))
    (sandwich_right (fresh_C_edge_orthogonal u v i n j hni hji hnj)
      (GaussianSplit.cut (edgeAlgebra u v i) (defectAsEdge u v i) r)
      (GaussianSplit.cut (edgeAlgebra u v i) (defectAsEdge u v i) s)) T T.property

theorem split_diagonal_filled (u v : ℝ) (i j k : ι) (hji : j≠i) (hjk : j≠k)
    (r s t : Bool) (hrs : ¬(r=true ∧ s=true)) :
    Relation (filledEdgeAlgebra u v i j) (splitBlock u v i j r s) (edgeCreation k t t) := by
  intro T
  exact GaussianExtension.orthogonality_extension (edgeAlgebra u v i) (weightedDefectCreation u v i j)
    (defectCovariance u v i) (weightedDefect_contraction u v i j hji) (splitBlock u v i j r s) (edgeCreation k t t)
    (splitBlock_weightedDefect u v i j hji r s hrs)
    (symm (fun a => diagonal_weightedDefect u v i j k hji hjk a t))
    (sandwich_left (fun a => fresh_C_diagonal_edge u v i j k hji hjk a t)
      (GaussianSplit.cut (edgeAlgebra u v i) (defectAsEdge u v i) r)
      (GaussianSplit.cut (edgeAlgebra u v i) (defectAsEdge u v i) s)) T T.property
end FreeGroupFactorMain.WeightedFock

end

namespace FreeGroupFactorMain.GaussianOrthogonal
variable {A : Type u_5} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]
variable {B : StarSubalgebra ℂ A} {L R : A}
theorem smul_left (h : Relation B L R) (z : ℂ) : Relation B (z • L) R := by
  intro a
  simp only [star_smul,smul_mul_assoc,h a,smul_zero]
theorem smul_right (h : Relation B L R) (z : ℂ) : Relation B L (z • R) := by
  intro a
  simp only [mul_smul_comm,h a,smul_zero]
end FreeGroupFactorMain.GaussianOrthogonal

namespace FreeGroupFactorMain.WeightedFock
open FreeFock GaussianOrthogonal
variable {ι : Type u_6} [DecidableEq ι]

def legAsFilled (u v : ℝ) (i j : ι) (r : Bool) : filledEdgeAlgebra u v i j :=
  ⟨supportedLeg u v i r,edgeAlgebra_le_filled u v i j (supportedLeg_mem_edge u v i r)⟩
def residualLegAsFilled (u v : ℝ) (i j : ι) (r : Option Bool) : filledEdgeAlgebra u v i j :=
  ⟨residualLeg u v i r,edgeAlgebra_le_filled u v i j (residualLeg_mem_edge u v i r)⟩

theorem normalized_fresh_diagonal (u v : ℝ) (i j n k : ι) (hji : j≠i)
    (hni : n≠i) (hnj : n≠j) (hnk : n≠k) (hjk : j≠k) (r s t : Bool) :
    Relation (filledEdgeAlgebra u v i j) (normalizedCreation u v i n r s)
      (normalizedDiagonal u v i k t) := by
  exact smul_right (smul_left (sandwich_right (sandwich_left
    (fresh_diagonal_filled u v i j n k hji hni hnj hnk hjk (!t))
    (legAsFilled u v i j r) (star (legAsFilled u v i j s)))
    (legAsFilled u v i j t) (star (legAsFilled u v i j t))) _) _

theorem normalized_fresh_residual (u v : ℝ) (i j n : ι) (hji : j≠i)
    (hni : n≠i) (hnj : n≠j) (r s : Bool) (a b : Option Bool)
    (hab : ¬(a=none ∧ b=none)) :
    Relation (filledEdgeAlgebra u v i j) (normalizedCreation u v i n r s)
      (normalizedResidual u v i j a b) := by
  have hh := sandwich_right (sandwich_left
    (fresh_split_filled u v i j n hji hni hnj (residualCut a) (residualCut b)
      (residual_allowed a b hab))
    (legAsFilled u v i j r) (star (legAsFilled u v i j s)))
    (residualLegAsFilled u v i j a) (star (residualLegAsFilled u v i j b))
  change Relation _ (supportedCreation u v i n r s)
    (residualLeg u v i a*splitBlock u v i j (residualCut a) (residualCut b)*star (residualLeg u v i b)) at hh
  rw [← residualCreation_split] at hh
  exact smul_right (smul_left hh _) _

theorem normalized_residual_diagonal (u v : ℝ) (i j k : ι) (hji : j≠i) (hjk : j≠k)
    (a b : Option Bool) (hab : ¬(a=none ∧ b=none)) (r : Bool) :
    Relation (filledEdgeAlgebra u v i j) (normalizedResidual u v i j a b)
      (normalizedDiagonal u v i k r) := by
  have hh := sandwich_right (sandwich_left
    (split_diagonal_filled u v i j k hji hjk (residualCut a) (residualCut b) (!r)
      (residual_allowed a b hab))
    (residualLegAsFilled u v i j a) (star (residualLegAsFilled u v i j b)))
    (legAsFilled u v i j r) (star (legAsFilled u v i j r))
  change Relation _
    (residualLeg u v i a*splitBlock u v i j (residualCut a) (residualCut b)*star (residualLeg u v i b))
    (transportedDiagonal u v i k r) at hh
  rw [← residualCreation_split] at hh
  exact smul_right (smul_left hh _) _

theorem normalizedCreation_annihilate (u v : ℝ) (i j n : ι) (hji : j≠i)
    (hni : n≠i) (hnj : n≠j) (r s : Bool) (T : filledEdgeAlgebra u v i j) :
    star (normalizedCreation u v i n r s) ((T : Operator ι) (vacuum u v))=0 := by
  simp only [normalizedCreation,star_smul,_root_.smul_apply,
    supportedCreation_filled_annihilation u v i j n hji hni hnj r s T,smul_zero]

theorem normalizedResidual_annihilate (u v : ℝ) (i j : ι) (hji : j≠i)
    (r s : Option Bool) (hrs : ¬(r=none ∧ s=none)) (T : filledEdgeAlgebra u v i j) :
    star (normalizedResidual u v i j r s) ((T : Operator ι) (vacuum u v))=0 := by
  simp only [normalizedResidual,star_smul,_root_.smul_apply,
    residualCreation_filled_annihilation u v i j hji r s hrs T,smul_zero]

theorem transportedDiagonal_annihilate (u v : ℝ) (i j k : ι) (hji : j≠i) (hjk : j≠k)
    (r : Bool) (T : filledEdgeAlgebra u v i j) :
    star (transportedDiagonal u v i k r) ((T : Operator ι) (vacuum u v))=0 := by
  have hh := diagonal_filled_annihilation u v i j k hji hjk (!r) (star (legAsFilled u v i j r)*T)
  simp only [transportedDiagonal,star_mul,star_star,mul_apply_eq_comp]
  change star (edgeCreation k (!r) (!r)) (star (supportedLeg u v i r) ((T : Operator ι) (vacuum u v)))=0 at hh
  rw [hh,map_zero]

theorem normalizedDiagonal_annihilate (u v : ℝ) (i j k : ι) (hji : j≠i) (hjk : j≠k)
    (r : Bool) (T : filledEdgeAlgebra u v i j) :
    star (normalizedDiagonal u v i k r) ((T : Operator ι) (vacuum u v))=0 := by
  simp only [normalizedDiagonal,star_smul,_root_.smul_apply,
    transportedDiagonal_annihilate u v i j k hji hjk r T,smul_zero]
end FreeGroupFactorMain.WeightedFock

end

end OAI
end

section
namespace OAI

universe u_1 u_2 u_3 u_4 u_5

noncomputable section
namespace FreeGroupFactorMain.RectangularAbsorption

section
variable {A : Type u_1} [Ring A]

def part (p q : A) (C : ℕ → A) (n : ℕ) : A := p*C n*q
def remainder (p q : A) (C : ℕ → A) (n : ℕ) : A := C n-part p q C n
def shifted (p q D : A) (C : ℕ → A) : ℕ → A
  | 0 => D+remainder p q C 0
  | n+1 => part p q C n+remainder p q C (n+1)

 theorem part_supported (p q : A) (hp : p*p=p) (hq : q*q=q) (C : ℕ → A) (n : ℕ) :
    p*part p q C n*q=part p q C n := by
  calc
    _ = (p*p)*C n*(q*q) := by dsimp [part];noncomm_ring
    _ = _ := by rw [hp,hq];rfl

 theorem remainder_compression (p q : A) (hp : p*p=p) (hq : q*q=q) (C : ℕ → A) (n : ℕ) :
    p*remainder p q C n*q=0 := by
  rw [remainder,mul_sub,sub_mul,part_supported p q hp hq]
  exact sub_self _

 theorem shifted_zero_compression (p q D : A) (hp : p*p=p) (hq : q*q=q)
    (hD : p*D*q=D) (C : ℕ → A) : p*shifted p q D C 0*q=D := by
  rw [shifted,mul_add,add_mul,hD,remainder_compression p q hp hq,add_zero]

 theorem shifted_succ_compression (p q D : A) (hp : p*p=p) (hq : q*q=q)
    (C : ℕ → A) (n : ℕ) : p*shifted p q D C (n+1)*q=part p q C n := by
  rw [shifted,mul_add,add_mul,part_supported p q hp hq,remainder_compression p q hp hq,add_zero]

 theorem recover (p q D : A) (hp : p*p=p) (hq : q*q=q) (hD : p*D*q=D)
    (C : ℕ → A) (n : ℕ) :
    C n=p*shifted p q D C (n+1)*q+shifted p q D C n-p*shifted p q D C n*q := by
  rw [shifted_succ_compression p q D hp hq]
  cases n with
  | zero => rw [shifted_zero_compression p q D hp hq hD,shifted,remainder];abel
  | succ n => rw [shifted_succ_compression p q D hp hq,shifted,remainder];abel

variable [StarRing A]
def paired (x y : A) : A := x+star y

 theorem paired_compression (p q x y : A) (hp : star p=p) (hq : star q=q) :
    paired (p*x*q) (q*y*p)=p*paired x y*q := by
  simp only [paired,star_mul,hp,hq,mul_add,add_mul,mul_assoc]

 theorem paired_shifted_zero (p q D E : A) (hp : star p=p) (hq : star q=q)
    (C F : ℕ → A) :
    paired (shifted p q D C 0) (shifted q p E F 0)=
      paired D E+paired (C 0) (F 0)-p*paired (C 0) (F 0)*q := by
  simp only [paired,shifted,remainder,part,star_add,star_sub,star_mul,hp,hq]
  noncomm_ring

 theorem paired_shifted_succ (p q D E : A) (hp : star p=p) (hq : star q=q)
    (C F : ℕ → A) (n : ℕ) :
    paired (shifted p q D C (n+1)) (shifted q p E F (n+1))=
      p*paired (C n) (F n)*q+paired (C (n+1)) (F (n+1))-
        p*paired (C (n+1)) (F (n+1))*q := by
  simp only [paired,shifted,remainder,part,star_add,star_sub,star_mul,hp,hq]
  noncomm_ring

 theorem recover_paired (p q D E : A) (hp : p*p=p) (hq : q*q=q)
    (hps : star p=p) (hqs : star q=q) (hD : p*D*q=D) (hE : q*E*p=E)
    (C F : ℕ → A) (n : ℕ) :
    paired (C n) (F n)=
      p*paired (shifted p q D C (n+1)) (shifted q p E F (n+1))*q+
      paired (shifted p q D C n) (shifted q p E F n)-
      p*paired (shifted p q D C n) (shifted q p E F n)*q := by
  have h := congrArg₂ paired (recover p q D hp hq hD C n) (recover q p E hq hp hE F n)
  rw [h]
  simp only [paired,star_sub,star_add,star_mul,hps,hqs]
  noncomm_ring

 theorem recover_supported_paired (p q D E : A) (hp : p*p=p) (hq : q*q=q)
    (hps : star p=p) (hqs : star q=q) (hD : p*D*q=D) (hE : q*E*p=E)
    (C F : ℕ → A) :
    paired D E=p*paired (shifted p q D C 0) (shifted q p E F 0)*q := by
  rw [← paired_compression p q _ _ hps hqs,
    shifted_zero_compression p q D hp hq hD,shifted_zero_compression q p E hq hp hE]

variable [Algebra ℂ A] [StarModule ℂ A]

 theorem generation_equivalence (p q D E : A) (hp : p*p=p) (hq : q*q=q)
    (hps : star p=p) (hqs : star q=q) (hD : p*D*q=D) (hE : q*E*p=E)
    (C F : ℕ → A) (M : StarSubalgebra ℂ A) (hMp : p∈M) (hMq : q∈M) :
    (paired D E∈M ∧ ∀ n,paired (C n) (F n)∈M) ↔
      ∀ n,paired (shifted p q D C n) (shifted q p E F n)∈M := by
  constructor
  · rintro ⟨hDE,hCF⟩ n
    cases n with
    | zero =>
      rw [paired_shifted_zero p q D E hps hqs]
      exact sub_mem (add_mem hDE (hCF 0)) (mul_mem (mul_mem hMp (hCF 0)) hMq)
    | succ n =>
      rw [paired_shifted_succ p q D E hps hqs]
      exact sub_mem (add_mem (mul_mem (mul_mem hMp (hCF n)) hMq) (hCF (n+1)))
        (mul_mem (mul_mem hMp (hCF (n+1))) hMq)
  · intro h
    constructor
    · rw [recover_supported_paired p q D E hp hq hps hqs hD hE C F]
      exact mul_mem (mul_mem hMp (h 0)) hMq
    · intro n
      rw [recover_paired p q D E hp hq hps hqs hD hE C F]
      exact sub_mem (add_mem (mul_mem (mul_mem hMp (h (n+1))) hMq) (h n))
        (mul_mem (mul_mem hMp (h n)) hMq)

end
section
variable {A : Type u_2} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]

structure Data (B : StarSubalgebra ℂ A) where
  p : B
  q : B
  projection : IsStarProjection p
  projectionq : IsStarProjection q
  τ : B →ₗ[ℂ] ℂ
  tracial : ∀ a b,τ (a*b)=τ (b*a)
  C : ℕ → A
  D : A
  D_supported : (p:A)*D*(q:A)=D
  C_cov : ∀ (a : B) n m,star (C n)*(a:A)*C m=if n=m then τ a • (1:A) else 0
  D_cov : ∀ (a : B),star D*(a:A)*D=τ (a*p) • (q:A)
  C_D : ∀ (a : B) n,star (C n)*(a:A)*D=0
  D_C : ∀ (a : B) n,star D*(a:A)*C n=0

namespace Data
variable {B : StarSubalgebra ℂ A} (d : Data B)

 theorem p_square : (d.p:A)*(d.p:A)=(d.p:A) :=
  congrArg Subtype.val d.projection.isIdempotentElem.eq
 theorem p_star : star (d.p:A)=(d.p:A) :=
  congrArg Subtype.val d.projection.isSelfAdjoint.star_eq
 theorem q_square : (d.q:A)*(d.q:A)=(d.q:A) :=
  congrArg Subtype.val d.projectionq.isIdempotentElem.eq
 theorem q_star : star (d.q:A)=(d.q:A) :=
  congrArg Subtype.val d.projectionq.isSelfAdjoint.star_eq
 theorem trace_pa (a : B) : d.τ (d.p*a)=d.τ (a*d.p) := d.tracial _ _
 theorem trace_pap (a : B) : d.τ (d.p*a*d.p)=d.τ (a*d.p) := by
  rw [mul_assoc,d.tracial,mul_assoc,d.projection.isIdempotentElem.eq]

 theorem part_part (a : B) (n m : ℕ) :
    star (part (d.p:A) (d.q:A) d.C n)*(a:A)*part (d.p:A) (d.q:A) d.C m=
      if n=m then d.τ (a*d.p) • (d.q:A) else 0 := by
  calc
    _ = (d.q:A)*(star (d.C n)*((d.p*a*d.p:B):A)*d.C m)*(d.q:A) := by
      simp only [part,star_mul,d.p_star,d.q_star,MulMemClass.coe_mul]
      noncomm_ring
    _ = _ := by
      rw [d.C_cov,d.trace_pap]
      split_ifs <;> simp only [mul_smul_comm,smul_mul_assoc,mul_one,d.q_square,mul_zero,zero_mul]

 theorem part_remainder (a : B) (n m : ℕ) :
    star (part (d.p:A) (d.q:A) d.C n)*(a:A)*remainder (d.p:A) (d.q:A) d.C m=0 := by
  calc
    _ = (d.q:A)*(star (d.C n)*((d.p*a:B):A)*d.C m)-
        (d.q:A)*(star (d.C n)*((d.p*a*d.p:B):A)*d.C m)*(d.q:A) := by
      simp only [part,remainder,star_mul,d.p_star,d.q_star,MulMemClass.coe_mul]
      noncomm_ring
    _ = 0 := by
      rw [d.C_cov,d.C_cov,d.trace_pa,d.trace_pap]
      split_ifs <;>
        simp only [mul_smul_comm,smul_mul_assoc,mul_one,d.q_square,mul_zero,zero_mul,sub_self]

 theorem remainder_part (a : B) (n m : ℕ) :
    star (remainder (d.p:A) (d.q:A) d.C n)*(a:A)*part (d.p:A) (d.q:A) d.C m=0 := by
  have h := congrArg star (d.part_remainder (star a) m n)
  simpa only [star_mul,star_star,StarMemClass.coe_star,star_zero,mul_assoc] using h

 theorem remainder_remainder (a : B) (n m : ℕ) :
    star (remainder (d.p:A) (d.q:A) d.C n)*(a:A)*remainder (d.p:A) (d.q:A) d.C m=
      if n=m then d.τ a • (1:A)-d.τ (a*d.p) • (d.q:A) else 0 := by
  calc
    _ = star (d.C n)*(a:A)*d.C m-
        (star (d.C n)*((a*d.p:B):A)*d.C m)*(d.q:A)-
        (d.q:A)*(star (d.C n)*((d.p*a:B):A)*d.C m)+
        (d.q:A)*(star (d.C n)*((d.p*a*d.p:B):A)*d.C m)*(d.q:A) := by
      simp only [part,remainder,star_sub,star_mul,d.p_star,d.q_star,MulMemClass.coe_mul]
      noncomm_ring
    _ = _ := by
      simp only [d.C_cov,d.trace_pa,d.trace_pap]
      split_ifs <;>
        simp only [mul_smul_comm,smul_mul_assoc,mul_one,one_mul,d.q_square,
          mul_zero,zero_mul,sub_zero,add_zero]
      all_goals abel

 theorem part_D (a : B) (n : ℕ) :
    star (part (d.p:A) (d.q:A) d.C n)*(a:A)*d.D=0 := by
  calc
    _ = (d.q:A)*(star (d.C n)*((d.p*a:B):A)*d.D) := by
      simp only [part,star_mul,d.p_star,d.q_star,MulMemClass.coe_mul,mul_assoc]
    _ = 0 := by rw [d.C_D,mul_zero]

 theorem D_part (a : B) (n : ℕ) :
    star d.D*(a:A)*part (d.p:A) (d.q:A) d.C n=0 := by
  calc
    _ = (star d.D*((a*d.p:B):A)*d.C n)*(d.q:A) := by
      simp only [part,MulMemClass.coe_mul,mul_assoc]
    _ = 0 := by rw [d.D_C,zero_mul]

 theorem remainder_D (a : B) (n : ℕ) :
    star (remainder (d.p:A) (d.q:A) d.C n)*(a:A)*d.D=0 := by
  simp only [remainder,star_sub,sub_mul,d.C_D,d.part_D,sub_self]

 theorem D_remainder (a : B) (n : ℕ) :
    star d.D*(a:A)*remainder (d.p:A) (d.q:A) d.C n=0 := by
  simp only [remainder,mul_sub,d.D_C,d.D_part,sub_self]

 theorem shifted_covariance (a : B) (n m : ℕ) :
    star (shifted (d.p:A) (d.q:A) d.D d.C n)*(a:A)*shifted (d.p:A) (d.q:A) d.D d.C m=
      if n=m then d.τ a • (1:A) else 0 := by
  cases n with
  | zero =>
    cases m with
    | zero =>
      simp only [shifted,star_add,add_mul,mul_add,d.D_cov,d.D_remainder,d.remainder_D,
        d.remainder_remainder,ite_true,add_zero,zero_add]
      abel
    | succ m =>
      simp only [shifted,star_add,add_mul,mul_add,d.D_part,d.D_remainder,d.remainder_part,
        d.remainder_remainder,Nat.zero_ne_add_one,ite_false,add_zero]
  | succ n =>
    cases m with
    | zero =>
      simp only [shifted,star_add,add_mul,mul_add,d.part_D,d.part_remainder,d.remainder_D,
        d.remainder_remainder,Nat.add_one_ne_zero,ite_false,add_zero]
    | succ m =>
      simp only [shifted,star_add,add_mul,mul_add,d.part_part,d.part_remainder,d.remainder_part,
        d.remainder_remainder,Nat.add_right_cancel_iff,add_zero,zero_add]
      split_ifs <;> abel

end Data
end
variable {A : Type u_3} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]

def Orthogonal (B : StarSubalgebra ℂ A) (x y : A) : Prop :=
  ∀ a : B,star x*(a:A)*y=0

namespace Orthogonal
variable {B : StarSubalgebra ℂ A} {x y z : A}
 theorem add_left (h : Orthogonal B x z) (k : Orthogonal B y z) : Orthogonal B (x+y) z := by
  intro a
  simp only [star_add,add_mul,h a,k a,add_zero]
 theorem sub_left (h : Orthogonal B x z) (k : Orthogonal B y z) : Orthogonal B (x-y) z := by
  intro a
  simp only [star_sub,sub_mul,h a,k a,sub_self]

 theorem symm (h : Orthogonal B x y) : Orthogonal B y x := by
  intro a
  have ht := congrArg star (h (star a))
  simpa only [star_mul,star_star,StarMemClass.coe_star,star_zero,mul_assoc] using ht
 theorem sandwich_left (h : Orthogonal B x y) (p q : B) :
    Orthogonal B ((p:A)*x*(q:A)) y := by
  intro a
  calc
    _ = star (q:A)*(star x*((star p*a:B):A)*y) := by
      simp only [star_mul,StarMemClass.coe_star,MulMemClass.coe_mul,mul_assoc]
    _ = 0 := by rw [h (star p*a),mul_zero]

 theorem part_left {C : ℕ → A} (h : ∀ n,Orthogonal B (C n) y) (p q : B) (n : ℕ) :
    Orthogonal B (part (p:A) (q:A) C n) y := (h n).sandwich_left p q

 theorem remainder_left {C : ℕ → A} (h : ∀ n,Orthogonal B (C n) y) (p q : B) (n : ℕ) :
    Orthogonal B (remainder (p:A) (q:A) C n) y := (h n).sub_left (part_left h p q n)

 theorem shifted_left {C : ℕ → A} {D : A} (hD : Orthogonal B D y)
    (hC : ∀ n,Orthogonal B (C n) y) (p q : B) (n : ℕ) :
    Orthogonal B (shifted (p:A) (q:A) D C n) y := by
  cases n with
  | zero => exact hD.add_left (remainder_left hC p q 0)
  | succ n => exact (part_left hC p q n).add_left (remainder_left hC p q (n+1))
 theorem shifted_right {C : ℕ → A} {D : A} (hD : Orthogonal B x D)
    (hC : ∀ n,Orthogonal B x (C n)) (p q : B) (n : ℕ) :
    Orthogonal B x (shifted (p:A) (q:A) D C n) :=
  (shifted_left hD.symm (fun n => (hC n).symm) p q n).symm

 theorem shifted {C F : ℕ → A} {D E : A} (hDE : Orthogonal B D E)
    (hDF : ∀ m,Orthogonal B D (F m)) (hCE : ∀ n,Orthogonal B (C n) E)
    (hCF : ∀ n m,Orthogonal B (C n) (F m)) (p q r s : B) (n m : ℕ) :
    Orthogonal B (RectangularAbsorption.shifted (p:A) (q:A) D C n)
      (RectangularAbsorption.shifted (r:A) (s:A) E F m) :=
  shifted_left (shifted_right hDE hDF r s m)
    (fun n => shifted_right (hCE n) (hCF n) r s m) p q n
end Orthogonal

structure Family (B : StarSubalgebra ℂ A) (I : Type u_4) where
  data : I → Data B
  CC : ∀ i j,i≠j → ∀ n m,Orthogonal B ((data i).C n) ((data j).C m)
  CD : ∀ i j,i≠j → ∀ n,Orthogonal B ((data i).C n) (data j).D
  DD : ∀ i j,i≠j → Orthogonal B (data i).D (data j).D

namespace Family
open scoped Classical
variable {B : StarSubalgebra ℂ A} {I : Type u_5} (d : Family B I)

def output (i : I) (n : ℕ) : A :=
  shifted ((d.data i).p:A) ((d.data i).q:A) (d.data i).D (d.data i).C n

 theorem output_cross {i j : I} (hij : i≠j) (n m : ℕ) :
    Orthogonal B (d.output i n) (d.output j m) :=
  Orthogonal.shifted (d.DD i j hij)
    (fun m => (d.CD j i hij.symm m).symm) (d.CD i j hij) (d.CC i j hij)
    (d.data i).p (d.data i).q (d.data j).p (d.data j).q n m

 theorem output_covariance (i j : I) (n m : ℕ) (a : B) :
    star (d.output i n)*(a:A)*d.output j m=
      if i=j ∧ n=m then (d.data i).τ a • (1:A) else 0 := by
  classical
  by_cases hij : i=j
  · subst j
    simpa only [output,true_and] using (d.data i).shifted_covariance a n m
  · rw [ite_eq_right (fun h => hij h.1)]
    exact d.output_cross hij n m a

 theorem output_generation (σ : I → I)
    (hpq : ∀ i,(d.data (σ i)).p=(d.data i).q)
    (hqp : ∀ i,(d.data (σ i)).q=(d.data i).p)
    (M : StarSubalgebra ℂ A)
    (hpM : ∀ i,((d.data i).p:A)∈M) (hqM : ∀ i,((d.data i).q:A)∈M) :
    ((∀ i,paired (d.data i).D (d.data (σ i)).D∈M) ∧
      ∀ i n,paired ((d.data i).C n) ((d.data (σ i)).C n)∈M) ↔
        ∀ i n,paired (d.output i n) (d.output (σ i) n)∈M := by
  have he (i : I) :
      (paired (d.data i).D (d.data (σ i)).D∈M ∧
        ∀ n,paired ((d.data i).C n) ((d.data (σ i)).C n)∈M) ↔
          ∀ n,paired (d.output i n) (d.output (σ i) n)∈M := by
    have hE : ((d.data i).q:A)*(d.data (σ i)).D*((d.data i).p:A)=(d.data (σ i)).D := by
      simpa only [hpq,hqp] using (d.data (σ i)).D_supported
    simpa only [output,hpq,hqp] using
      generation_equivalence ((d.data i).p:A) ((d.data i).q:A) (d.data i).D (d.data (σ i)).D
        (d.data i).p_square (d.data i).q_square (d.data i).p_star (d.data i).q_star
        (d.data i).D_supported hE (d.data i).C (d.data (σ i)).C M (hpM i) (hqM i)
  constructor
  · rintro ⟨hD,hC⟩ i
    exact (he i).mp ⟨hD i,hC i⟩
  · intro h
    exact ⟨fun i => ((he i).mpr (h i)).1,fun i => ((he i).mpr (h i)).2⟩

end Family
end FreeGroupFactorMain.RectangularAbsorption

end

end OAI
end

section
namespace OAI

noncomputable section

universe u_1 u_2 u_3 u_4 u_5

section
namespace FreeGroupFactorMain.Amplification
variable {A : Type u_1} [CStarAlgebra A]

def subalgebraCorner (M : StarSubalgebra ℂ A) (p : A) (hp : IsStarProjection p) (hpM : p∈M) :
    StarSubalgebra ℂ (Corner p hp) where
  carrier := {x | (x:A)∈M}
  zero_mem' := zero_mem M
  one_mem' := hpM
  add_mem' {a b} ha hb := show (a:A)+(b:A)∈M from add_mem ha hb
  mul_mem' {a b} ha hb := show (a:A)*(b:A)∈M from mul_mem ha hb
  algebraMap_mem' c := by
    change c • p∈M
    exact M.smul_mem hpM c
  star_mem' {x} hx := by
    change star (x:A)∈M
    exact star_mem hx

def sandwiched (p : A) (hp : IsStarProjection p) (a b x : A)
    (ha : p*a=a) (hb : p*b=b) : Corner p hp :=
  ⟨a*x*star b,by
    constructor
    · rw [← mul_assoc,← mul_assoc,ha]
    · have hb' : star b*p=star b := by
        simpa only [star_mul,hp.isSelfAdjoint.star_eq] using congrArg star hb
      rw [mul_assoc,hb']⟩
end FreeGroupFactorMain.Amplification

namespace FreeGroupFactorMain.WeightedFock
open FreeFock Amplification
variable {ι : Type u_2} [DecidableEq ι]

abbrev PCorner (ι : Type u_3) [DecidableEq ι] := Corner (P : Operator ι) projection_P

def pFilled (u v : ℝ) (i j : ι) : StarSubalgebra ℂ (PCorner ι) :=
  subalgebraCorner (filledEdgeAlgebra u v i j) P projection_P
    (edgeAlgebra_le_filled u v i j (P_mem_edge u v i))

def filledOfCorner {u v : ℝ} {i j : ι} (a : pFilled u v i j) : filledEdgeAlgebra u v i j :=
  ⟨a.val.val,a.property⟩

def pTrace (u v : ℝ) (i j : ι) : pFilled u v i j →ₗ[ℂ] ℂ where
  toFun a := pVacuumTrace u v a.val.val
  map_add' a b := by simp only [pVacuumTrace,vacuumTrace,AddMemClass.coe_add,add_apply,inner_add_right,mul_add]
  map_smul' c a := by
    simp only [pVacuumTrace,vacuumTrace,SetLike.val_smul,smul_apply,inner_smul_right,smul_eq_mul,RingHom.id_apply]
    ring

theorem pTrace_tracial (u v : ℝ) (hu : u≠0) (hv : v≠0) (i j : ι) (a b : pFilled u v i j) :
    pTrace u v i j (a*b)=pTrace u v i j (b*a) := by
  change (u:ℂ)⁻¹*(u:ℂ)⁻¹*vacuumTrace u v (a.val.val*b.val.val)=_
  rw [ambient_trace_mul u v hu hv
    ⟨a.val.val,filledEdgeAlgebra_le_ambient u v i j a.property⟩
    ⟨b.val.val,filledEdgeAlgebra_le_ambient u v i j b.property⟩]
  rfl

theorem P_mul_supportedLeg (u v : ℝ) (i : ι) (r : Bool) :
    P*supportedLeg u v i r=supportedLeg u v i r := by
  cases r
  · exact projection_P.isIdempotentElem.eq
  · exact edgePolar_left u v i

def pFresh (u v : ℝ) (i n : ι) (r s : Bool) : PCorner ι :=
  (u:ℂ)⁻¹ • sandwiched P projection_P (supportedLeg u v i r) (supportedLeg u v i s) (C u v n)
    (P_mul_supportedLeg u v i r) (P_mul_supportedLeg u v i s)

@[simp] theorem pFresh_val (u v : ℝ) (i n : ι) (r s : Bool) :
    (pFresh u v i n r s : Operator ι)=normalizedCreation u v i n r s := rfl

def pResidual (u v : ℝ) (i j : ι) (r s : Option Bool) : PCorner ι :=
  (u:ℂ)⁻¹ • sandwiched P projection_P (residualLeg u v i r) (residualLeg u v i s) (C u v j)
    (P_mul_residualLeg u v i r) (P_mul_residualLeg u v i s)

@[simp] theorem pResidual_val (u v : ℝ) (i j : ι) (r s : Option Bool) :
    (pResidual u v i j r s : Operator ι)=normalizedResidual u v i j r s := rfl

def pDiagonal (u v : ℝ) (i k : ι) (r : Bool) : PCorner ι :=
  ((weight u v (!r):ℂ)/(u:ℂ)) • sandwiched P projection_P
    (supportedLeg u v i r) (supportedLeg u v i r) (edgeCreation k (!r) (!r))
    (P_mul_supportedLeg u v i r) (P_mul_supportedLeg u v i r)

@[simp] theorem pDiagonal_val (u v : ℝ) (i k : ι) (r : Bool) :
    (pDiagonal u v i k r : Operator ι)=normalizedDiagonal u v i k r := rfl

theorem P_mul_legSupport (u v : ℝ) (i : ι) (r : Bool) : P*legSupport u v i r=legSupport u v i r := by
  cases r
  · exact projection_P.isIdempotentElem.eq
  · exact edgeRange_le_P u v i

theorem legSupport_projection (u v : ℝ) (i : ι) (r : Bool) : IsStarProjection (legSupport u v i r) := by
  cases r
  · exact projection_P
  · exact edgeRange_projection u v i

def pSupport (u v : ℝ) (i j : ι) (r : Bool) : pFilled u v i j :=
  ⟨⟨legSupport u v i r,P_mul_legSupport u v i r,by
    simpa only [star_mul,projection_P.isSelfAdjoint.star_eq,(legSupport_projection u v i r).isSelfAdjoint.star_eq]
      using congrArg star (P_mul_legSupport u v i r)⟩,
    edgeAlgebra_le_filled u v i j (by
      cases r with
      | false => exact P_mem_edge u v i
      | true => exact edgeRange_mem_edge u v i)⟩

theorem pSupport_projection (u v : ℝ) (i j : ι) (r : Bool) : IsStarProjection (pSupport u v i j r) := by
  constructor
  · apply Subtype.ext;apply Subtype.ext
    exact (legSupport_projection u v i r).isIdempotentElem.eq
  · apply Subtype.ext;apply Subtype.ext
    exact (legSupport_projection u v i r).isSelfAdjoint.star_eq

theorem pSupport_false (u v : ℝ) (i j : ι) : pSupport u v i j false=1 := rfl

theorem pFresh_covariance (u v : ℝ) (hu : u≠0) (hv : v≠0)
    (i j n m : ι) (hji : j≠i) (hni : n≠i) (hnj : n≠j) (hmi : m≠i) (hmj : m≠j)
    (r s r' s' : Bool) (a : pFilled u v i j) :
    star (pFresh u v i n r s)*(a : PCorner ι)*pFresh u v i m r' s'=
      if n=m ∧ r=r' ∧ s=s' then
        pTrace u v i j (a*pSupport u v i j r) • (pSupport u v i j s : PCorner ι) else 0 := by
  apply Subtype.ext
  have h := normalizedCreation_filled_covariance u v hu hv i j n m hji hni hnj hmi hmj r s r' s' (filledOfCorner a)
  split_ifs with hh
  · rw [ite_eq_left hh] at h
    exact h
  · rw [ite_eq_right hh] at h
    exact h

end FreeGroupFactorMain.WeightedFock

end

namespace FreeGroupFactorMain.WeightedFock

section
open FreeFock Amplification RectangularAbsorption
variable {ι : Type u_4} [DecidableEq ι]

theorem legSupport_mul_leg (u v : ℝ) (hv : 0<v) (hvu : v<u) (i : ι) (r : Bool) :
    legSupport u v i r*supportedLeg u v i r=supportedLeg u v i r := by
  cases r
  · exact projection_P.isIdempotentElem.eq
  · change (edgePolar u v i*star (edgePolar u v i))*edgePolar u v i=edgePolar u v i
    rw [mul_assoc,edgePolar_initial u v hv.le hvu,edgePolar_right]

theorem pFresh_supported (u v : ℝ) (hv : 0<v) (hvu : v<u) (i j n : ι) (r s : Bool) :
    (pSupport u v i j r : PCorner ι)*pFresh u v i n r s*(pSupport u v i j s : PCorner ι)=pFresh u v i n r s := by
  apply Subtype.ext
  change legSupport u v i r*normalizedCreation u v i n r s*legSupport u v i s=normalizedCreation u v i n r s
  have hs : star (supportedLeg u v i s)*legSupport u v i s=star (supportedLeg u v i s) := by
    simpa only [star_mul,(legSupport_projection u v i s).isSelfAdjoint.star_eq]
      using congrArg star (legSupport_mul_leg u v hv hvu i s)
  simp only [normalizedCreation,supportedCreation,mul_smul_comm,smul_mul_assoc]
  rw [← mul_assoc,← mul_assoc,legSupport_mul_leg u v hv hvu i r,mul_assoc,hs]

end

open FreeFock Amplification RectangularAbsorption
variable {ι : Type u_5} [DecidableEq ι]

def pResidualSupport (u v : ℝ) (i j : ι) : Option Bool → pFilled u v i j
  | none => 1-pSupport u v i j true
  | some _ => pSupport u v i j true

@[simp] theorem pResidualSupport_val (u v : ℝ) (i j : ι) (r : Option Bool) :
    ((pResidualSupport u v i j r : PCorner ι):Operator ι)=residualSupport u v i r := by
  cases r <;> rfl

theorem pResidualSupport_projection (u v : ℝ) (i j : ι) (r : Option Bool) :
    IsStarProjection (pResidualSupport u v i j r) := by
  cases r with
  | none => exact (pSupport_projection u v i j true).one_sub
  | some r => exact pSupport_projection u v i j true

theorem residualSupport_projection (u v : ℝ) (i : ι) (r : Option Bool) :
    IsStarProjection (residualSupport u v i r) := by
  cases r with
  | none => exact edgeDefect_projection u v i
  | some r => exact edgeRange_projection u v i

theorem residualSupport_mul_leg (u v : ℝ) (hv : 0<v) (hvu : v<u) (i : ι) (r : Option Bool) :
    residualSupport u v i r*residualLeg u v i r=residualLeg u v i r := by
  rcases r with _ | (_|_)
  · exact (edgeDefect_projection u v i).isIdempotentElem.eq
  · exact (edgeRange_projection u v i).isIdempotentElem.eq
  · exact legSupport_mul_leg u v hv hvu i true

theorem pResidual_supported (u v : ℝ) (hv : 0<v) (hvu : v<u) (i j : ι) (r s : Option Bool) :
    (pResidualSupport u v i j r : PCorner ι)*pResidual u v i j r s*
      (pResidualSupport u v i j s : PCorner ι)=pResidual u v i j r s := by
  apply Subtype.ext
  simp only [MulMemClass.coe_mul,pResidualSupport_val,pResidual_val]
  change residualSupport u v i r*normalizedResidual u v i j r s*residualSupport u v i s=normalizedResidual u v i j r s
  have hs : star (residualLeg u v i s)*residualSupport u v i s=star (residualLeg u v i s) := by
    simpa only [star_mul,(residualSupport_projection u v i s).isSelfAdjoint.star_eq]
      using congrArg star (residualSupport_mul_leg u v hv hvu i s)
  simp only [normalizedResidual,residualCreation,mul_smul_comm,smul_mul_assoc]
  rw [← mul_assoc,← mul_assoc,residualSupport_mul_leg u v hv hvu i r,mul_assoc,hs]

theorem pDiagonal_supported (u v : ℝ) (hv : 0<v) (hvu : v<u) (i j k : ι) (r : Bool) :
    (pSupport u v i j r : PCorner ι)*pDiagonal u v i k r*(pSupport u v i j r : PCorner ι)=pDiagonal u v i k r := by
  apply Subtype.ext
  change legSupport u v i r*normalizedDiagonal u v i k r*legSupport u v i r=normalizedDiagonal u v i k r
  have hs : star (supportedLeg u v i r)*legSupport u v i r=star (supportedLeg u v i r) := by
    simpa only [star_mul,(legSupport_projection u v i r).isSelfAdjoint.star_eq]
      using congrArg star (legSupport_mul_leg u v hv hvu i r)
  simp only [normalizedDiagonal,transportedDiagonal,mul_smul_comm,smul_mul_assoc]
  rw [← mul_assoc,← mul_assoc,legSupport_mul_leg u v hv hvu i r,mul_assoc,hs]

theorem pResidual_covariance (u v : ℝ) (hu : u≠0) (hv : v≠0)
    (i j : ι) (hji : j≠i) (r s r' s' : Option Bool)
    (hrs : ¬(r=none ∧ s=none)) (hrs' : ¬(r'=none ∧ s'=none)) (a : pFilled u v i j) :
    star (pResidual u v i j r s)*(a : PCorner ι)*pResidual u v i j r' s'=
      if r=r' ∧ s=s' then pTrace u v i j (a*pResidualSupport u v i j r) •
        (pResidualSupport u v i j s : PCorner ι) else 0 := by
  apply Subtype.ext
  have h := normalizedResidual_filled_covariance u v hu hv i j hji r s r' s' hrs hrs' (filledOfCorner a)
  split_ifs with hh
  · rw [ite_eq_left hh] at h
    change star (normalizedResidual u v i j r s)*a.val.val*normalizedResidual u v i j r' s'=
      pVacuumTrace u v (a.val.val*(pResidualSupport u v i j r).val.val) • (pResidualSupport u v i j s).val.val
    rw [pResidualSupport_val,pResidualSupport_val]
    exact h
  · rw [ite_eq_right hh] at h
    exact h

theorem pDiagonal_covariance (u v : ℝ) (hu : u≠0) (hv : v≠0)
    (i j k l : ι) (hji : j≠i) (hjk : j≠k) (hjl : j≠l)
    (r s : Bool) (a : pFilled u v i j) :
    star (pDiagonal u v i k r)*(a : PCorner ι)*pDiagonal u v i l s=
      if k=l ∧ r=s then pTrace u v i j (a*pSupport u v i j r) •
        (pSupport u v i j r : PCorner ι) else 0 := by
  apply Subtype.ext
  have h := normalizedDiagonal_filled_covariance u v hu hv i j k l hji hjk hjl r s (filledOfCorner a)
  split_ifs with hh
  · rw [ite_eq_left hh] at h
    exact h
  · rw [ite_eq_right hh] at h
    exact h

theorem pFresh_residual (u v : ℝ) (i j n : ι) (hji : j≠i) (hni : n≠i) (hnj : n≠j)
    (r s : Bool) (a b : Option Bool) (hab : ¬(a=none ∧ b=none)) :
    Orthogonal (pFilled u v i j) (pFresh u v i n r s) (pResidual u v i j a b) := by
  intro T
  apply Subtype.ext
  exact normalized_fresh_residual u v i j n hji hni hnj r s a b hab (filledOfCorner T)

theorem pFresh_diagonal (u v : ℝ) (i j n k : ι) (hji : j≠i) (hni : n≠i) (hnj : n≠j)
    (hnk : n≠k) (hjk : j≠k) (r s t : Bool) :
    Orthogonal (pFilled u v i j) (pFresh u v i n r s) (pDiagonal u v i k t) := by
  intro T
  apply Subtype.ext
  exact normalized_fresh_diagonal u v i j n k hji hni hnj hnk hjk r s t (filledOfCorner T)

theorem pResidual_diagonal (u v : ℝ) (i j k : ι) (hji : j≠i) (hjk : j≠k)
    (a b : Option Bool) (hab : ¬(a=none ∧ b=none)) (r : Bool) :
    Orthogonal (pFilled u v i j) (pResidual u v i j a b) (pDiagonal u v i k r) := by
  intro T
  apply Subtype.ext
  exact normalized_residual_diagonal u v i j k hji hjk a b hab r (filledOfCorner T)
end FreeGroupFactorMain.WeightedFock

end

end OAI
end

section
namespace OAI

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7

noncomputable section
namespace FreeGroupFactorMain.CircularRotation

def q : ℂ := (Real.sqrt 2 : ℂ)⁻¹

theorem q_star : star q=q := by
  simp only [q,Complex.star_def,map_inv₀,Complex.conj_ofReal]

theorem q_sq : q^2=1/2 := by
  have hs : (Real.sqrt 2 : ℂ)^2=2 := by
    exact_mod_cast Real.sq_sqrt (by norm_num : (0:ℝ)≤2)
  rw [q,inv_pow,hs]
  norm_num

theorem two_q_mul {A : Type u_1} [AddCommGroup A] [Module ℂ A] (X : A) :
    q • (q • X+q • X)=X := by
  rw [smul_add,smul_smul,← add_smul,← pow_two,q_sq]
  norm_num

theorem qI_star : star (q*Complex.I)=-(q*Complex.I) := by
  rw [star_mul,q_star,Complex.star_def,Complex.conj_I]
  ring

section

variable {A : Type u_2} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]

def plus (X Y : A) : A := q • X+(q*Complex.I) • Y
def minus (X Y : A) : A := q • X-(q*Complex.I) • Y

omit [StarRing A] [StarModule ℂ A] in
theorem plus_add_minus (X Y : A) : q • (plus X Y+minus X Y)=X := by
  rw [plus,minus]
  have he : q • X+(q*Complex.I) • Y+(q • X-(q*Complex.I) • Y)=q • X+q • X := by abel
  rw [he,two_q_mul]

omit [StarRing A] [StarModule ℂ A] in
theorem plus_sub_minus (X Y : A) : (-q*Complex.I) • (plus X Y-minus X Y)=Y := by
  have he : plus X Y-minus X Y=(q*Complex.I) • Y+(q*Complex.I) • Y := by unfold plus minus;abel
  rw [he,smul_add,smul_smul,← add_smul]
  have hc : (-q*Complex.I)*(q*Complex.I)+(-q*Complex.I)*(q*Complex.I)=1 := by
    calc
      _ = -2*q^2*Complex.I^2 := by ring
      _ = 1 := by rw [q_sq,Complex.I_sq];norm_num
  rw [hc,one_smul]

theorem paired_plus (X Y : A) : plus X Y+star (minus X Y)=plus (X+star X) (Y+star Y) := by
  simp only [plus,minus,star_sub,star_smul,q_star,qI_star,neg_smul,smul_add]
  abel

theorem paired_minus (X Y : A) : minus X Y+star (plus X Y)=minus (X+star X) (Y+star Y) := by
  simp only [plus,minus,star_add,star_smul,q_star,qI_star,neg_smul,smul_add]
  abel

theorem generation (X Y : A) (M : StarSubalgebra ℂ A) :
    (X+star X∈M ∧ Y+star Y∈M) ↔
      (plus X Y+star (minus X Y)∈M ∧ minus X Y+star (plus X Y)∈M) := by
  rw [paired_plus,paired_minus]
  constructor
  · rintro ⟨hX,hY⟩
    exact ⟨add_mem (M.smul_mem hX _) (M.smul_mem hY _),sub_mem (M.smul_mem hX _) (M.smul_mem hY _)⟩
  · rintro ⟨hP,hM⟩
    constructor
    · rw [← plus_add_minus (X+star X) (Y+star Y)]
      exact M.smul_mem (add_mem hP hM) _
    · rw [← plus_sub_minus (X+star X) (Y+star Y)]
      exact M.smul_mem (sub_mem hP hM) _

theorem contraction (X Y a Z : A)
    (hXX : star X*a*X=Z) (hYY : star Y*a*Y=Z)
    (hXY : star X*a*Y=0) (hYX : star Y*a*X=0) :
    star (plus X Y)*a*plus X Y=Z ∧ star (minus X Y)*a*minus X Y=Z ∧
      star (plus X Y)*a*minus X Y=0 ∧ star (minus X Y)*a*plus X Y=0 := by
  have h1 : q*q=1/2 := by rw [← pow_two,q_sq]
  have h2 : (q*Complex.I)*(q*Complex.I)=-(1/2) := by
    calc
      _ = q^2*Complex.I^2 := by ring
      _ = -(1/2) := by rw [q_sq,Complex.I_sq];ring
  simp only [plus,minus,star_add,star_sub,star_smul,q_star,qI_star,add_mul,sub_mul,mul_add,mul_sub,
    smul_mul_assoc,mul_smul_comm]
  simp only [hXX,hYY,hXY,hYX,smul_zero,add_zero,zero_add,sub_zero,zero_sub]
  simp only [smul_smul,mul_neg,neg_neg,h1,h2]
  repeat' constructor
  all_goals match_scalars
  all_goals ring_nf
  all_goals norm_num [q_sq,Complex.I_sq]

end

variable {A : Type u_3} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]

variable {S : Type u_4} {P : Type u_5}
abbrev PairedIndex (S : Type u_6) (P : Type u_7) := S ⊕ (P×Bool)

def flip : PairedIndex S P → PairedIndex S P
  | .inl i => .inl i
  | .inr (j,b) => .inr (j,!b)

def rotate (R : PairedIndex S P → A) : PairedIndex S P → A
  | .inl i => R (.inl i)
  | .inr (j,false) => plus (R (.inr (j,false))) (R (.inr (j,true)))
  | .inr (j,true) => minus (R (.inr (j,false))) (R (.inr (j,true)))

 theorem rotate_covariance [DecidableEq S] [DecidableEq P] (R : PairedIndex S P → A) (a Z : A)
    (h : ∀ i j,star (R i)*a*R j=if i=j then Z else 0) (i j : PairedIndex S P) :
    star (rotate R i)*a*rotate R j=if i=j then Z else 0 := by
  rcases i with i | ⟨i,b⟩ <;> rcases j with j | ⟨j,c⟩
  · exact h (.inl i) (.inl j)
  · cases c <;> simp [rotate,plus,minus,mul_add,mul_sub,h]
  · cases b <;> simp [rotate,plus,minus,star_add,star_sub,star_smul,add_mul,h]
  · by_cases hij : i=j
    · subst j
      have hXX : star (R (.inr (i,false)))*a*R (.inr (i,false))=Z := by simpa using h (.inr (i,false)) (.inr (i,false))
      have hYY : star (R (.inr (i,true)))*a*R (.inr (i,true))=Z := by simpa using h (.inr (i,true)) (.inr (i,true))
      have hXY : star (R (.inr (i,false)))*a*R (.inr (i,true))=0 := by simpa using h (.inr (i,false)) (.inr (i,true))
      have hYX : star (R (.inr (i,true)))*a*R (.inr (i,false))=0 := by simpa using h (.inr (i,true)) (.inr (i,false))
      have hh := contraction _ _ a Z hXX hYY hXY hYX
      cases b <;> cases c
      · simpa only [rotate,ite_true] using hh.1
      · simpa [rotate] using hh.2.2.1
      · simpa [rotate] using hh.2.2.2
      · simpa only [rotate,ite_true] using hh.2.1
    · cases b <;> cases c <;>
        simp [rotate,plus,minus,star_add,star_sub,star_smul,add_mul,mul_add,mul_sub,h,hij]

theorem rotate_generation (R : PairedIndex S P → A) (M : StarSubalgebra ℂ A) :
    (∀ i,R i+star (R i)∈M) ↔ (∀ i,rotate R i+star (rotate R (flip i))∈M) := by
  constructor
  · intro h i
    rcases i with i | ⟨j,(_|_)⟩
    · exact h (.inl i)
    · exact ((generation _ _ M).mp ⟨h (.inr (j,false)),h (.inr (j,true))⟩).1
    · exact ((generation _ _ M).mp ⟨h (.inr (j,false)),h (.inr (j,true))⟩).2
  · intro h i
    rcases i with i | ⟨j,(_|_)⟩
    · exact h (.inl i)
    · exact ((generation _ _ M).mpr ⟨h (.inr (j,false)),h (.inr (j,true))⟩).1
    · exact ((generation _ _ M).mpr ⟨h (.inr (j,false)),h (.inr (j,true))⟩).2
end FreeGroupFactorMain.CircularRotation

end

end OAI
end

section
namespace OAI

noncomputable section
namespace FreeGroupFactorMain.WeightedCornerIndex
open CircularRotation
abbrev SelfIndex := ℕ ⊕ (Bool ⊕ Bool)
abbrev PairIndex := ℕ ⊕ Fin 3
abbrev Index := PairedIndex SelfIndex PairIndex

inductive Kind where
  | fresh : ℕ → Bool → Bool → Kind
  | residual : Option Bool → Option Bool → Kind
  | diagonal : Bool → Kind
  deriving DecidableEq

namespace Kind

def valid : Kind → Prop
  | .fresh _ r s => ¬(r=false ∧ s=false)
  | .residual r s => ¬(r=none ∧ s=none)
  | .diagonal _ => True

instance (k : Kind) : Decidable k.valid := by cases k <;> unfold valid <;> infer_instance

def transpose : Kind → Kind
  | .fresh n r s => .fresh n s r
  | .residual r s => .residual s r
  | .diagonal r => .diagonal r
end Kind

def endpoints : Fin 3 → Option Bool × Option Bool :=
  Fin.cases (none,some false) (Fin.cases (none,some true) (fun _ => (some false,some true)))

def description : Index → Kind
  | .inl (.inl n) => .fresh n true true
  | .inl (.inr (.inl b)) => .residual (some b) (some b)
  | .inl (.inr (.inr b)) => .diagonal b
  | .inr (.inl n,b) => .fresh n b (!b)
  | .inr (.inr k,false) => .residual (endpoints k).1 (endpoints k).2
  | .inr (.inr k,true) => .residual (endpoints k).2 (endpoints k).1

def indexOf : Kind → Index
  | .fresh n false false => .inl (.inl n)
  | .fresh n false true => .inr (.inl n,false)
  | .fresh n true false => .inr (.inl n,true)
  | .fresh n true true => .inl (.inl n)
  | .residual none none => .inl (.inl 0)
  | .residual none (some false) => .inr (.inr 0,false)
  | .residual (some false) none => .inr (.inr 0,true)
  | .residual none (some true) => .inr (.inr 1,false)
  | .residual (some true) none => .inr (.inr 1,true)
  | .residual (some false) (some true) => .inr (.inr 2,false)
  | .residual (some true) (some false) => .inr (.inr 2,true)
  | .residual (some false) (some false) => .inl (.inr (.inl false))
  | .residual (some true) (some true) => .inl (.inr (.inl true))
  | .diagonal b => .inl (.inr (.inr b))

theorem indexOf_description (i : Index) : indexOf (description i)=i := by
  rcases i with (n | (b | b)) | ⟨(n | k),b⟩
  · rfl
  · cases b <;> rfl
  · rfl
  · cases b <;> rfl
  · fin_cases k <;> cases b <;> rfl

theorem description_injective : Function.Injective description :=
  Function.LeftInverse.injective indexOf_description

theorem description_valid (i : Index) : (description i).valid := by
  rcases i with (n | (b | b)) | ⟨(n | k),b⟩
  · simp [description,Kind.valid]
  · simp [description,Kind.valid]
  · trivial
  · cases b <;> simp [description,Kind.valid]
  · fin_cases k <;> cases b <;> decide

theorem description_flip (i : Index) :
    description (CircularRotation.flip i)=(description i).transpose := by
  rcases i with (n | (b | b)) | ⟨(n | k),b⟩
  · rfl
  · rfl
  · rfl
  · cases b <;> rfl
  · cases b <;> rfl

def reservoirCode : Index × ℕ ≃ ℕ :=
  @Denumerable.eqv _ (Classical.choice (nonempty_denumerable (Index × ℕ)))
end FreeGroupFactorMain.WeightedCornerIndex

end

end OAI
end

section
namespace OAI

noncomputable section

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10

namespace FreeGroupFactorMain.PairedAbsorption
open RectangularAbsorption CircularRotation
variable {A : Type u_1} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]
variable {S : Type u_2} {P : Type u_3} [DecidableEq S] [DecidableEq P]
abbrev Index (S : Type u_4) (P : Type u_5) := PairedIndex S P

structure Input (B : StarSubalgebra ℂ A) (S : Type u_6) (P : Type u_7) [DecidableEq S] [DecidableEq P] where
  τ : B →ₗ[ℂ] ℂ
  tracial : ∀ a b,τ (a*b)=τ (b*a)
  p : Index S P → B
  q : Index S P → B
  projection : ∀ i,IsStarProjection (p i)
  projectionq : ∀ i,IsStarProjection (q i)
  pq : ∀ i,p (CircularRotation.flip i)=q i
  qp : ∀ i,q (CircularRotation.flip i)=p i
  raw : Index S P → ℕ → A
  extra : Index S P → A
  supported : ∀ i,(p i:A)*extra i*(q i:A)=extra i
  raw_cov : ∀ i j n m (a : B),star (raw i n)*(a:A)*raw j m=
    if i=j ∧ n=m then τ a • (1:A) else 0
  extra_cov : ∀ i j (a : B),star (extra i)*(a:A)*extra j=
    if i=j then τ (a*p i) • (q i:A) else 0
  raw_extra : ∀ i j n (a : B),star (raw i n)*(a:A)*extra j=0

namespace Input
variable {B : StarSubalgebra ℂ A} (d : Input B S P)

def reservoir (i : Index S P) (n : ℕ) : A := rotate (fun k => d.raw k n) i

theorem reservoir_cov (i j : Index S P) (n m : ℕ) (a : B) :
    star (d.reservoir i n)*(a:A)*d.reservoir j m=
      if i=j ∧ n=m then d.τ a • (1:A) else 0 := by
  by_cases hnm : n=m
  · subst m
    have hh := rotate_covariance (fun k => d.raw k n) (a:A) (d.τ a • (1:A))
      (fun i j => by simpa only [and_true] using d.raw_cov i j n n a) i j
    simpa only [reservoir,and_true] using hh
  · rcases i with i | ⟨i,b⟩ <;> rcases j with j | ⟨j,c⟩
    · simpa only [reservoir,rotate,hnm,and_false,ite_false] using d.raw_cov (.inl i) (.inl j) n m a
    · cases c <;> simp [reservoir,rotate,plus,minus,mul_add,mul_sub,d.raw_cov,hnm]
    · cases b <;> simp [reservoir,rotate,plus,minus,star_smul,star_add,star_sub,add_mul,d.raw_cov,hnm]
    · cases b <;> cases c <;>
        simp [reservoir,rotate,plus,minus,star_smul,star_add,star_sub,add_mul,mul_add,mul_sub,d.raw_cov,hnm]

theorem reservoir_extra (i j : Index S P) (n : ℕ) (a : B) :
    star (d.reservoir i n)*(a:A)*d.extra j=0 := by
  rcases i with i | ⟨i,b⟩
  · exact d.raw_extra (.inl i) j n a
  · cases b <;> simp [reservoir,rotate,plus,minus,star_smul,star_add,star_sub,add_mul,d.raw_extra]

def data (i : Index S P) : Data B where
  τ := d.τ
  tracial := d.tracial
  p := d.p i
  q := d.q i
  projection := d.projection i
  projectionq := d.projectionq i
  C := d.reservoir i
  D := d.extra i
  D_supported := d.supported i
  C_cov a n m := by simpa only [true_and] using d.reservoir_cov i i n m a
  D_cov a := by simpa only [ite_true] using d.extra_cov i i a
  C_D a n := d.reservoir_extra i i n a
  D_C a n := (Orthogonal.symm (d.reservoir_extra i i n)) a

def family : Family B (Index S P) where
  data := d.data
  CC i j hij n m a := by simpa only [data,hij,false_and,ite_false] using d.reservoir_cov i j n m a
  CD i j _ n a := d.reservoir_extra i j n a
  DD i j hij a := by simpa only [data,ite_eq_right hij] using d.extra_cov i j a

def output (i : Index S P) (n : ℕ) : A := d.family.output i n

theorem output_cov (i j : Index S P) (n m : ℕ) (a : B) :
    star (d.output i n)*(a:A)*d.output j m=
      if i=j ∧ n=m then d.τ a • (1:A) else 0 := by
  have hh := d.family.output_covariance i j n m a
  split_ifs with h
  · rw [ite_eq_left h] at hh; exact hh
  · rw [ite_eq_right h] at hh; exact hh

theorem output_generation (M : StarSubalgebra ℂ A)
    (hpM : ∀ i,(d.p i:A)∈M) (hqM : ∀ i,(d.q i:A)∈M) :
    ((∀ i,d.extra i+star (d.extra (CircularRotation.flip i))∈M) ∧
      ∀ i n,d.raw i n+star (d.raw i n)∈M) ↔
        ∀ i n,d.output i n+star (d.output (CircularRotation.flip i) n)∈M := by
  have hh := d.family.output_generation CircularRotation.flip d.pq d.qp M hpM hqM
  change ((∀ i,d.extra i+star (d.extra (CircularRotation.flip i))∈M) ∧
      ∀ i n,d.reservoir i n+star (d.reservoir (CircularRotation.flip i) n)∈M) ↔
      ∀ i n,d.output i n+star (d.output (CircularRotation.flip i) n)∈M at hh
  rw [← hh]
  apply and_congr_right
  intro _
  constructor
  · intro h i n
    exact (rotate_generation (fun k => d.raw k n) M).mp (fun k => h k n) i
  · intro h i n
    exact (rotate_generation (fun k => d.raw k n) M).mpr (fun k => h k n) i
end Input
end FreeGroupFactorMain.PairedAbsorption

namespace FreeGroupFactorMain.WeightedFock
open FreeFock Amplification RectangularAbsorption WeightedCornerIndex

abbrev Base (u v : ℝ) := pFilled u v (0:ℕ) 1

def kindCreator (u v : ℝ) : Kind → PCorner ℕ
  | .fresh n r s => pFresh u v 0 (n+2) r s
  | .residual r s => pResidual u v 0 1 r s
  | .diagonal r => pDiagonal u v 0 0 r

def kindLeft (u v : ℝ) : Kind → Base u v
  | .fresh _ r _ => pSupport u v 0 1 r
  | .residual r _ => pResidualSupport u v 0 1 r
  | .diagonal r => pSupport u v 0 1 r

def kindRight (u v : ℝ) : Kind → Base u v
  | .fresh _ _ s => pSupport u v 0 1 s
  | .residual _ s => pResidualSupport u v 0 1 s
  | .diagonal r => pSupport u v 0 1 r

theorem kindLeft_projection (u v : ℝ) (k : Kind) : IsStarProjection (kindLeft u v k) := by
  cases k
  · exact pSupport_projection u v 0 1 _
  · exact pResidualSupport_projection u v 0 1 _
  · exact pSupport_projection u v 0 1 _

theorem kindRight_projection (u v : ℝ) (k : Kind) : IsStarProjection (kindRight u v k) := by
  cases k
  · exact pSupport_projection u v 0 1 _
  · exact pResidualSupport_projection u v 0 1 _
  · exact pSupport_projection u v 0 1 _

theorem kindLeft_transpose (u v : ℝ) (k : Kind) : kindLeft u v k.transpose=kindRight u v k := by
  cases k <;> rfl

theorem kindRight_transpose (u v : ℝ) (k : Kind) : kindRight u v k.transpose=kindLeft u v k := by
  cases k <;> rfl

theorem kindCreator_supported (u v : ℝ) (hv : 0<v) (hvu : v<u) (k : Kind) :
    (kindLeft u v k : PCorner ℕ)*kindCreator u v k*(kindRight u v k : PCorner ℕ)=kindCreator u v k := by
  cases k
  · exact pFresh_supported u v hv hvu 0 1 _ _ _
  · exact pResidual_supported u v hv hvu 0 1 _ _
  · exact pDiagonal_supported u v hv hvu 0 1 0 _

theorem kindCreator_covariance (u v : ℝ) (hu : u≠0) (hv : v≠0)
    (k l : Kind) (hk : k.valid) (hl : l.valid) (a : Base u v) :
    star (kindCreator u v k)*(a : PCorner ℕ)*kindCreator u v l=
      if k=l then pTrace u v 0 1 (a*kindLeft u v k) • (kindRight u v k : PCorner ℕ) else 0 := by
  cases k with
  | fresh n r s =>
    cases l with
    | fresh m t w =>
      have hh := pFresh_covariance u v hu hv (0:ℕ) 1 (n+2) (m+2) (by omega)
        (by omega) (by omega) (by omega) (by omega) r s t w a
      simpa only [kindCreator,kindLeft,kindRight,Kind.fresh.injEq,Nat.add_right_cancel_iff] using hh
    | residual t w =>
      rw [ite_eq_right (by simp)]
      exact pFresh_residual u v (0:ℕ) 1 (n+2) (by omega) (by omega) (by omega) r s t w hl a
    | diagonal t =>
      rw [ite_eq_right (by simp)]
      exact pFresh_diagonal u v (0:ℕ) 1 (n+2) 0 (by omega) (by omega) (by omega) (by omega) (by omega) r s t a
  | residual r s =>
    cases l with
    | fresh m t w =>
      rw [ite_eq_right (by simp)]
      exact (pFresh_residual u v (0:ℕ) 1 (m+2) (by omega) (by omega) (by omega) t w r s hk).symm a
    | residual t w =>
      simpa only [kindCreator,kindLeft,kindRight,Kind.residual.injEq]
        using pResidual_covariance u v hu hv (0:ℕ) 1 (by omega) r s t w hk hl a
    | diagonal t =>
      rw [ite_eq_right (by simp)]
      exact pResidual_diagonal u v (0:ℕ) 1 0 (by omega) (by omega) r s hk t a
  | diagonal r =>
    cases l with
    | fresh m t w =>
      rw [ite_eq_right (by simp)]
      exact (pFresh_diagonal u v (0:ℕ) 1 (m+2) 0 (by omega) (by omega) (by omega) (by omega) (by omega) t w r).symm a
    | residual t w =>
      rw [ite_eq_right (by simp)]
      exact (pResidual_diagonal u v (0:ℕ) 1 0 (by omega) (by omega) t w hl r).symm a
    | diagonal t =>
      simpa only [kindCreator,kindLeft,kindRight,Kind.diagonal.injEq,true_and]
        using pDiagonal_covariance u v hu hv (0:ℕ) 1 0 0 (by omega) (by omega) (by omega) r t a

def rawReservoir (u v : ℝ) (i : WeightedCornerIndex.Index) (n : ℕ) : PCorner ℕ :=
  pFresh u v 0 (reservoirCode (i,n)+2) false false

theorem rawReservoir_covariance (u v : ℝ) (hu : u≠0) (hv : v≠0)
    (i j : WeightedCornerIndex.Index) (n m : ℕ) (a : Base u v) :
    star (rawReservoir u v i n)*(a : PCorner ℕ)*rawReservoir u v j m=
      if i=j ∧ n=m then pTrace u v 0 1 a • (1:PCorner ℕ) else 0 := by
  have hh := pFresh_covariance u v hu hv (0:ℕ) 1 (reservoirCode (i,n)+2) (reservoirCode (j,m)+2)
    (by omega) (by omega) (by omega) (by omega) (by omega) false false false false a
  simpa only [rawReservoir,and_true,pSupport_false,mul_one,OneMemClass.coe_one,
    Nat.add_right_cancel_iff,reservoirCode.injective.eq_iff,Prod.mk.injEq] using hh

theorem rawReservoir_extra (u v : ℝ) (hu : u≠0) (hv : v≠0)
    (i : WeightedCornerIndex.Index) (n : ℕ) (k : Kind) (hk : k.valid) (a : Base u v) :
    star (rawReservoir u v i n)*(a : PCorner ℕ)*kindCreator u v k=0 := by
  cases k with
  | fresh m r s =>
    have hh := pFresh_covariance u v hu hv (0:ℕ) 1 (reservoirCode (i,n)+2) (m+2)
      (by omega) (by omega) (by omega) (by omega) (by omega) false false r s a
    rw [ite_eq_right (fun h => hk ⟨h.2.1.symm,h.2.2.symm⟩)] at hh
    exact hh
  | residual r s =>
    exact pFresh_residual u v (0:ℕ) 1 (reservoirCode (i,n)+2)
      (by omega) (by omega) (by omega) false false r s hk a
  | diagonal r =>
    exact pFresh_diagonal u v (0:ℕ) 1 (reservoirCode (i,n)+2) 0
      (by omega) (by omega) (by omega) (by omega) (by omega) false false r a

def cornerAbsorption (u v : ℝ) (hv : 0<v) (hvu : v<u) :
    PairedAbsorption.Input (Base u v) SelfIndex PairIndex where
  τ := pTrace u v 0 1
  tracial := pTrace_tracial u v (hv.trans hvu).ne' hv.ne' 0 1
  p i := kindLeft u v (description i)
  q i := kindRight u v (description i)
  projection i := kindLeft_projection u v _
  projectionq i := kindRight_projection u v _
  pq i := by rw [description_flip,kindLeft_transpose]
  qp i := by rw [description_flip,kindRight_transpose]
  raw := rawReservoir u v
  extra i := kindCreator u v (description i)
  supported i := kindCreator_supported u v hv hvu _
  raw_cov := rawReservoir_covariance u v (hv.trans hvu).ne' hv.ne'
  extra_cov i j a := by
    simpa only [description_injective.eq_iff] using
      kindCreator_covariance u v (hv.trans hvu).ne' hv.ne' _ _ (description_valid i) (description_valid j) a
  raw_extra i j n a := rawReservoir_extra u v (hv.trans hvu).ne' hv.ne' i n _ (description_valid j) a
end FreeGroupFactorMain.WeightedFock

namespace FreeGroupFactorMain.PairedAbsorption.Input
open RectangularAbsorption CircularRotation
variable {A : Type u_8} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]
variable {S : Type u_9} {P : Type u_10} [DecidableEq S] [DecidableEq P]
variable {B : StarSubalgebra ℂ A} (d : PairedAbsorption.Input B S P)

theorem output_mem (K : Submodule ℂ A)
    (hK : ∀ p q : B, ∀ x∈K,(p:A)*x*(q:A)∈K)
    (hextra : ∀ i,d.extra i∈K) (hraw : ∀ i n,d.raw i n∈K) (i : Index S P) (n : ℕ) :
    d.output i n∈K := by
  have hr (i : Index S P) (n : ℕ) : d.reservoir i n∈K := by
    rcases i with i | ⟨i,b⟩
    · exact hraw _ n
    · cases b
      · exact K.add_mem (K.smul_mem _ (hraw _ n)) (K.smul_mem _ (hraw _ n))
      · exact K.sub_mem (K.smul_mem _ (hraw _ n)) (K.smul_mem _ (hraw _ n))
  have hp (n : ℕ) : part (d.p i:A) (d.q i:A) (d.reservoir i) n∈K := hK _ _ _ (hr i n)
  have hrem (n : ℕ) : remainder (d.p i:A) (d.q i:A) (d.reservoir i) n∈K := K.sub_mem (hr i n) (hp n)
  cases n with
  | zero => exact K.add_mem (hextra i) (hrem 0)
  | succ n => exact K.add_mem (hp n) (hrem (n+1))
end FreeGroupFactorMain.PairedAbsorption.Input

end

end OAI
end

section
namespace OAI

noncomputable section

universe u_1 u_2 u_3 u_4 u_5 u_6

namespace FreeGroupFactorMain.WeightedFock
open FreeFock Amplification WeightedCornerIndex

def oldAnnihilators (u v : ℝ) : Submodule ℂ (PCorner ℕ) where
  carrier := {X | ∀ a : Base u v, star (X : Operator ℕ) ((a.val : Operator ℕ) (vacuum u v))=0}
  zero_mem' := by intro a; simp [star_zero (Operator ℕ)]
  add_mem' := by
    intro X Y hX hY a
    change star ((X : Operator ℕ)+(Y : Operator ℕ)) _=0
    rw [star_add (R := Operator ℕ),add_apply,hX a,hY a,add_zero]
  smul_mem' := by
    intro c X hX a
    change star (c • (X : Operator ℕ)) _=0
    rw [star_smul,smul_apply,hX a,smul_zero]

theorem oldAnnihilators_sandwich (u v : ℝ) (p q : Base u v) (X : PCorner ℕ)
    (hX : X∈oldAnnihilators u v) : (p:PCorner ℕ)*X*(q:PCorner ℕ)∈oldAnnihilators u v := by
  intro a
  change star ((p.val : Operator ℕ)*(X : Operator ℕ)*(q.val : Operator ℕ)) _=0
  rw [star_mul,star_mul,mul_apply_eq_comp,mul_apply_eq_comp]
  have hh := hX (star p*a)
  change star (X : Operator ℕ) (star (p.val : Operator ℕ) ((a.val : Operator ℕ) (vacuum u v)))=0 at hh
  rw [hh,map_zero]

end FreeGroupFactorMain.WeightedFock

namespace FreeGroupFactorMain.Amplification
variable {A : Type u_1} [CStarAlgebra A]

variable {E : Type u_2} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable (p : E →L[ℂ] E) (hp : IsStarProjection p) [CompleteSpace p.range]

end FreeGroupFactorMain.Amplification

namespace FreeGroupFactorMain.WeightedFock

section
open FreeFock Amplification Filter Topology
open scoped ENNReal
variable {ι : Type u_3} [DecidableEq ι]

end

open FreeFock Amplification
variable {ι : Type u_5} [DecidableEq ι]

end FreeGroupFactorMain.WeightedFock

end

end OAI
end


