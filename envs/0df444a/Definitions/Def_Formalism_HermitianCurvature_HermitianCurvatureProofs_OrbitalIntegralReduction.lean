-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralReduction
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralReduction
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T18:12:17.610472+00:00
-- url     : https://prove2.me/theorems/5e14e94f-7d5e-4342-b8a7-316ee3d4f37e
-- title:
--   Orbital Integral Reduction
-- statement:
--   Definitions and structural lemmas for Orbital Integral Reduction, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OrbitalIntegralReduction.lean

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelExplicitFormula
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralLatticeRefinementIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GramKernelHermitian
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_blk_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_revF
import Theorems.Thm_Formalism_DoubleCosetMeasures_P_Phase_revF_val
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x5_mv_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.blk_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_revF
attribute [local simp] Formalism.DoubleCosetMeasures.P.Phase.revF_val
attribute [local simp] Formalism.FourierDecayAlt.P.A5x5.mv_apply


set_option autoImplicit false
noncomputable section
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Formalism.FourierDecayAlt.P.A5x5 Formalism.FourierDecayAlt.P.A5x8 Formalism.FourierDecayAlt.P.A6x8 Filter Topology
namespace Formalism.FourierDecayAlt.P.OrbitalIntegralReduction
section Defs
variable {K : Type} [CommRing K]
abbrev Pr (n : ℕ) : Type := {p : Fin n × Fin n // p.1 < p.2}
def EE {n : ℕ} (y : Pr n → K) : Matrix (Fin n) (Fin n) K :=
  fun i j => if h : i < j then y ⟨(i, j), h⟩ else 0
def bx (R : Subring K) (Λ : AddSubgroup K) (ι : Type) [Fintype ι] (f : (ι → K) → ℂ) : ℂ :=
  (volL R Λ : ℂ) ^ Fintype.card ι * ∑ᶠ y : ι → K ⧸ Λ, f (fun i => Quotient.out (y i))
def BInv (Λ : AddSubgroup K) {ι : Type} (f : (ι → K) → ℂ) : Prop :=
  ∀ x l : ι → K, (∀ i, l i ∈ Λ) → f (x + l) = f x
def BSupp (L : AddSubgroup K) {ι : Type} (f : (ι → K) → ℂ) : Prop :=
  ∀ x, f x ≠ 0 → ∀ i, x i ∈ L
def HH {n : ℕ} (t : K) (d : Fin n → K) (y : Pr n → K) : Matrix (Fin n) (Fin n) K :=
  fun i j => if i = j then d i else if h : i < j then y ⟨(i, j), h⟩
    else if j.val + 1 = i.val then t else 0
def ZZ {n : ℕ} (t : K) (d : Fin n → K) (y : Pr n → K) : Matrix (Fin n) (Fin n) K :=
  (HH t d y).submatrix Fin.rev id
def Hm {m : ℕ} (t c : K) (ξ : Fin m → K) (u : Matrix (Fin (m + 1)) (Fin (m + 1)) K) :
    Matrix (Fin (m + 1)) (Fin (m + 1)) K :=
  fun i j => Fin.cases
    (∑ k : Fin m, ξ (Fin.rev k) * (t * u k.castSucc j) + if j = Fin.last m then c else 0)
    (fun i' => t * u i'.castSucc j) i
def IsHess {A : Type} [CommRing A] {n : ℕ} (t : A) (M : Matrix (Fin n) (Fin n) A) : Prop :=
  ∀ i j : Fin n, (j.val + 1 = i.val → M i j = t) ∧ (j.val + 1 < i.val → M i j = 0)
def sg {A : Type} [CommRing A] : ∀ {n : ℕ}, Matrix (Fin n) (Fin n) A → A
  | 0, _ => 0
  | 1, _ => 0
  | (n + 2), M => M 0 0 * sg (M.submatrix (Fin.succ : Fin (n + 1) → Fin (n + 2)) Fin.succ) +
      M 0 1 * ∏ k : Fin n, M k.succ.succ k.succ.succ
def Bd (R : Subring K) (ϖ : Kˣ) (k : ℕ) (x : K) : Prop := (ϖ : K) ^ k * x ∈ R
def Sm (R : Subring K) (ϖ : Kˣ) (k : ℕ) (x : K) : Prop := ∃ r ∈ R, x = (ϖ : K) ^ k * r
def x0 {m : ℕ} (D' : K) (x : Fin m → K) : K := D' * Ring.inverse (∏ k, x k)
def xt {m : ℕ} (D' : K) (x : Fin m → K) : Fin (m + 1) → K := Fin.cons (x0 D' x) x
def sd {m : ℕ} (i : Fin m) : Pr (m + 1) := ⟨(i.castSucc, i.succ), Fin.castSucc_lt_succ⟩
def g1 {m : ℕ} (D' : K) (x : Fin m → K) (y : Pr (m + 1) → K) : K :=
  x0 D' x * ∑ i : Fin m, y (sd i) * Ring.inverse (xt D' x i.castSucc) * Ring.inverse (xt D' x i.succ)
open Classical in

def GG (R : Subring K) (ψ : AddChar K ℂ) (Φ : ∀ n : ℕ, Matrix (Fin n) (Fin n) K → ℂ) {m : ℕ} (D' : K)
    (x : Fin m → K) (y : Pr (m + 1) → K) : ℂ :=
  if ∀ k, IsUnit (x k) then
    (((modK R (∏ k, x k))⁻¹ : ℝ) : ℂ) * Φ (m + 1) (ZZ 0 (xt D' x) y) * ψ (g1 D' x y) else 0
def ee {m : ℕ} : Fin m ⊕ Pr (m + 1) → Pr (m + 1) ⊕ Fin m
  | Sum.inl i => Sum.inl (sd i)
  | Sum.inr p => if h : p.1.1 = 0 then Sum.inr (p.1.2.pred (by
        intro h2; have := p.2; rw [h, h2] at this; exact lt_irrefl _ this))
      else Sum.inl ⟨((p.1.1.pred h).castSucc, p.1.2), by
        have := p.2
        rw [Fin.lt_def] at this ⊢
        simp only [Fin.val_castSucc, Fin.val_pred]
        omega⟩
def xs {m : ℕ} (n : Pr (m + 1) → K) : Fin m → K := fun i => n (sd i)
def ys {m : ℕ} (n : Pr (m + 1) → K) (τ : Fin m → K) : Pr (m + 1) → K :=
  fun p => Sum.elim n τ (ee (Sum.inr p))
end Defs
section Cst
variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]
structure Cst (R : Subring K) (ϖ : Kˣ) (L₀ Λ₀ : AddSubgroup K) (Q : Set K) (a b : ℕ) : Prop where
  adic : Adic R ϖ
  L0 : ∀ x ∈ L₀, Bd R ϖ a x
  Qb : ∀ d ∈ Q, Bd R ϖ a d
  Qi : ∀ d ∈ Q, ∀ d' : K, d * d' = 1 → Bd R ϖ a d'
  abelian₂ : ∀ x, Sm R ϖ b x → x ∈ Λ₀
end Cst
section BD
variable {K : Type} [CommRing K] {R : Subring K} {ϖ : Kˣ}
theorem Bd.add {k : ℕ} {x y : K} (hx : Bd R ϖ k x) (hy : Bd R ϖ k y) : Bd R ϖ k (x + y) := by
  unfold Bd; rw [mul_add]; exact R.add_mem hx hy
theorem Bd.sum {ι : Type} {k : ℕ} (S : Finset ι) (f : ι → K) (h : ∀ i ∈ S, Bd R ϖ k (f i)) :
    Bd R ϖ k (∑ i ∈ S, f i) := by
  unfold Bd; rw [Finset.mul_sum]; exact R.sum_mem h
theorem Sm.zero (k : ℕ) : Sm R ϖ k 0 := ⟨0, R.zero_mem, by simp⟩
theorem Sm.add {k : ℕ} {x y : K} (hx : Sm R ϖ k x) (hy : Sm R ϖ k y) : Sm R ϖ k (x + y) := by
  obtain ⟨r, hr, rfl⟩ := hx
  obtain ⟨q, hq, rfl⟩ := hy
  exact ⟨r + q, R.add_mem hr hq, by ring⟩
theorem Sm.sum {ι : Type} {k : ℕ} (S : Finset ι) (f : ι → K) (h : ∀ i ∈ S, Sm R ϖ k (f i)) :
    Sm R ϖ k (∑ i ∈ S, f i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using Sm.zero k
  | insert i S hi ih =>
    rw [Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self _ _)).add (ih fun j hj => h j (Finset.mem_insert_of_mem hj))
variable [TopologicalSpace K] [IsTopologicalRing K]
end BD
section TK
variable {K : Type} [CommRing K]
variable [TopologicalSpace K] [IsTopologicalRing K] {R : Subring K} {ψ : AddChar K ℂ}
end TK
section TKG
variable {V : Type} [AddCommGroup V]
def tk_S (V₀ M : AddSubgroup V) (f : V → ℂ) : ℂ :=
  (gi M V₀ : ℂ) * ∑ᶠ y : V ⧸ M, f (Quotient.out y)
variable [TopologicalSpace V] [IsTopologicalAddGroup V]
end TKG
section TKB
variable {K : Type} [CommRing K]
variable [TopologicalSpace K] [IsTopologicalRing K] {R : Subring K} {ψ : AddChar K ℂ}
end TKB
section LU
section LUalg
variable {K : Type} [CommRing K]
def lu_co {n : ℕ} (u : Matrix (Fin n) (Fin n) K) : Pr n → K := fun p => u p.1.1 p.1.2
def lu_M {n : ℕ} (u : Matrix (Fin n) (Fin n) K) : Matrix (Pr n) (Pr n) K :=
  fun p p' => if p'.1.2 = p.1.2 then u p.1.1 p'.1.1 else 0
theorem lu_EE_not_lt {n : ℕ} (y : Pr n → K) {i j : Fin n} (h : ¬ i < j) : EE y i j = 0 := by
  simp [EE, h]
theorem lu_up {n : ℕ} (y : Pr n → K) : IsUpUni (1 + EE y) := by
  constructor
  · intro i j hij
    have hij' : j < i := hij
    rw [Matrix.add_apply, Matrix.one_apply_ne (ne_of_gt hij'), lu_EE_not_lt y (not_lt.2 hij'.le),
      add_zero]
  · intro i
    rw [Matrix.add_apply, Matrix.one_apply_eq, lu_EE_not_lt y (lt_irrefl i), add_zero]
end LUalg
variable {K : Type} [CommRing K]
def lu_g {n : ℕ} (y : Pr n → K) : upUniG K n :=
  ⟨sec_gl (1 + EE y) (isUpUni_det K (lu_up y)), lu_up y⟩
variable [TopologicalSpace K] [IsTopologicalRing K] {R : Subring K} {ψ : AddChar K ℂ}
end LU
section ST
variable {K : Type} [CommRing K]
def antidiagonalBlock (n : ℕ) (z : Kˣ) : Matrix (Fin n) (Fin n) K :=
  pt (addBlock h0 n z).1 (addBlock h0 n z).2
end ST
section ST2
variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] {R : Subring K}
  {ψ : AddChar K ℂ}
end ST2
section HS
variable {A : Type} [CommRing A]
variable {K : Type} [CommRing K] {R : Subring K} {ϖ : Kˣ}
def hs_lift {n a : ℕ} (M : Matrix (Fin n) (Fin n) K) (hM : ∀ i j, Bd R ϖ a (M i j)) :
    Matrix (Fin n) (Fin n) R := fun i j => ⟨(ϖ : K) ^ a * M i j, hM i j⟩
def hs_L {m : ℕ} (ξ : Fin m → K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K :=
  fun i j => if i = j then 1 else if i = 0 then Fin.cases 0 (fun k => ξ (Fin.rev k)) j else 0
end HS
section E2
variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] {R : Subring K}
  {ψ : AddChar K ℂ} {ϖ : Kˣ} {L₀ Λ₀ : AddSubgroup K} {Q : Set K} {a b : ℕ}
end E2
section P2
variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] {R : Subring K}
  {ψ : AddChar K ℂ} {ϖ : Kˣ} {L₀ Λ₀ : AddSubgroup K} {Q : Set K} {a b : ℕ}
end P2
section PWa
variable {K : Type} [CommRing K]
end PWa
section PWb
variable {K : Type} [CommRing K]
def pw_Mx {m : ℕ} (t : K) (u : Matrix (Fin (m + 1)) (Fin (m + 1)) K) : Matrix (Fin m) (Fin m) K :=
  fun j k => t * u (Fin.rev k).castSucc j.succ
def pw_bv {m : ℕ} (c : K) : Fin m → K := fun j => if j.succ = Fin.last m then c else 0
def pw_ro {m : ℕ} (r : Fin m → K) : Matrix (Fin (m + 1)) (Fin (m + 1)) K :=
  fun i j => if i = j then 1 else
    Fin.cases (Fin.cases 0 (fun k => r (Fin.rev k)) j) (fun _ => 0) i
end PWb
section PWc
variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] {R : Subring K}
  {ψ : AddChar K ℂ} {ϖ : Kˣ} {L₀ Λ₀ : AddSubgroup K} {Q : Set K} {a b : ℕ}
def pw_Good (R : Subring K) (ϖ : Kˣ) (L₀ : AddSubgroup K) (a : ℕ) {m : ℕ} (n : Pr (m + 1) → K) : Prop :=
  (∀ k, xs n k ∈ L₀ ∧ IsUnit (xs n k) ∧ Bd R ϖ ((m + 1) * a) (Ring.inverse (xs n k))) ∧
    ∀ p : Pr (m + 1), p.1.1 ≠ 0 → ys n 0 p ∈ L₀
end PWc
section PW
variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] {R : Subring K}
  {ψ : AddChar K ℂ} {ϖ : Kˣ} {L₀ Λ₀ : AddSubgroup K} {Q : Set K} {a b : ℕ}
end PW
section FA0
variable {K : Type} [CommRing K]
end FA0
section FA1
variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] {R : Subring K}
  {ψ : AddChar K ℂ} {ϖ : Kˣ} {L₀ Λ₀ : AddSubgroup K} {Q : Set K} {a b : ℕ}
def InvP (R : Subring K) (ψ : AddChar K ℂ) (ϖ : Kˣ) (Φ : ∀ n : ℕ, Matrix (Fin n) (Fin n) K → ℂ)
    (m : ℕ) (D' : K) (b₁ : ℕ) : Prop :=
  ∀ μ ∈ R, ∀ (x l : Fin m → K) (y l' : Pr (m + 1) → K),
    (∀ k, ∃ r ∈ R, l k = μ * (ϖ : K) ^ b₁ * r) → (∀ p, ∃ r ∈ R, l' p = μ * (ϖ : K) ^ b₁ * r) →
    GG R ψ Φ D' (x + l) (y + l') = GG R ψ Φ D' x y ∧
    (GG R ψ Φ D' x y ≠ 0 → ∃ r ∈ R, g0 D' (x + l) - g0 D' x = μ * r)
end FA1
section FA2
variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K] {R : Subring K}
  {ψ : AddChar K ℂ} {ϖ : Kˣ} {L₀ Λ₀ : AddSubgroup K} {Q : Set K} {a b : ℕ}
end FA2
end Formalism.FourierDecayAlt.P.OrbitalIntegralReduction
namespace Formalism.FourierDecayAlt.P
end Formalism.FourierDecayAlt.P


