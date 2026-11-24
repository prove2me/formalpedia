-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_SiegelEisenstein_SymmetricPatternGroup
-- name    : Development_AbelianVarietyTheory_BlockTheory_SiegelEisenstein_SymmetricPatternGroup
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-24T21:50:01.396809+00:00
-- url     : https://prove2.me/theorems/1357c146-384c-4f75-a765-84a31cfdc83e
-- title:
--   Symmetric Pattern Group
-- statement:
--   Definitions and structural lemmas for Symmetric Pattern Group, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/SiegelEisenstein/SymmetricPatternGroup.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_StandardOrderExtendedBasisApplyLowBlock
import Theorems.Thm_GlobalTheory_StepData_residue_eq_iff_lt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
noncomputable section
namespace GlobalTheory.IndefiniteRowSideFullHecke.SymmetricPatternGroup
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData
section Pattern
variable {F : Type*} [Field F] [Finite F] {ι : Type*} [Fintype ι] [DecidableEq ι]
theorem mul_apply_of_no_path {A : ι → ι → Prop} {g h : Matrix ι ι F}
    (hg : ∀ r s, ¬ A r s → g r s = (1 : Matrix ι ι F) r s) (hh : ∀ r s, ¬ A r s → h r s = (1 : Matrix ι ι F) r s)
    (hi : ∀ r, ¬ A r r) {r s : ι} (hp : ∀ l, A r l → ¬ A l s) :
    (g * h) r s = g r s + h r s - (1 : Matrix ι ι F) r s := by
  have e : g * h = (g - 1) * (h - 1) + g + h - 1 := by noncomm_ring
  have z : ((g - 1) * (h - 1)) r s = 0 := by
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    by_cases h1 : A r l
    · simp [hh l s (hp l h1)]
    · simp [hg r l h1]
  rw [e]; simp [z]
variable (F) in

def patGrp (A : ι → ι → Prop) (hi : ∀ r, ¬ A r r) (ht : ∀ r l s, A r l → A l s → A r s) : Subgroup (GL ι F) :=
  let M : Submonoid (GL ι F) :=
    { carrier := {g | ∀ r s, ¬ A r s → g.val r s = (1 : Matrix ι ι F) r s}
      one_mem' := fun _ _ _ => rfl
      mul_mem' := fun {g h} hg hh r s hrs => by
        rw [Units.val_mul, mul_apply_of_no_path hg hh hi fun l h1 h2 => hrs (ht _ _ _ h1 h2), hg r s hrs, hh r s hrs,
          add_sub_cancel_right] }
  { M with
    inv_mem' := fun {g} hg => by
      have h0 : 0 < orderOf g := orderOf_pos g
      have e : g⁻¹ = g ^ (orderOf g - 1) := by
        rw [inv_eq_iff_mul_eq_one, ← pow_succ', Nat.sub_add_cancel h0, pow_orderOf_eq_one]
      rw [e]; exact M.pow_mem hg _ }
theorem mem_patGrp {A : ι → ι → Prop} {hi ht} {g : GL ι F} :
    g ∈ patGrp F A hi ht ↔ ∀ r s, ¬ A r s → g.val r s = (1 : Matrix ι ι F) r s := Iff.rfl
end Pattern
section Residue
variable (F : Type*) [Field F] [Finite F] (κ ρ : ℕ)
def symmetricBlockIndex : Fin κ ⊕ Fin (2 * ρ + 1) → ℕ := Sum.elim (fun _ => ρ) (fun l => l.val)
def EpsLt : Fin κ ⊕ Fin (2 * ρ + 1) → Fin κ ⊕ Fin (2 * ρ + 1) → Prop
  | .inl i, .inl j => i < j
  | _, _ => False
def radN : Subgroup (GL (Fin κ ⊕ Fin (2 * ρ + 1)) F) :=
  patGrp F (fun r s => symmetricBlockIndex κ ρ r < symmetricBlockIndex κ ρ s) (fun _ => lt_irrefl _) fun _ _ _ => lt_trans
def epsU : Subgroup (GL (Fin κ ⊕ Fin (2 * ρ + 1)) F) :=
  patGrp F (EpsLt κ ρ) (by rintro (i | i) <;> simp [EpsLt])
    (by rintro (i | i) (l | l) (j | j) <;> simp only [EpsLt, IsEmpty.forall_iff, implies_true]; exact lt_trans)
def SymFree (r s : Fin κ ⊕ Fin (2 * ρ + 1)) : Prop := symmetricBlockIndex κ ρ r < symmetricBlockIndex κ ρ s ∨ EpsLt κ ρ r s
theorem symFree_irrefl (r : Fin κ ⊕ Fin (2 * ρ + 1)) : ¬ SymFree κ ρ r r := by
  rcases r with i | i <;> simp [SymFree, EpsLt]
theorem symFree_trans (r l s : Fin κ ⊕ Fin (2 * ρ + 1)) : SymFree κ ρ r l → SymFree κ ρ l s → SymFree κ ρ r s := by
  rcases r with i | i <;> rcases l with l | l <;> rcases s with j | j <;>
    simp only [SymFree, EpsLt, symmetricBlockIndex, Sum.elim_inl, Sum.elim_inr, or_false, lt_irrefl, false_or] <;> omega
def symGrp : Subgroup (GL (Fin κ ⊕ Fin (2 * ρ + 1)) F) :=
  patGrp F (SymFree κ ρ) (symFree_irrefl κ ρ) (symFree_trans κ ρ)
variable {F κ ρ}
def sumB (g : GL (Fin κ ⊕ Fin (2 * ρ + 1)) F) : F :=
  ∑ i : Fin (2 * ρ + 1), ∑ j : Fin (2 * ρ + 1), if j.val = i.val + 1 then g.val (.inr i) (.inr j) else 0
def sumEps (g : GL (Fin κ ⊕ Fin (2 * ρ + 1)) F) : F :=
  ∑ i : Fin κ, ∑ j : Fin κ, if j.val = i.val + 1 then g.val (.inl i) (.inl j) else 0
theorem sumB_mul {g h : GL (Fin κ ⊕ Fin (2 * ρ + 1)) F} (hg : g ∈ symGrp F κ ρ) (hh : h ∈ symGrp F κ ρ) :
    sumB (g * h) = sumB g + sumB h := by
  simp only [sumB, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  split_ifs with hij
  · have hne : i ≠ j := by rintro rfl; omega
    rw [Units.val_mul, mul_apply_of_no_path (mem_patGrp.1 hg) (mem_patGrp.1 hh) (symFree_irrefl κ ρ)]
    · simp [hne]
    · rintro (l | l) <;>
        simp only [SymFree, EpsLt, symmetricBlockIndex, Sum.elim_inl, Sum.elim_inr, or_false] <;> omega
  · simp
theorem sumEps_mul {g h : GL (Fin κ ⊕ Fin (2 * ρ + 1)) F} (hg : g ∈ symGrp F κ ρ) (hh : h ∈ symGrp F κ ρ) :
    sumEps (g * h) = sumEps g + sumEps h := by
  simp only [sumEps, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  split_ifs with hij
  · have hne : i ≠ j := by rintro rfl; omega
    rw [Units.val_mul, mul_apply_of_no_path (mem_patGrp.1 hg) (mem_patGrp.1 hh) (symFree_irrefl κ ρ)]
    · simp [hne]
    · rintro (l | l) <;>
        simp only [SymFree, EpsLt, symmetricBlockIndex, Sum.elim_inl, Sum.elim_inr, or_false, lt_irrefl, false_or] <;> omega
  · simp
def symChar (ψ₀ : AddChar F Circle) : symGrp F κ ρ →* ℂˣ :=
  MonoidHom.mk' (fun g => Circle.toUnits (ψ₀ (sumB g.1)) * Circle.toUnits (ψ₀ (sumEps g.1))) fun g h => by
    rw [Subgroup.coe_mul, sumB_mul g.2 h.2, sumEps_mul g.2 h.2, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul,
      map_mul, map_mul, mul_mul_mul_comm]
end Residue
section Local
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
def IsUnif (ϖ : kˣ) : Prop := ∀ x : k, valuation k x < 1 ↔ valuation k x ≤ valuation k (ϖ : k)
theorem psi_congr {ψ : AddChar k Circle} (hψ : HasConductor ψ 1) {ϖ : kˣ} (hϖ : IsUnif ϖ) {a b : 𝒪[k]}
    (h : IsLocalRing.residue 𝒪[k] a = IsLocalRing.residue 𝒪[k] b) : ψ ((a : k) / ϖ) = ψ ((b : k) / ϖ) := by
  have h1 := (hϖ _).1 ((residue_eq_iff_lt a b).1 h)
  have h0 : 0 < valuation k (ϖ : k) := by simp [zero_lt_iff]
  have h2 : ψ (((a : k) - b) / ϖ) = 1 := (hψ _).2 (by
    rw [map_div₀, Units.val_one, map_one]; exact (div_le_one₀ h0).2 h1) _ le_rfl
  rw [show (a : k) / ϖ = ((a : k) - b) / ϖ + b / ϖ by ring, AddChar.map_add_eq_mul, h2, one_mul]
def psiZero {ψ : AddChar k Circle} (hψ : HasConductor ψ 1) {ϖ : kˣ} (hϖ : IsUnif ϖ) : AddChar 𝓀[k] Circle where
  toFun x := ψ (((Function.surjInv (IsLocalRing.residue_surjective (R := 𝒪[k])) x : 𝒪[k]) : k) / ϖ)
  map_zero_eq_one' := by
    rw [psi_congr hψ hϖ (b := 0) (by rw [Function.surjInv_eq (IsLocalRing.residue_surjective (R := 𝒪[k])), map_zero])]
    simp
  map_add_eq_mul' x y := by
    rw [← AddChar.map_add_eq_mul, ← add_div, ← Subring.coe_add]
    exact psi_congr hψ hϖ (by simp only [map_add, Function.surjInv_eq (IsLocalRing.residue_surjective (R := 𝒪[k]))])
def symLevel {ψ : AddChar k Circle} (hψ : HasConductor ψ 1) {ϖ : kˣ} (hϖ : IsUnif ϖ) (κ ρ : ℕ) :
    TypeDatum k (Fin κ ⊕ Fin (2 * ρ + 1)) :=
  TypeDatum.ofResidue (symGrp 𝓀[k] κ ρ) (symChar (psiZero hψ hϖ))
def symChain {ψ : AddChar k Circle} (hψ : HasConductor ψ 1) {ϖ : kˣ} (hϖ : IsUnif ϖ) (κ ρ τ : ℕ)
    (μ : ℕ → kˣ →* ℂˣ) (hμ : ∀ j, IsTame (μ j)) :
    Chain k (2 * ρ) (XIx (Fin κ) (Fin τ)) (Ix (Fin κ ⊕ Fin (2 * ρ + 1)) (Fin τ) (2 * ρ + 2)) :=
  typeChain (Fin τ) ϖ (symLevel hψ hϖ κ ρ) μ hμ
def fCoset (ϖ : kˣ) (κ τ s : ℕ) : Set (XIx (Fin κ) (Fin τ) (s + 1) → k) :=
  {y | (ϖ : k) • y - Pi.single (.inl (.inr 0)) 1 ∈ box (XIx (Fin κ) (Fin τ) (s + 1)) ϖ}
example (ϖ : kˣ) (κ τ s : ℕ) : (ϖ : k)⁻¹ • Pi.single (.inl (.inr 0)) (1 : k) ∈ fCoset ϖ κ τ s := by
  simp [fCoset, smul_smul]
example {ϖ : kˣ} (hϖ : IsUnif ϖ) (κ τ s : ℕ) : (fun _ => (0 : k)) ∉ fCoset ϖ κ τ s := fun h => by
  have := (hϖ _).2 (mem_box.1 h (.inl (.inr 0)))
  simp at this
variable [MeasurableSpace k] [BorelSpace k]
def AtMostOneCosetAt {ψ : AddChar k Circle} (hψ : HasConductor ψ 1) {ϖ : kˣ} (hϖ : IsUnif ϖ) (ν : Measure k)
    (κ ρ τ : ℕ) (μ : ℕ → kˣ →* ℂˣ) (hμ : ∀ j, IsTame (μ j)) : Prop :=
  let T := symChain hψ hϖ κ ρ τ μ hμ
  ((∀ j c (hjc : j + 1 + c = 2 * ρ) (h : GL (XIx (Fin κ) (Fin τ) (j + 1) ⊕ Fin (c + 1)) k),
      opE ψ ν 1 (om (μ (j + 1)) 1 h (T.Phi j (c + 1) (by omega))) ≠ 0 →
        ∃ r ∈ R k (XIx (Fin κ) (Fin τ) (j + 1)) (c + 1) 1, ∃ g ∈ (T.lev (j + 1) (c + 1) (by omega)).J, h = r * g) ∧
    ∀ A : RepFam k (2 * ρ) (XIx (Fin κ) (Fin τ)), T.IsRepSystem A ψ ν → T.RepsOne A →
      ∀ j c (hjc : j + 1 + c = 2 * ρ), A (j + 1) c hjc ⊆ {1}) ∧
  (∀ j c (_ : j + 1 + c = 2 * ρ),
    prX (R k (XIx (Fin κ) (Fin τ) (j + 1)) (c + 1) 1 ⊓ (T.lev (j + 1) (c + 1) (by omega)).J) =
      (T.lev (j + 1) (c + 1) (by omega)).J.comap (embX (c + 1))) ∧
  ((∃ Ψ : Matrix (XIx (Fin κ) (Fin τ) (2 * ρ + 1)) (XIx (Fin κ) (Fin τ) (2 * ρ)) k → ℂ,
      (∀ x₀, Ψ x₀ ≠ 0 → IntM x₀) ∧ (∀ x₀ y₀, MaxM y₀ → Ψ (x₀ + y₀) = Ψ x₀) ∧
      ∀ x, T.Phi (2 * ρ) 0 rfl x =
        Ψ x.toBlocks₁₁ * (fCoset ϖ κ τ (2 * ρ)).indicator (fun _ => (1 : ℂ)) fun r => x (.inl r) (.inr 0)) ∧
    ∀ g ∈ (T.lev (2 * ρ + 1) 0 rfl).J,
      (fun y => g.val.toBlocks₁₁ *ᵥ y) '' fCoset ϖ κ τ (2 * ρ) = fCoset ϖ κ τ (2 * ρ))
end Local
def AtMostOneCoset : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k]
    [BorelSpace k] (ψ : AddChar k Circle) (hψ : HasConductor ψ 1) (ϖ : kˣ) (hϖ : IsUnif ϖ) (ν : Measure k)
    (_ : IsUnitVol ν) (κ ρ τ : ℕ) (μ : ℕ → kˣ →* ℂˣ) (hμ : ∀ j, IsTame (μ j)),
    AtMostOneCosetAt hψ hϖ ν κ ρ τ μ hμ
end GlobalTheory.IndefiniteRowSideFullHecke.SymmetricPatternGroup


