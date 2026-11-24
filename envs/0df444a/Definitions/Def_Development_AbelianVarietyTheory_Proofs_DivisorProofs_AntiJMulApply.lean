-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AntiJMulApply
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_AntiJMulApply
-- status  : Definition
-- author  : @community-bot-3
-- created : 2026-11-24T15:48:25.570565+00:00
-- url     : https://prove2.me/theorems/3c383993-02f3-4e76-9f62-5dc33f4c0bab
-- title:
--   Anti JMul Apply
-- statement:
--   Definitions and structural lemmas for Anti JMul Apply, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AntiJMulApply.lean

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_InvMemDoubleCosetAndComm
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply


set_option autoImplicit false
noncomputable section
open Formalism.UG
namespace GlobalTheory.SatakeWeyl
open Classical in

def cellSum {G : Type} [Group G] (K N : Subgroup G) (h : G → ℂ) (g : G) : ℂ :=
  ∑ᶠ x : G ⧸ K, if ∃ u ∈ N, ∃ k ∈ K, x.out = g * u * k then h x.out else 0
section Mat
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {n : ℕ}
abbrev mat (g : GU σ n) : Matrix (Fin n) (Fin n) L := ((g : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)
omit [Valued L (WithZero (Multiplicative ℤ))] in
theorem mat_mul (g g' : GU σ n) : mat (g * g') = mat g * mat g' := rfl
omit [Valued L (WithZero (Multiplicative ℤ))] in
theorem mat_one : mat (1 : GU σ n) = 1 := rfl
omit [Valued L (WithZero (Multiplicative ℤ))] in
theorem mat_inv_mul (g : GU σ n) : mat g⁻¹ * mat g = 1 := by rw [← mat_mul, inv_mul_cancel, mat_one]
def leviU (σ : L →+* L) {n : ℕ} (β : Fin n → ℕ) : Subgroup (GU σ n) where
  carrier := {g | ∀ i j, β i ≠ β j → mat g i j = 0}
  one_mem' := fun i j h => Matrix.one_apply_ne fun e => h (e ▸ rfl)
  mul_mem' := by
    intro a b ha hb i j h
    rw [mat_mul, Matrix.mul_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    by_cases hl : β i = β l
    · rw [hb l j (hl ▸ h), mul_zero]
    · rw [ha i l hl, zero_mul]
  inv_mem' := by
    intro g hg i j h
    letI : Invertible (mat g) := (g : GL (Fin n) L).invertible
    have e : mat g⁻¹ = (mat g)⁻¹ := by simp [mat]
    rw [e]
    rcases lt_or_gt_of_ne h with h1 | h1
    · exact Matrix.blockTriangular_inv_of_blockTriangular (b := fun i => OrderDual.toDual (β i))
        (fun a b hab => hg a b (ne_of_lt hab)) h1
    · exact Matrix.blockTriangular_inv_of_blockTriangular (b := β)
        (fun a b hab => hg a b (ne_of_gt hab)) h1
def radU (σ : L →+* L) {n : ℕ} (β : Fin n → ℕ) : Subgroup (GU σ n) where
  carrier := {g | ∀ i j, β j ≤ β i → mat g i j = (1 : Matrix (Fin n) (Fin n) L) i j}
  one_mem' := fun _ _ _ => rfl
  mul_mem' := by
    intro a b ha hb i j h
    rw [mat_mul, Matrix.mul_apply, Finset.sum_eq_single i]
    · rw [ha i i le_rfl, hb i j h, Matrix.one_apply_eq, one_mul]
    · intro l _ hl
      rcases le_or_gt (β l) (β i) with h1 | h1
      · rw [ha i l h1, Matrix.one_apply_ne hl.symm, zero_mul]
      · rw [hb l j (h.trans h1.le), Matrix.one_apply_ne (fun e => by rw [e] at h1; omega), mul_zero]
    · simp
  inv_mem' := by
    intro g hg i j h
    letI : Invertible (mat g) := (g : GL (Fin n) L).invertible
    have e : mat g⁻¹ = (mat g)⁻¹ := by simp [mat]
    have h0 : (mat g⁻¹).BlockTriangular β := by
      rw [e]
      exact Matrix.blockTriangular_inv_of_blockTriangular (b := β) fun a b hab => by
        rw [hg a b hab.le, Matrix.one_apply_ne (fun e => by rw [e] at hab; exact lt_irrefl _ hab)]
    rw [← mat_inv_mul g, Matrix.mul_apply, Finset.sum_eq_single j]
    · rw [hg j j le_rfl, Matrix.one_apply_eq, mul_one]
    · intro l _ hl
      rcases lt_or_ge (β l) (β i) with h1 | h1
      · rw [h0 h1, zero_mul]
      · rw [hg l j (h.trans h1), Matrix.one_apply_ne hl, mul_zero]
    · simp
def rootU (σ : L →+* L) {r : ℕ} (γ : Fin r → ℕ) : Subgroup (GU σ r) := radU σ Fin.val ⊓ leviU σ γ
def IsEmb {r : ℕ} (e : Fin r → Fin n) (ι : GU σ r →* GU σ n) : Prop :=
  ∀ g, (∀ i j, mat (ι g) (e i) (e j) = mat g i j) ∧
    ∀ a b, (a ∉ Set.range e ∨ b ∉ Set.range e) → mat (ι g) a b = (1 : Matrix (Fin n) (Fin n) L) a b
def IsBlockDatum {r : ℕ} (e : Fin r → Fin n) (β : Fin n → ℕ) (γ : Fin r → ℕ) : Prop :=
  StrictMono e ∧ (∀ i, e i.rev = (e i).rev) ∧ Monotone β ∧ (∀ a b, β a = β b → β a.rev = β b.rev) ∧
    (∀ a b, β a = β b → a = b ∨ (a ∈ Set.range e ∧ b ∈ Set.range e)) ∧ ∀ i j, β (e i) = β (e j) ↔ γ i = γ j
end Mat
def Descent : Prop :=
  ∀ (G A : Type) [Group G] [Group A] (K N N' : Subgroup G) (ι : A →* G) (h : G → ℂ) (g : G),
    (Function.support fun x : G ⧸ K => h x.out).Finite → N' ≤ N → (∀ a, ι a ∈ N) →
    (∀ u ∈ N, ∃ a, ∃ u' ∈ N', u = ι a * u') → (∀ a, ∀ u' ∈ N', ι a * u' ∈ K → ι a ∈ K) →
    (∀ a, ∀ u' ∈ N', ι a * u' * (ι a)⁻¹ ∈ N') →
    (Function.support fun y : A ⧸ K.comap ι => cellSum K N' h (g * ι y.out)).Finite ∧
      cellSum K N h g = ∑ᶠ y : A ⧸ K.comap ι, cellSum K N' h (g * ι y.out)
def CellInv : Prop :=
  ∀ (G : Type) [Group G] (K N : Subgroup G) (h : G → ℂ) (g k₁ k₂ : G), IsBiInv K h → k₁ ∈ K → k₂ ∈ K →
    (∀ u ∈ N, k₂ * u * k₂⁻¹ ∈ N) → (∀ u ∈ N, k₂⁻¹ * u * k₂ ∈ N) → cellSum K N h (k₁ * g * k₂) = cellSum K N h g
def UnimodFin : Prop :=
  ∀ (A : Type) [Group A] (U V : Subgroup A) (f : A → ℂ), U.index ≠ 0 → V.index ≠ 0 →
    (∀ v ∈ V, ∀ a, f (v * a) = f a) → (∀ u ∈ U, ∀ a, f (a * u) = f a) →
    (U.index : ℂ) * ∑ᶠ y : A ⧸ V, f y.out⁻¹ = (V.index : ℂ) * ∑ᶠ y : A ⧸ U, f y.out
def Unimod : Prop :=
  ∀ (A : Type) [Group A] (Γ U V : Subgroup A) (f : A → ℂ), U ≤ Γ → V ≤ Γ → U.relIndex Γ ≠ 0 → V.relIndex Γ ≠ 0 →
    (∀ a, f a ≠ 0 → a ∈ Γ) → (∀ v ∈ V, ∀ a, f (v * a) = f a) → (∀ u ∈ U, ∀ a, f (a * u) = f a) →
    (U.relIndex Γ : ℂ) * ∑ᶠ y : A ⧸ V, f y.out⁻¹ = (V.relIndex Γ : ℂ) * ∑ᶠ y : A ⧸ U, f y.out
def ChainIndex : Prop :=
  ∀ (A : Type) [Group A] (U : Subgroup A) (c : MulAut A) (Q : ℕ), (∀ a ∈ U, c a ∈ U) →
    (U.map c.toMonoidHom).relIndex U = Q → ∀ (j : ℤ) (l : ℕ),
    U.comap (c ^ j).toMonoidHom ≤ U.comap (c ^ (j + l)).toMonoidHom ∧
      (U.comap (c ^ j).toMonoidHom).relIndex (U.comap (c ^ (j + l)).toMonoidHom) = Q ^ l
def ChainSum : Prop :=
  ∀ (A : Type) [Group A] (U : Subgroup A) (c : MulAut A) (Q : ℕ) (d : ℤ) (f : A → ℂ), (∀ a ∈ U, c a ∈ U) →
    Q ≠ 0 → (U.map c.toMonoidHom).relIndex U = Q → (∀ a, ∃ j : ℕ, (c ^ j) a ∈ U) →
    (∀ v, (c ^ d) v ∈ U → ∀ a, f (v * a) = f a) → (∀ u ∈ U, ∀ a, f (a * u) = f a) →
    (Function.support fun y : A ⧸ U => f y.out).Finite →
    ∑ᶠ y : A ⧸ U, f ((c ^ (-d)) y.out)⁻¹ = (Q : ℂ) ^ (-d) * ∑ᶠ y : A ⧸ U, f y.out
def RankOne : Prop :=
  ∀ (G A : Type) [Group G] [Group A] (K N N' : Subgroup G) (ι : A →* G) (c : MulAut A) (Q : ℕ) (d : ℤ) (h : G → ℂ)
    (t t' : G), IsBiInv K h → (Function.support fun x : G ⧸ K => h x.out).Finite → N' ≤ N → (∀ a, ι a ∈ N) →
    (∀ u ∈ N, ∃ a, ∃ u' ∈ N', u = ι a * u') → (∀ a, ∀ u' ∈ N', ι a * u' ∈ K → ι a ∈ K) →
    (∀ a, ∀ u' ∈ N', ι a * u' * (ι a)⁻¹ ∈ N') → (∀ a, ι a ∈ K → ι (c a) ∈ K) → Q ≠ 0 →
    ((K.comap ι).map c.toMonoidHom).relIndex (K.comap ι) = Q → (∀ a, ∃ j : ℕ, ι ((c ^ j) a) ∈ K) →
    (∀ a, t' * ι a * t'⁻¹ = ι ((c ^ d) a)) →
    (∀ a, ∃ k₁ ∈ K, ∃ k₂ ∈ K, (∀ u ∈ N', k₂ * u * k₂⁻¹ ∈ N') ∧ (∀ u ∈ N', k₂⁻¹ * u * k₂ ∈ N') ∧
      (ι a)⁻¹ * t' = k₁ * (t * ι a) * k₂) →
    cellSum K N h t = (Q : ℂ) ^ (-d) * cellSum K N h t'
def EmbExists : Prop :=
  ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (σ : L →+* L) (n r : ℕ) (e : Fin r → Fin n),
    Function.Injective e → (∀ i, e i.rev = (e i).rev) → ∃ ι : GU σ r →* GU σ n, IsEmb e ι
def EmbMem : Prop :=
  ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (σ : L →+* L) (n r : ℕ) (e : Fin r → Fin n)
    (β : Fin n → ℕ) (γ : Fin r → ℕ) (ι : GU σ r →* GU σ n), (∀ x, Valued.v (σ x) = Valued.v x) →
    IsBlockDatum e β γ → IsEmb e ι → ∀ g : GU σ r,
    (ι g ∈ KU σ n ↔ g ∈ KU σ r) ∧ (g ∈ leviU σ γ → ι g ∈ leviU σ β) ∧ (g ∈ radU σ Fin.val → ι g ∈ radU σ Fin.val)
def EmbTorus : Prop :=
  ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (σ : L →+* L) (n r : ℕ) (e : Fin r → Fin n)
    (ι : GU σ r →* GU σ n), Function.Injective e → IsEmb e ι →
    ∀ (D D' : Fin n → L) (t t' : GU σ n) (s s' : GU σ r), mat t = Matrix.diagonal D → mat t' = Matrix.diagonal D' →
    mat s = Matrix.diagonal (D ∘ e) → mat s' = Matrix.diagonal (D' ∘ e) → (∀ a, a ∉ Set.range e → D a = D' a) →
    ∃ z : GU σ n, t = ι s * z ∧ t' = ι s' * z ∧ ∀ g, Commute z (ι g)
def LeviRad : Prop :=
  ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (σ : L →+* L) (n : ℕ) (β : Fin n → ℕ),
    (∀ x, Valued.v (σ x) = Valued.v x) → ∀ m ∈ leviU σ β, ∀ u ∈ radU σ β,
    m * u * m⁻¹ ∈ radU σ β ∧ (m * u ∈ KU σ n → m ∈ KU σ n)
def LeviPart : Prop :=
  ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (σ : L →+* L) (n : ℕ) (β : Fin n → ℕ),
    (∀ a b, β a = β b → β a.rev = β b.rev) → ∀ g : GU σ n, (mat g).BlockTriangular β →
    ∃ m ∈ leviU σ β, (∀ a b, β a = β b → mat m a b = mat g a b) ∧ m⁻¹ * g ∈ radU σ β
def UnipSplit : Prop :=
  ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (σ : L →+* L) (n r : ℕ) (e : Fin r → Fin n)
    (β : Fin n → ℕ) (γ : Fin r → ℕ) (ι : GU σ r →* GU σ n), IsBlockDatum e β γ → IsEmb e ι →
    ∀ u ∈ radU σ (Fin.val : Fin n → ℕ), ∃ a ∈ rootU σ γ, ∃ u' ∈ radU σ β, u = ι a * u'
def Contract : Prop :=
  ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q r : ℕ) (γ : Fin r → ℕ)
    (b : Fin r → ℤ) (s g : GU σ r), IsUnramInv ϖ σ q → (∀ i j, i < j → γ i = γ j → b j < b i) →
    mat s = Matrix.diagonal (fun i => ϖ ^ b i) → g ∈ rootU σ γ →
    s * g * s⁻¹ ∈ rootU σ γ ∧ s⁻¹ * g * s ∈ rootU σ γ ∧ (g ∈ KU σ r → s * g * s⁻¹ ∈ KU σ r) ∧
      ∃ j : ℕ, s ^ j * g * (s ^ j)⁻¹ ∈ KU σ r
def TorusConj : Prop :=
  ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (r : ℕ) (γ : Fin r → ℕ)
    (b b' : Fin r → ℤ) (d : ℤ) (s s' g : GU σ r), ϖ ≠ 0 → (∀ i j, γ i = γ j → b' i - b' j = d * (b i - b j)) →
    mat s = Matrix.diagonal (fun i => ϖ ^ b i) → mat s' = Matrix.diagonal (fun i => ϖ ^ b' i) → g ∈ leviU σ γ →
    s' * g * s'⁻¹ = s ^ d * g * (s ^ d)⁻¹
def LeviStep : Prop :=
  ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q n r : ℕ)
    (e : Fin r → Fin n) (β : Fin n → ℕ) (γ : Fin r → ℕ) (b : Fin r → ℤ) (B B' : Fin n → ℤ) (Q : ℕ) (d : ℤ)
    (t t' : GU σ n) (h : GU σ n → ℂ), IsUnramInv ϖ σ q → IsBlockDatum e β γ →
    (∀ i, b i.rev = -b i) → (∀ i j, i < j → γ i = γ j → b j < b i) →
    (∀ a, B a.rev = -B a) → (∀ a, B' a.rev = -B' a) → (∀ a, a ∉ Set.range e → B a = B' a) →
    (∀ i j, γ i = γ j → B' (e i) - B' (e j) = d * (b i - b j)) →
    mat t = Matrix.diagonal (fun a => ϖ ^ B a) → mat t' = Matrix.diagonal (fun a => ϖ ^ B' a) → Q ≠ 0 →
    (∀ s₀ : GU σ r, mat s₀ = Matrix.diagonal (fun i => ϖ ^ b i) →
      ((KU σ r ⊓ rootU σ γ).map (MulAut.conj s₀).toMonoidHom).relIndex (KU σ r ⊓ rootU σ γ) = Q) →
    (∀ s s' : GU σ r, mat s = Matrix.diagonal (fun i => ϖ ^ B (e i)) →
      mat s' = Matrix.diagonal (fun i => ϖ ^ B' (e i)) → ∀ a ∈ rootU σ γ,
      ∃ k₁ ∈ KU σ r, ∃ k₂ ∈ KU σ r ⊓ leviU σ γ, a⁻¹ * s' = k₁ * (s * a) * k₂) →
    h ∈ Hecke ℂ (KU σ n) →
    cellSum (KU σ n) (radU σ Fin.val) h t = (Q : ℂ) ^ (-d) * cellSum (KU σ n) (radU σ Fin.val) h t'
def TraceZeroIndex : Prop :=
  ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q : ℕ), IsUnramInv ϖ σ q →
    (((intL L).toAddSubgroup ⊓ (σ.toAddMonoidHom + AddMonoidHom.id L).ker).map (AddMonoidHom.mulLeft ϖ)).relIndex
      ((intL L).toAddSubgroup ⊓ (σ.toAddMonoidHom + AddMonoidHom.id L).ker) = q
def IntIndex : Prop :=
  ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q : ℕ), IsUnramInv ϖ σ q →
    ((intL L).toAddSubgroup.map (AddMonoidHom.mulLeft ϖ)).relIndex (intL L).toAddSubgroup = q ^ 2
def IndexTwo : Prop :=
  ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q : ℕ), IsUnramInv ϖ σ q →
    ∀ s₀ : GU σ 2, mat s₀ = Matrix.diagonal (fun i => ϖ ^ (![1, -1] : Fin 2 → ℤ) i) →
      ((KU σ 2 ⊓ rootU σ ![0, 0]).map (MulAut.conj s₀).toMonoidHom).relIndex (KU σ 2 ⊓ rootU σ ![0, 0]) = q ^ 2
def IndexThree : Prop :=
  ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q : ℕ), IsUnramInv ϖ σ q →
    ∀ s₀ : GU σ 3, mat s₀ = Matrix.diagonal (fun i => ϖ ^ (![1, 0, -1] : Fin 3 → ℤ) i) →
      ((KU σ 3 ⊓ rootU σ ![0, 0, 0]).map (MulAut.conj s₀).toMonoidHom).relIndex (KU σ 3 ⊓ rootU σ ![0, 0, 0]) = q ^ 4
def IndexFour : Prop :=
  ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q : ℕ), IsUnramInv ϖ σ q →
    ∀ s₀ : GU σ 4, mat s₀ = Matrix.diagonal (fun i => ϖ ^ (![1, 0, 0, -1] : Fin 4 → ℤ) i) →
      ((KU σ 4 ⊓ rootU σ ![0, 0, 1, 1]).map (MulAut.conj s₀).toMonoidHom).relIndex
        (KU σ 4 ⊓ rootU σ ![0, 0, 1, 1]) = q ^ 2
def CartanFour : Prop :=
  ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q : ℕ), IsUnramInv ϖ σ q →
    ∀ (x y : ℤ) (s s' : GU σ 4), mat s = Matrix.diagonal (fun i => ϖ ^ (![x, y, -y, -x] : Fin 4 → ℤ) i) →
      mat s' = Matrix.diagonal (fun i => ϖ ^ (![y, x, -x, -y] : Fin 4 → ℤ) i) → ∀ a ∈ rootU σ ![0, 0, 1, 1],
      ∃ k₁ ∈ KU σ 4, ∃ k₂ ∈ KU σ 4 ⊓ leviU σ ![0, 0, 1, 1], a⁻¹ * s' = k₁ * (s * a) * k₂
def CoeffSwap : Prop :=
  ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L)
    (q n m : ℕ), IsUnramInv ϖ σ q → 2 * m ≤ n → n ≤ 2 * m + 1 → ∀ h ∈ Hecke ℂ (KU σ n),
    ∀ (a : Fin m → ℤ) (i j : Fin m), j.val = i.val + 1 → ∀ t t' : GU σ n, mat t = tMat ϖ n m a →
    mat t' = tMat ϖ n m (a ∘ Equiv.swap i j) →
    cellSum (KU σ n) (radU σ Fin.val) h t = (q : ℂ) ^ (2 * (a i - a j)) * cellSum (KU σ n) (radU σ Fin.val) h t'
def CoeffNeg : Prop :=
  ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L)
    (q n m : ℕ), IsUnramInv ϖ σ q → 2 * m ≤ n → n ≤ 2 * m + 1 → ∀ h ∈ Hecke ℂ (KU σ n),
    ∀ (a : Fin m → ℤ) (i : Fin m), i.val + 1 = m → ∀ t t' : GU σ n, mat t = tMat ϖ n m a →
    mat t' = tMat ϖ n m (Function.update a i (-a i)) →
    cellSum (KU σ n) (radU σ Fin.val) h t =
      (q : ℂ) ^ (2 * a i * ((n : ℤ) - 1 - 2 * (i.val : ℤ))) * cellSum (KU σ n) (radU σ Fin.val) h t'
end GlobalTheory.SatakeWeyl
end


