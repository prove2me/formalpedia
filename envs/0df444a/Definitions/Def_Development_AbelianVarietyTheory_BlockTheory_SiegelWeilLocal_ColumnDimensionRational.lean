-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_SiegelWeilLocal_ColumnDimensionRational
-- name    : Development_AbelianVarietyTheory_BlockTheory_SiegelWeilLocal_ColumnDimensionRational
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:07:34.251827+00:00
-- url     : https://prove2.me/theorems/d55a5aad-dc68-4958-8fd2-f6506bda76af
-- title:
--   Column Dimension Rational
-- statement:
--   Definitions and structural lemmas for Column Dimension Rational, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/SiegelWeilLocal/ColumnDimensionRational.lean

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_Formalism_LocalToGlobal_Columns_GenericUnipotentCharacter
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_FrameLats
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain MeasureTheory Matrix
open scoped TensorProduct nonZeroDivisors
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SgAlg GlobalTheory.SgGlob
namespace GlobalTheory.IndefiniteRowSideFullHecke.ParabolicSubgroups
section Groups
variable {A : Type} [CommRing A] {n r : ℕ}
def fixG (σ : A →+* A) (J : Matrix (Fin n) (Fin n) A) (P : Matrix (Fin n) (Fin (r + 1)) A)
    (f : Matrix (Fin n) (Fin r) A) : Subgroup ↥(Formalism.UG.UJ σ J) where
  carrier := {g | (g.1 : Matrix (Fin n) (Fin n) A) * P = P ∧ (g.1 : Matrix (Fin n) (Fin n) A) * f = f}
  one_mem' := by simp
  mul_mem' := by
    rintro a b ⟨h1, h2⟩ ⟨h3, h4⟩
    refine ⟨?_, ?_⟩
    · simp only [Subgroup.coe_mul, Units.val_mul, Matrix.mul_assoc, h3, h1]
    · simp only [Subgroup.coe_mul, Units.val_mul, Matrix.mul_assoc, h4, h2]
  inv_mem' := by
    rintro a ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · conv_lhs => rw [← h1]
      rw [Subgroup.coe_inv, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
    · conv_lhs => rw [← h2]
      rw [Subgroup.coe_inv, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
def unipG (σ : A →+* A) (J : Matrix (Fin n) (Fin n) A) (e : Matrix (Fin n) (Fin r) A) :
    Subgroup ↥(Formalism.UG.UJ σ J) where
  carrier := {g | (∃ ν ∈ Formalism.L2.Col.HU A r,
      (g.1 : Matrix (Fin n) (Fin n) A) * e = e * (ν : Matrix (Fin r) (Fin r) A)) ∧
    ∀ v : Fin n → A, (cT σ e * J).mulVec v = 0 →
      ∃ c, (g.1 : Matrix (Fin n) (Fin n) A).mulVec v - v = e.mulVec c}
  one_mem' := ⟨⟨1, Subgroup.one_mem _, by simp⟩, fun v _ => ⟨0, by simp⟩⟩
  mul_mem' := by
    rintro a b ⟨⟨ν, hν, h1⟩, h2⟩ ⟨⟨μ, hμ, h3⟩, h4⟩
    refine ⟨⟨ν * μ, Subgroup.mul_mem _ hν hμ, ?_⟩, fun v hv => ?_⟩
    · simp only [Subgroup.coe_mul, Units.val_mul]
      rw [Matrix.mul_assoc, h3, ← Matrix.mul_assoc, h1, Matrix.mul_assoc]
    · obtain ⟨c, hc⟩ := h2 v hv
      obtain ⟨d, hd⟩ := h4 v hv
      refine ⟨(ν : Matrix (Fin r) (Fin r) A).mulVec d + c, ?_⟩
      rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, ← h1, ← Matrix.mulVec_mulVec, ← hd, ← hc,
        Matrix.mulVec_sub]
      simp only [Subgroup.coe_mul, Units.val_mul, ← Matrix.mulVec_mulVec]
      abel
  inv_mem' := by
    rintro a ⟨⟨ν, hν, h1⟩, h2⟩
    have h5 : ((a.1⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) * e =
        e * ((ν⁻¹ : GL (Fin r) A) : Matrix (Fin r) (Fin r) A) := by
      have : e = (a.1 : Matrix (Fin n) (Fin n) A) * e * ((ν⁻¹ : GL (Fin r) A) : Matrix (Fin r) (Fin r) A) := by
        rw [h1, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
      conv_lhs => rw [this]
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
    refine ⟨⟨ν⁻¹, Subgroup.inv_mem _ hν, by rw [Subgroup.coe_inv]; exact h5⟩, fun v hv => ?_⟩
    obtain ⟨c, hc⟩ := h2 v hv
    refine ⟨-((ν⁻¹ : GL (Fin r) A) : Matrix (Fin r) (Fin r) A).mulVec c, ?_⟩
    rw [Matrix.mulVec_neg, Matrix.mulVec_mulVec, ← h5, ← Matrix.mulVec_mulVec, ← hc,
      Matrix.mulVec_sub, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec, Subgroup.coe_inv]
    abel
end Groups
section Points
variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
  (σ : E →ₐ[F] E) {n r : ℕ} (J : Matrix (Fin n) (Fin n) E)
def Hp (P : Matrix (Fin n) (Fin (r + 1)) E) (f : Matrix (Fin n) (Fin r) E) : Subgroup (HA R σ J) :=
  fixG (sigR R σ) (JR R J) (P.map (inclR R)) (f.map (inclR R))
def Np (P : Matrix (Fin n) (Fin (r + 1)) E) : Subgroup (HA R σ J) :=
  unipG (sigR R σ) (JR R J) ((eOf P).map (inclR R))
def Sp (P : Matrix (Fin n) (Fin (r + 1)) E) : Set (HA R σ J) :=
  {g | InS (sigR R σ) (JR R J) (P.map (inclR R))
    (HA.mat R σ J g : Matrix (Fin n) (Fin n) (R ⊗[F] E))}
theorem sig_incl (x : E) : sigR R σ (inclR R x) = inclR R (σ x) := by simp [sigR, inclR]
theorem bc_mem (γ : ↥(Formalism.UG.UJ (σ : E →+* E) J)) : Formalism.UG.bc (inclR R) γ.1 ∈ HR R σ J := by
  have h : Formalism.UG.cT (σ : E →+* E) (γ.1 : Matrix (Fin n) (Fin n) E) * J * γ.1 = J := γ.2
  show Formalism.UG.cT (sigR R σ) ((γ.1 : Matrix (Fin n) (Fin n) E).map (inclR R)) * J.map (inclR R) *
    (γ.1 : Matrix (Fin n) (Fin n) E).map (inclR R) = J.map (inclR R)
  have h2 : Formalism.UG.cT (sigR R σ) ((γ.1 : Matrix (Fin n) (Fin n) E).map (inclR R)) =
      (Formalism.UG.cT (σ : E →+* E) (γ.1 : Matrix (Fin n) (Fin n) E)).map (inclR (F := F) R) := by
    ext i j
    simp [Formalism.UG.cT, sig_incl]
  rw [h2, ← Matrix.map_mul, ← Matrix.map_mul, h]
def ratG : ↥(Formalism.UG.UJ (σ : E →+* E) J) →* HA R σ J :=
  ((Formalism.UG.bc (inclR R)).comp (Formalism.UG.UJ (σ : E →+* E) J).subtype).codRestrict (HR R σ J)
    (bc_mem R σ J)
abbrev HF (P : Matrix (Fin n) (Fin (r + 1)) E) (f : Matrix (Fin n) (Fin r) E) :=
  fixG (σ : E →+* E) J P f
theorem ratG_mem_Hp (P : Matrix (Fin n) (Fin (r + 1)) E) (f : Matrix (Fin n) (Fin r) E)
    (γ : ↥(HF σ J P f)) : ratG R σ J γ.1 ∈ Hp R σ J P f := by
  obtain ⟨h1, h2⟩ := γ.2
  refine ⟨?_, ?_⟩
  · show (γ.1.1 : Matrix (Fin n) (Fin n) E).map (inclR (F := F) R) * P.map (inclR R) = P.map (inclR R)
    rw [← Matrix.map_mul, h1]
  · show (γ.1.1 : Matrix (Fin n) (Fin n) E).map (inclR (F := F) R) * f.map (inclR R) = f.map (inclR R)
    rw [← Matrix.map_mul, h2]
def ratH (P : Matrix (Fin n) (Fin (r + 1)) E) (f : Matrix (Fin n) (Fin r) E) :
    ↥(HF σ J P f) →* ↥(Hp R σ J P f) :=
  ((ratG R σ J).comp (HF σ J P f).subtype).codRestrict (Hp R σ J P f) (ratG_mem_Hp R σ J P f)
abbrev NF (P : Matrix (Fin n) (Fin (r + 1)) E) := unipG (σ : E →+* E) J (eOf P)
def act (g : HA R σ J) (x : Fin n → R ⊗[F] E) : Fin n → R ⊗[F] E :=
  (HA.mat R σ J g : Matrix (Fin n) (Fin n) (R ⊗[F] E)).mulVec x
theorem act_one (x : Fin n → R ⊗[F] E) : act R σ J 1 x = x := by
  show ((1 : GL (Fin n) (R ⊗[F] E)) : Matrix (Fin n) (Fin n) _).mulVec x = x
  simp
theorem act_mul (g h : HA R σ J) (x : Fin n → R ⊗[F] E) :
    act R σ J (g * h) x = act R σ J g (act R σ J h x) := by
  show ((HA.mat R σ J g * HA.mat R σ J h : GL (Fin n) (R ⊗[F] E)) : Matrix (Fin n) (Fin n) _).mulVec x = _
  rw [Units.val_mul, ← Matrix.mulVec_mulVec]; rfl
theorem act_sub (g : HA R σ J) (x y : Fin n → R ⊗[F] E) :
    act R σ J g (x - y) = act R σ J g x - act R σ J g y := Matrix.mulVec_sub _ _ _
def stabA (M : AddSubgroup (Fin n → R ⊗[F] E)) : Subgroup (HA R σ J) where
  carrier := {g | ∀ x, x ∈ M ↔ act R σ J g x ∈ M}
  one_mem' := fun x => by rw [act_one]
  mul_mem' := fun {a b} ha hb x => by rw [act_mul]; exact (hb x).trans (ha _)
  inv_mem' := fun {a} ha x => by
    have := ha (act R σ J a⁻¹ x)
    rw [← act_mul, mul_inv_cancel, act_one] at this
    exact this.symm
def fixMod (M : AddSubgroup (Fin n → R ⊗[F] E)) (x : Fin n → R ⊗[F] E) : Subgroup (HA R σ J) where
  carrier := {g | g ∈ stabA R σ J M ∧ act R σ J g x - x ∈ M}
  one_mem' := ⟨Subgroup.one_mem _, by rw [act_one, sub_self]; exact M.zero_mem⟩
  mul_mem' := fun {a b} ha hb => ⟨Subgroup.mul_mem _ ha.1 hb.1, by
    have h := M.add_mem ((ha.1 _).1 hb.2) ha.2
    rw [act_sub, sub_add_sub_cancel] at h
    rwa [act_mul]⟩
  inv_mem' := fun {a} ha => ⟨Subgroup.inv_mem _ ha.1, by
    have h := M.neg_mem (((Subgroup.inv_mem _ ha.1 : a⁻¹ ∈ stabA R σ J M) _).1 ha.2)
    rwa [act_sub, ← act_mul, inv_mul_cancel, act_one, neg_sub] at h⟩
end Points
section Levels
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n r k : ℕ} (J : Matrix (Fin n) (Fin n) E)
def bigLat (P : Matrix (Fin n) (Fin (r + 1)) E) (f : Matrix (Fin n) (Fin r) E)
    (β : Matrix (Fin n) (Fin (k + 1)) E) (L : Submodule (𝓞 E) (Fin (k + 1) → E)) :
    Submodule (𝓞 E) (Fin n → E) :=
  Submodule.span (𝓞 E) {v | ∃ (b : Fin r) (a : E), a ∈ dInv E (r - (b : ℕ)) ∧ v = a • fun i => eOf P i b} ⊔
    L.map (β.mulVecLin.restrictScalars (𝓞 E)) ⊔
    Submodule.span (𝓞 E) {v | ∃ (b : Fin r) (a : E), a ∈ (dInv E (r - (b : ℕ)))⁻¹ ∧ v = a • fun i => f i b}
variable (F) in

def vecF (x : Fin n → E) : Fin n → Af F ⊗[F] E := fun i => inclR (Af F) (x i)
variable (F) in

def hat (Λ : Submodule (𝓞 E) (Fin n → E)) : AddSubgroup (Fin n → Af F ⊗[F] E) :=
  AddSubgroup.closure {y | ∃ (t : Af F) (x : Fin n → E),
    (∀ v, evalV F v t ∈ v.adicCompletionIntegers F) ∧ x ∈ Λ ∧ y = t • vecF F x}
variable (F) in

def hatI (I : Ideal (𝓞 E)) (Λ : Submodule (𝓞 E) (Fin n → E)) : AddSubgroup (Fin n → Af F ⊗[F] E) :=
  hat F (I • Λ)
def Kmax (Λ : Submodule (𝓞 E) (Fin n → E)) : Subgroup (HA (Af F) σ J) := stabA (Af F) σ J (hat F Λ)
def uniAt (Λ : Submodule (𝓞 E) (Fin n → E)) (w : Ideal (𝓞 E)) (ε : Fin k → Fin n → E) :
    Subgroup (HA (Af F) σ J) :=
  ⨅ i : Fin k, fixMod (Af F) σ J
    (hat F (Submodule.span (𝓞 E) (ε '' {j | j < i}) ⊔ w • Λ)) (vecF F (ε i))
variable (F) in

def Typed (g₁ g₂ : ℕ) : Set (HeightOneSpectrum (𝓞 F)) :=
  {p | (g₁ : 𝓞 F) ∈ p.asIdeal ∨ (g₂ : 𝓞 F) ∈ p.asIdeal}
def ga (k g : ℕ) : ENNReal :=
  (Nat.card (GL (Fin k) (ZMod g)) : ENNReal) / (Nat.card ↥(Formalism.L2.Col.HU (ZMod g) k) : ENNReal)
open Classical in
variable (F) in

def Gam1 (k g₁ g₂ : ℕ) : ENNReal :=
  ∏ᶠ p ∈ Typed F g₁ g₂, ga k (if (g₁ : 𝓞 F) ∈ p.asIdeal then g₁ else g₂)
variable (P : Matrix (Fin n) (Fin (r + 1)) E) (f : Matrix (Fin n) (Fin r) E)
  (Λ : Submodule (𝓞 E) (Fin n → E)) (g₁ g₂ : ℕ)
  (w : HeightOneSpectrum (𝓞 F) → HeightOneSpectrum (𝓞 E))
  (ε : HeightOneSpectrum (𝓞 F) → Fin k → Fin n → E)
def KH : Subgroup ↥(Hp (Af F) σ J P f) := (Kmax σ J Λ).subgroupOf _
def upperUnitriangularLevelSubgroup : Subgroup ↥(Hp (Af F) σ J P f) :=
  (Kmax σ J Λ ⊓ ⨅ p ∈ Typed F g₁ g₂, uniAt σ J Λ (w p).asIdeal (ε p)).subgroupOf _
def K2 : Set (HA (Af F) σ J) :=
  {x | x ∈ Kmax σ J Λ ∧ ∀ p ∈ Typed F g₁ g₂, ∃ a ∈ Np (Af F) σ J P ⊓ Kmax σ J Λ,
    ∃ u ∈ Hp (Af F) σ J P f ⊓ Kmax σ J Λ ⊓ uniAt σ J Λ (w p).asIdeal (ε p),
      ∀ y ∈ hat F Λ, act (Af F) σ J ((a * u)⁻¹ * x) y - y ∈
        hatI F (p.asIdeal.map (algebraMap (𝓞 F) (𝓞 E))) Λ}
def GamH : Subgroup ↥(Hp (Af F) σ J P f) := (ratH (Af F) σ J P f).range
def cols {V : Type} [AddCommGroup V] [Module ℂ V] (Kl : Subgroup ↥(Hp (Af F) σ J P f))
    (ψ : ↥Kl →* ℂˣ) (π : Representation ℂ ↥(Hp (Ainf F) σ J P f) V) :
    Submodule ℂ (↥(Hp (Af F) σ J P f) → V) where
  carrier := {φ | ∀ (γ : ↥(HF σ J P f)) (x : ↥(Hp (Af F) σ J P f)) (κ : ↥Kl),
    φ (ratH (Af F) σ J P f γ * x * κ) = (((ψ κ)⁻¹ : ℂˣ) : ℂ) • π (ratH (Ainf F) σ J P f γ) (φ x)}
  zero_mem' := fun γ x κ => by simp
  add_mem' := fun {a b} ha hb γ x κ => by simp only [Pi.add_apply, ha γ x κ, hb γ x κ, map_add, smul_add]
  smul_mem' := fun c a ha γ x κ => by
    simp only [Pi.smul_apply, ha γ x κ, map_smul]; rw [smul_comm]
def rho0 : ENNReal :=
  ∑' c : Formalism.UG.ClassSet (GamH σ J P f) (KH σ J P f Λ),
    (ENat.toENNReal (ENat.card ↥(Formalism.UG.stabAt (GamH σ J P f) (KH σ J P f Λ) (Quotient.out c))))⁻¹
def diagH : Subgroup (↥(Hp (Ainf F) σ J P f) × ↥(Hp (Af F) σ J P f)) :=
  ((ratH (Ainf F) σ J P f).prod (ratH (Af F) σ J P f)).range
def diagN : Subgroup (↥(Np (Ainf F) σ J P) × ↥(Np (Af F) σ J P)) :=
  ((NF σ J P).map ((ratG (Ainf F) σ J).prod (ratG (Af F) σ J))).comap
    ((Np (Ainf F) σ J P).subtype.prodMap (Np (Af F) σ J P).subtype)
def NO : Subgroup ↥(Np (Ainf F) σ J P) :=
  ((NF σ J P ⊓ (Kmax σ J Λ).comap (ratG (Af F) σ J)).map (ratG (Ainf F) σ J)).subgroupOf _
def muS (μN : Measure ↥(Np (Af F) σ J P)) (μH : Measure ↥(Hp (Af F) σ J P f))
    (B : Set (HA (Af F) σ J)) : ENNReal :=
  (μN.prod μH) {q | (q.1 : HA (Af F) σ J) * (q.2 : HA (Af F) σ J) ∈ B}
end Levels
def SplitsCompletely (E : Type) [Field E] [NumberField E] (g : ℕ) : Prop :=
  g.Prime ∧ {w : HeightOneSpectrum (𝓞 E) | (g : 𝓞 E) ∈ w.asIdeal}.ncard = Module.finrank ℚ E
def ColumnDim : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → Algebra.Unramified (𝓞 F) (𝓞 E) →
  ∀ (n r k : ℕ), n = k + 2 * r + 1 → 3 ≤ k →
  ∀ (T g₁ g₂ : ℕ), T.Prime → SplitsCompletely E g₁ → SplitsCompletely E g₂ → g₁ ≠ g₂ →
    g₁ ≠ T → g₂ ≠ T → 2 * k < g₁ → 2 * k < g₂ →

  ∀ (J : Matrix (Fin n) (Fin n) E) (P : Matrix (Fin n) (Fin (r + 1)) E) (f : Matrix (Fin n) (Fin r) E)
    (β : Matrix (Fin n) (Fin (k + 1)) E) (L : Submodule (𝓞 E) (Fin (k + 1) → E)) (z : Fin (k + 1) → E),
    IsHermU (σ : E →+* E) J → IsFrame (σ : E →+* E) J (T : E) P → IsDual (σ : E →+* E) J P f →
    IsHermU (σ : E →+* E) (pairM (σ : E →+* E) J β β) →
    pairM (σ : E →+* E) J β (eOf P) = 0 → pairM (σ : E →+* E) J β f = 0 →
    (β.mulVec z = fun i => P i (Fin.last r)) →
    (L, z) ∈ LzSet (σ : E →+* E) (pairM (σ : E →+* E) J β β) (T : E) →
    (∀ x : Fin (k + 1) → E, form (σ : E →+* E) (pairM (σ : E →+* E) J β β) x z = 0 → x ≠ 0 →
      TotPos (form (σ : E →+* E) (pairM (σ : E →+* E) J β β) x x)) →

  ∀ (w : HeightOneSpectrum (𝓞 F) → HeightOneSpectrum (𝓞 E))
    (ε₀ : HeightOneSpectrum (𝓞 F) → Fin k → Fin (k + 1) → E),
    (∀ p ∈ Typed F g₁ g₂, (w p).asIdeal.comap (algebraMap (𝓞 F) (𝓞 E)) = p.asIdeal ∧
      (∀ i, ε₀ p i ∈ L ∧ form (σ : E →+* E) (pairM (σ : E →+* E) J β β) (ε₀ p i) z = 0) ∧
      ∀ a : Fin k → 𝓞 E, ∑ i, a i • ε₀ p i ∈ (w p).asIdeal • L → ∀ i, a i ∈ (w p).asIdeal) →
  let Λ := bigLat P f β L
  let ε : HeightOneSpectrum (𝓞 F) → Fin k → Fin n → E := fun p i => β.mulVec (ε₀ p i)
  let K'' := upperUnitriangularLevelSubgroup σ J P f Λ g₁ g₂ w ε
  ∀ (ψ : ↥K'' →* ℂˣ) (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (π : Representation ℂ ↥(Hp (Ainf F) σ J P f) V), π.IsIrreducible →
  let d : ENNReal := (Module.finrank ℂ ↥(cols σ J P f K'' ψ π) : ℕ)
  let dπ : ENNReal := (Module.finrank ℂ V : ℕ)
  (FiniteDimensional ℂ ↥(cols σ J P f K'' ψ π) ∧ Finite (Formalism.UG.ClassSet (GamH σ J P f) K'') ∧
    d = dπ * (Nat.card (Formalism.UG.ClassSet (GamH σ J P f) K'') : ENNReal) ∧
    d = dπ * Gam1 F k g₁ g₂ * rho0 σ J P f Λ ∧
    d = dπ * Gam1 F k g₁ g₂ * massLz (σ : E →+* E) (pairM (σ : E →+* E) J β β) (T : E)) ∧
  ∀ (μHi : Measure ↥(Hp (Ainf F) σ J P f)) (μHf : Measure ↥(Hp (Af F) σ J P f))
    (𝓕H : Set (↥(Hp (Ainf F) σ J P f) × ↥(Hp (Af F) σ J P f))),
    μHi.IsHaarMeasure → μHf.IsHaarMeasure →
    IsFundamentalDomain ↥(diagH σ J P f) 𝓕H (μHi.prod μHf) →
    (μHi Set.univ ≠ 0 ∧ μHi Set.univ ≠ ⊤ ∧ μHf K'' ≠ 0 ∧ μHf K'' ≠ ⊤ ∧
      d = dπ * (μHi.prod μHf) 𝓕H / (μHi Set.univ * μHf K'')) ∧
    ∀ (μNi : Measure ↥(Np (Ainf F) σ J P)) (μNf : Measure ↥(Np (Af F) σ J P))
      (𝓕N : Set (↥(Np (Ainf F) σ J P) × ↥(Np (Af F) σ J P))) (𝓓 : Set ↥(Np (Ainf F) σ J P)),
      μNi.IsHaarMeasure → μNf.IsHaarMeasure →
      IsFundamentalDomain ↥(diagN σ J P) 𝓕N (μNi.prod μNf) →
      IsFundamentalDomain ↥(NO σ J P Λ) 𝓓 μNi →
      (μHi.prod μHf) 𝓕H = 1 → (μNi.prod μNf) 𝓕N = 1 →
      μNi 𝓓 ≠ 0 ∧ μNi 𝓓 ≠ ⊤ ∧
      (μNi 𝓓 * μHi Set.univ / dπ)⁻¹ = dπ / (μNi 𝓓 * μHi Set.univ) ∧
      dπ / (μNi 𝓓 * μHi Set.univ) =
        d * muS σ J P f μNf μHf (Sp (Af F) σ J P ∩ K2 σ J P f Λ g₁ g₂ w ε)
example (g : ℕ) : ga 0 g = 1 := by
  have h1 : Nat.card (GL (Fin 0) (ZMod g)) = 1 := Nat.card_unique
  have h2 : Nat.card ↥(Formalism.L2.Col.HU (ZMod g) 0) = 1 := Nat.card_unique
  simp [ga, h1, h2]
end GlobalTheory.IndefiniteRowSideFullHecke.ParabolicSubgroups


