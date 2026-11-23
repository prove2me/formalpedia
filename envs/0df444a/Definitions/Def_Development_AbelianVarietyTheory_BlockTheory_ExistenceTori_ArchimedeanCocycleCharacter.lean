-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_ArchimedeanCocycleCharacter
-- name    : Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_ArchimedeanCocycleCharacter
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:24:07.208971+00:00
-- url     : https://prove2.me/theorems/1078b510-8834-4cb3-9768-1be99b37cc8e
-- title:
--   Archimedean Cocycle Character
-- statement:
--   Definitions and structural lemmas for Archimedean Cocycle Character, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/ExistenceTori/ArchimedeanCocycleCharacter.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_AdelicNormWeight
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_NormsFree
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.IndefiniteRowSideFullHecke.ArchimedeanCocycleCharacter
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD NumberField
open Formalism.L2.Pj Formalism.L2.PjFree GlobalTheory.IndefiniteRowSideFullHecke.AdelicNormWeight
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
abbrev LevGrp (Dw : Datum H) (l : Level H) : Type := LevQ Dw l ≃ₗ[𝓞 E] LevQ Dw l
section Act
variable {Xo : Moduli Dw l} {c : Coeff l}
def FrAlong {ρ : Xo.X ⟶ Xo.X} (m : SABMap Xo.univ.t Xo.univ.t ρ) {k : Type} [CommRing k] [Algebra c.F k]
    (y y' : FrPt Xo c k) : Prop :=
  y.x ≫ ρ = y'.x ∧ (∀ τ i, y.u τ i ≫ m.φ = y'.u τ i) ∧
  ∃ (w₀ : LB.Iso Xo.univ.t.PP.L (Xo.univ.t.PP.L.pull m.φ)) (pm : Gx y.x ⟶ Gx y'.x)
    (t : LB.Sec (LB.LinComb (Xo.univ.t.PP.L.pull m.φ) (K := Fin 1)
      (fun _ => (snd (Over.mk y.x) Xo.univ.t.G).left) (fun _ => 1))),
    w₀.IsGen ∧
    LB.Gen.Maps (LB.linCombIso w₀ (K := PUnit) (fun _ => eSec Xo.univ.t.G) (fun _ => 1))
      Xo.univ.t.PP.rig (m.cm.rigPull Xo.univ.t.PP.L Xo.univ.t.PP.rig) ∧
    pm ≫ (snd (Over.mk y'.x) Xo.univ.t.G).left = (snd (Over.mk y.x) Xo.univ.t.G).left ≫ m.φ ∧
    pm ≫ (fst (Over.mk y'.x) Xo.univ.t.G).left = (fst (Over.mk y.x) Xo.univ.t.G).left ∧
    SecMaps (LB.linCombIso w₀ (K := Fin 1) (fun _ => (snd (Over.mk y.x) Xo.univ.t.G).left) (fun _ => 1))
      y.s t ∧
    ∀ (i : Fin 1 → Xo.univ.t.PP.L.ι)
      (h : (LB.LinComb (Xo.univ.t.PP.L.pull m.φ) (K := Fin 1)
        (fun _ => (snd (Over.mk y.x) Xo.univ.t.G).left) (fun _ => 1)).U (fun _ _ => i 0) ≤
          pm ⁻¹ᵁ (PPx y'.x).U i),
      (pm.appLE _ _ h).hom (y'.s.f i) = t.f (fun _ _ => i 0)
def IsLevelAct (κ : LevGrp Dw l) (f f' : Rul Xo c) : Prop :=
  ∃ (ρ : Xo.X ≅ Xo.X) (m : SABMap Xo.univ.t Xo.univ.t ρ.hom), ρ.hom ≫ Xo.s = Xo.s ∧
    (∀ a a' : Dw.La, (Submodule.Quotient.mk a' : LevQ Dw l) = κ (Submodule.Quotient.mk a) →
      (Xo.univ.eta a').left ≫ m.φ = ρ.hom ≫ (Xo.univ.eta a).left) ∧
    (∀ a : Dw.La, (Xo.univ.etaA a).left ≫ m.φ = ρ.hom ≫ (Xo.univ.etaA a).left) ∧
    ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra c.F k] (y : FrPt Xo c k),
      ∃ y' : FrPt Xo c k, FrAlong m y y' ∧ evR Xo c f' y = evR Xo c f y'
end Act
section Placed
variable (c : Coeff l) {n : ℕ}
def push (γ : Matrix (Fin n) (Fin n) E) : MvPolynomial (LtN Dw n) c.F →ₐ[c.F] MvPolynomial (LtN Dw n) c.F :=
  MvPolynomial.aeval fun m : LtN Dw n => letB c m.1 m.2.1 fun a => IsCMField.complexConj E (γ a m.2.2)
def archChar (dd : (E →+* ℂ) → ℤ) (γ : Matrix (Fin n) (Fin n) E) : c.F :=
  ∏ τ : E →+* ℂ, embF c τ γ.det ^ dd τ
def cocyc (dd : (E →+* ℂ) → ℤ) {J : Subgroup (UA E n)} (lam : J →* c.Fˣ) (γ : Matrix (Fin n) (Fin n) E) (k : J) : c.F :=
  archChar c dd γ * ((lam k : c.Fˣ) : c.F)
def IsPlaced (dd : (E →+* ℂ) → ℤ) {J : Subgroup (UA E n)} (lam : J →* c.Fˣ)
    {T : Type} [AddCommGroup T] [Module c.F T] (io : T →ₗ[c.F] MvPolynomial (LtN Dw n) c.F)
    (f : UA E n → T) : Prop :=
  ∀ (γ₀ : Matrix (Fin n) (Fin n) E) (γ : UA E n), γ.1 = γ₀.map (diagE E) → ∀ (h : UA E n) (k : J),
    io (f (γ * h * (k : UA E n))) = cocyc c dd lam γ₀ k • push c γ₀ (io (f h))
variable {c} {Xo : Moduli Dw l}
def IndLaw (d : DeltaDat Xo c n) (a : (E →+* ℂ) × ℕ → ℕ) (S : Finset (Plc E)) {J : Subgroup (UA E n)}
    (ep : UA E n → ℂ) (ph : (Fin n → ConjQ Dw l) → c.F) (phδ : (Fin n → LaJ Xo c d) → c.F)
    (dd : (E →+* ℂ) → ℤ) (lam : J →* c.Fˣ) : Prop :=
  ∀ (γ₀ : Matrix (Fin n) (Fin n) E) (γ h : UA E n) (k : J) (N N' : ℕ) (κ κ' : d.c₂.F)
    (P : MvPolynomial (LtN Dw n) c.F),
    γ.1 = γ₀.map (diagE E) → TrivOn S h → TrivOn S (γ * h * (k : UA E n)) →
    (AdelicNormWeight.latOf h).LevOK N d.l₂.M → (AdelicNormWeight.latOf (γ * h * (k : UA E n))).LevOK N' d.l₂.M →
    IsScalar (Dw := Dw) d.c₂ ep h κ → IsScalar (Dw := Dw) d.c₂ ep (γ * h * (k : UA E n)) κ' →
    P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)) →
    ∀ (K : Type) [Field K] [IsAlgClosed K] [Algebra d.c₂.F K] (y₂ : FrPt d.Xo₂ d.c₂ K) (v v' : K),
      ThLaValAt d.Xo₂ d.c₂ d.nab₂ (coverDatum d ph phδ) (AdelicNormWeight.latOf h) N
        (MvPolynomial.map (d.eF : c.F →+* d.c₂.F) P) y₂ v →
      ThLaValAt d.Xo₂ d.c₂ d.nab₂ (coverDatum d ph phδ) (AdelicNormWeight.latOf (γ * h * (k : UA E n))) N'
        (MvPolynomial.map (d.eF : c.F →+* d.c₂.F) (cocyc c dd lam γ₀ k • push c γ₀ P)) y₂ v' →
      algebraMap d.c₂.F K κ * v = algebraMap d.c₂.F K κ' * v'
def TupleOK (q₁ : ℕ) (a : (E →+* ℂ) × ℕ → ℕ) (dd : (E →+* ℂ) → ℤ) (d : DeltaDat Xo c n) {ι : Type} (vol : ℚ)
    (S : Finset (Plc E)) (J : Subgroup (UA E n)) (h : ι → UA E n) (N : ι → ℕ) (ep : UA E n → ℂ) (cξ : Rul Xo c)
    (ph : (Fin n → ConjQ Dw l) → c.F) (phδ : (Fin n → LaJ Xo c d) → c.F) (lam : J →* c.Fˣ) : Prop :=
  0 < vol ∧ CoverOK d phδ ∧ Admissible H q₁ d.l₂.M S J h N ∧
    (∀ g : UA E n, TrivOn S g → ‖ep g‖ = 1 ∧ ∃ κ, IsScalar (Dw := Dw) c ep g κ) ∧
    cξ ∈ sec Xo c 0 0 ∧ (∀ k, IsOfFinOrder (lam k)) ∧ IndLaw d a S ep ph phδ dd lam
end Placed
section Row
variable {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (σ : c.F →+* ℂ)
  {G : Type} [Group G] (Γ : Subgroup G) (dict : G → Σ k, Frame ((U σ).X k).Ψ r) (mu : G → ℂ) (xi : ℝ)
def jConst (a : (E →+* ℂ) × ℕ → ℕ) (cc : (U σ).Comp → ℂ) (f : Rul Xo c) (g : G) : ℂ :=
  cc (dict g).1 * ((lieFac Dw xi a : ℝ) : ℂ) * (mu g * rdU (U σ) f (dict g).1 (dict g).2)
def ReadOK : Prop :=
  (∀ σ', GoodEmb c σ' → IsUnf (U σ')) ∧ GoodEmb c σ ∧
    (∀ (k : (U σ).Comp) (τ : E →+* ℂ), ‖τ ((U σ).X k).ξ0‖ = xi) ∧
    (∀ g, (dict g).2 ∈ ((U σ).X (dict g).1).dom) ∧
    (∀ g τ i, ‖dmin ((U σ).X (dict g).1).Gm (dict g).2 τ i‖ = 1) ∧
    (∀ γ ∈ Γ, ∀ g, ∃ γ' ∈ ((U σ).X (dict g).1).Γ, dict (γ * g) = ⟨(dict g).1, lact γ' (dict g).2⟩) ∧
    (∀ k, ∀ x ∈ ((U σ).X k).dom, ∃ g, ∃ γ ∈ ((U σ).X k).Γ, ∃ b ∈ Bor ((U σ).X k).Ψ r,
      dict g = ⟨k, rmul (lact γ x) b⟩) ∧
    (∀ g g', mu (g * g') = mu g * mu g') ∧ (∀ g, ‖mu g‖ = 1) ∧ ∀ γ ∈ Γ, mu γ = 1
def IsCharFactor (cξ : Rul Xo c) : Prop :=
  ∃ (ω : ℂˣ) (χ : G →* ℂˣ), IsOfFinOrder ω ∧ IsOfFinOrder χ ∧ (∀ γ ∈ Γ, χ γ = 1) ∧
    ∀ g, rdU (U σ) cξ (dict g).1 (dict g).2 = ((ω * χ g : ℂˣ) : ℂ)
variable (a : (E →+* ℂ) × ℕ → ℕ) {n : ℕ}
  {T : Type} [AddCommGroup T] [Module c.F T] (io : T →ₗ[c.F] MvPolynomial (LtN Dw n) c.F)
  {Tup : Type} (d : Tup → DeltaDat Xo c n) {ι : Tup → Type} [∀ t, Fintype (ι t)] (vol : Tup → ℚ)
  (J : Tup → Subgroup (UA E n)) (h : ∀ t, ι t → UA E n) (N : ∀ t, ι t → ℕ) (ep : Tup → UA E n → ℂ)
  (cξ : Tup → Rul Xo c) (φ : Tup → (Fin n → ConjQ Dw l) → c.F) (φδ : ∀ t, (Fin n → LaJ Xo c (d t)) → c.F)
def ConstOK {Comp : Type} (cc : Comp → ℂ) (ph : ℂ) (z : LevGrp Dw l) (ze : Tup → ℂ) : Prop :=
  (∀ k, ‖cc k‖ = 1) ∧ ‖ph‖ = 1 ∧ z ∈ Subgroup.center (LevGrp Dw l) ∧ ∀ t, ∃ m : ℕ, 0 < m ∧ ze t ^ m = 1
def EqAt (cc : (U σ).Comp → ℂ) (ph : ℂ) (z : LevGrp Dw l) (ζ : ℂ) (t : Tup) (x : ι t → T) (θ : G → ℂ) : Prop :=
  (∃ F ∈ cusp Xo c U a n, ∃ F' ∈ cusp Xo c U a n,
    IsClassSumRuleDown Xo c (d t) (vol t) (J t) (h t) (N t) (ep t) (cξ t) (φ t) (φδ t) io x F ∧ IsLevelAct z F F') ∧
  ∀ F ∈ cusp Xo c U a n, ∀ F' ∈ cusp Xo c U a n,
    IsClassSumRuleDown Xo c (d t) (vol t) (J t) (h t) (N t) (ep t) (cξ t) (φ t) (φδ t) io x F → IsLevelAct z F F' →
      ∀ g, ph * θ g = ζ * jConst U σ dict mu xi a cc F' g
variable (dd : (E →+* ℂ) → ℤ) (lam : ∀ t, J t →* c.Fˣ) (thAd : Tup → (UA E n → T) → G → ℂ)
def RowAt (cc : (U σ).Comp → ℂ) (ph : ℂ) (z : LevGrp Dw l) (ze : Tup → ℂ) : Prop :=
  ConstOK cc ph z ze ∧ ∀ (t : Tup) (f : UA E n → T), IsPlaced c dd (lam t) io f →
    EqAt U σ dict mu xi a io d vol J h N ep cξ φ φδ cc ph z (ze t) t (fun i => f (h t i)) (thAd t f)
variable (q₁ : ℕ) (S : Tup → Finset (Plc E))
def DataOK : Prop :=
  ReadOK U σ Γ dict mu xi ∧ Dom a n ∧ LastPos Dw a ∧ IntoHarm c a io ∧
    ∀ t, TupleOK q₁ a dd (d t) (vol t) (S t) (J t) (h t) (N t) (ep t) (cξ t) (φ t) (φδ t) (lam t) ∧
      IsCharFactor U σ Γ dict (cξ t)
def ThetaDictionaryAt (cc : (U σ).Comp → ℂ) (ph : ℂ) (z : LevGrp Dw l) (ze : Tup → ℂ) : Prop :=
  DataOK U σ Γ dict mu xi a io d vol J h N ep cξ φ φδ dd lam q₁ S ∧
    RowAt U σ dict mu xi a io d vol J h N ep cξ φ φδ dd lam thAd cc ph z ze
def ThetaDictionary : Prop :=
  ∃ (cc : (U σ).Comp → ℂ) (ph : ℂ) (z : LevGrp Dw l) (ze : Tup → ℂ),
    ThetaDictionaryAt U σ Γ dict mu xi a io d vol J h N ep cξ φ φδ dd lam thAd q₁ S cc ph z ze
end Row
example (c : Coeff l) {n : ℕ} (dd : (E →+* ℂ) → ℤ) {J : Subgroup (UA E n)} (lam : J →* c.Fˣ)
    (io : c.F →ₗ[c.F] MvPolynomial (LtN Dw n) c.F) : IsPlaced c dd lam io (0 : UA E n → c.F) := by
  intro γ₀ γ _ h k
  simp
end GlobalTheory.IndefiniteRowSideFullHecke.ArchimedeanCocycleCharacter


