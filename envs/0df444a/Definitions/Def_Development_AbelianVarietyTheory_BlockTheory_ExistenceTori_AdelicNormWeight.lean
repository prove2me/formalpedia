-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_AdelicNormWeight
-- name    : Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_AdelicNormWeight
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T15:15:38.438739+00:00
-- url     : https://prove2.me/theorems/f0bdd439-ae10-4825-85ff-91dc3092d842
-- title:
--   Adelic Norm Weight
-- statement:
--   Definitions and structural lemmas for Adelic Norm Weight, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/ExistenceTori/AdelicNormWeight.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThShort
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IsThRule
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RowDeg
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IsCombAt
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
namespace GlobalTheory.IndefiniteRowSideFullHecke.AdelicNormWeight
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField IsDedekindDomain
open scoped TensorProduct
section Adelic
variable (E : Type) [Field E] [NumberField E] [IsCMField E]
abbrev Plc : Type := HeightOneSpectrum (𝓞 (maximalRealSubfield E))
abbrev AdF : Type := FiniteAdeleRing (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E)
def AdE : Type := AdF E ⊗[maximalRealSubfield E] E
instance : CommRing (AdE E) := inferInstanceAs (CommRing (AdF E ⊗[maximalRealSubfield E] E))
def adConj : (AdF E ⊗[maximalRealSubfield E] E) →ₐ[maximalRealSubfield E] (AdF E ⊗[maximalRealSubfield E] E) :=
  Algebra.TensorProduct.map (AlgHom.id _ _) (IsCMField.complexConj E).toAlgHom
theorem adConj_adConj (x : AdF E ⊗[maximalRealSubfield E] E) : adConj E (adConj E x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [adConj]
  | add x y hx hy => simp [hx, hy]
instance : StarRing (AdE E) where
  star x := adConj E x
  star_involutive x := adConj_adConj E x
  star_mul x y := by
    show adConj E (x * y) = adConj E y * adConj E x
    rw [mul_comm (adConj E y)]
    exact map_mul (adConj E) x y
  star_add x y := map_add (adConj E) x y
def diagE : E →+* AdE E :=
  (Algebra.TensorProduct.includeRight (R := maximalRealSubfield E) (A := AdF E) (B := E)).toRingHom
def inclF : AdF E →+* AdE E :=
  Algebra.TensorProduct.includeLeftRingHom (R := maximalRealSubfield E) (A := AdF E) (B := E)
variable {E} in

def compF (v : Plc E) : AdF E →ₐ[maximalRealSubfield E] v.adicCompletion (maximalRealSubfield E) where
  toFun a := a v
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl
variable {E} in

def compE (v : Plc E) : AdE E →+* (v.adicCompletion (maximalRealSubfield E) ⊗[maximalRealSubfield E] E) :=
  (Algebra.TensorProduct.map (compF v) (AlgHom.id (maximalRealSubfield E) E)).toRingHom
def intAd : Subring (AdE E) :=
  Subring.closure ((inclF E '' {a | ∀ v : Plc E, a v ∈ v.adicCompletionIntegers (maximalRealSubfield E)}) ∪
    Set.range fun o : 𝓞 E => diagE E (o : E))
abbrev UA (n : ℕ) : Type := Matrix.unitaryGroup (Fin n) (AdE E)
variable {E} {n : ℕ}
def ptsIn (n : ℕ) (R : Subring (AdE E)) : Subgroup (UA E n) where
  carrier := {k | (∀ a b, k.1 a b ∈ R) ∧ ∀ a b, (k⁻¹).1 a b ∈ R}
  one_mem' := by
    have : ∀ a b : Fin n, (1 : UA E n).1 a b ∈ R := fun a b => by
      show (1 : Matrix (Fin n) (Fin n) (AdE E)) a b ∈ R
      rw [Matrix.one_apply]
      split_ifs
      exacts [R.one_mem, R.zero_mem]
    exact ⟨this, by rw [inv_one]; exact this⟩
  mul_mem' := by
    have key : ∀ x y : UA E n, (∀ a b, x.1 a b ∈ R) → (∀ a b, y.1 a b ∈ R) → ∀ a b, (x * y).1 a b ∈ R :=
      fun x y hx hy a b => by
        show (x.1 * y.1) a b ∈ R
        rw [Matrix.mul_apply]
        exact R.sum_mem fun j _ => R.mul_mem (hx a j) (hy j b)
    intro x y hx hy
    exact ⟨key x y hx.1 hy.1, by rw [mul_inv_rev]; exact key _ _ hy.2 hx.2⟩
  inv_mem' := fun {x} hx => ⟨hx.2, by rw [inv_inv]; exact hx.1⟩
variable (E) in

def ratPts (n : ℕ) : Subgroup (UA E n) := ptsIn n (diagE E).range
variable (E) in

def maxCpt (n : ℕ) : Subgroup (UA E n) := ptsIn n (intAd E)
def IsLevelGrp (J : Subgroup (UA E n)) : Prop :=
  J ≤ maxCpt E n ∧
  (∃ m : ℕ, m ≠ 0 ∧ ∀ k ∈ maxCpt E n,
    (∀ a b, ∃ u ∈ intAd E, (k.1 - 1) a b = (m : AdE E) * u) → k ∈ J) ∧
  ∀ k : UA E n, (∀ v : Plc E, ∃ j ∈ J, ∀ a b, compE v (k.1 a b) = compE v (j.1 a b)) → k ∈ J
def TrivOn (S : Finset (Plc E)) (h : UA E n) : Prop :=
  ∀ v ∈ S, ∀ a b, compE v (h.1 a b) = compE v ((1 : Matrix (Fin n) (Fin n) (AdE E)) a b)
def Covers (S : Finset (Plc E)) (m : ℕ) : Prop :=
  ∀ v : Plc E, (m : 𝓞 (maximalRealSubfield E)) ∈ v.asIdeal → v ∈ S
def latOf (h : UA E n) : GenLat E n where
  La :=
  { carrier := {x | ∃ u : Fin n → AdE E, (∀ b, u b ∈ intAd E) ∧ ∀ a, diagE E (x a) = ∑ b, star (h.1 a b) * u b}
    zero_mem' := ⟨0, fun _ => (intAd E).zero_mem, fun a => by simp⟩
    add_mem' := by
      rintro x y ⟨u, hu, hx⟩ ⟨w, hw, hy⟩
      refine ⟨u + w, fun b => (intAd E).add_mem (hu b) (hw b), fun a => ?_⟩
      simp [hx a, hy a, mul_add, Finset.sum_add_distrib]
    smul_mem' := by
      rintro o x ⟨u, hu, hx⟩
      refine ⟨fun b => diagE E (o : E) * u b,
        fun b => (intAd E).mul_mem (Subring.subset_closure (Or.inr ⟨o, rfl⟩)) (hu b), fun a => ?_⟩
      have : (o • x) a = (o : E) * x a := rfl
      rw [this, map_mul, hx a, Finset.mul_sum]
      exact Finset.sum_congr rfl fun b _ => by ring }
def stab (J : Subgroup (UA E n)) (h : UA E n) : Subgroup (UA E n) :=
  ratPts E n ⊓ J.comap (MulAut.conj h⁻¹).toMonoidHom
def weight (vol : ℚ) (J : Subgroup (UA E n)) (h : UA E n) : ℚ := vol / (Nat.card (stab J h) : ℚ)
def normH (r : ℕ) (h : UA E n) : ℕ :=
  ((latOf h).Ln.toAddSubgroup.addSubgroupOf (latOf h).La.toAddSubgroup).index ^ r
def IsRepSystem {ι : Type} (S : Finset (Plc E)) (J : Subgroup (UA E n)) (h : ι → UA E n) : Prop :=
  (∀ i, TrivOn S (h i)) ∧ ∀ g : UA E n, ∃! i, ∃ γ ∈ ratPts E n, ∃ k ∈ J, g = γ * h i * k
def Admissible {ι : Type} (H : Host E) (q₁ M : ℕ) (S : Finset (Plc E)) (J : Subgroup (UA E n))
    (h : ι → UA E n) (N : ι → ℕ) : Prop :=
  IsLevelGrp J ∧ Covers S (2 * q₁ * H.d * M) ∧ IsRepSystem S J h ∧ ∀ i, (latOf (h i)).LevOK (N i) M
def SplitSupp (H : Host E) (Λ : GenLat E n) : Prop :=
  ∃ 𝔞 : Ideal (𝓞 E), (∀ 𝔭 : Ideal (𝓞 E), 𝔭.IsMaximal → 𝔭.map (H.bar : 𝓞 E →+* 𝓞 E) = 𝔭 → ¬ 𝔞 ≤ 𝔭) ∧
    𝔞 • Λ.La ≤ stdLat E n ∧ 𝔞 • stdLat E n ≤ Λ.La
def ScalarPin (H : Host E) (S : Finset (Plc E)) (χ : Ideal (𝓞 E) → ℂˣ) (ep : UA E n → ℂ) : Prop :=
  ∀ h : UA E n, TrivOn S h → ‖ep h‖ = 1 ∧
    ∀ 𝔠 : Ideal (𝓞 E), 𝔠 ⊔ 𝔠.map (H.bar : 𝓞 E →+* 𝓞 E) = ⊤ →
      𝔠 • Submodule.span (𝓞 E) (detSet (latOf h).La) =
        𝔠.map (H.bar : 𝓞 E →+* 𝓞 E) • (1 : Submodule (𝓞 E) E) →
      (ep h = (((χ 𝔠)⁻¹ : ℂˣ) : ℂ) ∨ ep h = -(((χ 𝔠)⁻¹ : ℂˣ) : ℂ)) ∧
        (SplitSupp H (latOf h) → ep h = (((χ 𝔠)⁻¹ : ℂˣ) : ℂ))
variable (E) in

def StabFinite (n : ℕ) : Prop :=
  ∀ (J : Subgroup (UA E n)) (h : UA E n), IsLevelGrp J → Finite (stab J h)
def RepsExist (H : Host E) (n : ℕ) : Prop :=
  ∀ (q₁ M : ℕ) (S : Finset (Plc E)) (J : Subgroup (UA E n)), Odd M → IsLevelGrp J →
    Covers S (2 * q₁ * H.d * M) →
      ∃ (k : ℕ) (h : Fin k → UA E n) (N : Fin k → ℕ), Admissible H q₁ M S J h N
example (S : Finset (Plc E)) : TrivOn S (1 : UA E n) := fun _ _ _ _ => rfl
example (J : Subgroup (UA E n)) (h γ : UA E n) : γ ∈ stab J h ↔ γ ∈ ratPts E n ∧ h⁻¹ * γ * h ∈ J := by
  simp [stab]
end Adelic
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l)
abbrev ConjQ (Dw : Datum H) (l : Level H) : Type := Dw.La ⧸ (Mfr l • ⊤ : Submodule (𝓞 E) Dw.La)
def fourierSum {n : ℕ} (ph : (Fin n → ConjQ Dw l) → c.F) : (Fin n → LevQ Dw l) → c.F :=
  fun q => ∑ᶠ x : Fin n → ConjQ Dw l, ph x * zetaM c ^ (-pairL (l := l) (fun b => qRep (x b)) (fun b => levRep (q b)))
def fourierCoeff {n : ℕ} (ph : (Fin n → ConjQ Dw l) → c.F) : (Fin n → LevQ Dw l) → c.F :=
  fun q => ((Nat.card (Fin n → LevQ Dw l) : c.F))⁻¹ * fourierSum c ph q
def FixesDatum {n : ℕ} (J : Subgroup (UA E n)) (ph : (Fin n → ConjQ Dw l) → c.F) : Prop :=
  ∀ k ∈ J, ∀ κ : Fin n → Fin n → 𝓞 E,
    (∀ a b, ∃ u ∈ intAd E, star (k.1 a b) - diagE E (κ a b : E) = (l.M : AdE E) * u) →
      ∀ x, ph (fun a => ∑ b, κ a b • x b) = ph x
def ThLaValAt (nab : NabV Xo c) {n : ℕ} (ph : (Fin n → ConjQ Dw l) → c.F) (Λ : GenLat E n) (N : ℕ)
    (P : MvPolynomial (LtN Dw n) c.F) {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (v : S) : Prop :=
  ShortValAt Xo c nab (fourierSum c ph) Λ 1 N P y v
def IsScalar {n : ℕ} (ep : UA E n → ℂ) (h : UA E n) (κ : c.F) : Prop :=
  (κ : ℂ) = ep h * (((Real.sqrt (normH (Dw.p + Dw.q) h : ℝ))⁻¹ : ℝ) : ℂ)
def PolySumValAt (nab : NabV Xo c) {n : ℕ} {ι : Type} [Fintype ι] (vol : ℚ) (J : Subgroup (UA E n))
    (h : ι → UA E n) (N : ι → ℕ) (ep : UA E n → ℂ) (cξ : Rul Xo c) (ph : (Fin n → ConjQ Dw l) → c.F)
    (P : ι → MvPolynomial (LtN Dw n) c.F) {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (v : S) : Prop :=
  ∃ (κ : ι → c.F) (t : ι → S), (∀ i, IsScalar (Dw := Dw) c ep (h i) (κ i)) ∧
    (∀ i, ThLaValAt Xo c nab ph (latOf (h i)) (N i) (P i) y (t i)) ∧
    v = evR Xo c cξ y * ∑ i, algebraMap c.F S ((weight vol J (h i) : c.F) * κ i) * t i
def ClassSumValAt (nab : NabV Xo c) {n : ℕ} {ι : Type} [Fintype ι] (vol : ℚ) (J : Subgroup (UA E n))
    (h : ι → UA E n) (N : ι → ℕ) (ep : UA E n → ℂ) (cξ : Rul Xo c) (ph : (Fin n → ConjQ Dw l) → c.F)
    {T : Type} [AddCommGroup T] [Module c.F T] (io : T →ₗ[c.F] MvPolynomial (LtN Dw n) c.F) (x : ι → T)
    {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (v : S) : Prop :=
  PolySumValAt Xo c nab vol J h N ep cξ ph (fun i => io (x i)) y v
def IsClassSumRule (nab : NabV Xo c) {n : ℕ} {ι : Type} [Fintype ι] (vol : ℚ) (J : Subgroup (UA E n))
    (h : ι → UA E n) (N : ι → ℕ) (ep : UA E n → ℂ) (cξ : Rul Xo c) (ph : (Fin n → ConjQ Dw l) → c.F)
    {T : Type} [AddCommGroup T] [Module c.F T] (io : T →ₗ[c.F] MvPolynomial (LtN Dw n) c.F) (x : ι → T)
    (f : Rul Xo c) : Prop :=
  ∀ (p : TRing c.F) (y : FrPt Xo c p.R), ClassSumValAt Xo c nab vol J h N ep cξ ph io x y (f p y)
def IsDetFactor (σ0 : c.F →+* ℂ) (Cls : Type) [CommGroup Cls] (ξ : Cls →* c.Fˣ) (gdet : FrPt Xo c (CAt σ0) → Cls)
    (cξ : Rul Xo c) : Prop :=
  cξ ∈ sec Xo c 0 0 ∧ ∀ y : FrPt Xo c (CAt σ0),
    evR Xo c cξ y = algebraMap c.F (CAt σ0) ((ξ (gdet y) : c.Fˣ) : c.F)
variable {Xo c} in

def coverDatum {n : ℕ} (d : DeltaDat Xo c n) (ph : (Fin n → ConjQ Dw l) → c.F) (phδ : (Fin n → LaJ Xo c d) → c.F) :
    (Fin n → ConjQ Dw d.l₂) → d.c₂.F :=
  fun x => d.eF (ph (fun b => Submodule.Quotient.mk (qRep (x b))) * phδ (fun b => Submodule.Quotient.mk (qRep (x b))))
variable {Xo c} in

def DeltaEquiv {n : ℕ} (d : DeltaDat Xo c n) (phδ : (Fin n → LaJ Xo c d) → c.F)
    (ψ : (LaI Xo c d ≃ₗ[𝓞 E] LaI Xo c d) →* c.Fˣ) : Prop :=
  ∀ (k : LaI Xo c d ≃ₗ[𝓞 E] LaI Xo c d) (kst : LaJ Xo c d ≃ₗ[𝓞 E] LaJ Xo c d),
    (∀ u v : Dw.La, ((d.pd : ℤ) ∣ Dw.EF (qRep (kst (Submodule.Quotient.mk u))) (cHalf H d.I • v) -
      Dw.EF u (cHalf H d.I • qRep (k (Submodule.Quotient.mk v))))) →
    ∀ x, phδ (fun b => kst (x b)) = (((ψ k)⁻¹ : c.Fˣ) : c.F) * phδ x
variable {Xo c} in

def CoverOK {n : ℕ} (d : DeltaDat Xo c n) (phδ : (Fin n → LaJ Xo c d) → c.F) : Prop :=
  d.IsLev ∧ d.l₂.A = l.A ∧
    ∃ ψ : (LaI Xo c d ≃ₗ[𝓞 E] LaI Xo c d) →* c.Fˣ, d.PsiTie ψ ∧ DeltaEquiv d phδ ψ
def IsClassSumRuleDown {n : ℕ} (d : DeltaDat Xo c n) {ι : Type} [Fintype ι] (vol : ℚ) (J : Subgroup (UA E n))
    (h : ι → UA E n) (N : ι → ℕ) (ep : UA E n → ℂ) (cξ : Rul Xo c) (ph : (Fin n → ConjQ Dw l) → c.F)
    (phδ : (Fin n → LaJ Xo c d) → c.F)
    {T : Type} [AddCommGroup T] [Module c.F T] (io : T →ₗ[c.F] MvPolynomial (LtN Dw n) c.F) (x : ι → T)
    (f : Rul Xo c) : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra c.F k] [Algebra d.c₂.F k],
    (∀ a : c.F, algebraMap d.c₂.F k (d.eF a) = algebraMap c.F k a) →
    ∀ (y : FrPt Xo c k) (y₂ : FrPt d.Xo₂ d.c₂ k), FrOver d y₂ y →
      ∃ v : k, PolySumValAt d.Xo₂ d.c₂ d.nab₂ vol J h N ep d.cδ (coverDatum d ph phδ)
          (fun i => MvPolynomial.map (d.eF : c.F →+* d.c₂.F) (io (x i))) y₂ v ∧
        evR Xo c f y = evR Xo c cξ y * v
def IntoHarm {n : ℕ} (a : (E →+* ℂ) × ℕ → ℕ) {T : Type} [AddCommGroup T] [Module c.F T]
    (io : T →ₗ[c.F] MvPolynomial (LtN Dw n) c.F) : Prop :=
  ∀ t, io t ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i))
def ClassSumTot (nab : NabV Xo c) (q₁ : ℕ) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) : Prop :=
  ∀ (ι : Type) [Fintype ι] (vol : ℚ) (S : Finset (Plc E)) (J : Subgroup (UA E n)) (h : ι → UA E n) (N : ι → ℕ)
    (ep : UA E n → ℂ) (cξ : Rul Xo c) (ph : (Fin n → ConjQ Dw l) → c.F)
    (T : Type) [AddCommGroup T] [Module c.F T] (io : T →ₗ[c.F] MvPolynomial (LtN Dw n) c.F) (x : ι → T),
    0 < vol → Admissible H q₁ l.M S J h N → (∀ i, ∃ κ, IsScalar (Dw := Dw) c ep (h i) κ) →
    cξ ∈ sec Xo c 0 0 → IntoHarm c a io →
      (∀ (R : Type) [CommRing R] [Algebra c.F R] (y : FrPt Xo c R),
        ∃! v, ClassSumValAt Xo c nab vol J h N ep cξ ph io x y v) ∧
      ∃ f ∈ sec Xo c a n, IsClassSumRule Xo c nab vol J h N ep cξ ph io x f
def ClassSumDownTot (q₁ : ℕ) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (d : DeltaDat Xo c n) : Prop :=
  ∀ (ι : Type) [Fintype ι] (vol : ℚ) (S : Finset (Plc E)) (J : Subgroup (UA E n)) (h : ι → UA E n) (N : ι → ℕ)
    (ep : UA E n → ℂ) (cξ : Rul Xo c) (ph : (Fin n → ConjQ Dw l) → c.F) (phδ : (Fin n → LaJ Xo c d) → c.F)
    (T : Type) [AddCommGroup T] [Module c.F T] (io : T →ₗ[c.F] MvPolynomial (LtN Dw n) c.F) (x : ι → T),
    0 < vol → CoverOK d phδ → Admissible H q₁ d.l₂.M S J h N → (∀ i, ∃ κ, IsScalar (Dw := Dw) c ep (h i) κ) →
    cξ ∈ sec Xo c 0 0 → IntoHarm c a io →
      (∀ (R : Type) [CommRing R] [Algebra d.c₂.F R] (y₂ : FrPt d.Xo₂ d.c₂ R),
        ∃! v, PolySumValAt d.Xo₂ d.c₂ d.nab₂ vol J h N ep d.cδ (coverDatum d ph phδ)
          (fun i => MvPolynomial.map (d.eF : c.F →+* d.c₂.F) (io (x i))) y₂ v) ∧
      ∃ f ∈ sec Xo c a n, IsClassSumRuleDown Xo c d vol J h N ep cξ ph phδ io x f
def ClassSumInCusp (nab : NabV Xo c) (cusp : ((E →+* ℂ) × ℕ → ℕ) → ℕ → Submodule c.F (Rul Xo c)) (q₁ : ℕ)
    (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) : Prop :=
  ∀ (ι : Type) [Fintype ι] (vol : ℚ) (S : Finset (Plc E)) (J : Subgroup (UA E n)) (h : ι → UA E n) (N : ι → ℕ)
    (ep : UA E n → ℂ) (cξ : Rul Xo c) (ph : (Fin n → ConjQ Dw l) → c.F)
    (T : Type) [AddCommGroup T] [Module c.F T] (io : T →ₗ[c.F] MvPolynomial (LtN Dw n) c.F) (x : ι → T)
    (σ0 : c.F →+* ℂ) (Cls : Type) [CommGroup Cls] (ξ : Cls →* c.Fˣ) (gdet : FrPt Xo c (CAt σ0) → Cls) (f : Rul Xo c),
    Dom a n → LastPos Dw a → 0 < vol → Admissible H q₁ l.M S J h N →
    (∀ z, IsOfFinOrder (ξ z)) → IsDetFactor Xo c σ0 Cls ξ gdet cξ → IntoHarm c a io →
      IsClassSumRule Xo c nab vol J h N ep cξ ph io x f → f ∈ cusp a n
def ClassSumDownInCusp (cusp : ((E →+* ℂ) × ℕ → ℕ) → ℕ → Submodule c.F (Rul Xo c)) (q₁ : ℕ)
    (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (d : DeltaDat Xo c n) : Prop :=
  ∀ (ι : Type) [Fintype ι] (vol : ℚ) (S : Finset (Plc E)) (J : Subgroup (UA E n)) (h : ι → UA E n) (N : ι → ℕ)
    (ep : UA E n → ℂ) (cξ : Rul Xo c) (ph : (Fin n → ConjQ Dw l) → c.F) (phδ : (Fin n → LaJ Xo c d) → c.F)
    (T : Type) [AddCommGroup T] [Module c.F T] (io : T →ₗ[c.F] MvPolynomial (LtN Dw n) c.F) (x : ι → T)
    (σ0 : c.F →+* ℂ) (Cls : Type) [CommGroup Cls] (ξ : Cls →* c.Fˣ) (gdet : FrPt Xo c (CAt σ0) → Cls)
    (σ₂ : d.c₂.F →+* ℂ) (Cls₂ : Type) [CommGroup Cls₂] (δ : Cls₂ →* d.c₂.Fˣ)
    (gdet₂ : FrPt d.Xo₂ d.c₂ (CAt σ₂) → Cls₂) (inv : Bool) (f : Rul Xo c),
    Dom a n → LastPos Dw a → 0 < vol → CoverOK d phδ → Admissible H q₁ d.l₂.M S J h N →
    (∀ z, IsOfFinOrder (ξ z)) → IsDetFactor Xo c σ0 Cls ξ gdet cξ →
    (∀ z, IsOfFinOrder (δ z)) → CMP Xo c d σ₂ Cls₂ δ gdet₂ inv → IntoHarm c a io →
      f ∈ sec Xo c a n → IsClassSumRuleDown Xo c d vol J h N ep cξ ph phδ io x f → f ∈ cusp a n
example {n : ℕ} : fourierSum (Dw := Dw) c (0 : (Fin n → ConjQ Dw l) → c.F) = 0 := by
  funext q
  simp [fourierSum]
end GlobalTheory.IndefiniteRowSideFullHecke.AdelicNormWeight


