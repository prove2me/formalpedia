-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_UnitaryDeterminantRoot
-- name    : Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_UnitaryDeterminantRoot
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:47:29.03168+00:00
-- url     : https://prove2.me/theorems/d428d188-e74c-4411-b39c-0c015b127612
-- title:
--   Unitary Determinant Root
-- statement:
--   Definitions and structural lemmas for Unitary Determinant Root, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/ExistenceTori/UnitaryDeterminantRoot.lean

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThShort
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThGerm
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IsLevMove
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_LiftLaSpec
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_NormsFree
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_ComplexResidueRing
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.IndefiniteRowSideFullHecke.UnitaryDeterminantRoot
open Formalism.L2.Pj Formalism.L2.PjFree NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.ComplexResidueRing
open scoped TensorProduct
section Adeles
variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [IsCMField E] [Algebra F E]
def IsRealIn : Prop := ∀ a : F, cc (algebraMap F E a) = algebraMap F E a
instance realIn_max : Fact (IsRealIn (maximalRealSubfield E) E) :=
  ⟨fun a => (IsCMField.complexConj E).commutes a⟩
abbrev AdE : Type := FiniteAdeleRing (𝓞 F) F ⊗[F] E
def IsIntF (a : FiniteAdeleRing (𝓞 F) F) : Prop := ∀ v, a v ∈ v.adicCompletionIntegers F
def intAdE : AddSubgroup (AdE F E) :=
  AddSubgroup.closure {z | ∃ a, IsIntF F a ∧ ∃ o : 𝓞 E, z = a ⊗ₜ (o : E)}
variable {E}
def diagE : E →+* AdE F E := Algebra.TensorProduct.includeRight.toRingHom
def vecA {r : ℕ} (v : Fin r → E) : Fin r → AdE F E := fun i => diagE F (v i)
def latHat {r : ℕ} {La : Type} [AddCommGroup La] [Module (𝓞 E) La] (ι : La →ₗ[𝓞 E] (Fin r → E)) :
    AddSubgroup (Fin r → AdE F E) :=
  AddSubgroup.closure {z | ∃ a, IsIntF F a ∧ ∃ x : La, z = fun i => a ⊗ₜ ι x i}
def IsUnitaryQ {r : ℕ} (Gm γ : Matrix (Fin r) (Fin r) E) : Prop :=
  ∀ x y, herm Gm (γ.mulVec x) (γ.mulVec y) = herm Gm x y
variable [hF : Fact (IsRealIn F E)]
def conjF : E →ₐ[F] E where
  toRingHom := (IsCMField.complexConj E).toRingEquiv.toRingHom
  commutes' := hF.out
def conjA : AdE F E →ₐ[F] AdE F E := Algebra.TensorProduct.map (AlgHom.id F _) (conjF F)
variable {F}
def IsUnitaryA {r : ℕ} (Gm : Matrix (Fin r) (Fin r) E) (g : Matrix (Fin r) (Fin r) (AdE F E)) : Prop :=
  g.transpose * Gm.map (diagE F) * g.map (conjA F) = Gm.map (diagE F)
def IsDetRootA {r : ℕ} (g : Matrix (Fin r) (Fin r) (AdE F E)) (x : (AdE F E)ˣ) : Prop :=
  (x : AdE F E) = g.det * conjA F (x : AdE F E)
def IsTwist (ξ : (AdE F E)ˣ →* Circle) (N : ℕ) : Prop :=
  (∃ m : ℕ, 0 < m ∧ ∀ x, ξ x ^ m = 1) ∧
  (∀ x : (AdE F E)ˣ, conjA F (x : AdE F E) = x → ξ x = 1) ∧
  (∀ (x : (AdE F E)ˣ) (z : E), (x : AdE F E) = diagE F z → ξ x = 1) ∧
  ∀ x : (AdE F E)ˣ, (x : AdE F E) ∈ intAdE F E → ((x⁻¹ : (AdE F E)ˣ) : AdE F E) ∈ intAdE F E →
    (∃ y ∈ intAdE F E, (x : AdE F E) - 1 = N • y) → ξ x = 1
example {r : ℕ} (Gm : Matrix (Fin r) (Fin r) E) (N : ℕ) :
    IsUnitaryA Gm (1 : Matrix (Fin r) (Fin r) (AdE F E)) ∧ IsDetRootA (1 : Matrix (Fin r) (Fin r) (AdE F E)) 1 ∧
      IsTwist (1 : (AdE F E)ˣ →* Circle) N := by
  refine ⟨?_, ?_, ⟨1, one_pos, fun _ => by simp⟩, fun _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ _ => rfl⟩
  · simp [IsUnitaryA]
  · simp [IsDetRootA]
end Adeles
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [IsCMField E] [Algebra F E]
variable {H : Host E} {Dw : Datum H} {r : ℕ}
section Clauses
variable {La' : Type} [AddCommGroup La'] [Module (𝓞 E) La']
def IsomEmb (Gm : Matrix (Fin r) (Fin r) E) (ξ0 : E) (Di : Datum H) (φ : Di.La →ₗ[𝓞 E] (Fin r → E)) : Prop :=
  Function.Injective φ ∧ ∀ a b, ((Di.EF a b : ℤ) : ℚ) = Algebra.trace ℚ E (-ξ0 * herm Gm (φ a) (φ b))
def LatAt (ι : Dw.La →ₗ[𝓞 E] (Fin r → E)) (φ : La' →ₗ[𝓞 E] (Fin r → E)) (g : Matrix (Fin r) (Fin r) (AdE F E)) : Prop :=
  ∀ v : Fin r → E, (∃ b, φ b = v) ↔ ∃ z ∈ latHat F ι, vecA F v = g.mulVec z
def MarkAt (l : Level H) (ι : Dw.La →ₗ[𝓞 E] (Fin r → E)) (φ : La' →ₗ[𝓞 E] (Fin r → E)) (t : Dw.La →ₗ[𝓞 E] La')
    (g : Matrix (Fin r) (Fin r) (AdE F E)) : Prop :=
  ∀ a ∈ Mfr l • (⊤ : Submodule (𝓞 E) Dw.La), ∃ z ∈ latHat F ι,
    vecA F (φ (t a)) - g.mulVec (vecA F (ι a)) = l.M • g.mulVec z
def AtClass (l : Level H) (Gm : Matrix (Fin r) (Fin r) E) (ι : Dw.La →ₗ[𝓞 E] (Fin r → E)) (φ : La' →ₗ[𝓞 E] (Fin r → E))
    (t : Dw.La →ₗ[𝓞 E] La') (h : Matrix (Fin r) (Fin r) (AdE F E)) : Prop :=
  ∃ γ : Matrix (Fin r) (Fin r) E, IsUnitaryQ Gm γ ∧
    LatAt ι φ (γ.map (diagE F) * h) ∧ MarkAt l ι φ t (γ.map (diagE F) * h)
example (l : Level H) (ι : Dw.La →ₗ[𝓞 E] (Fin r → E)) :
    MarkAt l ι ι LinearMap.id (1 : Matrix (Fin r) (Fin r) (AdE F E)) :=
  fun a _ => ⟨0, zero_mem _, by simp⟩
end Clauses
section Value
variable [Fact (IsRealIn F E)] {l : Level H} (Xo : Moduli Dw l) (c : Coeff l)
def sig0 : c.F →+* ℂ := c.F.val.toRingHom
variable {Xo c}
def XiValAt (Gm : Matrix (Fin r) (Fin r) E) (ι : Dw.La →ₗ[𝓞 E] (Fin r → E)) (ξ : (AdE F E)ˣ →* Circle)
    (σ : c.F →+* ℂ) {g : ℕ} {ty : Fin g → (E →+* ℂ)}
    (Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty)
    (φ : ∀ i, (Fu.Di i).La →ₗ[𝓞 E] (Fin r → E)) (f : Rul Xo c) : Prop :=
  ∀ (i : Fin Fu.n) (h : Matrix (Fin r) (Fin r) (AdE F E)) (x : (AdE F E)ˣ),
    IsUnitaryA Gm h → AtClass l Gm ι (φ i) (Fu.t i) h → IsDetRootA h x →
    ∀ P : (Fu.Di i).La →+ (Fin g → ℂ), IsPeriod (Fu.Di i) ty P →
      ∀ y : FrPt Xo c (CAt σ), y.x = Fu.u i P → toC (evR Xo c f y) = ((ξ x : Circle) : ℂ)
def AllMarked (F : Type) [Field F] [NumberField F] [Algebra F E] [Fact (IsRealIn F E)]
    (Gm : Matrix (Fin r) (Fin r) E) (ξ0 : E) (ι : Dw.La →ₗ[𝓞 E] (Fin r → E))
    {σ : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)} (Fu : FamilyUnif Xo σ ty)
    (φ : ∀ i, (Fu.Di i).La →ₗ[𝓞 E] (Fin r → E)) : Prop :=
  ∀ i, IsomEmb Gm ξ0 (Fu.Di i) (φ i) ∧ ∃ (h : Matrix (Fin r) (Fin r) (AdE F E)) (x : (AdE F E)ˣ),
    IsUnitaryA Gm h ∧ AtClass l Gm ι (φ i) (Fu.t i) h ∧ IsDetRootA h x
def AllClasses (F : Type) [Field F] [NumberField F] [Algebra F E] [Fact (IsRealIn F E)]
    (Gm : Matrix (Fin r) (Fin r) E) (ι : Dw.La →ₗ[𝓞 E] (Fin r → E))
    {σ : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)} (Fu : FamilyUnif Xo σ ty)
    (φ : ∀ i, (Fu.Di i).La →ₗ[𝓞 E] (Fin r → E)) : Prop :=
  ∀ h : Matrix (Fin r) (Fin r) (AdE F E), IsUnitaryA Gm h → ∃ i, AtClass l Gm ι (φ i) (Fu.t i) h
variable (Xo c)
def XiVal (Gm : Matrix (Fin r) (Fin r) E) (ξ0 : E) (ι : Dw.La →ₗ[𝓞 E] (Fin r → E)) (ξ : (AdE F E)ˣ →* Circle)
    (σ : c.F →+* ℂ) (f : Rul Xo c) : Prop :=
  r = Dw.p + Dw.q ∧ ∃ (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ))
    (Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1))
    (φ : ∀ i, (Fu.Di i).La →ₗ[𝓞 E] (Fin r → E)),
    AllMarked F Gm ξ0 ι Fu φ ∧ XiValAt Gm ι ξ σ Fu φ f
def IsXiDet (Gm : Matrix (Fin r) (Fin r) E) (ξ0 : E) (ι : Dw.La →ₗ[𝓞 E] (Fin r → E)) (ξ : (AdE F E)ˣ →* Circle)
    (f : Rul Xo c) : Prop :=
  f ∈ sec Xo c 0 0 ∧ XiVal Xo c Gm ξ0 ι ξ (sig0 c) f
def XiExists (Gm : Matrix (Fin r) (Fin r) E) (ξ0 : E) (ι : Dw.La →ₗ[𝓞 E] (Fin r → E)) (ξ : (AdE F E)ˣ →* Circle) : Prop :=
  1 ≤ r → r = Dw.p + Dw.q → IsomEmb Gm ξ0 Dw ι → IsTwist ξ l.M → (∀ x, ((ξ x : Circle) : ℂ) ∈ c.F) →
    ∃ f, IsXiDet Xo c Gm ξ0 ι ξ f
def XiUnique (Gm : Matrix (Fin r) (Fin r) E) (ξ0 : E) (ι : Dw.La →ₗ[𝓞 E] (Fin r → E)) (ξ : (AdE F E)ˣ →* Circle) : Prop :=
  ∀ f f', IsXiDet Xo c Gm ξ0 ι ξ f → IsXiDet Xo c Gm ξ0 ι ξ f' → f = f'
def XiRootsOfUnity (Gm : Matrix (Fin r) (Fin r) E) (ξ0 : E) (ι : Dw.La →ₗ[𝓞 E] (Fin r → E))
    (ξ : (AdE F E)ˣ →* Circle) : Prop :=
  ∀ (m : ℕ) (f : Rul Xo c), (∀ x, ξ x ^ m = 1) → IsXiDet Xo c Gm ξ0 ι ξ f → f ^ m = 1
def XiLevelLaw (Gm : Matrix (Fin r) (Fin r) E) (ξ0 : E) (ι : Dw.La →ₗ[𝓞 E] (Fin r → E))
    (ξ : (AdE F E)ˣ →* Circle) : Prop :=
  ∀ f, IsXiDet Xo c Gm ξ0 ι ξ f → ∀ (k : Matrix (Fin r) (Fin r) (AdE F E)) (x : (AdE F E)ˣ) (gM gA : Dw.La →ₗ[𝓞 E] Dw.La),
    IsUnitaryA Gm k → (∀ z, z ∈ latHat F ι ↔ k.mulVec z ∈ latHat F ι) → MarkAt l ι ι gM k → IsDetRootA k x →
    ∀ y y' : FrPt Xo c (CAt (sig0 c)), levR (gM, gA) y y' →
      toC (evR Xo c f y') = ((ξ x : Circle) : ℂ) * toC (evR Xo c f y)
end Value
section Action
variable {l : Level H} (Xo : Moduli Dw l) (c : Coeff l) {G : Type} [Group G]
  (lev : G → (Dw.La →ₗ[𝓞 E] Dw.La) × (Dw.La →ₗ[𝓞 E] Dw.La))
def levAct (g : G) : Rul Xo c →ₗ[c.F] Rul Xo c :=
  actL (K := c.F) (fun S _ _ => FrPt Xo c S) (fun g y y' => levActR (Xo := Xo) (c := c) lev g y y') g
def LevActLaws : Prop :=
  ActLaws (K := c.F) (G := G) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z)
    (fun t y y' => FrBor t y y') (fun g y y' => levActR (Xo := Xo) (c := c) lev g y y')
def levAll (l : Level H) (γ : LaMod Dw l ≃ₗ[𝓞 E] LaMod Dw l) : (Dw.La →ₗ[𝓞 E] Dw.La) × (Dw.La →ₗ[𝓞 E] Dw.La) :=
  (liftLa γ, LinearMap.id)
def LevKeepsCusp (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) : Prop :=
  ∀ g, ∀ f ∈ cusp Xo c U a n, levAct Xo c lev g f ∈ cusp Xo c U a n
variable {c} {c' : Coeff l}
def LevActExtends (h : c.F ≤ c'.F) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) : Prop :=
  ∀ g, ∀ f ∈ sec Xo c a n, levAct Xo c' lev g (ruleUp h f) = ruleUp h (levAct Xo c lev g f)
end Action
section Row
variable {l : Level H} (Xo : Moduli Dw l) {c c' : Coeff l} {n : ℕ}
def unfoldingOfFieldLe (h : c.F ≤ c'.F) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) : Unf Xo c' (sig0 c') r :=
  unfUp h (sig0 c') (U (sig0 c))
def IsClassSum {Cl : Type} [Fintype Cl] {Vs : Type} [AddCommGroup Vs] [Module c'.F Vs] (d : DeltaDat Xo c' n)
    (w : Cl → (Fin n → LevQ Dw d.l₂) → c'.F) (La : Cl → GenLat E n) (Nc gam : Cl → ℕ) (vol : c'.F) (ep : Cl → c'.F)
    (io : Vs →ₗ[c'.F] MvPolynomial (LtN Dw n) c'.F) (x : Cl → Vs) (f : Rul Xo c') : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra c'.F k] [Algebra d.c₂.F k],
    (∀ a : c'.F, algebraMap d.c₂.F k (d.eF a) = algebraMap c'.F k a) →
    ∀ (y : FrPt Xo c' k) (y₂ : FrPt d.Xo₂ d.c₂ k), FrOver d y₂ y →
      ∃ v : Cl → k, (∀ cl, ShortValAt d.Xo₂ d.c₂ d.nab₂ (fun q => d.eF (w cl q)) (La cl) 1 (Nc cl)
          (MvPolynomial.map (d.eF : c'.F →+* d.c₂.F) (io (x cl))) y₂ (v cl)) ∧
        evR Xo c' f y = evR d.Xo₂ d.c₂ d.cδ y₂ * ∑ cl, algebraMap c'.F k (vol * ((gam cl : c'.F))⁻¹ * ep cl) * v cl
variable {Pt : Type} {G : Type} [Group G] {Tup : Type*} {Vs : Type} [AddCommGroup Vs] [Module c'.F Vs]
def RowUp (h : c.F ≤ c'.F) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r)
    (dict : Pt → Σ k, Frame ((U (sig0 c)).X k).Ψ r) (mu : Pt → ℂ) (xr : ℝ) (a : (E →+* ℂ) × ℕ → ℕ)
    (lev : G → (Dw.La →ₗ[𝓞 E] Dw.La) × (Dw.La →ₗ[𝓞 E] Dw.La)) (d : Tup → DeltaDat Xo c' n)
    (Cl : Tup → Type) [∀ t, Fintype (Cl t)] (w : ∀ t, Cl t → (Fin n → LevQ Dw (d t).l₂) → c'.F)
    (La : ∀ t, Cl t → GenLat E n) (Nc gam : ∀ t, Cl t → ℕ) (vol : Tup → c'.F) (ep : ∀ t, Cl t → c'.F)
    (io : Vs →ₗ[c'.F] MvPolynomial (LtN Dw n) c'.F) (thAd : ∀ t, (Cl t → Vs) → Pt → ℂ) (Pl : ∀ t, (Cl t → Vs) → Prop)
    (LL : IntermediateField ℚ ℂ) (cst : (U (sig0 c)).Comp → ℂ) (ph : ℂ) : Prop :=
  (∀ k, ‖cst k‖ = 1) ∧ ‖ph‖ = 1 ∧ ∃ z : G, z ∈ Subgroup.center G ∧
    ∀ t : Tup, ∃ ze : ℂ, ze ∈ LL ∧ (∃ m : ℕ, 0 < m ∧ ze ^ m = 1) ∧ ∀ x : Cl t → Vs, Pl t x →
      (∃ f ∈ cusp Xo c' (unfFamUp h U) a n, IsClassSum Xo (d t) (w t) (La t) (Nc t) (gam t) (vol t) (ep t) io x f) ∧
      ∀ f ∈ sec Xo c' a n, IsClassSum Xo (d t) (w t) (La t) (Nc t) (gam t) (vol t) (ep t) io x f →
        ∀ q : Pt, ph * thAd t x q = ze * cst (dict q).1 * (lieFac Dw xr a : ℂ) *
          (mu q * rdU (unfoldingOfFieldLe Xo h U) (levAct Xo c' lev z f) (dict q).1 (dict q).2)
def TieUp [Fact (IsRealIn F E)] (h : c.F ≤ c'.F) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r)
    (dict : Pt → Σ k, Frame ((U (sig0 c)).X k).Ψ r) (mu : Pt → ℂ) (xr : ℝ) (a : (E →+* ℂ) × ℕ → ℕ)
    (lev : G → (Dw.La →ₗ[𝓞 E] Dw.La) × (Dw.La →ₗ[𝓞 E] Dw.La)) (d : Tup → DeltaDat Xo c' n)
    (Cl : Tup → Type) [∀ t, Fintype (Cl t)] (w : ∀ t, Cl t → (Fin n → LevQ Dw (d t).l₂) → c'.F)
    (La : ∀ t, Cl t → GenLat E n) (Nc gam : ∀ t, Cl t → ℕ) (vol : Tup → c'.F) (ep : ∀ t, Cl t → c'.F)
    (io : Vs →ₗ[c'.F] MvPolynomial (LtN Dw n) c'.F) (thAd : ∀ t, (Cl t → Vs) → Pt → ℂ) (Pl : ∀ t, (Cl t → Vs) → Prop)
    (LL : IntermediateField ℚ ℂ) (cst : (U (sig0 c)).Comp → ℂ) (ph : ℂ)
    (ι : Dw.La →ₗ[𝓞 E] (Fin r → E)) (ξ : Tup → (AdE F E)ˣ →* Circle) : Prop :=
  LL ≤ c'.F ∧ LevActLaws Xo c lev ∧ LevActLaws Xo c' lev ∧ LevActExtends Xo lev h a n ∧ CuspBaseChange Xo h U a n ∧
    (∀ t, (d t).IsLev ∧ (d t).l₂.A = 1 ∧ (∃ _ : StarRing (𝓞 E), IsNab (d t).Xo₂ (d t).c₂ (d t).nab₂) ∧
      ∀ k : (U (sig0 c)).Comp, IsXiDet (d t).Xo₂ (d t).c₂ ((U (sig0 c)).X k).Gm ((U (sig0 c)).X k).ξ0 ι (ξ t) (d t).cδ) ∧
    Nonempty (U (sig0 c)).Comp ∧ (∀ k, IsomEmb ((U (sig0 c)).X k).Gm ((U (sig0 c)).X k).ξ0 Dw ι) ∧
    RowUp Xo h U dict mu xr a lev d Cl w La Nc gam vol ep io thAd Pl LL cst ph
end Row
end GlobalTheory.IndefiniteRowSideFullHecke.UnitaryDeterminantRoot


