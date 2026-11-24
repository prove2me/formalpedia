-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_OrthogonalFrameIff
-- name    : Development_AbelianVarietyTheory_Proofs_UnitaryExistence_OrthogonalFrameIff
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-24T14:02:07.032817+00:00
-- url     : https://prove2.me/theorems/bd3efccd-cfce-48cf-936f-399fd041b537
-- title:
--   Orthogonal Frame Iff
-- statement:
--   Definitions and structural lemmas for Orthogonal Frame Iff, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/OrthogonalFrameIff.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_LatticeEmbeddingHalf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdelicCompletionRationalPointsAndApproximation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsLatticeRationalVectorsInAdelicTranslate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_CramerMemAdelicCompletionOfElementSet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_InfAdeleTensorBijective
import Theorems.Thm_GlobalTheory_Idele_adelicMulEquiv_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Idele.adelicMulEquiv_mk


set_option autoImplicit false
noncomputable section
namespace GlobalTheory.DictPinCompare
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicLatticeBase (Fin𝔸 Inf𝔸 toFin latAd latBase CongrAt half IsLatEmb crd vec IsModelOf IsOrthoFrame IsArchAt
  IsRatUnitary ratTo LatMark IsMarkStab IsLevelStab IsDictOf IsFamilyOf unitaryOver AdelicU AdPinU)
open scoped TensorProduct nonZeroDivisors Matrix
abbrev conjHom (E : Type) [Field E] [NumberField E] [IsCMField E] : E →+* E :=
  (IsCMField.complexConj E).toRingEquiv.toRingHom
section First
variable (F : Type) [Field F] [NumberField F] {E : Type} [Field E] [NumberField E] [IsCMField E] [Algebra F E]
  {W : Type} [AddCommGroup W] [Module E W] [Module (𝓞 E) W] [IsScalarTower (𝓞 E) E W] {n r : ℕ}
  (fr : Module.Basis (Fin n) E W) (hT : W →ₛₗ[conjHom E] W →ₗ[E] E) (L0 : Submodule (𝓞 E) W)
  (AA : FractionalIdeal (𝓞 E)⁰ E) (xi0 : E) {G : Type} [Group G]
  (infHom : G →* GL (Fin n) (Inf𝔸 F ⊗[F] E)) (finHom : G →* GL (Fin n) (Fin𝔸 F ⊗[F] E)) (GQ GfC : Subgroup G)
def gramOf : Matrix (Fin n) (Fin n) E := Matrix.of fun a b => hT (fr a) (fr b)
def latHat : AddSubgroup (Fin n → Fin𝔸 F ⊗[F] E) :=
  AddSubgroup.closure {z | ∃ a : Fin𝔸 F, (∀ v, a v ∈ v.adicCompletionIntegers F) ∧
    ∃ x ∈ L0, z = fun i => a ⊗ₜ fr.repr x i}
def archM (th' : Inf𝔸 F ⊗[F] E →+* ℂ) (h : G) : Matrix (Fin n) (Fin n) ℂ := (infHom h).1.map th'
def finVec (v : Fin n → E) : Fin n → Fin𝔸 F ⊗[F] E := fun i => (1 : Fin𝔸 F) ⊗ₜ v i
def gLat (g : G) : Set (Fin n → Fin𝔸 F ⊗[F] E) :=
  (finHom g).1.mulVec '' (latHat F fr L0 : Set (Fin n → Fin𝔸 F ⊗[F] E))
def latG (g : G) : Submodule (𝓞 E) (Fin n → E) :=
  Submodule.span (𝓞 E) {w | ∃ a : E, a ∈ AA ∧ ∃ v, finVec F v ∈ gLat F fr L0 finHom g ∧ w = a • v}
def latGHat (g : G) : AddSubgroup (Fin n → Fin𝔸 F ⊗[F] E) :=
  AddSubgroup.closure {w | ∃ a : E, a ∈ AA ∧ ∃ z ∈ gLat F fr L0 finHom g,
    w = fun i => ((1 : Fin𝔸 F) ⊗ₜ a) * z i}
def LatEmb {La : Type} [AddCommGroup La] [Module (𝓞 E) La] (ι : La →ₗ[𝓞 E] (Fin n → E)) : Prop :=
  Function.Injective ι ∧ LinearMap.range ι = latG F fr L0 AA finHom 1
def LatIsom {La : Type} [AddCommGroup La] [Module (𝓞 E) La] (EF : LinearMap.BilinForm ℤ La)
    (ι : La →ₗ[𝓞 E] (Fin n → E)) : Prop :=
  ∃ ε : ℤˣ, ∀ x y, ((EF x y : ℤ) : ℚ) = ((ε : ℤ) : ℚ) *
    Algebra.trace ℚ E (xi0 * hT (fr.equivFun.symm (ι x)) (fr.equivFun.symm (ι y)))
def ModelW (hr : n = r) (X : Data E r) : Prop :=
  X.Gm = -(Matrix.reindex (finCongr hr) (finCongr hr) (gramOf fr hT)).transpose ∧ X.ξ0 = -xi0
def IsOrthogonalFrame (X : Data E r) (x₀ : (E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) : Prop :=
  ∀ τ ∈ X.Ψ, gram τ X.Gm (x₀ τ) = Matrix.diagonal fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ)
def halfVec (b : 𝓞 E) (z : Fin n → Fin𝔸 F ⊗[F] E) : Fin n → Fin𝔸 F ⊗[F] E :=
  fun i => ((1 : Fin𝔸 F) ⊗ₜ (b : E)) * z i
def KfHalf (Kf : Subgroup G) (M : ℕ) (Mh : Ideal (𝓞 E)) : Prop :=
  ∀ k, k ∈ Kf ↔ k ∈ GfC ∧ ∀ b ∈ Mh, ∀ z ∈ latHat F fr L0, ∃ y ∈ latHat F fr L0,
    (finHom k).1.mulVec (halfVec F b z) - halfVec F b z = M • y
variable {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
  {σ : c.F →+* ℂ}
open Classical in

def DictLat (U : Unf Xo c σ r) (hr : n = r) (dict : G → Σ k, Frame (U.X k).Ψ r)
    (ι : Dw.La →ₗ[𝓞 E] (Fin n → E)) {g : ℕ} (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ))
    (Fm : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1))
    (ik : U.Comp → Fin Fm.n) (φ : ∀ k, (Fm.Di (ik k)).La ≃ₗ[𝓞 E] (U.X k).Λ)
    (th : ∀ k, (U.X k).Ψ → (Inf𝔸 F ⊗[F] E →+* ℂ))
    (x₀ : (E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) : Prop :=
  ((∀ k a b, (((Fm.Di (ik k)).EF a b : ℤ) : ℚ) = Algebra.trace ℚ E
        (-(U.X k).ξ0 * herm (U.X k).Gm (φ k a : Fin r → E) (φ k b))) ∧
    ∀ k (x : (U.X k).dom), ∃ Pm : (Fm.Di (ik k)).La →+ (Fin g → ℂ),
      (∀ a j, Pm a j = perFr (U.X k) x.1 (φ k a : Fin r → E) (relab c σ (e j).1) (e j).2) ∧
      IsPeriod (Fm.Di (ik k)) (fun j => relab c σ (e j).1) Pm ∧ (U.un k x).x = Fm.u (ik k) Pm ∧
      ∀ τ (i : Fin (Dw.mult τ)), IsDerivAt0 (fun z => (Fm.ex (ik k) Pm z).left) (Pi.single (e.symm ⟨τ, i⟩) 1)
        ((U.un k x).u τ i)) ∧
    ∀ h : G, ∃ γ ∈ GQ,
      ((U.X (dict h).1).Λ : Set (Fin r → E)) =
        (fun v : Fin n → E => v ∘ Fin.cast hr.symm) '' (latG F fr L0 AA finHom (γ * h) : Set _) ∧
      (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) Dw.La),
        ∃ w ∈ latGHat F fr L0 AA finHom (γ * h),
        finVec F ((φ (dict h).1 (Fm.t (ik (dict h).1) a) : Fin r → E) ∘ Fin.cast hr) -
          (finHom (γ * h)).1.mulVec (finVec F (ι a)) = (l.M : ℕ) • w) ∧
      ∀ τ : (U.X (dict h).1).Ψ, mat (dict h).2 τ =
        Matrix.reindex (finCongr hr) (finCongr hr) (archM F infHom (th (dict h).1 τ) (γ * h)) * x₀ τ.1
def AdPinWith (U : Unf Xo c σ r) (dict : G → Σ k, Frame (U.X k).Ψ r)
    (x₀ : (E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) (ι₀ : Dw.La →ₗ[𝓞 E] (Fin r → E))
    (Q : ∀ k, (Dw.La → (U.X k).Λ) → Prop) : Prop :=
  ∃ (hr : n = r)
    (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ))
    (Fm : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun i => relab c σ (e i).1))
    (ik : U.Comp → Fin Fm.n) (φ : ∀ k, (Fm.Di (ik k)).La ≃ₗ[𝓞 E] (U.X k).Λ)
    (th : ∀ k, (U.X k).Ψ → (Inf𝔸 F ⊗[F] E →+* ℂ)),
    let ι := LinearMap.funLeft (𝓞 E) E (Fin.cast hr) ∘ₗ ι₀
    (LatEmb F fr L0 AA finHom ι ∧ LatIsom fr hT xi0 Dw.EF ι ∧ (∀ k τ, IsArchAt F τ.1 (th k τ)) ∧
      DictLat F fr L0 AA infHom finHom GQ U hr dict ι e Fm ik φ th x₀) ∧
    ∀ k, Q k fun a => φ k (Fm.t (ik k) a)
def AdPin (U : Unf Xo c σ r) (dict : G → Σ k, Frame (U.X k).Ψ r)
    (x₀ : (E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) (ι₀ : Dw.La →ₗ[𝓞 E] (Fin r → E)) : Prop :=
  ∃ (hr : n = r)
    (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ))
    (Fm : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun i => relab c σ (e i).1))
    (ik : U.Comp → Fin Fm.n) (φ : ∀ k, (Fm.Di (ik k)).La ≃ₗ[𝓞 E] (U.X k).Λ)
    (th : ∀ k, (U.X k).Ψ → (Inf𝔸 F ⊗[F] E →+* ℂ)),
    let ι := LinearMap.funLeft (𝓞 E) E (Fin.cast hr) ∘ₗ ι₀
    LatEmb F fr L0 AA finHom ι ∧ LatIsom fr hT xi0 Dw.EF ι ∧ (∀ k τ, IsArchAt F τ.1 (th k τ)) ∧
      DictLat F fr L0 AA infHom finHom GQ U hr dict ι e Fm ik φ th x₀
def TypeClause (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (q : ℕ) (X : Data E r) : Prop :=
  X.p0 = q ∧ ∀ τ : E →+* ℂ, τ ∈ X.Ψ ↔ τ (H.rt : E) = H.rt0
def flipForm (x y : W) : E := hT y x
def IsRatPoints : Prop :=
  (∀ γ ∈ GQ, ∃ γ₀, IsRatUnitary fr (flipForm hT) γ₀ ∧ finHom γ = ratTo F (Fin𝔸 F) γ₀ ∧ infHom γ = ratTo F (Inf𝔸 F) γ₀) ∧
    ∀ γ₀, IsRatUnitary fr (flipForm hT) γ₀ →
      ∃ γ ∈ GQ, finHom γ = ratTo F (Fin𝔸 F) γ₀ ∧ infHom γ = ratTo F (Inf𝔸 F) γ₀
end First
section Compare
variable {F : Type} [Field F] [NumberField F] {E : Type} [Field E] [NumberField E] [IsCMField E] [Algebra F E]
  {W : Type} [AddCommGroup W] [Module E W] [Module (𝓞 E) W] [IsScalarTower (𝓞 E) E W] {n r : ℕ}
  (fr : Module.Basis (Fin n) E W) (hT : W →ₛₗ[conjHom E] W →ₗ[E] E) (L0 : Submodule (𝓞 E) W)
  (AA : FractionalIdeal (𝓞 E)⁰ E) (xi0 : E) {G : Type} [Group G]
  (infHom : G →* GL (Fin n) (Inf𝔸 F ⊗[F] E)) (finHom : G →* GL (Fin n) (Fin𝔸 F ⊗[F] E)) (GQ GfC : Subgroup G)
def coord : W ≃ₗ[𝓞 E] (Fin n → E) := fr.equivFun.restrictScalars (𝓞 E)
def fixMod {R : Type} [CommRing R] (k : Matrix (Fin n) (Fin n) R) (M : ℕ) (P : AddSubgroup (Fin n → R)) :
    AddSubgroup (Fin n → R) where
  carrier := {v | ∃ y ∈ P, k *ᵥ v - v = M • y}
  zero_mem' := ⟨0, zero_mem _, by simp⟩
  add_mem' := by
    rintro v w ⟨y, hy, h⟩ ⟨y', hy', h'⟩
    exact ⟨y + y', add_mem hy hy', by rw [Matrix.mulVec_add, smul_add, ← h, ← h']; abel⟩
  neg_mem' := by
    rintro v ⟨y, hy, h⟩
    exact ⟨-y, neg_mem hy, by rw [Matrix.mulVec_neg, smul_neg, ← h]; abel⟩
abbrev ad (F : Type) [Field F] [NumberField F] {E : Type} [Field E] [Algebra F E] (a : E) : Fin𝔸 F ⊗[F] E := 1 ⊗ₜ a
def FixesHalf (k : Matrix (Fin n) (Fin n) (Fin𝔸 F ⊗[F] E)) (M : ℕ) (Mh : Ideal (𝓞 E)) : Prop :=
  ∀ b ∈ Mh, ∀ z ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicLatticeBase.latHat F fr L0,
    ad F (algebraMap (𝓞 E) E b) • z ∈ fixMod k M (GlobalTheory.IndefiniteRowSideFullHecke.AdelicLatticeBase.latHat F fr L0)
variable {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
  {σ : c.F →+* ℂ}
def embW (hr : n = r) (ι₀ : Dw.La →ₗ[𝓞 E] (Fin r → E)) : Dw.La →ₗ[𝓞 E] W :=
  (coord fr).symm.toLinearMap ∘ₗ LinearMap.funLeft (𝓞 E) E (Fin.cast hr) ∘ₗ ι₀
def SidePins (U : Unf Xo c σ r) (hr : n = r) (Kf : Subgroup G) (x₀ : (E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) : Prop :=
  (∀ k, ModelW fr hT xi0 hr (U.X k)) ∧ (∀ k, IsOrthogonalFrame (U.X k) x₀) ∧
    KfHalf F fr L0 finHom GfC Kf l.M (l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)) ∧ ∀ k, TypeClause H Dw.q (U.X k)
section Joint
variable [IsTotallyReal F] (cj : E ≃ₐ[F] E) (hfg : L0.FG) (hsp : Submodule.span E (L0 : Set W) = ⊤) (hA : AA ≠ 0)
  (hherm : ∀ x y, cc (hT x y) = hT y x) (hnd : (gramOf fr hT).det ≠ 0) (hxi : cc xi0 = -xi0)
  (hsgn : ∀ τ : E →+* ℂ, τ (H.rt : E) = H.rt0 → 0 < (τ xi0).im)
  (hU : ∀ g, finHom g ∈ unitaryOver F cj fr (flipForm hT) (Fin𝔸 F)) (hGf : ∀ k, k ∈ GfC ↔ infHom k = 1)
  (hQ : IsRatPoints F fr hT infHom finHom GQ)
  (U : Unf Xo c σ r) (hr : n = r) (dict : G → Σ k, Frame (U.X k).Ψ r) (Kf : Subgroup G)
include hfg hsp hA hherm hnd hxi hsgn hU hGf hQ
end Joint
def withGroup (X : Data E r) (Γ : Subgroup (GL (Fin r) E)) (hle : Γ ≤ X.Γ)
    (hidx : ∃ S : Finset (GL (Fin r) E), ∀ γ, IsUStab X.Gm X.Λ γ → ∃ s ∈ S, s⁻¹ * γ ∈ Γ) (m : ℕ) (hm : 0 < m)
    (htr : ∀ ξ ∈ X.Λ, herm X.Gm ξ ξ = 0 → ∀ s : E, cc s = s → IsIntegral ℤ s →
      ∃ γ ∈ Γ, (γ : Matrix (Fin r) (Fin r) E) = transvMat X.Gm ξ ((m : E) * s * X.κ0)) : Data E r :=
  { X with
    Γ := Γ
    Γ_stab := fun γ h => X.Γ_stab γ (hle h)
    Γ_index := hidx
    Γ_free := fun γ h => X.Γ_free γ (hle h)
    χ_mul := fun la γ h γ' h' => X.χ_mul la γ (hle h) γ' (hle h')
    χ_add := fun la la' γ h => X.χ_add la la' γ (hle h)
    χ_fin := fun la => (X.χ_fin la).imp fun _ h => ⟨h.1, fun γ hγ => h.2 γ (hle hγ)⟩
    m := m
    m_pos := hm
    transv := htr }
section Adelic
variable (cj : E ≃ₐ[F] E)
def infU (h : W → W → E) : AdelicU F cj fr h →* GL (Fin n) (Inf𝔸 F ⊗[F] E) :=
  (Subgroup.subtype _).comp (MonoidHom.fst _ _)
def finU (h : W → W → E) : AdelicU F cj fr h →* GL (Fin n) (Fin𝔸 F ⊗[F] E) :=
  (Subgroup.subtype _).comp (MonoidHom.snd _ _)
def ratU (h : W → W → E) : Subgroup (AdelicU F cj fr h) :=
  (MonoidHom.range ((Matrix.GeneralLinearGroup.map
      (Algebra.TensorProduct.includeRight : E →ₐ[F] Inf𝔸 F ⊗[F] E).toRingHom).prod (Matrix.GeneralLinearGroup.map
      (Algebra.TensorProduct.includeRight : E →ₐ[F] Fin𝔸 F ⊗[F] E).toRingHom))).comap
    ((infU fr cj h).prod (finU fr cj h))
end Adelic
end Compare
end GlobalTheory.DictPinCompare


