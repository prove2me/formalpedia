-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_ThConst
-- name    : Development_AbelianVarietyTheory_Definitions_ThetaValues_ThConst
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T18:16:08.834071+00:00
-- url     : https://prove2.me/theorems/868bff49-e68e-4a1e-8d64-08e2482a074e
-- title:
--   Th Const
-- statement:
--   Definitions and structural lemmas for Th Const, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaValues/ThConst.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_AnChartAsm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_VtFrRdA
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThShort
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
namespace GlobalTheory.AnVal
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
def fock {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (q : ℤ) (a : Fin g → ℂ) (θ : (Fin g → ℂ) → ℂ) :
    (Fin g → ℂ) → ℂ := fun z =>
  Complex.exp (-((q : ℂ) * Real.pi * hermForm Hm z a) - (q : ℂ) * Real.pi * hermForm Hm a a / 2) * θ (z + a)
def colsOf (n g : ℕ) (v : Fin (n * g) → ℂ) : Fin n → Fin g → ℂ := fun i j => v (finProdFinEquiv (i, j))
def renN (n g m : ℕ) : Jet ℂ (Fin 1 × Fin (n * g)) m →ₐ[ℂ] Jet ℂ (Fin n × Fin g) m :=
  jetMap (fun p => MvPolynomial.X (finProdFinEquiv.symm p.2)) fun _ => X_mem_orig _
def jetN {n g : ℕ} (m : ℕ) (f : (Fin n → Fin g → ℂ) → ℂ) : Jet ℂ (Fin n × Fin g) m :=
  renN n g m (jetOf m fun v => f (colsOf n g v))
section General
variable {S : Scheme.{0}} (A : Over S) [GrpObj A] (L : RigLB A) (x0 : Sp ℂ ⟶ S) (g : ℕ)
structure AnFr where
  e : (Fin g → ℂ) → (Over.mk x0 ⟶ A)
  lat : AddSubgroup (Fin g → ℂ)
  span : Submodule.span ℝ (lat : Set (Fin g → ℂ)) = ⊤
  e_add : ∀ z w, e (z + w) = e z * e w
  e_onto : Function.Surjective e
  e_ker : ∀ z, e z = 1 ↔ z ∈ lat
  hol : IsHolFam (fun z => (e z).left)
  Hm : Matrix (Fin g) (Fin g) ℂ
  herm : Hm.IsHermitian
  χ : (Fin g → ℂ) → ℂ
  fr : L.L.ι → (Fin g → ℂ) → ℂ
  fr_hol : ∀ j, DifferentiableOn ℂ (fr j) {z | ⊤ ≤ (e z).left ⁻¹ᵁ L.L.U j}
  fr_ne : ∀ j z, ⊤ ≤ (e z).left ⁻¹ᵁ L.L.U j → fr j z ≠ 0
  fr_g : ∀ j j' z, ⊤ ≤ (e z).left ⁻¹ᵁ (L.L.U j ⊓ L.L.U j') →
    fr j z = valAt' (e z).left (L.L.U j ⊓ L.L.U j') (L.L.g j j').val * fr j' z
  fr_0 : ∀ j, ⊤ ≤ (e 0).left ⁻¹ᵁ L.L.U j →
    fr j 0 = valAt' x0 ((L.L.pull (eSec A)).U (fun _ => j)) (L.rig.s (fun _ => j)).val
  χ_norm : ∀ a ∈ lat, ‖χ a‖ = 1
  fr_per : ∀ a ∈ lat, ∀ j z, ⊤ ≤ (e z).left ⁻¹ᵁ L.L.U j →
    fr j z = χ a * Complex.exp (Real.pi * hermForm Hm z a + Real.pi / 2 * hermForm Hm a a) * fr j (z + a)
variable {A L x0 g} (Φ : AnFr A L x0 g)
def AnFr.fac (a z : Fin g → ℂ) : ℂ :=
  Φ.χ a * Complex.exp (Real.pi * hermForm Φ.Hm z a + Real.pi / 2 * hermForm Φ.Hm a a)
def AnFr.IsTh (k : ℤ) (θ : (Fin g → ℂ) → ℂ) : Prop :=
  Differentiable ℂ θ ∧ ∀ a ∈ Φ.lat, ∀ z, θ (z + a) = Φ.fac a z ^ k * θ z
def AnFr.Rd (k : ℤ) (F : LB.Sec (LPow A L.L k (Over.mk x0))) (θ : (Fin g → ℂ) → ℂ) : Prop :=
  ∀ j z (pt : Sp ℂ ⟶ (Over.mk x0 ⊗ A).left), pt ≫ (snd (Over.mk x0) A).left = (Φ.e z).left →
    pt ≫ (fst (Over.mk x0) A).left = 𝟙 (Sp ℂ) → ⊤ ≤ (Φ.e z).left ⁻¹ᵁ L.L.U j →
    valAt' pt ((LPow A L.L k (Over.mk x0)).U (fun _ => j)) (F.f (fun _ => j)) = θ z * Φ.fr j z ^ k
def AnFr.GenRd {Z : Scheme.{0}} {K : Type} [Fintype K] (φ : K → (Z ⟶ A.left)) (ε : K → ℤ)
    (t : LB.Gen (LB.LinComb L.L φ ε)) (q : Sp ℂ ⟶ Z) (p : K → Fin g → ℂ) (v : ℂ) : Prop :=
  (∀ k, q ≫ φ k = (Φ.e (p k)).left) ∧ ∀ j : K → L.L.ι, ⊤ ≤ q ⁻¹ᵁ LB.wchart L.L φ j →
    valAt' q (LB.wchart L.L φ j) (t.s j).val = v * ∏ k, Φ.fr (j k) (p k) ^ ε k
def AnFr.ThConst (k : ℤ) (U : ThetaGrp A L.L k (Over.mk x0)) (x : Fin g → ℂ) (c : ℂ) : Prop :=
  U.pt = Φ.e x ∧ ∀ z, Φ.GenRd ![(snd (Over.mk x0) A).left, (translPt A U.pt).left] ![k, -k] U.φ
    (ptSecT A (Φ.e z)).left ![z, x + z] (c * fock Φ.Hm k x (fun _ => 1) z)
def AnFr.Imm : Prop :=
  ∀ w : Fin g → ℂ, w ≠ 0 → ∃ (U : A.left.Opens) (f : Γ(A.left, U)), ⊤ ≤ (Φ.e 0).left ⁻¹ᵁ U ∧
    fderiv ℂ (fun z => valAt' (Φ.e z).left U f) 0 w ≠ 0
def AnFr.JetMap {n : ℕ} (m : ℕ) (ψ : Sp (Jet ℂ (Fin n × Fin g) m) ⟶ A.left)
    (Λ : (Fin n → Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) : Prop :=
  ∃ hol : IsHolFam (fun v : Fin (n * g) → ℂ => (Φ.e (Λ (colsOf n g v))).left),
    ψ = spMap (renN n g m : Jet ℂ (Fin 1 × Fin (n * g)) m →+* Jet ℂ (Fin n × Fin g) m) ≫ jetPt _ hol m
def AnFr.JetRd {n : ℕ} (m : ℕ) {K : Type} [Fintype K] (φ : K → (Sp (Jet ℂ (Fin n × Fin g) m) ⟶ A.left)) (ε : K → ℤ)
    (τ : LB.Gen (LB.LinComb L.L φ ε)) (Λ : K → (Fin n → Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) : Prop :=
  (∀ k, Φ.JetMap m (φ k) (Λ k)) ∧ ∀ (j : K → L.L.ι) (h : ⊤ ≤ LB.wchart L.L φ j),
    ((Sp (Jet ℂ (Fin n × Fin g) m)).presheaf.map (homOfLE h).op).hom (τ.s j).val =
      toΓ _ (jetN m fun w => ∏ k, Φ.fr (j k) (Λ k w) ^ ε k)
end General
section Pt
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} [Algebra c.F ℂ]
def tyAct {g : ℕ} (ty : Fin g → (E →+* ℂ)) (a : 𝓞 E) : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ) :=
  LinearMap.pi fun k => ty k (a : E) • LinearMap.proj k
structure AnPt (y : FrPt Xo c ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (el : Fin g ≃ Lt1 Dw)
    extends AnFr Xo.univ.t.G Xo.univ.t.PP y.x g where
  lin : ∀ (a : 𝓞 E) z, e (tyAct ty a z) = e z ≫ Xo.univ.t.act.act a
  adj : ∀ (a : 𝓞 E) z w, hermForm Hm (tyAct ty a z) w = hermForm Hm z (tyAct ty (H.bar a) w)
  der : ∀ ℓ : Lt1 Dw, IsDerivAt0 (fun z => (e z).left) (Pi.single (el.symm ℓ) 1) (y.u ℓ.1 ℓ.2)
variable {y : FrPt Xo c ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)} {el : Fin g ≃ Lt1 Dw} (Φ : AnPt y g ty el)
def AnPt.jx (m : ℕ) : jO y g m 1 ⟶ Xo.univ.t.G := anJX y.x Φ.e Φ.hol m
def psumL (n g : ℕ) (I : ULift.{0} (Finset (Fin n))) : (Fin n → Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ) :=
  ∑ i ∈ I.down, LinearMap.proj i
def AnPt.IsAnE (e : ∀ m, FrTy y g Φ.jx m) : Prop :=
  ∀ m, (e m).IsGen ∧ Φ.toAnFr.JetRd m (cφ ![jpt y g Φ.jx m (0 : Fin 2), jpt y g Φ.jx m (1 : Fin 2)]) (cε 2) (e m)
    (psumL 2 g)
def letDir (el : Fin g ≃ Lt1 Dw) {n : ℕ} (ℓ : LtN Dw n) : Fin n → Fin g → ℂ :=
  Pi.single ℓ.2.2 (Pi.single (el.symm ⟨ℓ.1, ℓ.2.1⟩) 1)
def AnPt.OfFam {σ' : KA l →+* ℂ} (F : FamilyUnif Xo σ' ty) (i : Fin F.n) (P : (F.Di i).La →+ (Fin g → ℂ)) : Prop :=
  (∀ z, (Φ.e z).left = (F.ex i P z).left) ∧ Φ.lat = P.range ∧
    ∀ a b, (hermForm Φ.Hm (P a) (P b)).im = (F.Di i).EF a b
end Pt
end GlobalTheory.AnVal


