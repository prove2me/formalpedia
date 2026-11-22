-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:41:03.390284+00:00
-- url     : https://prove2.me/theorems/e01efb50-97f1-4e98-b590-5f8adbb49b0f
-- title:
--   Is Hol Periods
-- statement:
--   Definitions and structural lemmas for Is Hol Periods, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/BirationalGeometry/ToroidalCompactification/IsHolPeriods.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Clauses
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
def IsTypeFn (H : Host E) (p q : ℕ) {g : ℕ} (ty : Fin g → (E →+* ℂ)) : Prop :=
  ∀ τ : E →+* ℂ, (τ (H.rt : E) = H.rt0 → Nat.card {i // ty i = τ} = p) ∧ (τ (H.rt : E) ≠ H.rt0 → Nat.card {i // ty i = τ} = q)
def IsPeriod (D : Datum H) {g : ℕ} (ty : Fin g → (E →+* ℂ)) (P : D.La →+ (Fin g → ℂ)) : Prop :=
  (∀ (a : 𝓞 E) x i, P (a • x) i = ty i (a : E) * P x i) ∧ Function.Injective P ∧ DiscreteTopology P.range ∧
    Submodule.span ℝ (Set.range P) = ⊤ ∧
    ∃ Hm : Matrix (Fin g) (Fin g) ℂ, Hm.IsHermitian ∧ (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) ∧
      ∀ x y, (hermForm Hm (P x) (P y)).im = D.EF x y
def IsHolTo {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {X : Scheme.{0}} (B : Set V) (y : V → (Sp ℂ ⟶ X)) : Prop :=
  ∀ (U : X.Opens) (f : Γ(X, U)), IsOpen {b ∈ B | ⊤ ≤ y b ⁻¹ᵁ U} ∧
    DifferentiableOn ℂ (fun b => valAt' (y b) U f) {b ∈ B | ⊤ ≤ y b ⁻¹ᵁ U}
def IsHolPeriods (D : Datum H) {g m : ℕ} (ty : Fin g → (E →+* ℂ)) (B : Set (Fin m → ℂ))
    (P : (Fin m → ℂ) → (D.La →+ (Fin g → ℂ))) : Prop :=
  (∀ b ∈ B, IsPeriod D ty (P b)) ∧ ∀ x, DifferentiableOn ℂ (fun b => P b x) B
def IsDerivAt0 {g : ℕ} {X : Scheme.{0}} (e : (Fin g → ℂ) → (Sp ℂ ⟶ X)) (w : Fin g → ℂ) (v : Sp (DualNumber ℂ) ⟶ X) : Prop :=
  spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v = e 0 ∧
    ∀ (U : X.Opens) (h : ⊤ ≤ v ⁻¹ᵁ U) (f : Γ(X, U)),
      TrivSqZeroExt.snd (show DualNumber ℂ from
        (Scheme.ΓSpecIso (CommRingCat.of (DualNumber ℂ))).hom.hom ((v.appLE U ⊤ h).hom f)) =
        fderiv ℂ (fun z => valAt' (e z) U f) 0 w
def IsThetaFrame {g m : ℕ} {S : Scheme.{0}} {G : Over S} [GrpObj G] (L : RigLB G) (B : Set (Fin m → ℂ))
    (y : (Fin m → ℂ) → (Sp ℂ ⟶ S)) (e : (Fin m → ℂ) → (Fin g → ℂ) → (Sp ℂ ⟶ G.left))
    (θ : (Fin m → ℂ) → (Fin g → ℂ) → ℂ) : Prop :=
  ∃ fr : L.L.ι → (Fin m → ℂ) × (Fin g → ℂ) → ℂ,
    (∀ j, DifferentiableOn ℂ (fr j) {bz | bz.1 ∈ B ∧ ⊤ ≤ e bz.1 bz.2 ⁻¹ᵁ L.L.U j}) ∧
    (∀ j b z, b ∈ B → ⊤ ≤ e b z ⁻¹ᵁ L.L.U j → fr j (b, z) ≠ 0) ∧
    (∀ j j' b z, b ∈ B → ⊤ ≤ e b z ⁻¹ᵁ (L.L.U j ⊓ L.L.U j') →
      fr j (b, z) = valAt' (e b z) (L.L.U j ⊓ L.L.U j') (L.L.g j j').val * fr j' (b, z)) ∧
    (∀ j b, b ∈ B → ⊤ ≤ e b 0 ⁻¹ᵁ L.L.U j →
      fr j (b, 0) = valAt' (y b) ((L.L.pull (eSec G)).U (fun _ => j)) (L.rig.s (fun _ => j)).val) ∧
    ∀ b ∈ B, ∃ s : (L.L.pull (pullback.fst G.hom (y b))).Sec, ∀ j z (x : Sp ℂ ⟶ pullback G.hom (y b)),
      x ≫ pullback.fst _ _ = e b z → x ≫ pullback.snd _ _ = 𝟙 _ → ⊤ ≤ e b z ⁻¹ᵁ L.L.U j →
      valAt' x ((L.L.pull (pullback.fst G.hom (y b))).U (fun _ => j)) (s.f (fun _ => j)) = θ b z * fr j (b, z)
structure FamilyUnif {D : Datum H} {l : Level H} (Xo : Moduli D l) (σ : KA l →+* ℂ) {g : ℕ}
    (ty : Fin g → (E →+* ℂ)) where
  n : ℕ
  n_pos : 0 < n
  Di : Fin n → Datum H
  sig : ∀ i, (Di i).p = D.p ∧ (Di i).q = D.q

  t : ∀ i, D.La →ₗ[𝓞 E] (Di i).La
  t_inj : ∀ i a, (∃ b, t i a = l.M' • b) ↔ ∃ b, a = l.M' • b
  t_surj : ∀ i b, ∃ a e, b = t i a + l.M' • e
  u : ∀ i, ((Di i).La →+ (Fin g → ℂ)) → (Sp ℂ ⟶ Xo.X)
  ex : ∀ i P, (Fin g → ℂ) → (Over.mk (u i P) ⟶ Xo.univ.t.G)
  over_σ : ∀ i P, IsPeriod (Di i) ty P → u i P ≫ Xo.s = spMap σ
  ex_add : ∀ i P, IsPeriod (Di i) ty P → ∀ z w, ex i P (z + w) = ex i P z * ex i P w
  ex_onto : ∀ i P, IsPeriod (Di i) ty P → Function.Surjective (ex i P)
  ex_ker : ∀ i P, IsPeriod (Di i) ty P → ∀ z, ex i P z = 1 ↔ z ∈ P.range
  ex_lin : ∀ i P, IsPeriod (Di i) ty P → ∀ (a : 𝓞 E) z,
    ex i P (fun k => ty k (a : E) * z k) = ex i P z ≫ Xo.univ.t.act.act a
  ex_weil : ∀ i P, IsPeriod (Di i) ty P → ∀ (k : ℕ) (a b : (Di i).La) (c : ℂˣ), 0 < k →
    (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * ((Di i).EF a b : ℂ) / k) →
    Out.WeilIs Xo.univ.t.G Xo.univ.t.PP.L k (ex i P ((k : ℂ)⁻¹ • P a)) (ex i P ((k : ℂ)⁻¹ • P b)) (unitOn c)
  ex_eta : ∀ i P, IsPeriod (Di i) ty P →
    ∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La),
      toUnit _ ≫ Xo.univ.eta a = ex i P ((l.M : ℂ)⁻¹ • P (t i a))
  ex_etaA : ∀ i P, IsPeriod (Di i) ty P → ∀ a, toUnit _ ≫ Xo.univ.etaA a = ex i P ((l.A : ℂ)⁻¹ • P (t i a))
  onto : ∀ y : Sp ℂ ⟶ Xo.X, y ≫ Xo.s = spMap σ → ∃ i P, IsPeriod (Di i) ty P ∧ u i P = y
  disj : ∀ i j P P', IsPeriod (Di i) ty P → IsPeriod (Di j) ty P' → u i P = u j P' → i = j
  fibre : ∀ i P P', IsPeriod (Di i) ty P → IsPeriod (Di i) ty P' → (u i P = u i P' ↔
    ∃ (gam : (Di i).La ≃ₗ[𝓞 E] (Di i).La) (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)),
      (∀ a b, (Di i).EF (gam a) (gam b) = (Di i).EF a b) ∧
      (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) (Di i).La), ∃ e, gam a = a + l.M • e) ∧
      (∀ a, ∃ e, gam a = a + l.A • e) ∧ ∀ a, P' (gam a) = h (P a))

  hol : ∀ i (m : ℕ) (B : Set (Fin m → ℂ)) (P : (Fin m → ℂ) → ((Di i).La →+ (Fin g → ℂ))), IsOpen B →
    IsHolPeriods (Di i) ty B P →
    IsHolTo B (fun b => u i (P b)) ∧
      IsHolTo (B ×ˢ Set.univ) (fun bz : (Fin m → ℂ) × (Fin g → ℂ) => (ex i (P bz.1) bz.2).left)

  ex_diff : ∀ i P, IsPeriod (Di i) ty P →
    (∀ w, ∃! v : epsPt (u i P) ⟶ Xo.univ.t.G, IsDerivAt0 (fun z => (ex i P z).left) w v.left) ∧
    ∀ v : epsPt (u i P) ⟶ Xo.univ.t.G,
      spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (ex i P 0).left →
      ∃! w, IsDerivAt0 (fun z => (ex i P z).left) w v.left

  theta : ∀ i (m : ℕ) (B : Set (Fin m → ℂ)) (P : (Fin m → ℂ) → ((Di i).La →+ (Fin g → ℂ)))
    (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] (Di i).La) (sgn : ℤˣ) (h τ : (Fin m → ℂ) → Matrix (Fin g) (Fin g) ℂ),
    IsOpen B → IsPreconnected B → IsHolPeriods (Di i) ty B P →
    (∀ a b, (Di i).EF (bas a) (bas b) = sgn * omegaStd a b) →
    (∀ b ∈ B, ((τ b).map Complex.im).PosDef ∧ ∀ k,
      (h b).mulVec (P b (bas (Pi.single (.inl k) 1))) = Pi.single k 1 ∧
      (h b).mulVec (P b (bas (Pi.single (.inr k) 1))) = (τ b).mulVec (Pi.single k 1)) →
    ∃ c₁ c₂ : Fin g → ℂ, (∀ k, c₁ k = 0 ∨ c₁ k = 1 / 2) ∧ (∀ k, c₂ k = 0 ∨ c₂ k = 1 / 2) ∧
      IsThetaFrame Xo.univ.t.PP B (fun b => u i (P b)) (fun b z => (ex i (P b) z).left)
        (fun b z => thetaChar (τ b) c₁ c₂ ((h b).mulVec z))

  lift : ∀ (m : ℕ) (B : Set (Fin m → ℂ)) (y : (Fin m → ℂ) → (Sp ℂ ⟶ Xo.X)), IsOpen B →
    (∀ b ∈ B, y b ≫ Xo.s = spMap σ) → IsHolTo B y → ∀ b₀ ∈ B,
    ∃ (B' : Set (Fin m → ℂ)) (i : Fin n) (P : (Fin m → ℂ) → ((Di i).La →+ (Fin g → ℂ))),
      IsOpen B' ∧ b₀ ∈ B' ∧ B' ⊆ B ∧ IsHolPeriods (Di i) ty B' P ∧ ∀ b ∈ B', u i (P b) = y b
def N1c : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)), 1 ≤ D.p + D.q → σ (baseKA l).ρ = H.rt0 →
    IsTypeFn H D.p D.q ty → Nonempty (FamilyUnif Xo σ ty)
end ReciprocityTheory.ChartRestriction.G.Geo.Tor


