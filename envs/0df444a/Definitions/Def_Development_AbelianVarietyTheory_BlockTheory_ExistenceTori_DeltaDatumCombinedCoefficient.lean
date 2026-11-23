-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_DeltaDatumCombinedCoefficient
-- name    : Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_DeltaDatumCombinedCoefficient
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:46:37.268117+00:00
-- url     : https://prove2.me/theorems/9383cdc0-7258-4a24-ad54-c585e15d57c9
-- title:
--   Delta Datum Combined Coefficient
-- statement:
--   Definitions and structural lemmas for Delta Datum Combined Coefficient, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/ExistenceTori/DeltaDatumCombinedCoefficient.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_LevelIndexFourierCharacter
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_NsmulMemSmulTop
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isGen_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_maps_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_mem_pull

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
namespace GlobalTheory.IndefiniteRowSideFullHecke.DeltaDatumCombinedCoefficient
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.IndefiniteRowSideFullHecke.LevelSpanSeparation
attribute [local instance] Over.cartesianMonoidalCategory
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
structure IsAuxiliarySplitSquarefreeLevel (l : Level H) where
  p : ℕ
  prime_or_one : p.Prime ∨ p = 1
  coprime : p.Coprime l.M'
  l₂ : Level H
  dvd : l.Dvd l₂
  M_eq : l₂.M = l.M * p
  A_eq : l₂.A = l.A
namespace IsAuxiliarySplitSquarefreeLevel
variable {l : Level H} (a : IsAuxiliarySplitSquarefreeLevel l)
def pId : Ideal (𝓞 E) := Ideal.span {(a.p : 𝓞 E)}
def named : Ideal (𝓞 E) := a.l₂.Mb ⊔ a.pId
def conj : Ideal (𝓞 E) := conjHalf a.l₂ ⊔ a.pId
def SplitsCompletely : Prop :=
  ∀ 𝔮 : Ideal (𝓞 E), 𝔮.IsMaximal → (a.p : 𝓞 E) ∈ 𝔮 → Ideal.absNorm 𝔮 = a.p ∧ (a.p : 𝓞 E) ∉ 𝔮 ^ 2
theorem conj_le_comap : a.conj ≤ a.named.comap (H.bar : 𝓞 E →+* 𝓞 E) := by
  refine sup_le (fun x hx => ?_) ?_
  · exact Ideal.mem_sup_left (bar_mem_of_mem_conjHalf a.l₂ hx)
  · rw [pId, Ideal.span_le, Set.singleton_subset_iff]
    change (H.bar : 𝓞 E →+* 𝓞 E) (a.p : 𝓞 E) ∈ a.named
    rw [map_natCast]
    exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)
def barQuot : (𝓞 E ⧸ a.conj) →+* (𝓞 E ⧸ a.named) :=
  Ideal.quotientMap a.named (H.bar : 𝓞 E →+* 𝓞 E) a.conj_le_comap
theorem KA_le : KA l ≤ KA a.l₂ := by rw [KA, KA, a.A_eq]
def red (D : Datum H) : ConjCl D a.l₂ →ₗ[𝓞 E] ConjCl D l :=
  Submodule.mapQ _ _ LinearMap.id (Submodule.smul_mono_left (Ideal.map_mono a.dvd.2.1))
def triv (l : Level H) : IsAuxiliarySplitSquarefreeLevel l where
  p := 1
  prime_or_one := Or.inr rfl
  coprime := Nat.coprime_one_left _
  l₂ := l
  dvd := ⟨dvd_rfl, le_rfl, dvd_rfl⟩
  M_eq := (Nat.mul_one _).symm
  A_eq := rfl
theorem triv_pId (l : Level H) : (triv l).pId = ⊤ := by simp [pId, triv]
end IsAuxiliarySplitSquarefreeLevel
structure DeltaChar {l : Level H} (a : IsAuxiliarySplitSquarefreeLevel l) (F : Type) [Field F] where
  loc : MulChar (𝓞 E ⧸ a.named) F
  ideal : Ideal (𝓞 E) →*₀ F
  ideal_zero : ∀ 𝔞, 𝔞 ⊔ a.pId ≠ ⊤ → ideal 𝔞 = 0
  principal : ∀ α : 𝓞 E, α ≠ 0 → Ideal.span {α} ⊔ a.pId = ⊤ →
    ideal (Ideal.span {α}) * loc (Ideal.Quotient.mk _ α) = loc (Ideal.Quotient.mk _ (H.bar α))
  real : ∀ 𝔟 : Ideal (𝓞 (maximalRealSubfield E)), 𝔟 ≠ ⊥ →
    𝔟.map (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E)) ⊔ a.pId = ⊤ →
    ideal (𝔟.map (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E))) = 1
def IsDetMod (D : Datum H) (I : Ideal (𝓞 E)) (k : D.La →ₗ[𝓞 E] D.La) (d : 𝓞 E ⧸ I) : Prop :=
  ∀ (φ : D.La [⋀^Fin (D.p + D.q)]→ₗ[𝓞 E] (𝓞 E ⧸ I)) (x : Fin (D.p + D.q) → D.La), φ (fun i => k (x i)) = d * φ x
def indexIdeal {D D' : Datum H} (β₀ : D'.La →ₗ[𝓞 E] D.La) : Ideal (𝓞 E) :=
  Ideal.span {z | ∃ (φ : D.La [⋀^Fin (D.p + D.q)]→ₗ[𝓞 E] 𝓞 E) (x : Fin (D.p + D.q) → D'.La), z = φ fun i => β₀ (x i)}
section Datum
variable {D : Datum H} {l : Level H} {a : IsAuxiliarySplitSquarefreeLevel l}
structure Vol (D : Datum H) (a : IsAuxiliarySplitSquarefreeLevel l) where
  ω : ConjCl D a.l₂ [⋀^Fin (D.p + D.q)]→ₗ[𝓞 E] (𝓞 E ⧸ a.conj)
  gen : ∃ u, ω u = 1
def Vol.det₁ (v : Vol D a) {n : ℕ} (x : Fin n → ConjCl D a.l₂) : 𝓞 E ⧸ a.conj :=
  if h : D.p + D.q ≤ n then v.ω fun i => x (Fin.castLE h i) else 0
variable {F : Type} [Field F]
def phiDelta (δ : DeltaChar a F) (v : Vol D a) {n : ℕ} (x : Fin n → ConjCl D a.l₂) : F :=
  δ.loc⁻¹ (a.barQuot (v.det₁ x))
end Datum
section Cover
variable {D : Datum H} {l : Level H}
def IsLevelMap (Xo : Moduli D l) (a : IsAuxiliarySplitSquarefreeLevel l) (Xo₂ : Moduli D a.l₂) (r : Xo₂.X ⟶ Xo.X)
    (m : SABMap Xo₂.univ.t Xo.univ.t r) : Prop :=
  r ≫ Xo.s = Xo₂.s ≫ spMap (IntermediateField.inclusion a.KA_le).toRingHom ∧
    (∀ x, (Xo₂.univ.eta x ^ a.p).left ≫ m.φ = r ≫ (Xo.univ.eta x).left) ∧
    ∀ x, (Xo₂.univ.etaA x).left ≫ m.φ = r ≫ (Xo.univ.etaA x).left
def IsBundleIso {S S' : Scheme.{0}} {t' : SAB H S'} {t : SAB H S} {f : S' ⟶ S} (m : SABMap t' t f)
    (w : LB.Iso t'.PP.L (t.PP.L.pull m.φ)) : Prop :=
  w.IsGen ∧
    LB.Gen.Maps (LB.linCombIso w (K := PUnit) (fun _ => eSec t'.G) (fun _ => 1)) t'.PP.rig
      (m.cm.rigPull t.PP.L t.PP.rig) ∧
    LB.Gen.Maps (LB.linCombIso w (thφ t'.G (x3 t'.G)) thε) t'.cub.t (m.cm.thetaPull t.PP.L t.cub.t)
structure Cover (Xo : Moduli D l) (c : Coeff l) (a : IsAuxiliarySplitSquarefreeLevel l) where
  Xo₂ : Moduli D a.l₂
  c₂ : Coeff a.l₂
  field_eq : c.F = c₂.F
  r : Xo₂.X ⟶ Xo.X
  m : SABMap Xo₂.univ.t Xo.univ.t r
  w : LB.Iso Xo₂.univ.t.PP.L (Xo.univ.t.PP.L.pull m.φ)
  level : IsLevelMap Xo a Xo₂ r m
  bundle : IsBundleIso m w
variable {Xo : Moduli D l} {c : Coeff l} {a : IsAuxiliarySplitSquarefreeLevel l} (C : Cover Xo c a)
namespace Cover
def incl : c.F →+* C.c₂.F := (IntermediateField.inclusion C.field_eq.le).toRingHom
def IsGroupMap {S S' : Type} [CommRing S] [CommRing S'] (φ : S →+* S') (x₂ : Sp S' ⟶ C.Xo₂.X) (x : Sp S ⟶ Xo.X)
    (pm : Gx x₂ ⟶ Gx x) : Prop :=
  pm ≫ (snd (Over.mk x) Xo.univ.t.G).left = (snd (Over.mk x₂) C.Xo₂.univ.t.G).left ≫ C.m.φ ∧
    pm ≫ (fst (Over.mk x) Xo.univ.t.G).left = (fst (Over.mk x₂) C.Xo₂.univ.t.G).left ≫ spMap φ
def SecOver {S S' : Type} [CommRing S] [CommRing S'] {x₂ : Sp S' ⟶ C.Xo₂.X} {x : Sp S ⟶ Xo.X} (pm : Gx x₂ ⟶ Gx x)
    (k : ℤ) (F₂ : LB.Sec (Out.LPow C.Xo₂.univ.t.G C.Xo₂.univ.t.PP.L k (Over.mk x₂)))
    (F : LB.Sec (Out.LPow Xo.univ.t.G Xo.univ.t.PP.L k (Over.mk x))) : Prop :=
  ∀ (i : Xo.univ.t.PP.L.ι) (j : C.Xo₂.univ.t.PP.L.ι) (W : (Gx x₂).Opens)
    (h₁ : W ≤ pm ⁻¹ᵁ (Out.LPow Xo.univ.t.G Xo.univ.t.PP.L k (Over.mk x)).U fun _ => i)
    (h₂ : W ≤ (Out.LPow C.Xo₂.univ.t.G C.Xo₂.univ.t.PP.L k (Over.mk x₂)).U fun _ => j)
    (h₃ : W ≤ (snd (Over.mk x₂) C.Xo₂.univ.t.G).left ⁻¹ᵁ
      (LB.div (Xo.univ.t.PP.L.pull C.m.φ) C.Xo₂.univ.t.PP.L).U (fun _ => i, j)),
    (pm.appLE _ W h₁).hom (F.f fun _ => i) =
      ((res h₃ (pullU (snd (Over.mk x₂) C.Xo₂.univ.t.G).left _ (C.w.s (fun _ => i, j))) ^ k : Γ(Gx x₂, W)ˣ) :
        Γ(Gx x₂, W)) * ((Gx x₂).presheaf.map (homOfLE h₂).op).hom (F₂.f fun _ => j)
def LiesOver {S S' : Type} [CommRing S] [Algebra c.F S] [CommRing S'] [Algebra C.c₂.F S'] (φ : S →+* S')
    (y₂ : FrPt C.Xo₂ C.c₂ S') (y : FrPt Xo c S) : Prop :=
  φ.comp (algebraMap c.F S) = (algebraMap C.c₂.F S').comp C.incl ∧
    y₂.x ≫ C.r = spMap φ ≫ y.x ∧
    (∀ τ i, y₂.u τ i ≫ C.m.φ = spMap (dualMap φ) ≫ y.u τ i) ∧
    ∃ pm : Gx y₂.x ⟶ Gx y.x, C.IsGroupMap φ y₂.x y.x pm ∧ C.SecOver pm 1 y₂.s y.s
def NabOver (nab : NabV Xo c) (nab₂ : NabV C.Xo₂ C.c₂) : Prop :=
  ∀ (S : Type) [CommRing S] [Algebra c.F S] [Algebra C.c₂.F S] (y₂ : FrPt C.Xo₂ C.c₂ S) (y : FrPt Xo c S),
    C.LiesOver (RingHom.id S) y₂ y → ∀ pm : Gx y₂.x ⟶ Gx y.x, C.IsGroupMap (RingHom.id S) y₂.x y.x pm →
    ∀ (k : ℤ) (F₂ : LB.Sec (Out.LPow C.Xo₂.univ.t.G C.Xo₂.univ.t.PP.L k (Over.mk y₂.x)))
      (F : LB.Sec (Out.LPow Xo.univ.t.G Xo.univ.t.PP.L k (Over.mk y.x))), C.SecOver pm k F₂ F →
      ∀ α, nab₂ y₂ k F₂ α = nab y k F α
end Cover
def fnAt {X : Scheme.{0}} {S : Type} [CommRing S] (y : Sp S ⟶ X) (f : Γ(X, ⊤)) : S :=
  (Scheme.ΓSpecIso (CommRingCat.of S)).hom.hom (y.appTop.hom f)
def basePt {Xo : Moduli D l} {c : Coeff l} {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) :
    Sp S ⟶ Xo.XF c :=
  pullback.lift y.x (spMap (algebraMap c.F S)) (by
    rw [y.x_over, sOf]
    simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp])
structure IsPresentation (a : IsAuxiliarySplitSquarefreeLevel l) (D' : Datum H) (t : D.La →ₗ[𝓞 E] D'.La) (m : ℕ)
    (β₀ : D'.La →ₗ[𝓞 E] D.La) (𝔞 : Ideal (𝓞 E)) (d : 𝓞 E ⧸ a.named) : Prop where
  pos : 0 < m
  coprime : m.Coprime a.p
  isom : ∀ x y, D.EF (β₀ x) (β₀ y) = (m : ℤ) ^ 2 * D'.EF x y
  ne_bot : 𝔞 ≠ ⊥
  prime_to : 𝔞 ⊔ a.pId = ⊤
  index : indexIdeal β₀ * 𝔞.map (H.bar : 𝓞 E →+* 𝓞 E) = Ideal.span {(m : 𝓞 E) ^ (D.p + D.q)} * 𝔞
  det : IsDetMod D a.named (β₀ ∘ₗ t) d
def IsDeltaDet (δ : DeltaChar a C.c₂.F) (f : Γ(C.Xo₂.XF C.c₂, ⊤)) : Prop :=
  ∀ (g : ℕ) (ty : Fin g → (E →+* ℂ)), IsTypeFn H D.p D.q ty →
    ∀ (U : FamilyUnif C.Xo₂ (KA a.l₂).val.toRingHom ty) (i : Fin U.n) (P : (U.Di i).La →+ (Fin g → ℂ)),
      IsPeriod (U.Di i) ty P → ∀ y : Sp ℂ ⟶ C.Xo₂.XF C.c₂, y ≫ pullback.fst _ _ = U.u i P →
      y ≫ pullback.snd _ _ = spMap C.c₂.F.val.toRingHom →
      ∀ (m : ℕ) (β₀ : (U.Di i).La →ₗ[𝓞 E] D.La) (𝔞 : Ideal (𝓞 E)) (d : 𝓞 E ⧸ a.named),
        IsPresentation a (U.Di i) (U.t i) m β₀ 𝔞 d →
        fnAt y f * ((δ.loc ((m : 𝓞 E ⧸ a.named) ^ (D.p + D.q)) : C.c₂.F) : ℂ) =
          ((δ.loc d * δ.ideal 𝔞 : C.c₂.F) : ℂ)
end Cover
section Delta
variable {D : Datum H} {l : Level H}
structure DeltaDatum (Xo : Moduli D l) (c : Coeff l) (nab : NabV Xo c) where
  a : IsAuxiliarySplitSquarefreeLevel l
  split : a.SplitsCompletely
  cov : Cover Xo c a
  nab₂ : NabV cov.Xo₂ cov.c₂
  nab_over : cov.NabOver nab nab₂
  δ : DeltaChar a cov.c₂.F
  vol : Vol D a
  fn : Γ(cov.Xo₂.XF cov.c₂, ⊤)
  fn_eq : IsDeltaDet cov δ fn
namespace DeltaDatum
variable {Xo : Moduli D l} {c : Coeff l} {nab : NabV Xo c} (Δ : DeltaDatum Xo c nab)
def fnVal {S : Type} [CommRing S] [Algebra Δ.cov.c₂.F S] (y₂ : FrPt Δ.cov.Xo₂ Δ.cov.c₂ S) : S :=
  fnAt (basePt y₂) Δ.fn
def deltaCoeff {n : ℕ} (t : Fin n → NamedCl D Δ.a.l₂) : Δ.cov.c₂.F :=
  fourier Δ.cov.c₂ (phiDelta Δ.δ Δ.vol) t
def combined {n : ℕ} (x₀ : Fin n → ConjCl D l) (x : Fin n → ConjCl D Δ.a.l₂) : Δ.cov.c₂.F :=
  Δ.cov.incl (indicatorCl c x₀ fun b => Δ.a.red D (x b)) * phiDelta Δ.δ Δ.vol x
def combinedCoeff {n : ℕ} (x₀ : Fin n → ConjCl D l) (t : Fin n → NamedCl D Δ.a.l₂) : Δ.cov.c₂.F :=
  fourier Δ.cov.c₂ (Δ.combined x₀) t
def CoeffProduct (n : ℕ) : Prop :=
  ∀ (x₀ : Fin n → ConjCl D l) (u₁ u₂ : Fin n → D.La),
    Δ.combinedCoeff x₀ (fun b => Submodule.Quotient.mk (Δ.a.p • u₁ b + l.M • u₂ b)) =
      Δ.cov.incl (indCoeff c x₀ fun b => Submodule.Quotient.mk (u₁ b)) *
        Δ.deltaCoeff fun b => Submodule.Quotient.mk (l.M • u₂ b)
def CoeffTransform (n : ℕ) : Prop :=
  ∀ g : Sim D, g.InGam l Δ.a.l₂ → ∀ d, IsDetMod D Δ.a.named (g.f Δ.a.l₂.M) d →
    ∀ (x₀ : Fin n → ConjCl D l) (u : Fin n → D.La),
      Δ.combinedCoeff x₀ (fun b => Submodule.Quotient.mk (g.f Δ.a.l₂.M (u b))) =
        Δ.δ.loc d * Δ.combinedCoeff x₀ fun b => Submodule.Quotient.mk (u b)
def FnTransform : Prop :=
  ∀ (g : Sim D) (ρ : Δ.cov.Xo₂.X ≅ Δ.cov.Xo₂.X), g.InGam l Δ.a.l₂ → Δ.cov.Xo₂.LevAut g ρ →
    ∀ d, IsDetMod D Δ.a.named (g.f Δ.a.l₂.M) d →
    ∀ (S : Type) [CommRing S] (β : Δ.cov.c₂.F →+* S) (y y' : Sp S ⟶ Δ.cov.Xo₂.XF Δ.cov.c₂),
      y ≫ pullback.snd _ _ = spMap β → y' ≫ pullback.snd _ _ = spMap β →
      y' ≫ pullback.fst _ _ = y ≫ pullback.fst _ _ ≫ ρ.hom → fnAt y' Δ.fn = β (Δ.δ.loc d) * fnAt y Δ.fn
def FnRootOfUnity : Prop := ∃ N : ℕ, 0 < N ∧ Δ.fn ^ N = 1
end DeltaDatum
variable {Xo : Moduli D l} {c : Coeff l} {a : IsAuxiliarySplitSquarefreeLevel l} (C : Cover Xo c a)
def PresentationExists : Prop :=
  ∀ (g : ℕ) (ty : Fin g → (E →+* ℂ)), IsTypeFn H D.p D.q ty →
    ∀ (U : FamilyUnif C.Xo₂ (KA a.l₂).val.toRingHom ty) (i : Fin U.n),
      ∃ m β₀ 𝔞 d, IsPresentation a (U.Di i) (U.t i) m β₀ 𝔞 d
def DeltaDetExists (δ : DeltaChar a C.c₂.F) : Prop := ∃ f, IsDeltaDet C δ f
def DeltaDetUnique (δ : DeltaChar a C.c₂.F) : Prop := ∀ f f', IsDeltaDet C δ f → IsDeltaDet C δ f' → f = f'
def IsGaloisCover : Prop :=
  (∀ g : Sim D, g.InGam l a.l₂ → ∃ ρ : C.Xo₂.X ≅ C.Xo₂.X, C.Xo₂.LevAut g ρ ∧ ρ.hom ≫ C.r = C.r) ∧
  ∃ rF : C.Xo₂.XF C.c₂ ⟶ Xo.XF c, rF ≫ pullback.fst _ _ = pullback.fst _ _ ≫ C.r ∧
    rF ≫ pullback.snd _ _ = pullback.snd _ _ ≫ spMap C.incl ∧ IsFinite rF ∧ Etale rF ∧ Surjective rF ∧
    ∀ (k : Type) [Field k] [IsAlgClosed k] (y y' : Sp k ⟶ C.Xo₂.XF C.c₂), y ≫ rF = y' ≫ rF →
      (∃ (g : Sim D) (ρ : C.Xo₂.X ≅ C.Xo₂.X), g.InGam l a.l₂ ∧ C.Xo₂.LevAut g ρ ∧ ρ.hom ≫ C.r = C.r ∧
        y' ≫ pullback.fst _ _ = y ≫ pullback.fst _ _ ≫ ρ.hom) ∧
      ∀ (g : Sim D) (ρ : C.Xo₂.X ≅ C.Xo₂.X), g.InGam l a.l₂ → C.Xo₂.LevAut g ρ →
        y ≫ pullback.fst _ _ ≫ ρ.hom = y ≫ pullback.fst _ _ → g.TrivAt a.l₂
def FramesOverFrames : Prop :=
  (∀ (S : Type) [CommRing S] [Algebra c.F S] [Algebra C.c₂.F S],
    algebraMap c.F S = (algebraMap C.c₂.F S).comp C.incl →
    ∀ y₂ : FrPt C.Xo₂ C.c₂ S, ∃! y : FrPt Xo c S, C.LiesOver (RingHom.id S) y₂ y) ∧
  ∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S),
    ∃ (S' : Type) (_ : CommRing S') (_ : Algebra C.c₂.F S') (φ : S →+* S') (y₂ : FrPt C.Xo₂ C.c₂ S'),
      φ.Finite ∧ φ.Etale ∧ φ.FaithfullyFlat ∧ C.LiesOver φ y₂ y
end Delta
section Trivial
variable {D : Datum H} {l : Level H}
instance subsingleton_named : Subsingleton (𝓞 E ⧸ (IsAuxiliarySplitSquarefreeLevel.triv l).named) :=
  Ideal.Quotient.subsingleton_iff.2 (by rw [IsAuxiliarySplitSquarefreeLevel.named, IsAuxiliarySplitSquarefreeLevel.triv_pId, sup_top_eq])
instance subsingleton_conj : Subsingleton (𝓞 E ⧸ (IsAuxiliarySplitSquarefreeLevel.triv l).conj) :=
  Ideal.Quotient.subsingleton_iff.2 (by rw [IsAuxiliarySplitSquarefreeLevel.conj, IsAuxiliarySplitSquarefreeLevel.triv_pId, sup_top_eq])
def Cover.triv (Xo : Moduli D l) (c : Coeff l) : Cover Xo c (IsAuxiliarySplitSquarefreeLevel.triv l) where
  Xo₂ := Xo
  c₂ := c
  field_eq := rfl
  r := 𝟙 _
  m := GlobalTheory.ObjLower.sabId Xo.univ.t
  w := GlobalTheory.ObjLower.idIso Xo.univ.t.PP.L
  level := by
    refine ⟨?_, fun x => ?_, fun x => ?_⟩
    · have e : (IntermediateField.inclusion (IsAuxiliarySplitSquarefreeLevel.triv l).KA_le).toRingHom = RingHom.id (KA l) :=
        RingHom.ext fun _ => rfl
      rw [e]
      exact (Category.id_comp _).trans ((Category.comp_id _).symm.trans (congrArg (Xo.s ≫ ·) (Spec.map_id _).symm))
    · change (Xo.univ.eta x ^ 1).left ≫ 𝟙 _ = 𝟙 _ ≫ _
      rw [pow_one]
      exact (Category.comp_id _).trans (Category.id_comp _).symm
    · exact (Category.comp_id _).trans (Category.id_comp _).symm
  bundle := ⟨(isGen_iff _).2 (GlobalTheory.ObjLower.pgen_idIso Xo.univ.t.PP.isLB),
    (maps_iff _ _ (fun _ => eSec Xo.univ.t.G) _ Xo.univ.t.PP.rig Xo.univ.t.PP.rig (𝟙 _) _
      (rigPull_le _ _ (GlobalTheory.ObjLower.cubeId Xo.univ.t.G).e_comm Xo.univ.t.PP.L) (fun _ => rfl)).2
      (GlobalTheory.ObjLower.pmaps_idIso _ _ _ _ Xo.univ.t.PP.rigGen),
    (maps_iff _ _ (thφ Xo.univ.t.G (x3 Xo.univ.t.G)) _ Xo.univ.t.cub.t Xo.univ.t.cub.t (𝟙 _) _
      ((GlobalTheory.ObjLower.cubeId Xo.univ.t.G).theta_le Xo.univ.t.PP.L) (fun _ => rfl)).2
      (GlobalTheory.ObjLower.pmaps_idIso _ _ _ _ Xo.univ.t.cub.isGen)⟩
open Classical in

def DeltaChar.triv (l : Level H) (F : Type) [Field F] : DeltaChar (IsAuxiliarySplitSquarefreeLevel.triv l) F where
  loc := 1
  ideal :=
    { toFun := fun 𝔞 => if 𝔞 = 0 then 0 else 1
      map_zero' := if_pos rfl
      map_one' := if_neg one_ne_zero
      map_mul' := fun 𝔞 𝔟 => by by_cases h : 𝔞 = 0 <;> by_cases h' : 𝔟 = 0 <;>
        simp only [mul_eq_zero, h, h', or_true, true_or, or_self, if_true, if_false, mul_zero, zero_mul, _root_.mul_one] }
  ideal_zero := fun 𝔞 h => absurd (by rw [IsAuxiliarySplitSquarefreeLevel.triv_pId, sup_top_eq]) h
  principal := fun α hα _ => by
    rw [MulChar.one_apply (isUnit_of_subsingleton _), MulChar.one_apply (isUnit_of_subsingleton _), _root_.mul_one]
    exact if_neg (by simpa using hα)
  real := fun 𝔟 h _ => if_neg fun e => h ((Ideal.map_eq_bot_iff_of_injective
    (FaithfulSMul.algebraMap_injective _ _)).1 e)
theorem Cover.triv_nabOver (Xo : Moduli D l) (c : Coeff l) (nab : NabV Xo c) :
    (Cover.triv Xo c).NabOver @nab @nab := by
  intro S _ i₁ i₂ y₂ y h pm hpm k F₂ F hF α
  obtain rfl : i₁ = i₂ := Algebra.algebra_ext _ _ fun r => RingHom.congr_fun h.1 r
  have key : ∀ {x : Sp S ⟶ Xo.X} (pm : Gx x ⟶ Gx x), (Cover.triv Xo c).IsGroupMap (RingHom.id S) x x pm →
      ∀ (k : ℤ) (F₂ F : LB.Sec (Out.LPow Xo.univ.t.G Xo.univ.t.PP.L k (Over.mk x))),
        (Cover.triv Xo c).SecOver pm k F₂ F → F₂ = F := by
    intro x pm hpm k F₂ F hF
    obtain rfl : pm = 𝟙 _ := by
      have e : spMap (RingHom.id S) = 𝟙 _ := Spec.map_id _
      have h2 := hpm.2
      rw [e] at h2
      exact pullback.hom_ext (h2.trans ((Category.comp_id _).trans (Category.id_comp _).symm))
        (hpm.1.trans ((Category.comp_id _).trans (Category.id_comp _).symm))
    obtain ⟨f₂, c₂⟩ := F₂
    obtain ⟨f, c₁⟩ := F
    congr 1
    funext J
    obtain ⟨i, rfl⟩ : ∃ i, J = fun _ => i := ⟨J 0, funext fun a => congrArg J (Subsingleton.elim _ _)⟩
    have hle : (Out.LPow Xo.univ.t.G Xo.univ.t.PP.L k (Over.mk x)).U (fun _ => i) ≤
        (snd (Over.mk x) Xo.univ.t.G).left ⁻¹ᵁ Xo.univ.t.PP.L.U i :=
      LB.wchart_le Xo.univ.t.PP.L (fun _ : Fin 1 => (snd (Over.mk x) Xo.univ.t.G).left) (fun _ => i) 0
    have H := hF i i _ le_rfl le_rfl (fun z hz => ⟨mem_pull.2 (hle hz), hle hz⟩)
    have hw : (Cover.triv Xo c).w.s (fun _ => i, i) = 1 := by
      have h0 := congrArg (res (inf_le_right : (Xo.univ.t.PP.L.pull (𝟙 _)).U (fun _ => i) ⊓ Xo.univ.t.PP.L.U i ≤
        Xo.univ.t.PP.L.U i)) (Xo.univ.t.PP.isLB.g_self i)
      rw [map_one] at h0
      refine Eq.trans (Units.ext ?_) h0
      change _ = (Xo.univ.t.G.left.presheaf.map _ ≫ Xo.univ.t.G.left.presheaf.map _).hom _
      erw [← Functor.map_comp]
      rfl
    have hid : ∀ (Y : Scheme.{0}) (U : Y.Opens) (z : Γ(Y, U)), (Y.presheaf.map (homOfLE (le_refl U)).op).hom z = z :=
      fun Y U z => by
        have : (homOfLE (le_refl U)).op = 𝟙 _ := rfl
        rw [this, CategoryTheory.Functor.map_id]; rfl
    rw [hw, map_one, map_one, one_zpow, Units.val_one, _root_.one_mul] at H
    exact (hid _ _ _).symm.trans (H.symm.trans (hid _ _ _))
  obtain ⟨x₂, hx₂, u₂, t₂, e₂, b₂, s₂, g₂⟩ := y₂
  obtain ⟨x, hx, u, t, e, b, s, g⟩ := y
  obtain ⟨-, h1, h2, pm', h3, h4⟩ := h
  have e : spMap (RingHom.id S) = 𝟙 _ := Spec.map_id _
  have e' : spMap (dualMap (RingHom.id S)) = 𝟙 _ := by
    have : dualMap (RingHom.id S) = RingHom.id _ := RingHom.ext fun z => TrivSqZeroExt.inl_fst_add_inr_snd_eq z
    rw [this]; exact Spec.map_id _
  obtain rfl : x₂ = x := by
    rw [e] at h1
    exact (Category.comp_id _).symm.trans (h1.trans (Category.id_comp _))
  obtain rfl : u₂ = u := by
    funext τ i
    have := h2 τ i
    rw [e'] at this
    exact (Category.comp_id _).symm.trans (this.trans (Category.id_comp _))
  obtain rfl : s₂ = s := key pm' h3 1 _ _ h4
  obtain rfl : F₂ = F := key pm hpm k _ _ hF
  rfl
def DeltaDatum.triv (Xo : Moduli D l) (c : Coeff l) (nab : NabV Xo c) : DeltaDatum Xo c nab where
  a := IsAuxiliarySplitSquarefreeLevel.triv l
  split := fun 𝔮 h h1 => absurd ((Ideal.eq_top_iff_one _).2 (by simpa [IsAuxiliarySplitSquarefreeLevel.triv] using h1)) h.ne_top
  cov := Cover.triv Xo c
  nab₂ := @nab
  nab_over := Cover.triv_nabOver Xo c @nab
  δ := DeltaChar.triv l _
  vol := ⟨0, fun _ => 0, Subsingleton.elim _ _⟩
  fn := 1
  fn_eq := fun g ty _ U i P _ y _ _ m β₀ 𝔞 d h => by
    have h1 : ∀ z, (DeltaChar.triv l (Cover.triv Xo c).c₂.F).loc z = 1 := fun z =>
      MulChar.one_apply (isUnit_of_subsingleton _)
    have h2 : (DeltaChar.triv l (Cover.triv Xo c).c₂.F).ideal 𝔞 = 1 := if_neg h.ne_bot
    rw [h1, h1, h2]
    simp [fnAt]
end Trivial
end GlobalTheory.IndefiniteRowSideFullHecke.DeltaDatumCombinedCoefficient


