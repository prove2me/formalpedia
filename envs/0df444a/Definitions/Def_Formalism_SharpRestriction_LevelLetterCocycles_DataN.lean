-- Prove2me | Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataN
-- name    : Formalism_SharpRestriction_LevelLetterCocycles_DataN
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-24T18:13:14.009862+00:00
-- url     : https://prove2.me/theorems/595d0658-209b-4a5c-83ce-8140e389346d
-- title:
--   Data N
-- statement:
--   Definitions and structural lemmas for Data N, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/LevelLetterCocycles/DataN.lean

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_Params
import Definitions.Def_Formalism_LocalRingCardinality_DataHost
import Definitions.Def_Formalism_LocalRingCardinality_DataRows
import Definitions.Def_Formalism_GaloisCohomology_Statement
import Definitions.Def_Formalism_CyclotomicNorms_StatementT
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace Formalism.BasicNotions
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal
def heckeEig {O X M : Type} [CommRing O] [IsDomain O] [AddCommGroup M] [Module O M]
    (T : Subalgebra O (X → O)) (act : T →ₐ[O] Module.End O M) (x : X) :
    Submodule (FractionRing O) (TensorProduct O (FractionRing O) M) :=
  ⨅ f : T, Module.End.eigenspace ((act f).baseChange (FractionRing O))
    (algebraMap O (FractionRing O) ((f : X → O) x))
def heckeMult {O X M : Type} [CommRing O] [IsDomain O] [AddCommGroup M] [Module O M]
    (T : Subalgebra O (X → O)) (act : T →ₐ[O] Module.End O M) (x : X) : ℕ :=
  Module.finrank (FractionRing O) (heckeEig T act x)
def ccIdeal {O X : Type} [CommRing O] (T : Subalgebra O (X → O)) (Z : Finset X) : Ideal T :=
  RingHom.ker ((RingHom.pi (fun y : {x // x ∉ Z} => Pi.evalRingHom (fun _ : X => O) y.1)).comp
    T.val.toRingHom)
def ccAt {O X : Type} [CommRing O] (T : Subalgebra O (X → O)) (Z : Finset X) (π : X) : Ideal O :=
  Ideal.map ((Pi.evalRingHom (fun _ : X => O) π).comp T.val.toRingHom) (ccIdeal T Z)
def lenUnit {O : Type} [CommRing O] (l : ℕ) (M : Type) [AddCommGroup M] [Module O M] : ℚ :=
  ((Module.length O M).toNat : ℚ) / ((Module.length O (O ⧸ Ideal.span {(l : O)})).toNat : ℚ)
def placesOver (E : Type) [Field E] [NumberField E] (p : ℕ) : Set (HeightOneSpectrum (𝓞 E)) :=
  {v | ((p : ℕ) : 𝓞 E) ∈ v.asIdeal}
abbrev KmodO (O : Type) [CommRing O] [IsDomain O] : Type :=
  FractionRing O ⧸ LinearMap.range (Algebra.linearMap O (FractionRing O))
def IsConjPl {R : Ranks} (H : Host R) (w w' : HeightOneSpectrum (𝓞 H.E)) : Prop :=
  ∀ x y : 𝓞 H.E, (y : H.E) = H.conj (x : H.E) → (x ∈ w.asIdeal ↔ y ∈ w'.asIdeal)
def TameGenAt {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] (A : ValuationSubring Ω)
    (γ : G E Ω) : Prop :=
  γ ∈ Ine (F := E) A ∧ ((Ine (F := E) A : Subgroup (G E Ω)) : Set (G E Ω)) ⊆
    closure ((Subgroup.closure (insert γ {σ : G E Ω | ∀ y : Ω, y ≠ 0 → A.valuation (σ y / y - 1) < 1}) :
      Subgroup (G E Ω)) : Set (G E Ω))
def IsSplitPl {R : Ranks} (H : Host R) (v : HeightOneSpectrum (𝓞 H.E)) : Prop :=
  ∃ x : 𝓞 H.E, x ∈ v.asIdeal ∧ ∀ y : 𝓞 H.E, (y : H.E) = H.conj (x : H.E) → y ∉ v.asIdeal
set_option synthInstance.maxHeartbeats 400000 in

structure NData (R : Ranks) (H : Host R) (what₂ : Rows.Data R) where

  Om : Type
  [instOm : Field Om]
  [algOm : Algebra H.E Om]
  [acOm : IsAlgClosure H.E Om]

  plOm : Formalism.GaloisCohomology.Places H.E Om

  ldat : ∀ (p : ℕ) [Fact p.Prime], Formalism.GaloisCohomology.LData H.E Om p

  sha_eq : ∀ (p : ℕ) [Fact p.Prime] (e : ℕ), 0 < e → e < R.t → ∀ n : ℕ,
    Formalism.GaloisCohomology.shaLen (ldat p) (e : ℤ) = (n : ℕ∞) → what₂.shaLen p e = (n : ℚ)

  Loc : Type
  l : Loc → ℕ
  [lPrime : ∀ i, Fact (l i).Prime]
  j : Loc → ℕ
  j_range : ∀ i, 1 ≤ j i ∧ j i ≤ R.m
  mu : Loc → what₂.Tup
  w : Loc → what₂.places.Pl
  w_l : ∀ i, what₂.places.resChar (w i) = l i

  mu_w : ∀ i, mu i = what₂.muTw (w i)

  w_tw : ∀ i, what₂.muAt (w i) ≠ what₂.mu0

  locs : ℕ → what₂.places.Pl → Finset Loc
  locs_mem : ∀ j' w' i, i ∈ locs j' w' ↔ j i = j' ∧ w i = w'

  O : Loc → Type
  [instO : ∀ i, CommRing (O i)]
  [domO : ∀ i, IsDomain (O i)]
  [dvrO : ∀ i, IsDiscreteValuationRing (O i)]
  [algO : ∀ i, Algebra ℤ_[l i] (O i)]
  [finO : ∀ i, Module.Finite ℤ_[l i] (O i)]
  [topO : ∀ i, TopologicalSpace (O i)]
  [trO : ∀ i, IsTopologicalRing (O i)]
  O_adic : ∀ i, IsAdic (IsLocalRing.maximalIdeal (O i))
  O_complete : ∀ i, IsAdicComplete (IsLocalRing.maximalIdeal (O i)) (O i)

  embK : ∀ i, what₂.LL →+* FractionRing (O i)
  embK_w : ∀ i (x : what₂.LL), 0 ≤ what₂.places.val (w i) x ↔
    embK i x ∈ (algebraMap (O i) (FractionRing (O i))).range

  X : Loc → Type
  [finX : ∀ i, Fintype (X i)]
  [neX : ∀ i, Nonempty (X i)]
  T : ∀ i, Subalgebra (O i) (X i → O i)
  T_local : ∀ i, IsLocalRing (T i)
  T_sep : ∀ i (x y : X i), x ≠ y → ∃ f ∈ T i, (f : X i → O i) x ≠ (f : X i → O i) y

  Mt : Loc → Type
  [acgMt : ∀ i, AddCommGroup (Mt i)]
  [modMt : ∀ i, Module (O i) (Mt i)]
  [freeMt : ∀ i, Module.Free (O i) (Mt i)]
  [finMt : ∀ i, Module.Finite (O i) (Mt i)]
  act : ∀ i, T i →ₐ[O i] Module.End (O i) (Mt i)
  act_inj : ∀ i, Function.Injective (act i)

  prMt : ∀ i, what₂.MtL (mu i) (j i) →ₛₗ[embK i] TensorProduct (O i) (FractionRing (O i)) (Mt i)
  prMt_span : ∀ i, Submodule.span (FractionRing (O i)) (Set.range (prMt i)) = ⊤
  prMt_lat : ∀ i, Submodule.span (O i)
      (prMt i '' {x | what₂.jMt (mu i) (j i) x ∈ (what₂.MtLat (mu i) (j i)).gen}) =
    LinearMap.range (TensorProduct.mk (O i) (FractionRing (O i)) (Mt i) 1)

  eig_ne : ∀ i x, heckeEig (T i) (act i) x ≠ ⊥

  chi : ∀ i, ℕ → (G H.E Om →* (O i)ˣ)
  chi_cont : ∀ i c, Continuous (fun g => ((chi i c g : (O i)ˣ) : O i))

  chi_def : ∀ i c, 1 ≤ c → c ≤ R.t → chi i c = chi i 1 *
    ((Units.map (algebraMap ℤ_[l i] (O i)).toMonoidHom).comp
      (cycZ (F := H.E) (Ω := Om) (l i))) ^ (-((c : ℤ) - 1))

  Z : ∀ i, Finset (X i)
  Zgood : ∀ i, Finset (X i)

  s0 : Loc → ℕ
  restNLevelExponent_of_odd : ∀ i, l i ≠ 2 → s0 i = max 1 (H.QS.factorization (l i))
  restNLevelExponent_of_two : ∀ i, l i = 2 → s0 i = H.QS.factorization 2

  S : Loc → Finset (HeightOneSpectrum (𝓞 H.E))
  Q : Loc → Finset (HeightOneSpectrum (𝓞 H.E))

  SQ_split : ∀ i v, v ∈ S i ∨ v ∈ Q i → IsSplitPl H v
  SQ_disj : ∀ i, Disjoint (S i) (Q i)
  SQ_l : ∀ i v, v ∈ S i ∨ v ∈ Q i → v ∉ placesOver H.E (l i)

  S_def : ∀ i v, v ∈ S i ↔ (v ∈ placesOver H.E (H.g 0) ∨ v ∈ placesOver H.E (H.g 1) ∨
      v ∈ placesOver H.E (if l i = H.pde then H.pde' else H.pde)) ∧ v ∉ placesOver H.E (l i)

  hT : ∀ i, HeightOneSpectrum (𝓞 H.E) → ℕ → T i
  T_gen : ∀ i, Algebra.adjoin (O i) {f : X i → O i | ∃ v k, IsSplitPl H v ∧
      v ∉ placesOver H.E (l i) ∧ v ∉ S i ∧ v ∉ Q i ∧ 1 ≤ k ∧ k ≤ R.nV ∧ f = (hT i v k : X i → O i)} =
    T i

  gam0 : Loc → HeightOneSpectrum (𝓞 H.E) → G H.E Om
  locNd_chebotarevPlace_mem : ∀ i v, gam0 i v ∈ Ine (F := H.E) (plOm.1 v)

  restN_tameGenerator_generates : ∀ i v, v ∈ S i ∨ v ∈ Q i → TameGenAt (plOm.1 v) (gam0 i v)

  chi_ram_Q : ∀ i, ∀ v ∈ Q i, ∃ g ∈ Ine (F := H.E) (plOm.1 v), chi i 1 g ≠ 1

  Bj : Loc → Type
  [acgBj : ∀ i, AddCommGroup (Bj i)]
  [modBj : ∀ i, Module (O i) (Bj i)]
  [freeBj : ∀ i, Module.Free (O i) (Bj i)]
  [finBj : ∀ i, Module.Finite (O i) (Bj i)]

  g_split : ∀ k, (placesOver H.E (H.g k)).ncard = Module.finrank ℚ H.E

  PlG : Fin 2 → Type
  [finPlG : ∀ k, Fintype (PlG k)]
  card_PlG : ∀ k, Fintype.card (PlG k) = R.f

  lab : ∀ k, what₂.FT → PlG k → Polynomial (ZMod (H.g k))
  lab_monic : ∀ k σ v, (lab k σ v).Monic ∧ (lab k σ v).natDegree = R.r

  chiT : ∀ k, PlG k → Fin R.m → (ZMod (H.g k))ˣ

  restN_card_levelGroup_eq : what₂.restRowsFiniteGroupCard = ∏ k : Fin 2, (Nat.card (GL (Fin R.r) (ZMod (H.g k)))) ^ R.f
attribute [instance] NData.instOm NData.algOm NData.acOm NData.lPrime NData.instO NData.domO
  NData.dvrO NData.algO NData.finO NData.topO NData.trO NData.finX NData.neX NData.acgMt
  NData.modMt NData.freeMt NData.finMt NData.acgBj NData.modBj NData.freeBj NData.finBj
  NData.finPlG
namespace NData
variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂)
def Bj_rank : Prop := ∀ i, Module.finrank (N.O i) (N.Bj i) = Module.finrank ℂ (what₂.Mj (N.j i))
def ShaFin : Prop := ∀ (p : ℕ) [Fact p.Prime] (e : ℕ), 0 < e → e < R.t →
  Formalism.GaloisCohomology.shaLen (N.ldat p) (e : ℤ) ≠ ⊤
def ShaFinOdd : Prop := ∀ (p : ℕ) [Fact p.Prime] (e : ℕ), p ≠ 2 → 0 < e → e < R.t →
  Formalism.GaloisCohomology.shaLen (N.ldat p) (e : ℤ) ≠ ⊤
def ShaFinTwo : Prop := ∀ (e : ℕ), 0 < e → e < R.t → Formalism.GaloisCohomology.shaLen (N.ldat 2) (e : ℤ) ≠ ⊤
def EigSpan : Prop := ∀ i, ⨆ x, heckeEig (N.T i) (N.act i) x = ⊤
def ZgoodSub : Prop := ∀ i, N.Zgood i ⊆ N.Z i
def LocsCover : Prop := ∀ j' w', 1 ≤ j' → j' ≤ R.m → what₂.muAt w' ≠ what₂.mu0 →
  ∑ i ∈ N.locs j' w', Module.finrank (N.O i) (N.Mt i) =
    Module.finrank what₂.LL (what₂.MtL (what₂.muTw w') j')
def MtIn (i : N.Loc) : Submodule (N.O i) (TensorProduct (N.O i) (FractionRing (N.O i)) (N.Mt i)) :=
  LinearMap.range (TensorProduct.mk (N.O i) (FractionRing (N.O i)) (N.Mt i) 1)
def eigSum (i : N.Loc) (Y : Set (N.X i)) :
    Submodule (FractionRing (N.O i)) (TensorProduct (N.O i) (FractionRing (N.O i)) (N.Mt i)) :=
  ⨆ x ∈ Y, heckeEig (N.T i) (N.act i) x
def MtUp (i : N.Loc) : Submodule (N.O i) (TensorProduct (N.O i) (FractionRing (N.O i)) (N.Mt i)) :=
  (N.eigSum i ↑(N.Zgood i)).restrictScalars (N.O i) ⊓
    (N.MtIn i ⊔ (N.eigSum i (↑(N.Zgood i))ᶜ).restrictScalars (N.O i))
def MtLow (i : N.Loc) : Submodule (N.O i) (TensorProduct (N.O i) (FractionRing (N.O i)) (N.Mt i)) :=
  N.MtIn i ⊓ (N.eigSum i ↑(N.Zgood i)).restrictScalars (N.O i)
def etaLoc (i : N.Loc) : ℚ :=
  lenUnit (O := N.O i) (N.l i) (↥(N.MtUp i) ⧸ (N.MtLow i).comap (N.MtUp i).subtype)
def cc (i : N.Loc) : Ideal (N.T i) := ccIdeal (N.T i) (N.Z i)
def vcc (i : N.Loc) (π : N.X i) : ℚ :=
  lenUnit (O := N.O i) (N.l i) (N.O i ⧸ ccAt (N.T i) (N.Z i) π)
def mult (i : N.Loc) (π : N.X i) : ℕ := heckeMult (N.T i) (N.act i) π
def zeta (i : N.Loc) (v : HeightOneSpectrum (𝓞 H.E)) : N.O i :=
  ((N.chi i 1 (N.gam0 i v) : (N.O i)ˣ) : N.O i)
def vdel (i : N.Loc) : ℚ := ∑ k ∈ Finset.Ioo 0 R.t, ((N.s0 i : ℚ) + padicValNat (N.l i) k)
def goodRow (σ : what₂.FT) : Prop :=
  ∀ k, haveI : Fact (H.g k).Prime := ⟨H.g_prime k⟩
    Formalism.CyclotomicNorms.IsGood R.r (H.g k) (N.lab k σ) (N.chiT k) ∧
    Formalism.CyclotomicNorms.IsGood R.r (H.g k) (N.lab k σ) (fun v j => (N.chiT k v j)⁻¹)
end NData
def IsCMConjOm (E Ω : Type) [Field E] [Field Ω] [Algebra E Ω] (c : Ω ≃+* Ω) : Prop :=
  (∃ j : Ω →+* ℂ, ∀ x, j (c x) = starRingEnd ℂ (j x)) ∧
    ∀ x : E, ∃ y : E, c (algebraMap E Ω x) = algebraMap E Ω y
def AntiHom {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω] {A : Type} [CommGroup A]
    (c : Ω ≃+* Ω) (φ : G E Ω →* A) : Prop :=
  ∀ g g' : G E Ω, (∀ x, g' x = c (g (c.symm x))) → φ g' = (φ g)⁻¹
def RamExactly {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] {A : Type} [Group A]
    (φ : G E Ω →* A) (Q : Set (HeightOneSpectrum (𝓞 E))) : Prop :=
  ∀ v : HeightOneSpectrum (𝓞 E), ∀ A : ValuationSubring Ω, IsPlaceOver A v →
    ((∃ σ ∈ Ine (F := E) A, φ σ ≠ 1) ↔ v ∈ Q)
set_option synthInstance.maxHeartbeats 400000 in

structure NTw (R : Ranks) (H : Host R) (what₂ : Rows.Data R) [NumberField what₂.LL] [StarRing what₂.LL]
    (LL0 : IntermediateField ℚ what₂.LL) (N : NData R H what₂) where

  cc : N.Om ≃+* N.Om
  cc_cm : IsCMConjOm H.E N.Om cc

  Tw : Type
  l : Tw → ℕ
  [lPrime : ∀ i, Fact (l i).Prime]

  O0 : Tw → Type
  [crO0 : ∀ i, CommRing (O0 i)]
  [twistBaseCoefficientRing_isDomain : ∀ i, IsDomain (O0 i)]
  [twistBaseCoefficientRing_isDVR : ∀ i, IsDiscreteValuationRing (O0 i)]
  [algO0 : ∀ i, Algebra ℤ_[l i] (O0 i)]
  [twistBaseCoefficientRing_finite_padic : ∀ i, Module.Finite ℤ_[l i] (O0 i)]
  twistBaseCoefficientRing_residueField_finite : ∀ i, Finite (IsLocalRing.ResidueField (O0 i))
  [topO0 : ∀ i, TopologicalSpace (O0 i)]
  [twistBaseCoefficientRing_topologicalRing : ∀ i, IsTopologicalRing (O0 i)]
  twistBaseCoefficientRing_isAdic : ∀ i, IsAdic (IsLocalRing.maximalIdeal (O0 i))

  emb0 : ∀ i, LL0 →+* FractionRing (O0 i)
  emb0b : ∀ i, LL0 →+* FractionRing (O0 i)
  restX_coefficientEmbedding_conj : ∀ i (x y : LL0), (y : what₂.LL) = star (x : what₂.LL) → emb0b i x = emb0 i y

  O : Tw → Type
  [crO : ∀ i, CommRing (O i)]
  [domO : ∀ i, IsDomain (O i)]
  [dvrO : ∀ i, IsDiscreteValuationRing (O i)]
  [algO : ∀ i, Algebra (O0 i) (O i)]
  O_inj : ∀ i, Function.Injective (algebraMap (O0 i) (O i))

  O_l : ∀ i, ((l i : ℕ) : O i) ∈ IsLocalRing.maximalIdeal (O i)
  [topO : ∀ i, TopologicalSpace (O i)]
  [trO : ∀ i, IsTopologicalRing (O i)]
  O_adic : ∀ i, IsAdic (IsLocalRing.maximalIdeal (O i))
  resO_ac : ∀ i, IsAlgClosed (IsLocalRing.ResidueField (O i))
  O_complete : ∀ i, IsAdicComplete (IsLocalRing.maximalIdeal (O i)) (O i)

  Ok : Tw → ℕ → Type
  [crOk : ∀ i k, CommRing (Ok i k)]
  [domOk : ∀ i k, IsDomain (Ok i k)]
  [dvrOk : ∀ i k, IsDiscreteValuationRing (Ok i k)]
  [algOk : ∀ i k, Algebra (O i) (Ok i k)]
  Ok_inj : ∀ i k, Function.Injective (algebraMap (O i) (Ok i k))
  Ok_fin : ∀ i k, Module.Finite (O i) (Ok i k)
  zk : ∀ i k, (Ok i k)ˣ
  zk_prim : ∀ i k, IsPrimitiveRoot ((zk i k : Ok i k)) (l i ^ k)

  Ok_gen : ∀ i k (x : FractionRing (Ok i k)), ∃ p : Polynomial (O i), ∃ d : O i, d ≠ 0 ∧
    x * algebraMap (Ok i k) (FractionRing (Ok i k)) (algebraMap (O i) (Ok i k) d) =
      algebraMap (Ok i k) (FractionRing (Ok i k)) (Polynomial.aeval (zk i k : Ok i k) p)

  pD : Tw → Finset (HeightOneSpectrum (𝓞 H.E))
  pD_eq : ∀ i, (pD i : Set (HeightOneSpectrum (𝓞 H.E))) =
    placesOver H.E (if l i = H.pde then H.pde' else H.pde)
  delta : ∀ i, G H.E N.Om →* (O0 i)ˣ

  delta_open : ∀ i, IsOpen ((delta i).ker : Set (G H.E N.Om))
  delta_anti : ∀ i, AntiHom cc (delta i)
  delta_ram : ∀ i, RamExactly (delta i) ↑(pD i)
  delta_15 : ∀ i, ∀ v ∈ pD i, ∀ A : ValuationSubring N.Om, IsPlaceOver A v →
    Nat.card ((Ine (F := H.E) A).map (delta i)) = 15
  delta_tame : ∀ i, ∀ v ∈ pD i, Ideal.absNorm v.asIdeal % 15 = 1

  chi1 : ∀ i, ℕ → Bool → (G H.E N.Om →* (O0 i)ˣ)
  twistCharacterFamily_continuous : ∀ i j b, Continuous (fun g => ((chi1 i j b g : (O0 i)ˣ) : O0 i))

  twistCharacterFamily_unramified : ∀ i j b v, v ∉ placesOver H.E (l i) → (∀ k, v ∉ placesOver H.E (H.g k)) → v ∉ pD i →
    ∀ A : ValuationSubring N.Om, IsPlaceOver A v → ∀ σ ∈ Ine (F := H.E) A, chi1 i j b σ = 1
  twistCharacterFamily_at_auxiliaryPlaces : ∀ i j b, ∀ v ∈ pD i, ∀ A : ValuationSubring N.Om, IsPlaceOver A v →
    ∀ σ ∈ Ine (F := H.E) A, chi1 i j b σ = if b then delta i σ else (delta i σ)⁻¹
  twistCharacterFamily_tame : ∀ i j b k v, v ∈ placesOver H.E (H.g k) → v ∉ placesOver H.E (l i) →
    ∀ A : ValuationSubring N.Om, IsPlaceOver A v → ∀ σ ∈ Ine (F := H.E) A,
      chi1 i j b σ ^ (H.g k - 1) = 1

  Sig : Tw → Type
  [finSig : ∀ i, Fintype (Sig i)]
  jS : ∀ i, Sig i → ℕ
  jS_range : ∀ i s, 1 ≤ jS i s ∧ jS i s ≤ R.m
  side : ∀ i, Sig i → Bool
  rhoS : ∀ i, Sig i → (G H.E N.Om →* GL (Fin R.r) (O0 i))
  rhoS_cont : ∀ i s, Continuous (fun g => ((rhoS i s g : GL (Fin R.r) (O0 i)) :
    Matrix (Fin R.r) (Fin R.r) (O0 i)))

  S0 : Tw → Finset (HeightOneSpectrum (𝓞 H.E))
  twistExcludedPlaces_contains_residueChar : ∀ i, placesOver H.E (l i) ⊆ ↑(S0 i)
  placesOver_subset_exceptional : ∀ i k, placesOver H.E (H.g k) ⊆ ↑(S0 i)
  primes_subset_exceptional : ∀ i, pD i ⊆ S0 i

  B : Tw → ℕ → Bool → Type
  [acgB : ∀ i j b, AddCommGroup (B i j b)]
  [modB : ∀ i j b, Module (O i) (B i j b)]
  [freeB : ∀ i j b, Module.Free (O i) (B i j b)]
  [finB : ∀ i j b, Module.Finite (O i) (B i j b)]
  Theta : ∀ i j b, Submodule (O i) (B i j b)

  ThetaPsi : ∀ i j b k, Finset (HeightOneSpectrum (𝓞 H.E)) → (G H.E N.Om →* (Ok i k)ˣ) →
    Submodule (Ok i k) (TensorProduct (O i) (Ok i k) (B i j b))
  ThetaPsi_one : ∀ i j b k, ThetaPsi i j b k ∅ 1 = (Theta i j b).baseChange (Ok i k)

  hk : ∀ i j b, ℕ → HeightOneSpectrum (𝓞 H.E) → Module.End (O i) (B i j b)

  hk_zero : ∀ i j b P, hk i j b 0 P = 1
  hEig : ∀ i, Sig i → ℕ → HeightOneSpectrum (𝓞 H.E) → O i

  abelian₂ : Tw → Type
  [finLam : ∀ i, Fintype (abelian₂ i)]
  jL : ∀ i, abelian₂ i → ℕ
  sideL : ∀ i, abelian₂ i → Bool
  s2 : ∀ i, abelian₂ i → ℤ
  jL_range : ∀ i lam, 1 ≤ jL i lam ∧ jL i lam ≤ R.m

  lamG : ∀ i, abelian₂ i → (G H.E N.Om →* (O i)ˣ)
  lamG_cont : ∀ i lam, Continuous (fun g => ((lamG i lam g : (O i)ˣ) : O i))
  lamG_unr : ∀ i lam v, v ∉ S0 i → ∀ A : ValuationSubring N.Om, IsPlaceOver A v →
    ∀ σ ∈ Ine (F := H.E) A, lamG i lam σ = 1
  lamG_pD : ∀ i lam, ∀ v ∈ pD i, ∀ A : ValuationSubring N.Om, IsPlaceOver A v →
    ∀ σ ∈ Ine (F := H.E) A, ∃ n : ℕ,
      (lamG i lam σ * (Units.map (algebraMap (O0 i) (O i)).toMonoidHom
        (if sideL i lam then delta i σ else (delta i σ)⁻¹))⁻¹) ^ (Ideal.absNorm v.asIdeal ^ n) = 1

  lamG_anti : ∀ i lam, AntiHom cc (lamG i lam)
  Xv : ∀ i, abelian₂ i → HeightOneSpectrum (𝓞 H.E) → O i

  Xv_def : ∀ i lam P, P ∉ S0 i → ∀ σ : G H.E N.Om, IsFrob (F := H.E) (N.plOm.1 P) (normV P) σ →
    Xv i lam P = ((lamG i lam σ : (O i)ˣ) : O i)
  qs : ∀ i, abelian₂ i → HeightOneSpectrum (𝓞 H.E) → FractionRing (O i)
  qs_sq : ∀ i lam P, P ∉ S0 i → qs i lam P ^ 2 = ((Ideal.absNorm P.asIdeal : ℕ) : FractionRing (O i)) ^ (-(s2 i lam))

  qs_conj : ∀ i lam P P', IsConjPl H P P' → qs i lam P = qs i lam P'

  RCG : Tw → Finset (HeightOneSpectrum (𝓞 H.E)) → Type
  [grpRCG : ∀ i Q, CommGroup (RCG i Q)]
  [finRCG : ∀ i Q, Fintype (RCG i Q)]
  RCG_l : ∀ i Q (x : RCG i Q), ∃ n : ℕ, x ^ (l i ^ n) = 1
  art : ∀ i Q, G H.E N.Om →* RCG i Q
  art_surj : ∀ i Q, Function.Surjective (art i Q)
  art_cont : ∀ i Q, IsOpen ((art i Q).ker : Set (G H.E N.Om))
  art_anti : ∀ i Q, AntiHom cc (art i Q)
  art_unr : ∀ i Q v, v ∉ Q → ∀ A : ValuationSubring N.Om, IsPlaceOver A v →
    ∀ σ ∈ Ine (F := H.E) A, art i Q σ = 1

  art_univ : ∀ i Q, (∀ v ∈ Q, v ∉ placesOver H.E (l i)) → ∀ (A' : Type) [CommGroup A'] [Finite A'],
    (∀ x : A', ∃ n : ℕ, x ^ (l i ^ n) = 1) → ∀ φ : G H.E N.Om →* A',
    IsOpen (φ.ker : Set (G H.E N.Om)) → AntiHom cc φ →
    (∀ v, v ∉ Q → ∀ A : ValuationSubring N.Om, IsPlaceOver A v → ∀ σ ∈ Ine (F := H.E) A, φ σ = 1) →
    ∃ f : RCG i Q →* A', f.comp (art i Q) = φ
  res : ∀ i (Q Q' : Finset (HeightOneSpectrum (𝓞 H.E))), Q' ⊆ Q → (RCG i Q →* RCG i Q')
  res_art : ∀ i Q Q' (h : Q' ⊆ Q), (res i Q Q' h).comp (art i Q) = art i Q'

  th : ∀ i Q, abelian₂ i → RCG i Q → FractionRing (O i)

  twOf : N.Loc → Tw
  twSide : N.Loc → Bool
  twOf_l : ∀ a, l (twOf a) = N.l a
  twist₂ : ∀ a, O0 (twOf a) →+* N.O a
  twO_emb : ∀ a (x : LL0) (y : O0 (twOf a)),
    algebraMap (O0 (twOf a)) (FractionRing (O0 (twOf a))) y =
      (if twSide a then emb0 (twOf a) else emb0b (twOf a)) x →
    N.embK a (x : what₂.LL) = algebraMap (N.O a) (FractionRing (N.O a)) (twist₂ a y)

  psiL : ∀ a : N.Loc, G H.E N.Om →* (N.O a)ˣ
  psiL_ord : ∀ a g, ∃ n : ℕ, psiL a g ^ (N.l a ^ n) = 1
  psiL_open : ∀ a, IsOpen ((psiL a).ker : Set (G H.E N.Om))
  psiL_anti : ∀ a, AntiHom cc (psiL a)
  psiL_ram : ∀ a, RamExactly (psiL a) ↑(N.Q a)
  psiL_l : ∀ a v, v ∈ placesOver H.E (N.l a) → ∀ A : ValuationSubring N.Om, IsPlaceOver A v →
    ∀ σ ∈ Dec (F := H.E) A, psiL a σ = 1

  chi_tw : ∀ a, N.chi a 1 =
    (Units.map (twist₂ a).toMonoidHom).comp (chi1 (twOf a) (N.j a) (twSide a)) * psiL a
attribute [instance] NTw.lPrime NTw.topO0 NTw.twistBaseCoefficientRing_topologicalRing NTw.topO NTw.trO NTw.crO0 NTw.twistBaseCoefficientRing_isDomain NTw.twistBaseCoefficientRing_isDVR NTw.algO0 NTw.twistBaseCoefficientRing_finite_padic NTw.crO NTw.domO
  NTw.dvrO NTw.algO NTw.crOk NTw.domOk NTw.dvrOk NTw.algOk NTw.finSig NTw.acgB NTw.modB
  NTw.freeB NTw.finB NTw.finLam NTw.grpRCG NTw.finRCG
namespace NTw
variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} [NumberField what₂.LL] [StarRing what₂.LL]
  {LL0 : IntermediateField ℚ what₂.LL} {N : NData R H what₂} (X : NTw R H what₂ LL0 N)
def sig_eig : Prop := ∀ i s, ∃ x : TensorProduct (X.O i) (FractionRing (X.O i)) (X.B i (X.jS i s) (X.side i s)), x ≠ 0 ∧
    ∀ k P, 1 ≤ k → k ≤ R.r → IsSplitPl H P → P ∉ X.S0 i →
      ((X.hk i (X.jS i s) (X.side i s) k P).lTensor (FractionRing (X.O i))) x =
      algebraMap (X.O i) (FractionRing (X.O i)) (X.hEig i s k P) • x
def sig_allB : Prop := ∀ i j b (x : TensorProduct (X.O i) (FractionRing (X.O i)) (X.B i j b))
      (ev : ℕ → HeightOneSpectrum (𝓞 H.E) → FractionRing (X.O i)), x ≠ 0 →
    (∀ k P, 1 ≤ k → k ≤ R.r → IsSplitPl H P → P ∉ X.S0 i → ((X.hk i j b k P).lTensor (FractionRing (X.O i))) x = ev k P • x) →
    ∃ s : X.Sig i, X.jS i s = j ∧ X.side i s = b ∧
      ∀ k P, 1 ≤ k → k ≤ R.r → IsSplitPl H P → P ∉ X.S0 i →
        algebraMap (X.O i) (FractionRing (X.O i)) (X.hEig i s k P) = ev k P
def TwCover : Prop := ∀ p : ℕ, p.Prime → ∀ w : HeightOneSpectrum (𝓞 ↥LL0), ((p : ℕ) : 𝓞 ↥LL0) ∈ w.asIdeal →
  ∃ i, X.l i = p ∧ ∀ x : 𝓞 ↥LL0, x ∈ w.asIdeal ↔
    ∃ y ∈ IsLocalRing.maximalIdeal (X.O0 i),
      algebraMap (X.O0 i) (FractionRing (X.O0 i)) y = X.emb0 i (x : ↥LL0)
def NonzeroIndexPlace (i : X.Tw) : Prop :=
  ∃ w' : what₂.places.Pl, what₂.muAt w' ≠ what₂.mu0 ∧ ∀ x : 𝓞 ↥LL0,
    (∃ y ∈ IsLocalRing.maximalIdeal (X.O0 i),
      algebraMap (X.O0 i) (FractionRing (X.O0 i)) y = X.emb0 i (x : ↥LL0)) ↔
    0 < what₂.places.val w' ((x : ↥LL0) : what₂.LL)
def CoverAtSplitPlaces : Prop := ∀ p : ℕ, p.Prime → ∀ w : HeightOneSpectrum (𝓞 ↥LL0), ((p : ℕ) : 𝓞 ↥LL0) ∈ w.asIdeal →
  (∃ w' : what₂.places.Pl, what₂.muAt w' ≠ what₂.mu0 ∧
    ∀ x : 𝓞 ↥LL0, x ∈ w.asIdeal ↔ 0 < what₂.places.val w' ((x : ↥LL0) : what₂.LL)) →
  ∃ i, X.l i = p ∧ ∀ x : 𝓞 ↥LL0, x ∈ w.asIdeal ↔
    ∃ y ∈ IsLocalRing.maximalIdeal (X.O0 i),
      algebraMap (X.O0 i) (FractionRing (X.O0 i)) y = X.emb0 i (x : ↥LL0)
def ThetaFull : Prop :=
  ∀ i j b, Module.finrank (X.O i) (X.Theta i j b) = Module.finrank (X.O i) (X.B i j b)
def sigEig (i : X.Tw) (s : X.Sig i) : Submodule (FractionRing (X.O i))
    (TensorProduct (X.O i) (FractionRing (X.O i)) (X.B i (X.jS i s) (X.side i s))) :=
  ⨅ (k : ℕ) (P : HeightOneSpectrum (𝓞 H.E)) (_ : 1 ≤ k ∧ k ≤ R.r ∧ IsSplitPl H P ∧ P ∉ X.S0 i),
    Module.End.eigenspace ((X.hk i (X.jS i s) (X.side i s) k P).baseChange (FractionRing (X.O i)))
      (algebraMap (X.O i) (FractionRing (X.O i)) (X.hEig i s k P))
def SigSpan : Prop := ∀ i j b, 1 ≤ j → j ≤ R.m →
  Submodule.span (FractionRing (X.O i))
    {x : TensorProduct (X.O i) (FractionRing (X.O i)) (X.B i j b) | ∃ s : X.Sig i, X.jS i s = j ∧
      X.side i s = b ∧ ∀ k P, 1 ≤ k → k ≤ R.r → IsSplitPl H P → P ∉ X.S0 i →
        ((X.hk i j b k P).baseChange (FractionRing (X.O i))) x =
          algebraMap (X.O i) (FractionRing (X.O i)) (X.hEig i s k P) • x} = ⊤
end NTw
section Aut
open Polynomial
abbrev PlE {R : Ranks} (H : Host R) : Type := HeightOneSpectrum (𝓞 H.E)
structure Part (CG : ℕ → Type) where
  a : ℕ
  π : CG a
  d : ℕ
def heckePol {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (i : N.Loc)
    (x : N.X i) (w : PlE H) : Polynomial (N.O i) :=
  X ^ R.nV + ∑ k ∈ Finset.Icc 1 R.nV,
    C ((-1 : N.O i) ^ k * ((normV w : ℕ) : N.O i) ^ (k * (k - 1) / 2) *
      ((N.hT i w k : N.X i → N.O i) x)) * X ^ (R.nV - k)
def SplitOut {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (i : N.Loc)
    (w : PlE H) : Prop :=
  IsSplitPl H w ∧ w ∉ placesOver H.E (N.l i) ∧ w ∉ N.S i ∧ w ∉ N.Q i
set_option synthInstance.maxHeartbeats 400000 in

structure NAut {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) where

  iotaQ : ∀ i, FractionRing (N.O i) →+* Qbar (N.l i)
  iotaQC : ∀ i, Qbar (N.l i) ≃+* ℂ
  iota_LL : ∀ i x, iotaQC i (iotaQ i (N.embK i x)) = what₂.embLL x

  iotaQ_alg : ∀ i (z : ℤ_[N.l i]), iotaQ i (algebraMap (N.O i) (FractionRing (N.O i))
    (algebraMap ℤ_[N.l i] (N.O i) z)) = algebraMap ℚ_[N.l i] (Qbar (N.l i)) (z : ℚ_[N.l i])

  LP : PlE H → Type
  lpDim : ∀ {w}, LP w → ℕ
  lpZero : ∀ w, LP w
  lpSum : ∀ {w}, LP w → LP w → LP w

  lpTw : ∀ {w}, LP w → ℝ → LP w

  lpChar : ∀ {w}, LP w → LP w → LP w

  lpUnr : ∀ w, Multiset ℂ → LP w

  mono0 : ∀ {w}, LP w → Prop

  unr : ∀ {w}, LP w → Prop

  frobEig : ∀ {w}, LP w → Multiset ℂ
  tempered : ∀ {w}, LP w → Prop

  inePol : ∀ {w}, LP w → G H.E N.Om → Polynomial ℂ

  items₂ : ∀ (k : Fin 2) (w : PlE H), LP w → Polynomial (ZMod (H.g k))
  lpDim_zero : ∀ w, lpDim (lpZero w) = 0
  lpDim_sum : ∀ {w} (a b : LP w), lpDim (lpSum a b) = lpDim a + lpDim b
  lpDim_tw : ∀ {w} (a : LP w) (s : ℝ), lpDim (lpTw a s) = lpDim a
  lpUnr_spec : ∀ w (m : Multiset ℂ), (0 : ℂ) ∉ m → unr (lpUnr w m) ∧ frobEig (lpUnr w m) = m ∧
    lpDim (lpUnr w m) = Multiset.card m

  unr_sum : ∀ {w} (a b : LP w), unr (lpSum a b) ↔ unr a ∧ unr b
  monomial_sum_iff : ∀ {w} (a b : LP w), mono0 (lpSum a b) ↔ mono0 a ∧ mono0 b
  frobEig_sum : ∀ {w} (a b : LP w), unr a → unr b → frobEig (lpSum a b) = frobEig a + frobEig b
  unr_tw : ∀ {w} (a : LP w) (s : ℝ), unr (lpTw a s) ↔ unr a
  monomial_twist_iff : ∀ {w} (a : LP w) (s : ℝ), mono0 (lpTw a s) ↔ mono0 a
  frobEig_tw : ∀ {w} (a : LP w) (s : ℝ), unr a →
    frobEig (lpTw a s) = (frobEig a).map (· * ((normV w : ℕ) : ℂ) ^ ((s : ℝ) : ℂ))
  frobEig_char : ∀ {w} (a χ : LP w) (c : ℂ), unr a → unr χ → lpDim χ = 1 → frobEig χ = {c} →
    frobEig (lpChar a χ) = (frobEig a).map (· * c)

  lpDim_char : ∀ {w} (a χ : LP w), lpDim χ = 1 → lpDim (lpChar a χ) = lpDim a
  unr_char : ∀ {w} (a χ : LP w), lpDim χ = 1 → unr a → unr χ → unr (lpChar a χ)
  monomial_char_iff : ∀ {w} (a χ : LP w), lpDim χ = 1 → (mono0 (lpChar a χ) ↔ mono0 a)

  lpZero_unr : ∀ w, unr (lpZero w)
  frobEig_zero : ∀ w, frobEig (lpZero w) = 0
  lpSum_zero : ∀ {w} (a : LP w), lpSum a (lpZero w) = a
  lpSum_comm : ∀ {w} (a b : LP w), lpSum a b = lpSum b a
  lpSum_assoc : ∀ {w} (a b c : LP w), lpSum (lpSum a b) c = lpSum a (lpSum b c)
  lpTw_zero : ∀ {w} (a : LP w), lpTw a 0 = a
  lpTw_add : ∀ {w} (a : LP w) (s t : ℝ), lpTw (lpTw a s) t = lpTw a (s + t)
  lpTw_sum : ∀ {w} (a b : LP w) (s : ℝ), lpTw (lpSum a b) s = lpSum (lpTw a s) (lpTw b s)
  unr_eq_lpUnr : ∀ {w} (a : LP w), unr a → a = lpUnr w (frobEig a)
  unr_mono0 : ∀ {w} (a : LP w), unr a → mono0 a
  frobEig_ne_zero : ∀ {w} (a : LP w), unr a → (0 : ℂ) ∉ frobEig a
  frobEig_card : ∀ {w} (a : LP w), unr a → Multiset.card (frobEig a) = lpDim a

  tempered_unr : ∀ {w} (a : LP w), unr a → (tempered a ↔ ∀ α ∈ frobEig a, ‖α‖ = 1)

  inePol_sum : ∀ {w} (a b : LP w) σ, inePol (lpSum a b) σ = inePol a σ * inePol b σ
  inePol_tw : ∀ {w} (a : LP w) (s : ℝ), ∀ σ ∈ Ine (F := H.E) (N.plOm.1 w), inePol (lpTw a s) σ = inePol a σ
  unr_iff_ine : ∀ {w} (a : LP w), unr a ↔ mono0 a ∧
    ∀ σ ∈ Ine (F := H.E) (N.plOm.1 w), inePol a σ = (X - 1) ^ lpDim a

  inertiaCharpoly_zero : ∀ k w, items₂ k w (lpZero w) = 1
  inertiaCharpoly_add : ∀ k w (a b : LP w), items₂ k w (lpSum a b) = items₂ k w a * items₂ k w b

  CG : ℕ → Type

  csd : ∀ {a}, CG a → Prop

  ralg : ∀ {a}, CG a → Prop

  locG : ∀ {a}, CG a → ∀ w, LP w
  locG_dim : ∀ {a} (π : CG a) w, lpDim (locG π w) = a

  locG_unr_ae : ∀ {a} (π : CG a), ∀ᶠ w in Filter.cofinite, unr (locG π w)

  tw : ∀ {a}, CG a → CG 1 → CG a
  locG_tw : ∀ {a} (π : CG a) (χ : CG 1) w, locG (tw π χ) w = lpChar (locG π w) (locG χ w)

  infG : ∀ {a}, CG a → (H.E →+* ℂ) → Multiset ℂ
  infG_card : ∀ {a} (π : CG a) τ, Multiset.card (infG π τ) = a

  ralg_def : ∀ {a} (π : CG a), ralg π ↔ ∀ τ, (infG π τ).Nodup ∧
    ∀ z ∈ infG π τ, ∃ n : ℤ, z = (n : ℂ) + ((a : ℂ) - 1) / 2

  infG_tw : ∀ {a} (π : CG a) (χ : CG 1) τ (s : ℂ), infG χ τ = {s} → infG (tw π χ) τ = (infG π τ).map (· + s)
  csd_tw : ∀ {a} (π : CG a) (χ : CG 1), csd χ → csd π → csd (tw π χ)

  csd_unr : ∀ {a} (π : CG a) w w', csd π → IsConjPl H w w' → unr (locG π w) →
    unr (locG π w') ∧ frobEig (locG π w') = (frobEig (locG π w)).map (·⁻¹)

  muC : N.Loc → CG 1
  etaT : CG 1
  etaTinv : CG 1

  etaT_unr : ∀ w, unr (locG etaT w)
  etaT_inert : ∀ w, ¬ IsSplitPl H w → frobEig (locG etaT w) = {-1}
  etaTinv_def : ∀ w, unr (locG etaTinv w) ∧ frobEig (locG etaTinv w) = (frobEig (locG etaT w)).map (·⁻¹)

  etaT_split : ∀ w w', IsSplitPl H w → IsConjPl H w w' → ∀ a b : ℂ, frobEig (locG etaT w) = {a} →
    frobEig (locG etaT w') = {b} → a * b = 1

  muC_csd : ∀ i, csd (muC i)

  AV : N.Loc → Type
  [finAV : ∀ i, Finite (AV i)]

  ptV : ∀ i, AV i → Option (N.X i)

  typeV : ∀ i, AV i → Submodule ℂ (what₂.Mt (N.mu i) (N.j i))
  typeV_ne : ∀ i P, typeV i P ≠ ⊥
  typeV_indep : ∀ i, iSupIndep (typeV i)
  typeV_top : ∀ i, ⨆ P, typeV i P = ⊤

  pt_surj : ∀ i x, ∃ P, ptV i P = some x
  eig_dim : ∀ i x, N.mult i x = Module.finrank ℂ ↥(⨆ P ∈ {P | ptV i P = some x}, typeV i P)

  locV : ∀ i, AV i → ∀ w, LP w
  satV : ∀ i, AV i → PlE H → Multiset ℂ

  locV_unr : ∀ i P w, IsSplitPl H w → w ∉ N.Q i → (∀ k, w ∉ placesOver H.E (H.g k)) →
    w ∉ placesOver H.E (if N.l i = H.pde then H.pde' else H.pde) → unr (locV i P w)

  pt_loc : ∀ i P x, ptV i P = some x → ∀ w, SplitOut N i w →
    (heckePol N i x w).map (((iotaQC i).toRingHom.comp (iotaQ i)).comp
      (algebraMap (N.O i) (FractionRing (N.O i)))) =
    ((frobEig (lpTw (locV i P w) ((1 - (R.nV : ℝ)) / 2))).map fun α => X - C α).prod

  infWt : N.Loc → (H.E →+* ℂ) → Multiset ℂ

  locW : ∀ i : N.Loc, what₂.FT → ∀ w, LP w
  satW : ∀ i : N.Loc, what₂.FT → PlE H → Multiset ℂ

  plGw : ∀ k, N.PlG k → PlE H
  plGw_over : ∀ k v, plGw k v ∈ placesOver H.E (H.g k)

  plGw_inj : ∀ k, Function.Injective (plGw k)
  plGw_nconj : ∀ k v v', ¬ IsConjPl H (plGw k v) (plGw k v')

  lab_loc : ∀ i k σ v, N.lab k σ v = items₂ k (plGw k v) (locW i σ (plGw k v))

  wdOf : ∀ i {a}, (G H.E N.Om →* GL (Fin a) (Qbar (N.l i))) → ∀ w, LP w

  wdOf_dim : ∀ i {a} (r : G H.E N.Om →* GL (Fin a) (Qbar (N.l i))) w, lpDim (wdOf i r w) = a
  wdOf_unr : ∀ i {a} (r : G H.E N.Om →* GL (Fin a) (Qbar (N.l i))) w, w ∉ placesOver H.E (N.l i) →
    Continuous (fun g => ((r g : GL (Fin a) (Qbar (N.l i))) : Matrix (Fin a) (Fin a) (Qbar (N.l i)))) →
    (unr (wdOf i r w) ↔ ∀ σ ∈ Ine (F := H.E) (N.plOm.1 w), r σ = 1)
  wdOf_frob : ∀ i {a} (r : G H.E N.Om →* GL (Fin a) (Qbar (N.l i))) w, w ∉ placesOver H.E (N.l i) →
    Continuous (fun g => ((r g : GL (Fin a) (Qbar (N.l i))) : Matrix (Fin a) (Fin a) (Qbar (N.l i)))) →
    unr (wdOf i r w) → ∀ (B : ValuationSubring N.Om) (σ : G H.E N.Om), IsPlaceOver (F := H.E) B w →
    IsFrob (F := H.E) B (normV w) σ →
    ((r σ : GL (Fin a) (Qbar (N.l i))) : Matrix (Fin a) (Fin a) (Qbar (N.l i))).charpoly.map
        (iotaQC i).toRingHom =
      ((frobEig (wdOf i r w)).map fun α => X - C α).prod

  wdOf_ine : ∀ i {a} (r : G H.E N.Om →* GL (Fin a) (Qbar (N.l i))) w, w ∉ placesOver H.E (N.l i) →
    Continuous (fun g => ((r g : GL (Fin a) (Qbar (N.l i))) : Matrix (Fin a) (Fin a) (Qbar (N.l i)))) →
    ∀ σ ∈ Ine (F := H.E) (N.plOm.1 w),
    ((r σ : GL (Fin a) (Qbar (N.l i))) : Matrix (Fin a) (Fin a) (Qbar (N.l i))).charpoly.map
        (iotaQC i).toRingHom = inePol (wdOf i r w) σ
  wdOf_mono0 : ∀ i {a} (r : G H.E N.Om →* GL (Fin a) (Qbar (N.l i))) w, w ∉ placesOver H.E (N.l i) →
    Continuous (fun g => ((r g : GL (Fin a) (Qbar (N.l i))) : Matrix (Fin a) (Fin a) (Qbar (N.l i)))) →
    (mono0 (wdOf i r w) ↔ (r '' (Ine (F := H.E) (N.plOm.1 w) : Set (G H.E N.Om))).Finite)

  IsCrysW : ∀ i {a}, (G H.E N.Om →* GL (Fin a) (Qbar (N.l i))) → PlE H → Prop
  IsPotCrysW : ∀ i {a}, (G H.E N.Om →* GL (Fin a) (Qbar (N.l i))) → PlE H → Prop
  IsdRW : ∀ i {a}, (G H.E N.Om →* GL (Fin a) (Qbar (N.l i))) → PlE H → Prop
  jumpsW : ∀ i {a}, (G H.E N.Om →* GL (Fin a) (Qbar (N.l i))) → (H.E →+* Qbar (N.l i)) →
    Multiset ℤ

  wdOf_unrL : ∀ i {a} (r : G H.E N.Om →* GL (Fin a) (Qbar (N.l i))) w, w ∈ placesOver H.E (N.l i) →
    Continuous (fun g => ((r g : GL (Fin a) (Qbar (N.l i))) : Matrix (Fin a) (Fin a) (Qbar (N.l i)))) →
    IsdRW i r w → (unr (wdOf i r w) ↔ IsCrysW i r w)

  wdOf_mono0L : ∀ i {a} (r : G H.E N.Om →* GL (Fin a) (Qbar (N.l i))) w, w ∈ placesOver H.E (N.l i) →
    Continuous (fun g => ((r g : GL (Fin a) (Qbar (N.l i))) : Matrix (Fin a) (Fin a) (Qbar (N.l i)))) →
    IsdRW i r w → (mono0 (wdOf i r w) ↔ IsPotCrysW i r w)

  jumpsInf : ∀ i {a}, CG a → (H.E →+* Qbar (N.l i)) → Multiset ℤ

  locAutHodgeTateWeightsLevelZero : ∀ i, (H.E →+* Qbar (N.l i)) → Multiset ℤ

  jumpsInf_def : ∀ i {a} (π : CG a) (τ : H.E →+* Qbar (N.l i)), ralg π →
    (jumpsInf i π τ).map (fun n : ℤ => (n : ℂ)) =
      (infG π ((iotaQC i).toRingHom.comp τ)).map (fun z => -z + ((a : ℂ) - 1) / 2)
  locAut_hodgeTateWeightsLevelZero_def : ∀ i (τ : H.E →+* Qbar (N.l i)),
    (locAutHodgeTateWeightsLevelZero i τ).map (fun n : ℤ => (n : ℂ)) =
      (infWt i ((iotaQC i).toRingHom.comp τ)).map (fun z => -z + ((R.nV : ℂ) - 1) / 2)

  chi_mu : ∀ i w, SplitOut N i w → unr (locG (tw (muC i) etaTinv) w) ∧
    ∀ (B : ValuationSubring N.Om) (σ : G H.E N.Om), IsPlaceOver (F := H.E) B w →
      IsFrob (F := H.E) B (normV w) σ →
      frobEig (lpTw (locG (tw (muC i) etaTinv) w) (((R.t : ℝ) - 1) / 2 + (1 - (R.nV : ℝ)) / 2)) =
        {(iotaQC i) (iotaQ i (algebraMap (N.O i) (FractionRing (N.O i)) ((N.chi i 1 σ : (N.O i)ˣ) : N.O i)))}

  kFbar : ∀ i, IsLocalRing.ResidueField (N.O i) →+* Formalism.CyclotomicNorms.Fbar (N.l i)
attribute [instance] NAut.finAV
end Aut
set_option synthInstance.maxHeartbeats 400000 in

structure NBC {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂} (A : NAut N) where

  AU : ℕ → Type

  multAU : ∀ j, AU j → ℕ

  sphAU : ∀ j, AU j → PlE H → Prop

  locAU : ∀ j, AU j → ∀ w : PlE H, A.LP w

  satAU : ∀ j, AU j → PlE H → Multiset ℂ
  satAU_card : ∀ j (π : AU j) w, Multiset.card (satAU j π w) = R.nV / 2

  Wt : ℕ → Type

  infW : ∀ j, Wt j → (H.E →+* ℂ) → Multiset ℂ
  infW_card : ∀ j (W : Wt j) τ, Multiset.card (infW j W τ) = R.nV

  wtAU : ∀ j, AU j → Wt j

  infW_alg : ∀ j (W : Wt j) τ, (infW j W τ).Nodup ∧
    ∀ x ∈ infW j W τ, ∃ k : ℤ, x = (k : ℂ) + ((R.nV : ℂ) - 1) / 2

  embAV : ∀ i, A.AV i → AU (N.j i)
  embAV_inj : ∀ i, Function.Injective (embAV i)
  embAV_loc : ∀ i (P : A.AV i) w, A.locV i P w = locAU (N.j i) (embAV i P) w
  embAV_sat : ∀ i (P : A.AV i) w, A.satV i P w = satAU (N.j i) (embAV i P) w
  embAV_sph : ∀ i (P : A.AV i) w, ¬ IsSplitPl H w → sphAU (N.j i) (embAV i P) w
  embAV_inf : ∀ i (P : A.AV i), A.infWt i = infW (N.j i) (wtAU (N.j i) (embAV i P))
def NBC.AU_ext {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂} {A : NAut N} (B : NBC A) : Prop :=
  ∀ j (π π' : B.AU j), (∀ w, IsSplitPl H w → B.locAU j π w = B.locAU j π' w) →
    (∀ w, ¬ IsSplitPl H w → B.sphAU j π w ∧ B.sphAU j π' w ∧
      B.satAU j π w + (B.satAU j π w).map (·⁻¹) + (if Odd R.nV then ({1} : Multiset ℂ) else 0) =
        B.satAU j π' w + (B.satAU j π' w).map (·⁻¹) + (if Odd R.nV then ({1} : Multiset ℂ) else 0)) →
    B.wtAU j π = B.wtAU j π' → π = π'
section Exp
open scoped TensorProduct
abbrev G0g {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) : Type :=
  ∀ kv : (Σ k : Fin 2, N.PlG k), GL (Fin R.r) (ZMod (H.g kv.1))
abbrev DelQM {R : Ranks} (H : Host R) (l : ℕ) (Q : Finset (PlE H)) (M : ℕ) : Type :=
  ↥Q → ZMod (l ^ M)
set_option synthInstance.maxHeartbeats 400000 in

structure NExp (R : Ranks) (H : Host R) (what₂ : Rows.Data R) [NumberField what₂.LL] [StarRing what₂.LL]
    (LL0 : IntermediateField ℚ what₂.LL) (N : NData R H what₂) (tw : NTw R H what₂ LL0 N) where

  Fm : tw.Tw → ℕ → Bool → Type
  [acgFm : ∀ i j b, AddCommGroup (Fm i j b)]
  [modFmK : ∀ i j b, Module (FractionRing (tw.O i)) (Fm i j b)]
  [modFmO : ∀ i j b, Module (tw.O i) (Fm i j b)]
  [towFm : ∀ i j b, IsScalarTower (tw.O i) (FractionRing (tw.O i)) (Fm i j b)]
  [fdFm : ∀ i j b, FiniteDimensional (FractionRing (tw.O i)) (Fm i j b)]

  actG : ∀ i j b, G0g N →* (Fm i j b ≃ₗ[FractionRing (tw.O i)] Fm i j b)

  U : Subgroup (G0g N)
  psiU : ∀ i (b : Bool), U →* (FractionRing (tw.O i))ˣ

  eAlg : ∀ i (b : Bool), MonoidAlgebra (FractionRing (tw.O i)) (G0g N)

  eLL0 : G0g N → LL0
  eAlg_def : ∀ i b (g : G0g N), (eAlg i b).coeff g =
    IsFractionRing.map (A := tw.O0 i) (B := tw.O i) (K := FractionRing (tw.O0 i))
      (L := FractionRing (tw.O i)) (tw.O_inj i) ((if b then tw.emb0 i else tw.emb0b i) (eLL0 g))
  eAlg_idem : ∀ i b, eAlg i b * eAlg i b = eAlg i b
  eAlg_central : ∀ i b x, eAlg i b * x = x * eAlg i b

  Bsup : ∀ i j b, Submodule (tw.O i) (Fm i j b)

  Dat : tw.Tw → ℕ → Bool → Type
  th : ∀ i j b, Dat i j b → Fm i j b
  lev : ∀ i j b, Dat i j b → Finset (PlE H)

  thPsi : ∀ i j b k (Q : Finset (PlE H)) (ψ : G H.E N.Om →* (tw.Ok i k)ˣ),
    Dat i j b → Set (tw.Ok i k ⊗[tw.O i] Fm i j b)

  thPsi_one : ∀ i j b k (d : Dat i j b), thPsi i j b k ∅ 1 d = {(1 : tw.Ok i k) ⊗ₜ[tw.O i] th i j b d}

  thU : ∀ i j b (Q : Finset (PlE H)) (M : ℕ), Dat i j b →
    Fm i j b ⊗[tw.O i] AddMonoidAlgebra (tw.O i) (DelQM H (tw.l i) Q M)

  twPsi : ∀ i j b k (ψ : G H.E N.Om →* (tw.Ok i k)ˣ),
    Fm i j b →ₗ[tw.O i] (tw.Ok i k ⊗[tw.O i] Fm i j b)
  twPsi_one : ∀ i j b k (f : Fm i j b), twPsi i j b k 1 f = (1 : tw.Ok i k) ⊗ₜ[tw.O i] f

  twDel : ∀ i j b (Q : Finset (PlE H)) (M : ℕ),
    Fm i j b →ₗ[tw.O i] (Fm i j b ⊗[tw.O i] AddMonoidAlgebra (tw.O i) (DelQM H (tw.l i) Q M))

  delU : ∀ i (Q : Finset (PlE H)) (M : ℕ), G H.E N.Om →* Multiplicative (DelQM H (tw.l i) Q M)
  delU_unr : ∀ i Q M v, v ∉ Q → ∀ A : ValuationSubring N.Om, IsPlaceOver A v →
    ∀ σ ∈ Ine (F := H.E) A, delU i Q M σ = 1
  delU_l : ∀ i Q M v, v ∈ placesOver H.E (tw.l i) → ∀ A : ValuationSubring N.Om, IsPlaceOver A v →
    ∀ σ ∈ Dec (F := H.E) A, delU i Q M σ = 1
  delU_anti : ∀ i Q M, AntiHom tw.cc (delU i Q M)

  delU_open : ∀ i (Q : Finset (PlE H)) (M : ℕ), IsOpen ((delU i Q M).ker : Set (G H.E N.Om))

  delU_res : ∀ i (M : ℕ) (Q' Q : Finset (PlE H)) (h : Q' ⊆ Q),
    (∀ P ∈ Q', ∀ P', IsConjPl H P P' → P' ∈ Q') → (∀ P ∈ Q, ∀ P', IsConjPl H P P' → P' ∈ Q) →
    ∀ (σ : G H.E N.Om) (P : PlE H) (hP : P ∈ Q'),
      Multiplicative.toAdd (delU i Q' M σ) ⟨P, hP⟩ = Multiplicative.toAdd (delU i Q M σ) ⟨P, h hP⟩

  delU_conj : ∀ i (Q : Finset (PlE H)) (M : ℕ) (P : PlE H) (hP : P ∈ Q) (P' : PlE H) (hP' : P' ∈ Q),
    IsConjPl H P P' → ∃ s : ℤˣ, ∀ σ : G H.E N.Om,
      Multiplicative.toAdd (delU i Q M σ) ⟨P', hP'⟩ =
        ((s : ℤ) : ZMod (tw.l i ^ M)) * Multiplicative.toAdd (delU i Q M σ) ⟨P, hP⟩

  MtV : ∀ i (j : ℕ) (b : Bool) k (Q : Finset (PlE H)) (ψ : G H.E N.Om →* (tw.Ok i k)ˣ), Type
  [acgMt : ∀ i j b k Q ψ, AddCommGroup (MtV i j b k Q ψ)]
  [modMtK : ∀ i j b k Q ψ, Module (FractionRing (tw.Ok i k)) (MtV i j b k Q ψ)]
  [modMtO : ∀ i j b k Q ψ, Module (tw.Ok i k) (MtV i j b k Q ψ)]
  [towMt : ∀ i j b k Q ψ, IsScalarTower (tw.Ok i k) (FractionRing (tw.Ok i k)) (MtV i j b k Q ψ)]
  [fdMt : ∀ i j b k Q ψ, FiniteDimensional (FractionRing (tw.Ok i k)) (MtV i j b k Q ψ)]
  MtLat : ∀ i j b k Q ψ, Submodule (tw.Ok i k) (MtV i j b k Q ψ)

  MtLat_fg : ∀ i j b k Q ψ, (MtLat i j b k Q ψ).FG
  MtLat_span : ∀ i j b k Q ψ,
    Submodule.span (FractionRing (tw.Ok i k)) (MtLat i j b k Q ψ : Set (MtV i j b k Q ψ)) = ⊤

  thP : ∀ i j b k Q ψ, MtV i j b k Q ψ →ₗ[tw.Ok i k] (tw.Ok i k ⊗[tw.O i] Fm i j b)

  hkF : ∀ i j b, ℕ → PlE H → Module.End (FractionRing (tw.O i)) (Fm i j b)

  embB : ∀ i j b, tw.B i j b →ₗ[tw.O i] Fm i j b
  embB_inj : ∀ i j b, Function.Injective (embB i j b)

  eH : ∀ i j b, Module.End (FractionRing (tw.O i)) (Fm i j b)
  eH_idem : ∀ i j b, eH i j b * eH i j b = eH i j b
attribute [instance] NExp.acgFm NExp.modFmK NExp.modFmO NExp.towFm NExp.fdFm NExp.acgMt NExp.modMtK
  NExp.modMtO NExp.towMt NExp.fdMt
namespace NExp
variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} [NumberField what₂.LL] [StarRing what₂.LL]
  {LL0 : IntermediateField ℚ what₂.LL} {N : NData R H what₂} {tw : NTw R H what₂ LL0 N}
  (Y : NExp R H what₂ LL0 N tw)
def embB_hk : Prop :=
  ∀ i j b k P, P ∉ tw.S0 i → ∀ x, Y.embB i j b (tw.hk i j b k P x) = Y.hkF i j b k P (Y.embB i j b x)
def eH_comm : Prop := ∀ i j b k P, P ∉ tw.S0 i → Y.eH i j b * Y.hkF i j b k P = Y.hkF i j b k P * Y.eH i j b
def eH_eig : Prop := ∀ i j b (x : Y.Fm i j b) (ev : ℕ → PlE H → FractionRing (tw.O i)), x ≠ 0 →
    (∀ k P, 1 ≤ k → k ≤ R.r → IsSplitPl H P → P ∉ tw.S0 i → Y.hkF i j b k P x = ev k P • x) →
    (Y.eH i j b x = x ∧ ∃ s : tw.Sig i, tw.jS i s = j ∧ tw.side i s = b ∧ ∀ k P, 1 ≤ k → k ≤ R.r →
        IsSplitPl H P → P ∉ tw.S0 i →
        algebraMap (tw.O i) (FractionRing (tw.O i)) (tw.hEig i s k P) = ev k P) ∨
    (Y.eH i j b x = 0 ∧ ¬ ∃ s : tw.Sig i, tw.jS i s = j ∧ tw.side i s = b ∧ ∀ k P, 1 ≤ k → k ≤ R.r →
        IsSplitPl H P → P ∉ tw.S0 i →
        algebraMap (tw.O i) (FractionRing (tw.O i)) (tw.hEig i s k P) = ev k P)
def sig_all : Prop := ∀ i j b (x : Y.Fm i j b) (ev : ℕ → PlE H → FractionRing (tw.O i)), x ≠ 0 →
    MonoidAlgebra.lift (FractionRing (tw.O i)) (Module.End (FractionRing (tw.O i)) (Y.Fm i j b)) (G0g N)
      (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp (Y.actG i j b)) (Y.eAlg i b) x = x →
    (∀ k P, 1 ≤ k → k ≤ R.r → IsSplitPl H P → P ∉ tw.S0 i → Y.hkF i j b k P x = ev k P • x) →
    ∃ s : tw.Sig i, tw.jS i s = j ∧ tw.side i s = b ∧ ∀ k P, 1 ≤ k → k ≤ R.r → IsSplitPl H P →
      P ∉ tw.S0 i → algebraMap (tw.O i) (FractionRing (tw.O i)) (tw.hEig i s k P) = ev k P
def ThetaDef : Prop := ∀ i j b, (tw.Theta i j b).map (Y.embB i j b) =
  Submodule.span (tw.O i) (Set.range fun d : Y.Dat i j b => Y.eH i j b (Y.th i j b d))
def ThetaPsiDef : Prop := ∀ i j b k Q ψ,
  (tw.ThetaPsi i j b k Q ψ).map ((Y.embB i j b).baseChange (tw.Ok i k)) =
    Submodule.span (tw.Ok i k) (⋃ d : Y.Dat i j b,
      (((Y.eH i j b).restrictScalars (tw.O i)).baseChange (tw.Ok i k)) '' Y.thPsi i j b k Q ψ d)
end NExp
end Exp
section Types
open Polynomial
abbrev Fb (l : ℕ) (hl : l.Prime) : Type := @Formalism.CyclotomicNorms.Fbar l ⟨hl⟩
set_option synthInstance.maxHeartbeats 400000 in

structure NTypes {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂} (A : NAut N) where

  Mray : Type
  [instMray : Field Mray]
  [nfMray : NumberField Mray]

  [algKM : Algebra H.K Mray]
  Mray_gal : IsGalois H.K Mray
  Mray_ab : ∀ σ τ : Mray ≃ₐ[H.K] Mray, σ * τ = τ * σ
  Mray_unr : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ NumberField.discr Mray → p ∣ H.QS * H.q * H.d

  g_Mray : ∀ k, (placesOver Mray (H.g k)).ncard = Module.finrank ℚ Mray
  g_cond : ∀ k, H.g k % (H.QS * H.q * H.d) = 1
  BB_disj : Disjoint (Formalism.CyclotomicNorms.BB R.r (H.g 0)) (Formalism.CyclotomicNorms.BB R.r (H.g 1))

  bc : what₂.FT → Multiset (ℕ × ℕ)
  bc_pos : ∀ σ, ∀ p ∈ bc σ, 0 < p.1 ∧ 0 < p.2
  bc_sum : ∀ σ, ((bc σ).map (fun p => p.1 * p.2)).sum = R.r

  rbar : what₂.FT → ∀ w : what₂.places.Pl,
    G H.E N.Om →* GL (Fin R.r) (Fb (what₂.places.resChar w) (what₂.places.resChar_prime w))
  rbar_open : ∀ σ w, IsOpen ((rbar σ w).ker : Set (G H.E N.Om))

  tg : ∀ k, N.PlG k → G H.E N.Om
  tg_mem : ∀ k v, tg k v ∈ Ine (F := H.E) (N.plOm.1 (A.plGw k v))

  tg_gen : ∀ k v, TameGenAt (N.plOm.1 (A.plGw k v)) (tg k v)

  heckeLoc_gamma_places : ∀ i k v, N.gam0 i (A.plGw k v) = tg k v

  iota : ∀ k (v : N.PlG k) (w : what₂.places.Pl),
    Fb (H.g k) (H.g_prime k) →* Fb (what₂.places.resChar w) (what₂.places.resChar_prime w)
  iota_inj : ∀ k v w, ∀ x y : Fb (H.g k) (H.g_prime k), x ≠ 0 → y ≠ 0 →
      (orderOf x).Coprime (what₂.places.resChar w) → (orderOf y).Coprime (what₂.places.resChar w) →
      iota k v w x = iota k v w y → x = y

  teichC : ∀ k, Fb (H.g k) (H.g_prime k) →* ℂ
  teichC_inj : ∀ k, ∀ x y : Fb (H.g k) (H.g_prime k), x ≠ 0 → y ≠ 0 →
    teichC k x = teichC k y → x = y

  inertiaCharpoly_type : ∀ k v (L : A.LP (A.plGw k v)), (A.items₂ k (A.plGw k v) L).natDegree = A.lpDim L →
    haveI : Fact (H.g k).Prime := ⟨H.g_prime k⟩
    A.inePol L (tg k v) =
      ((Formalism.CyclotomicNorms.rootsBar (A.items₂ k (A.plGw k v) L)).map fun x => X - C (teichC k x)).prod

  chiT_tg : ∀ i k v, N.l i ≠ H.g k →
    haveI : Fact (H.g k).Prime := ⟨H.g_prime k⟩
    (A.iotaQC i (A.iotaQ i (algebraMap (N.O i) (FractionRing (N.O i))
        ((N.chi i 1 (tg k v) : (N.O i)ˣ) : N.O i))) =
      teichC k (algebraMap (ZMod (H.g k)) (Formalism.CyclotomicNorms.Fbar (H.g k))
        ((N.chiT k v ⟨N.j i - 1, by have := N.j_range i; omega⟩ : (ZMod (H.g k))ˣ) : ZMod (H.g k)))) ∨
    (A.iotaQC i (A.iotaQ i (algebraMap (N.O i) (FractionRing (N.O i))
        ((N.chi i 1 (tg k v) : (N.O i)ˣ) : N.O i))) =
      teichC k (algebraMap (ZMod (H.g k)) (Formalism.CyclotomicNorms.Fbar (H.g k))
        (((N.chiT k v ⟨N.j i - 1, by have := N.j_range i; omega⟩)⁻¹ : (ZMod (H.g k))ˣ) : ZMod (H.g k))))

  eSer : ∀ k, (ZMod (H.g k))[X] → MonoidAlgebra ℂ (GL (Fin R.r) (ZMod (H.g k)))
  eSer_idem : ∀ k f, eSer k f * eSer k f = eSer k f
  eSer_central : ∀ k f a, eSer k f * a = a * eSer k f
  eSer_orth : ∀ k f f', f ≠ f' → eSer k f * eSer k f' = 0
  eSer_zero : ∀ k f, ¬ (f.Monic ∧ f.natDegree = R.r ∧ f.coeff 0 ≠ 0) → eSer k f = 0
  eSer_sum : ∀ k, ∃ S : Finset (ZMod (H.g k))[X],
    (∀ f, f ∈ S ↔ f.Monic ∧ f.natDegree = R.r ∧ f.coeff 0 ≠ 0) ∧ ∑ f ∈ S, eSer k f = 1

  cenAmb : ∀ μ, Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g N)) →ₐ[ℂ] Module.End ℂ (what₂.Amb μ)
  cenMt : ∀ μ j, Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g N)) →ₐ[ℂ] Module.End ℂ (what₂.Mt μ j)

  Par : Type
  labPar : ∀ k, Par → N.PlG k → (ZMod (H.g k))[X]
  labPar_monic : ∀ k σ v, (labPar k σ v).Monic ∧ (labPar k σ v).natDegree = R.r

  locPar : Par → ∀ w, A.LP w
  locPar_dim : ∀ σ w, A.lpDim (locPar σ w) = R.r
  labPar_def : ∀ k σ v, labPar k σ v = A.items₂ k (A.plGw k v) (locPar σ (A.plGw k v))
  MtPar : ∀ μ j, Par → Submodule ℂ (what₂.Mt μ j)

  AmbPar : ∀ μ, Par → Submodule ℂ (what₂.Amb μ)
attribute [instance] NTypes.instMray NTypes.nfMray NTypes.algKM
namespace NTypes
variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂} {A : NAut N} (X : NTypes A)
def cond (_X : NTypes A) : ℕ := H.QS * H.q * H.d
def admissible (p : ℕ) : Prop :=
  p.Prime ∧ (placesOver H.E p).ncard = Module.finrank ℚ H.E ∧
    (placesOver X.Mray p).ncard = Module.finrank ℚ X.Mray ∧ p % X.cond = 1
def cuspidal (σ : what₂.FT) : Prop := X.bc σ = ({(R.r, 1)} : Multiset (ℕ × ℕ))
def goodTuple (_X : NTypes A) (f : ∀ k, N.PlG k → (ZMod (H.g k))[X]) : Prop :=
  ∀ k, haveI : Fact (H.g k).Prime := ⟨H.g_prime k⟩
    Formalism.CyclotomicNorms.IsGood R.r (H.g k) (f k) (N.chiT k) ∧
    Formalism.CyclotomicNorms.IsGood R.r (H.g k) (f k) (fun v j => (N.chiT k v j)⁻¹)
def e0 : MonoidAlgebra ℂ (G0g N) :=
  haveI : ∀ k, NeZero (H.g k) := fun k => ⟨(H.g_prime k).ne_zero⟩
  haveI : ∀ k, Fact (H.g k).Prime := fun k => ⟨H.g_prime k⟩
  MonoidAlgebra.ofCoeff <| Finsupp.equivFunOnFinite.symm fun g : G0g N =>
    ∑ᶠ a : (∀ kv : (Σ k : Fin 2, N.PlG k), (Fin R.r → ZMod (H.g kv.1))),
      (open Classical in if X.goodTuple (fun k v => Formalism.CyclotomicNorms.monicOf (a ⟨k, v⟩)) then
        ∏ kv : (Σ k : Fin 2, N.PlG k), (X.eSer kv.1 (Formalism.CyclotomicNorms.monicOf (a kv))).coeff (g kv) else 0)
def Qchi : IntermediateField ℚ ℂ :=
  IntermediateField.adjoin ℚ {z | ∃ (k : Fin 2) (v : N.PlG k) (j : Fin R.m), haveI : Fact (H.g k).Prime := ⟨H.g_prime k⟩
    z = X.teichC k (algebraMap (ZMod (H.g k)) (Formalism.CyclotomicNorms.Fbar (H.g k)) ((N.chiT k v j : ZMod (H.g k))))}
def goodPar (σ : X.Par) : Prop := X.goodTuple (fun k v => X.labPar k σ v)
def onAmb (μ : what₂.Tup) (z : MonoidAlgebra ℂ (G0g N)) : Module.End ℂ (what₂.Amb μ) :=
  open Classical in
  if h : z ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g N)) then X.cenAmb μ ⟨z, h⟩ else 0
def onMt (μ : what₂.Tup) (j : ℕ) (z : MonoidAlgebra ℂ (G0g N)) : Module.End ℂ (what₂.Mt μ j) :=
  open Classical in
  if h : z ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g N)) then X.cenMt μ j ⟨z, h⟩ else 0
def IdempotentMatchesAction : Prop :=
  (∀ μ, what₂.eOp μ = X.onAmb μ X.e0) ∧ ∀ μ j, what₂.eMt μ j = X.onMt μ j X.e0
end NTypes
end Types
open scoped TensorProduct in
set_option synthInstance.maxHeartbeats 400000 in

structure NTh (R : Ranks) (H : Host R) (what₂ : Rows.Data R) [NumberField what₂.LL] [StarRing what₂.LL]
    (LL0 : IntermediateField ℚ what₂.LL) (N : NData R H what₂) (tw : NTw R H what₂ LL0 N)
    (ex : NExp R H what₂ LL0 N tw) where

  iC : ∀ i : tw.Tw, FractionRing (tw.O i) →+* ℂ_[tw.l i]
  iC_int : ∀ i (x : FractionRing (tw.O i)), ‖iC i x‖ ≤ 1 ↔
    x ∈ (algebraMap (tw.O i) (FractionRing (tw.O i))).range

  aL : tw.Tw → ℕ
  aL_g : ∀ i k, tw.l i = H.g k → aL i = 1
  aL_off : ∀ i, (∀ k, tw.l i ≠ H.g k) → aL i = 0

  Pt : tw.Tw → ℕ → Type

  ev : ∀ i j b, ex.Fm i j b →+ (Pt i j → ℂ_[tw.l i])
  ev_smul : ∀ i j b (a : FractionRing (tw.O i)) (f : ex.Fm i j b) (y : Pt i j),
    ev i j b (a • f) y = iC i a * ev i j b f y
  ev_inj : ∀ i j b, Function.Injective (ev i j b)

  Lt : tw.Tw → ℕ → Type
  [acgLt : ∀ i j, AddCommGroup (Lt i j)]
  [modLt : ∀ i j, Module (𝓞 H.E) (Lt i j)]
  [freeLt : ∀ i j, Module.Free ℤ (Lt i j)]
  [finLt : ∀ i j, Module.Finite ℤ (Lt i j)]

  Let : tw.Tw → ℕ → Type
  [finLet : ∀ i j, Fintype (Let i j)]
  Harm : ∀ i j, Set (MvPolynomial (Let i j) (tw.O i))

  Ctr : tw.Tw → ℕ → Type
  ctrC : ∀ i j, Ctr i j → Let i j → Let i j → tw.O i
  Harm_def : ∀ i j (P : MvPolynomial (Let i j) (tw.O i)), P ∈ Harm i j ↔
    ∀ κ : Ctr i j, ∑ a, ∑ b, MvPolynomial.C (ctrC i j κ a b) *
      MvPolynomial.pderiv a (MvPolynomial.pderiv b P) = 0

  thV : ∀ i j, (Lt i j → FractionRing (tw.O i)) → MvPolynomial (Let i j) (tw.O i) →
    Pt i j → ℂ_[tw.l i]

  thV_add : ∀ i j φ φ' P y, thV i j (φ + φ') P y = thV i j φ P y + thV i j φ' P y
  thV_smul : ∀ i j (a : FractionRing (tw.O i)) φ P y, thV i j (a • φ) P y = iC i a * thV i j φ P y
  thV_addP : ∀ i j φ P P' y, thV i j φ (P + P') y = thV i j φ P y + thV i j φ P' y
  thV_smulP : ∀ i j (c : tw.O i) φ P y, thV i j φ (c • P) y =
    iC i (algebraMap (tw.O i) (FractionRing (tw.O i)) c) * thV i j φ P y

  datPhi : ∀ i j b, ex.Dat i j b → Lt i j → FractionRing (tw.O i)
  datP : ∀ i j b, ex.Dat i j b → MvPolynomial (Let i j) (tw.O i)

  recDet : ∀ i j, Pt i j → G H.E N.Om

  Kq : ∀ (_ : tw.Tw) (_ : ℕ), HeightOneSpectrum (𝓞 H.E) → Type
  [grpKq : ∀ i j P, Group (Kq i j P)]
  actK : ∀ i j P, Kq i j P → Pt i j → Pt i j
  actK_one : ∀ i j P y, actK i j P 1 y = y
  actK_mul : ∀ i j P (k k' : Kq i j P) y, actK i j P (k * k') y = actK i j P k' (actK i j P k y)

  recDetq : ∀ i j (_ : HeightOneSpectrum (𝓞 H.E)), Pt i j → G H.E N.Om
  recDetq_mem : ∀ i j P y, recDetq i j P y ∈ Dec (F := H.E) (N.plOm.1 P)

  recDet_act : ∀ i j P (k : Kq i j P) y (A' : Type) [CommGroup A'] (χ : G H.E N.Om →* A'),
    IsOpen (χ.ker : Set (G H.E N.Om)) → AntiHom tw.cc χ → χ (recDet i j (actK i j P k y)) * χ (recDetq i j P y) =
      χ (recDet i j y) * χ (recDetq i j P (actK i j P k y))
  recDetq_act : ∀ i j P P' (k : Kq i j P) y (A' : Type) [CommGroup A'] (χ : G H.E N.Om →* A'),
    IsOpen (χ.ker : Set (G H.E N.Om)) → P' ≠ P → ¬ IsConjPl H P P' → χ (recDetq i j P' (actK i j P k y)) = χ (recDetq i j P' y)

  hkIdx : ∀ (_ : tw.Tw) (_ : ℕ), ℕ → PlE H → Type
  [finHk : ∀ i j k P, Fintype (hkIdx i j k P)]
  hkMove : ∀ i j k P, hkIdx i j k P → Pt i j → Pt i j
  hkU : ∀ i j (_ : Bool) k P, hkIdx i j k P → Pt i j → ℂ_[tw.l i]
  hk_ev : ∀ i j b k P, 1 ≤ k → k ≤ R.r → IsSplitPl H P → P ∉ tw.S0 i → ∀ (f : ex.Fm i j b) y,
    ev i j b (ex.hkF i j b k P f) y = ∑ c, hkU i j b k P c y * ev i j b f (hkMove i j k P c y)

  MaximalUnramifiedExtension : ∀ i, Subfield (FractionRing (tw.O i))
  FmUr : ∀ i j b, AddSubgroup (ex.Fm i j b)
  FmUr_smul : ∀ i j b (a : FractionRing (tw.O i)) (f : ex.Fm i j b), a ∈ MaximalUnramifiedExtension i → f ∈ FmUr i j b →
    a • f ∈ FmUr i j b
  FmUr_span : ∀ i j b, Submodule.span (FractionRing (tw.O i)) (FmUr i j b : Set (ex.Fm i j b)) = ⊤
  Bsup_def : ∀ i j b, ex.Bsup i j b =
    Submodule.span (tw.O i) {f | f ∈ FmUr i j b ∧ ∀ y, ‖ev i j b f y‖ ≤ 1}
attribute [instance] NTh.acgLt NTh.modLt NTh.freeLt NTh.finLt NTh.finLet NTh.grpKq NTh.finHk
def NTh.EmbBRange {R : Ranks} {H : Host R} {what₂ : Rows.Data R} [NumberField what₂.LL] [StarRing what₂.LL]
    {LL0 : IntermediateField ℚ what₂.LL} {N : NData R H what₂} {tw : NTw R H what₂ LL0 N}
    {ex : NExp R H what₂ LL0 N tw} (T : NTh R H what₂ LL0 N tw ex) : Prop :=
  ∀ i j b, (∀ k, tw.l i ≠ H.g k) → ∀ f : ex.Fm i j b,
    f ∈ LinearMap.range (ex.embB i j b) ↔ ∃ f', (∀ y, ‖T.ev i j b f' y‖ ≤ 1) ∧ f = ex.eH i j b f'
def NTh.ThEv {R : Ranks} {H : Host R} {what₂ : Rows.Data R} [NumberField what₂.LL] [StarRing what₂.LL]
    {LL0 : IntermediateField ℚ what₂.LL} {N : NData R H what₂} {tw : NTw R H what₂ LL0 N}
    {ex : NExp R H what₂ LL0 N tw} (T : NTh R H what₂ LL0 N tw ex) : Prop :=
  ∀ i j b (d : ex.Dat i j b) (y : T.Pt i j),
    T.ev i j b (ex.th i j b d) y = T.thV i j (T.datPhi i j b d) (T.datP i j b d) y
end Formalism.BasicNotions
namespace Formalism.BasicNotions
open Loc Formalism.WeaklyAdmissibleFiltrations
namespace LocBridge
variable {l : ℕ} [Fact l.Prime] {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω] {Gw : Subgroup (Ω ≃ₐ[E] Ω)}
  {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω Gw O)
def repE (LL' : FinExt l) {m : ℕ} (r : ↥Gw →* Matrix.GeneralLinearGroup (Fin m) ↥LL'.1) :
    Representation ↥LL'.1 ↥(GK Bw.Kw) (Fin m → ↥LL'.1) :=
  ((Matrix.toLinAlgEquiv' : Matrix (Fin m) (Fin m) ↥LL'.1 ≃ₐ[↥LL'.1] _) : _ →* _).comp
    ((Units.coeHom _).comp (r.comp Bw.e.symm.toMonoidHom))
def IsCrysE (P : LocPrime l) (LL' : FinExt l) {m : ℕ} (r : ↥Gw →* Matrix.GeneralLinearGroup (Fin m) ↥LL'.1) : Prop :=
  IsCrys (P.PD Bw.Kw) (Bw.repE LL' r)
def IsdRE (P : LocPrime l) (LL' : FinExt l) {m : ℕ} (r : ↥Gw →* Matrix.GeneralLinearGroup (Fin m) ↥LL'.1) : Prop :=
  Module.finrank ↥LL'.1 ↥(DdR (P.PD Bw.Kw) (Bw.repE LL' r)) = Module.finrank ℚ_[l] ↥Bw.Kw.1 * m
def IsPotCrysE (P : LocPrime l) (LL' : FinExt l) {m : ℕ}
    (r : ↥Gw →* Matrix.GeneralLinearGroup (Fin m) ↥LL'.1) : Prop :=
  ∃ (K' : FinExt l) (h : Bw.Kw.1 ≤ K'.1),
    IsCrys (P.PD K') ((Bw.repE LL' r).comp (Subgroup.inclusion (GK_le h)))
def IsJumpE (P : LocPrime l) (LL' : FinExt l) {m : ℕ} (r : ↥Gw →* Matrix.GeneralLinearGroup (Fin m) ↥LL'.1)
    (τ : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1) (a : ℤ) : Prop :=
  IsJumpV (P.PD Bw.Kw) (Bw.repE LL' r) τ a
def multW (P : LocPrime l) {m : ℕ} (r : ↥Gw →* Matrix.GeneralLinearGroup (Fin m) O)
    (τ : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥Bw.LL.1) (a : ℤ) : ℤ :=
  multV (P.PD Bw.Kw) (Bw.rep r) τ a
def multE (P : LocPrime l) (LL' : FinExt l) {m : ℕ} (r : ↥Gw →* Matrix.GeneralLinearGroup (Fin m) ↥LL'.1)
    (τ : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1) (a : ℤ) : ℤ :=
  multV (P.PD Bw.Kw) (Bw.repE LL' r) τ a
end LocBridge
end Formalism.BasicNotions
namespace Formalism.MainNotions.N
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal
section SharedN4
open Polynomial
variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R}
section Rep
variable {Γ : Type} [Group Γ] {k : Type} [Field k] {a : ℕ}
def IsInv (ρ : Γ →* GL (Fin a) k) (W : Submodule k (Fin a → k)) : Prop :=
  ∀ g, ∀ v ∈ W, (ρ g : Matrix (Fin a) (Fin a) k).mulVec v ∈ W
def IsSSRep (ρ : Γ →* GL (Fin a) k) : Prop :=
  ∀ W, IsInv ρ W → ∃ W', IsInv ρ W' ∧ IsCompl W W'
def IsIrrSub (ρ : Γ →* GL (Fin a) k) (W : Submodule k (Fin a → k)) : Prop :=
  W ≠ ⊥ ∧ IsInv ρ W ∧ ∀ W', W' ≤ W → IsInv ρ W' → W' = ⊥ ∨ W' = W
def IsoSub (ρ : Γ →* GL (Fin a) k) (W₁ W₂ : Submodule k (Fin a → k)) : Prop :=
  ∃ e : W₁ ≃ₗ[k] W₂, ∀ g (v : W₁) (h : (ρ g : Matrix (Fin a) (Fin a) k).mulVec v ∈ W₁),
    ((e ⟨_, h⟩ : W₂) : Fin a → k) = (ρ g : Matrix (Fin a) (Fin a) k).mulVec (e v)
end Rep
def mapRep {Γ : Type} [Group Γ] {A B : Type} [CommRing A] [CommRing B] {a : ℕ} (f : A →+* B)
    (ρ : Γ →* GL (Fin a) A) : Γ →* GL (Fin a) B :=
  (Units.map (f.mapMatrix : Matrix (Fin a) (Fin a) A →+* Matrix (Fin a) (Fin a) B).toMonoidHom).comp ρ
def AbsIrrSub {Γ : Type} [Group Γ] {k : Type} [Field k] {a : ℕ} (ρ : Γ →* GL (Fin a) k)
    (W : Submodule k (Fin a → k)) : Prop :=
  IsIrrSub (mapRep (algebraMap k (AlgebraicClosure k)) ρ)
    (Submodule.span (AlgebraicClosure k) ((fun v => (algebraMap k (AlgebraicClosure k)) ∘ v) '' W))
section Glob
variable (N : NData R H what₂) (A : NAut N)
abbrev Kf (i : N.Loc) : Type := FractionRing (N.O i)
def iotaO (i : N.Loc) : N.O i →+* ℂ :=
  ((A.iotaQC i).toRingHom.comp (A.iotaQ i)).comp (algebraMap (N.O i) (FractionRing (N.O i)))
def iotaOQ (i : N.Loc) : N.O i →+* Qbar (N.l i) :=
  (A.iotaQ i).comp (algebraMap (N.O i) (FractionRing (N.O i)))
def InducesW (i : N.Loc) (τ : H.E →+* Qbar (N.l i)) (w : PlE H) : Prop :=
  ∀ x : 𝓞 H.E, ‖τ (x : H.E)‖ < 1 ↔ x ∈ w.asIdeal
def chi1 (i : N.Loc) (g : G H.E N.Om) : N.O i := ((N.chi i 1 g : (N.O i)ˣ) : N.O i)
def IsHeckeGalois (i : N.Loc) (x : N.X i) (r : G H.E N.Om →* GL (Fin R.nV) (N.O i)) : Prop :=
  Continuous (fun g => ((r g : GL (Fin R.nV) (N.O i)) : Matrix (Fin R.nV) (Fin R.nV) (N.O i))) ∧
  IsSSRep (mapRep (algebraMap (N.O i) (Kf N i)) r) ∧
  ∀ w, SplitOut N i w → ∀ (B : ValuationSubring N.Om) (σ : G H.E N.Om),
    IsPlaceOver (F := H.E) B w → IsFrob (F := H.E) B (normV w) σ →
    ((r σ : GL (Fin R.nV) (N.O i)) : Matrix (Fin R.nV) (Fin R.nV) (N.O i)).charpoly =
      heckePol N i x w
def GoodR (i : N.Loc) (r : N.X i → (G H.E N.Om →* GL (Fin R.nV) (N.O i))) : Prop :=
  ∀ x, IsHeckeGalois N i x (r x)
def redRep (i : N.Loc) {a : ℕ} (ρ : G H.E N.Om →* GL (Fin a) (N.O i)) :
    G H.E N.Om →* GL (Fin a) (IsLocalRing.ResidueField (N.O i)) :=
  mapRep (IsLocalRing.residue (N.O i)) ρ
def spehLoc (p : Part A.CG) (w : PlE H) : A.LP w :=
  (List.range p.d).foldr
    (fun k acc => A.lpSum (A.lpTw (A.locG p.π w) (((p.d : ℝ) - 1) / 2 - k)) acc) (A.lpZero w)
def isoLoc (P : List (Part A.CG)) (w : PlE H) : A.LP w :=
  P.foldr (fun p acc => A.lpSum (spehLoc N A p w) acc) (A.lpZero w)
def isoInf (P : List (Part A.CG)) (τ : H.E →+* ℂ) : Multiset ℂ :=
  (P.map fun p => ((List.range p.d).map fun k =>
    (A.infG p.π τ).map (· + (((p.d : ℂ) - 1) / 2 - k))).sum).sum
def rankIso (P : List (Part A.CG)) : ℕ := (P.map fun p => p.a * p.d).sum
def twistIso (P : List (Part A.CG)) (χ : A.CG 1) : List (Part A.CG) :=
  P.map fun p => ⟨p.a, A.tw p.π χ, p.d⟩
def muPart (i : N.Loc) : Part A.CG := ⟨1, A.muC i, R.t⟩
end Glob
def ubc (n : ℕ) (α : Multiset ℂ) : Multiset ℂ :=
  α + α.map (·⁻¹) + (if Odd n then ({1} : Multiset ℂ) else 0)
def galPol {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂} (A : NAut N)
    {w : PlE H} (L : A.LP w) : Polynomial ℂ :=
  ((A.frobEig L).map fun α => X - C α).prod
section Glob2
variable (N : NData R H what₂) (A : NAut N)
def IsBCV (i : N.Loc) (P : A.AV i) (Pa : List (Part A.CG)) : Prop :=
  (∀ p ∈ Pa, 1 ≤ p.a ∧ 1 ≤ p.d ∧ A.csd p.π) ∧
  (Pa.map fun p => ((⟨p.a, p.π⟩ : Σ a, A.CG a), p.d)).Nodup ∧
  rankIso N A Pa = R.nV ∧
  (∀ w, IsSplitPl H w → isoLoc N A Pa w = A.locV i P w) ∧
  (∀ w, ¬ IsSplitPl H w → A.unr (isoLoc N A Pa w) ∧
    A.frobEig (isoLoc N A Pa w) = ubc R.nV (A.satV i P w)) ∧
  ∀ τ, isoInf N A Pa τ = A.infWt i τ
def HasParamW (i : N.Loc) (σ : what₂.FT) (Sig : List (Part A.CG)) : Prop :=
  (∀ p ∈ Sig, 1 ≤ p.a ∧ 1 ≤ p.d) ∧ rankIso N A Sig = R.r ∧
  (∀ w, IsSplitPl H w → isoLoc N A Sig w = A.locW i σ w)
def IsCuspIso (Sig : List (Part A.CG)) : Prop := ∃ π : A.CG R.r, Sig = [⟨R.r, π, 1⟩]
def goodSig (Sig : List (Part A.CG)) : Prop :=
  ∀ k, haveI : Fact (H.g k).Prime := ⟨H.g_prime k⟩
    Formalism.CyclotomicNorms.IsGood R.r (H.g k) (fun v => A.items₂ k (A.plGw k v) (isoLoc N A Sig (A.plGw k v)))
      (N.chiT k) ∧
    Formalism.CyclotomicNorms.IsGood R.r (H.g k) (fun v => A.items₂ k (A.plGw k v) (isoLoc N A Sig (A.plGw k v)))
      (fun v j => (N.chiT k v j)⁻¹)
def ZN (i : N.Loc) : Set (N.X i) :=
  {x | ∃ P, A.ptV i P = some x ∧ ∃ Pa, IsBCV N A i P Pa ∧
    (⟨1, A.tw (A.muC i) A.etaTinv, R.t⟩ : Part A.CG) ∈ Pa}
def HasParamX (i : N.Loc) (x : N.X i) (Sig : List (Part A.CG)) : Prop :=
  ∃ P, A.ptV i P = some x ∧ IsBCV N A i P (twistIso N A (Sig ++ [muPart N A i]) A.etaTinv)
def ZgoodN (i : N.Loc) : Set (N.X i) :=
  {x | x ∈ ZN N A i ∧ ∃ Sig, HasParamX N A i x Sig ∧ goodSig N A Sig}
def thetaOf (i : N.Loc) (σ : what₂.FT) (P : A.AV i) : Prop :=
  (what₂.isot (N.j i) σ).map (what₂.thetaT (N.mu i) (N.j i)) ≠ ⊥ ∧
  (what₂.isot (N.j i) σ).map (what₂.thetaT (N.mu i) (N.j i)) ≤ A.typeV i P
def MjSig (i : N.Loc) (Sig : List (Part A.CG)) : Submodule ℂ (what₂.Mj (N.j i)) :=
  ⨆ σ ∈ {σ | HasParamW N A i σ Sig}, what₂.isot (N.j i) σ
def eigC (i : N.Loc) (x : N.X i) : Submodule ℂ (what₂.Mt (N.mu i) (N.j i)) :=
  ⨆ P ∈ {P | A.ptV i P = some x}, A.typeV i P
def AtM (i : N.Loc) (σ : what₂.FT) : Prop :=
  ∃ Sig, HasParamW N A i σ Sig ∧ ∃ x : N.X i, ∀ w, SplitOut N i w →
    ∃ p : Polynomial (N.O i), p.map (iotaO N A i) =
        galPol A (A.lpTw (isoLoc N A (twistIso N A (Sig ++ [muPart N A i]) A.etaTinv) w)
          ((1 - (R.nV : ℝ)) / 2)) ∧
      p.map (IsLocalRing.residue (N.O i)) = (heckePol N i x w).map (IsLocalRing.residue (N.O i))
def goodPartM (i : N.Loc) : Submodule ℂ (what₂.Mj (N.j i)) :=
  ⨆ σ ∈ {σ | N.goodRow σ ∧ AtM N A i σ}, what₂.isot (N.j i) σ
def dM (i : N.Loc) : ℕ := Module.finrank ℂ ↥(goodPartM N A i)
def IsRhoBar (i : N.Loc) (rb : G H.E N.Om →* GL (Fin R.r) (IsLocalRing.ResidueField (N.O i))) :
    Prop :=
  IsOpen (rb.ker : Set (G H.E N.Om)) ∧ ∀ x w, SplitOut N i w → ∀ (B : ValuationSubring N.Om) (σ : G H.E N.Om),
    IsPlaceOver (F := H.E) B w → IsFrob (F := H.E) B (normV w) σ →
    ((rb σ : GL _ _) : Matrix (Fin R.r) (Fin R.r) _).charpoly *
      ∏ c ∈ Finset.Icc 1 R.t, (X - C (IsLocalRing.residue (N.O i) ((N.chi i c σ : (N.O i)ˣ) : N.O i))) =
    (heckePol N i x w).map (IsLocalRing.residue (N.O i))
def IsRepOfSig (i : N.Loc) (Sig : List (Part A.CG)) (ρ : G H.E N.Om →* GL (Fin R.r) (N.O i)) :
    Prop :=
  Continuous (fun g => ((ρ g : GL (Fin R.r) (N.O i)) : Matrix (Fin R.r) (Fin R.r) (N.O i))) ∧
  IsSSRep (mapRep (algebraMap (N.O i) (Kf N i)) ρ) ∧
  ∀ᶠ w in Filter.cofinite, ∀ (B : ValuationSubring N.Om) (σ : G H.E N.Om),
    IsPlaceOver (F := H.E) B w → IsFrob (F := H.E) B (normV w) σ →
    ((ρ σ : GL _ _) : Matrix (Fin R.r) (Fin R.r) (N.O i)).charpoly.map (iotaO N A i) =
      galPol A (A.lpTw (isoLoc N A Sig w) ((1 - (R.r : ℝ)) / 2))
def HG (i : N.Loc) : Prop := (ZgoodN N A i).Nonempty
def CrysIffWD : Prop := ∀ i (a : ℕ) (r : G H.E N.Om →* GL (Fin a) (Qbar (N.l i))) w,
  w ∈ placesOver H.E (N.l i) →
  Continuous (fun g => ((r g : GL (Fin a) (Qbar (N.l i))) : Matrix (Fin a) (Fin a) (Qbar (N.l i)))) →
  (A.IsCrysW i r w ↔ A.IsdRW i r w ∧ A.unr (A.wdOf i r w))
def PotCrysIffWD : Prop := ∀ i (a : ℕ) (r : G H.E N.Om →* GL (Fin a) (Qbar (N.l i))) w,
  w ∈ placesOver H.E (N.l i) →
  Continuous (fun g => ((r g : GL (Fin a) (Qbar (N.l i))) : Matrix (Fin a) (Fin a) (Qbar (N.l i)))) →
  (A.IsPotCrysW i r w ↔ A.IsdRW i r w ∧ A.mono0 (A.wdOf i r w))
def JumpsCard : Prop := ∀ i (a : ℕ) (r : G H.E N.Om →* GL (Fin a) (Qbar (N.l i))) w τ,
  w ∈ placesOver H.E (N.l i) → InducesW N i τ w → A.IsdRW i r w → Multiset.card (A.jumpsW i r τ) = a
def BcTie (X : NTypes A) : Prop := ∀ i σ Sig, HasParamW N A i σ Sig → (∀ p ∈ Sig, A.csd p.π) →
  (∀ p ∈ Sig, ∀ τ, (A.infG p.π τ).Nodup ∧ ∀ z ∈ A.infG p.π τ, ∃ k : ℤ, z = (k : ℂ) + ((R.r : ℂ) - (p.d : ℂ)) / 2) →
  X.bc σ = Multiset.ofList (Sig.map fun p => (p.a, p.d))
def fbCast {p q : ℕ} (h : p = q) (hp : p.Prime) (hq : q.Prime) : Fb p hp ≃+* Fb q hq := by
  subst h; exact RingEquiv.refl _
def RbarTie (X : NTypes A) : Prop := ∀ i σ Sig (ρ : G H.E N.Om →* GL (Fin R.r) (N.O i)),
  HasParamW N A i σ Sig → IsRepOfSig N A i Sig ρ →
  IsSSRep (X.rbar σ (N.w i)) ∧
    ∀ g, (((X.rbar σ (N.w i) g : GL _ _) : Matrix (Fin R.r) (Fin R.r) _).charpoly).map
        (fbCast (N.w_l i) (what₂.places.resChar_prime (N.w i)) (N.lPrime i).out).toRingHom =
      ((ρ g : GL _ _) : Matrix (Fin R.r) (Fin R.r) (N.O i)).charpoly.map
        ((A.kFbar i).comp (IsLocalRing.residue (N.O i)))
def MtParTie (X : NTypes A) : Prop := ∀ i (σ' : X.Par),
  X.MtPar (N.mu i) (N.j i) σ' =
    ⨆ P ∈ {P | ∃ Sig, (∀ w, isoLoc N A Sig w = X.locPar σ' w) ∧
      IsBCV N A i P (twistIso N A (Sig ++ [muPart N A i]) A.etaTinv)}, A.typeV i P
def LocTie (L : LocTheory)
    (nbr : ∀ (i : N.Loc) (w : PlE H), w ∈ placesOver H.E (N.l i) →
      LocBridge (N.l i) H.E N.Om (Dec (F := H.E) (N.plOm.1 w)) (N.O i)) : Prop :=
  ∀ (i : N.Loc) (w : PlE H) (hw : w ∈ placesOver H.E (N.l i)),
    (∀ x : N.O i, iotaOQ N A i x = (((nbr i w hw).toLL x : ↥(nbr i w hw).LL.1) : Loc.Om (N.l i))) ∧
    (∀ (m : ℕ) (ρ : G H.E N.Om →* GL (Fin m) (N.O i)),
      Continuous (fun g => ((ρ g : GL (Fin m) (N.O i)) : Matrix (Fin m) (Fin m) (N.O i))) →
      (A.IsCrysW i (mapRep (iotaOQ N A i) ρ) w ↔
        (nbr i w hw).IsCrysW (L (N.l i)) (ρ.comp (Dec (F := H.E) (N.plOm.1 w)).subtype)) ∧
      (A.IsdRW i (mapRep (iotaOQ N A i) ρ) w ↔
        (nbr i w hw).IsdRW (L (N.l i)) (ρ.comp (Dec (F := H.E) (N.plOm.1 w)).subtype)) ∧
      (A.IsPotCrysW i (mapRep (iotaOQ N A i) ρ) w ↔
        (nbr i w hw).IsPotCrysW (L (N.l i)) (ρ.comp (Dec (F := H.E) (N.plOm.1 w)).subtype)) ∧
      ∀ (τ : H.E →+* Qbar (N.l i)) (τ' : ↥(nbr i w hw).Kw.1 →ₐ[ℚ_[N.l i]] ↥(nbr i w hw).LL.1),
        (∀ x : H.E, τ x = ((τ' ⟨(nbr i w hw).j (algebraMap H.E N.Om x), (nbr i w hw).j_E x⟩ :
          ↥(nbr i w hw).LL.1) : Loc.Om (N.l i))) →
        ((nbr i w hw).IsdRW (L (N.l i)) (ρ.comp (Dec (F := H.E) (N.plOm.1 w)).subtype) →
          ∀ a : ℤ, a ∈ A.jumpsW i (mapRep (iotaOQ N A i) ρ) τ ↔
          (nbr i w hw).IsJumpW (L (N.l i)) (ρ.comp (Dec (F := H.E) (N.plOm.1 w)).subtype) τ' a) ∧
        ((nbr i w hw).IsdRW (L (N.l i)) (ρ.comp (Dec (F := H.E) (N.plOm.1 w)).subtype) →
          ∀ a : ℤ, ((A.jumpsW i (mapRep (iotaOQ N A i) ρ) τ).count a : ℤ) =
            (nbr i w hw).multW (L (N.l i)) (ρ.comp (Dec (F := H.E) (N.plOm.1 w)).subtype) τ' a)) ∧
    ∀ (LL' : Loc.FinExt (N.l i)), (nbr i w hw).LL.1 ≤ LL'.1 →
      ∀ (m : ℕ) (ρ : G H.E N.Om →* GL (Fin m) ↥LL'.1),
      Continuous (fun g => ((ρ g : GL (Fin m) ↥LL'.1) : Matrix (Fin m) (Fin m) ↥LL'.1)) →
      (A.IsCrysW i (mapRep (algebraMap ↥LL'.1 (Qbar (N.l i))) ρ) w ↔
        (nbr i w hw).IsCrysE (L (N.l i)) LL' (ρ.comp (Dec (F := H.E) (N.plOm.1 w)).subtype)) ∧
      (A.IsdRW i (mapRep (algebraMap ↥LL'.1 (Qbar (N.l i))) ρ) w ↔
        (nbr i w hw).IsdRE (L (N.l i)) LL' (ρ.comp (Dec (F := H.E) (N.plOm.1 w)).subtype)) ∧
      (A.IsPotCrysW i (mapRep (algebraMap ↥LL'.1 (Qbar (N.l i))) ρ) w ↔
        (nbr i w hw).IsPotCrysE (L (N.l i)) LL' (ρ.comp (Dec (F := H.E) (N.plOm.1 w)).subtype)) ∧
      ∀ (τ : H.E →+* Qbar (N.l i)) (τ' : ↥(nbr i w hw).Kw.1 →ₐ[ℚ_[N.l i]] ↥LL'.1),
        (∀ x : H.E, τ x = ((τ' ⟨(nbr i w hw).j (algebraMap H.E N.Om x), (nbr i w hw).j_E x⟩ :
          ↥LL'.1) : Loc.Om (N.l i))) →
        ((nbr i w hw).IsdRE (L (N.l i)) LL' (ρ.comp (Dec (F := H.E) (N.plOm.1 w)).subtype) →
          ∀ a : ℤ, a ∈ A.jumpsW i (mapRep (algebraMap ↥LL'.1 (Qbar (N.l i))) ρ) τ ↔
          (nbr i w hw).IsJumpE (L (N.l i)) LL' (ρ.comp (Dec (F := H.E) (N.plOm.1 w)).subtype) τ' a) ∧
        ((nbr i w hw).IsdRE (L (N.l i)) LL' (ρ.comp (Dec (F := H.E) (N.plOm.1 w)).subtype) →
          ∀ a : ℤ, ((A.jumpsW i (mapRep (algebraMap ↥LL'.1 (Qbar (N.l i))) ρ) τ).count a : ℤ) =
            (nbr i w hw).multE (L (N.l i)) LL' (ρ.comp (Dec (F := H.E) (N.plOm.1 w)).subtype) τ' a)
end Glob2
end SharedN4
end Formalism.MainNotions.N
end


