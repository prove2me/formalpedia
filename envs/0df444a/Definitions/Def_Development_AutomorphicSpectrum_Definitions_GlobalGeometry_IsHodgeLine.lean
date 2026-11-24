-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_IsHodgeLine
-- name    : Development_AutomorphicSpectrum_Definitions_GlobalGeometry_IsHodgeLine
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-24T13:20:28.593906+00:00
-- url     : https://prove2.me/theorems/ca891b7a-1b48-4c54-aac7-f9a3dcb6868b
-- title:
--   Is Hodge Line
-- statement:
--   Definitions and structural lemmas for Is Hodge Line, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/GlobalGeometry/IsHodgeLine.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_PushInvertible
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ArithmeticHilbertSamuelLowerBound
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_HodgeIPIffHodgeFormConj
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_MemEigSpOfMemHtDual
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_IsGenericFlag
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_HodgeForm_conj
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_HodgeIP_conj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CompanionTheory.Ar
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
abbrev CMType (H : Host E) : Type := {τ : E →+* ℂ // τ (H.rt : E) = H.rt0}
def labelEmb (c : Coeff l) : CMType H ⊕ CMType H → (𝓞 E →+* c.F)
  | .inl τ => (τ.1.codRestrict c.F (c.conj τ.1)).comp (algebraMap (𝓞 E) E)
  | .inr τ => ((τ.1.codRestrict c.F (c.conj τ.1)).comp (algebraMap (𝓞 E) E)).comp (H.bar : 𝓞 E →+* 𝓞 E)
abbrev labelRk (D : Datum H) : CMType H ⊕ CMType H → ℕ := Sum.elim (fun _ => D.p) (fun _ => D.q)
def htLabel {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {G : Over X} [GrpObj G]
    {Li : Type} [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li) (L : LB G.left) (n : ℕ)
    (ρ : 𝓞 E →+* Module.End Ω Li) (σ : CMType H ⊕ CMType H → (𝓞 E →+* Ω)) : CMType H ⊕ CMType H → Lat ξ Li
  | .inl τ => M.htW L n ρ (σ (.inl τ)) (differentIdeal ℤ (𝓞 E))
  | .inr τ => M.htDual L n ρ (σ (.inr τ))
variable {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
structure HodgeCpt (Y : Model Xo c β) (S : Finset ℕ) {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type}
    (y : (Σ k, J k) → Ω) where

  X : Scheme.{0}

  ξ : Spec (CommRingCat.of Ω) ⟶ X
  all : ∀ q : X, genPt ξ ⤳ q
  tie : CoordTie ℤ ξ fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩
  normal : IsNormalScheme X

  f : X ⟶ Y.X

  Ω₀ : Type
  [fld₀ : Field Ω₀]

  ξ₀ : Spec (CommRingCat.of Ω₀) ⟶ Y.X
  gen₀ : IsCptGen ξ₀

  cst : c.F →+* Ω
  cst_over : ξ ≫ f ≫ Y.s = spMap (cst.comp β)

  fn : Ω₀ →+* Ω
  fn_over : GlobalTheory.CompanionTheory.Ar.Dominates ξ ξ₀ f fn

  t : SAB H X
  m : SABMap t Y.t f

  Li : Type
  [acg : AddCommGroup Li]
  [mod : Module Ω Li]
  M : LieModel t.G ξ Li

  ρ : 𝓞 E →+* Module.End Ω Li
  act : M.IsActOf t.act.act ρ
  S_prime : ∀ p ∈ S, p.Prime

  R : ℕ → ℕ
  R_ge : ∀ p ∈ S, 4 ≤ R p
  tors : ∀ p ∈ S, FullTorsion t.G ξ (p ^ R p)
  vb : ∀ s, (Lat.patch S (M.eigLat ρ (cst.comp (labelEmb c s)))
      fun p => htLabel M t.PP.L (p ^ R p) ρ (fun s' => cst.comp (labelEmb c s')) s).IsVB (labelRk D s)
    (eigSp ρ (cst.comp (labelEmb c s)))
attribute [instance] HodgeCpt.fld₀ HodgeCpt.acg HodgeCpt.mod
namespace HodgeCpt
variable {Y : Model Xo c β} {S : Finset ℕ} {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type}
  {y : (Σ k, J k) → Ω} (𝔐 : HodgeCpt Y S y)
def emb (s : CMType H ⊕ CMType H) : 𝓞 E →+* Ω := 𝔐.cst.comp (labelEmb c s)
def Vgen (s : CMType H ⊕ CMType H) : Submodule Ω 𝔐.Li := eigSp 𝔐.ρ (𝔐.emb s)
def dR (s : CMType H ⊕ CMType H) : Lat 𝔐.ξ 𝔐.Li := 𝔐.M.eigLat 𝔐.ρ (𝔐.emb s)
def HT (p : ℕ) (s : CMType H ⊕ CMType H) : Lat 𝔐.ξ 𝔐.Li := htLabel 𝔐.M 𝔐.t.PP.L (p ^ 𝔐.R p) 𝔐.ρ 𝔐.emb s
def V (s : CMType H ⊕ CMType H) : Lat 𝔐.ξ 𝔐.Li := Lat.patch S (𝔐.dR s) fun p => 𝔐.HT p s
def IsCover (d : ℕ) : Prop :=
  0 < d ∧ letI := 𝔐.fn.toAlgebra; Module.finrank 𝔐.Ω₀ Ω = d
def Interior {R : Type} [CommRing R] [IsLocalRing R] (z : Spec (CommRingCat.of R) ⟶ 𝔐.X) : Prop :=
  centre z ∈ abLocus 𝔐.t.G
structure Flag where

  b : ∀ s, Fin (labelRk D s) → 𝔐.Li
  sub : ∀ s, (𝔐.V s).IsFlagVBOn Set.univ (b s)

  Li₀ : Type
  [acg : AddCommGroup Li₀]
  [mod : Module 𝔐.Ω₀ Li₀]
  M₀ : LieModel Y.t.G 𝔐.ξ₀ Li₀

  j : Li₀ →+ 𝔐.Li
  j_pt : ∀ e, (𝔐.M.pt (j e)).left ≫ 𝔐.m.φ = spMap (dualMap 𝔐.fn) ≫ (M₀.pt e).left

  V₀ : CMType H ⊕ CMType H → Submodule 𝔐.Ω₀ Li₀
  V₀_mem : ∀ s e, e ∈ V₀ s ↔ j e ∈ 𝔐.Vgen s

  deg : ℕ
  generic : letI := 𝔐.fn.toAlgebra; IsGenericFlag (Ω' := Ω) j V₀ b deg
attribute [instance] Flag.acg Flag.mod
variable {𝔐}
def rootIdx (D : Datum H) (r : CMType H × Fin (D.p + D.q)) : Σ s, Fin (labelRk D s) :=
  if h : (r.2 : ℕ) < D.p then ⟨.inl r.1, ⟨r.2, h⟩⟩
  else ⟨.inr r.1, ⟨D.p + D.q - 1 - r.2, by have := r.2.2; show _ < D.q; omega⟩⟩
def rootSgn (D : Datum H) (r : CMType H × Fin (D.p + D.q)) : ℤ := if (r.2 : ℕ) < D.p then 1 else -1
def Flag.rootLat (Fl : 𝔐.Flag) (r : CMType H × Fin (D.p + D.q)) : Lat 𝔐.ξ Ω :=
  Lat.tens (fun _ : Unit => (𝔐.V (rootIdx D r).1).gr (Fl.b (rootIdx D r).1) (rootIdx D r).2) fun _ => rootSgn D r
def Flag.RootLines (Fl : 𝔐.Flag) (xdeg : CMType H × Fin (D.p + D.q) → K → ℤ)
    (e : CMType H × Fin (D.p + D.q) → Ω) : Prop :=
  ∀ r, (Fl.rootLat r).IsDegOn Set.univ y (xdeg r) (e r)
def Flag.IsHodgeLine [∀ k, Fintype (J k)] (Fl : 𝔐.Flag) (r : CMType H × Fin (D.p + D.q)) (e₀ : Ω)
    (A : HermLine J) : Prop :=
  ∀ (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X) (w : (Σ k, J k) → ℂ), CoordsAt 𝔐.ξ y z w → 𝔐.Interior z →
    ∀ t ν, 𝔐.M.IsGrNorm 𝔐.t.PP.L (𝔐.V (rootIdx D r).1) (Fl.b (rootIdx D r).1) (rootIdx D r).2 z t ν →
      SecNorm 𝔐.ξ y A e₀ z w (t ^ rootSgn D r) (ν ^ rootSgn D r)
end HodgeCpt
end GlobalTheory.CompanionTheory.Ar


