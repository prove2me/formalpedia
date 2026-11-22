-- Prove2me | Definitions.Def_AlpoGeRow0
-- name    : AlpoGeRow0
-- status  : Definition
-- author  : @RSoulat
-- created : 2026-11-22T15:33:23.357665+00:00
-- url     : https://prove2.me/theorems/c98641a2-b5fb-4f9e-bef4-c1b839f27862
-- title:
--   Alpöge’s Row0 interface for local–global compatibility
-- statement:
--   The $p$-adic place predicate $\operatorname{IsQp}(w)$ requires a continuous ring isomorphism from $\mathbb Q_p$ to the completion $E_w$ for some prime $p$. The records Away, Above, and Props express the local–global comparisons and weight conditions of UpperTheory.GalStar.Row0. The quantified existence assertion Row0 uses the same automorphic and Galois data as Row0b, with the tame compatibility clause applying at places satisfying $\operatorname{IsQp}(w)$.
--
--   This interface makes the stronger local compatibility statement independently importable while reusing the published global and local arithmetic definitions.
-- source:
--   L. Alpöge with Claude, 20 November 2026 Lean release, WeightsConjAlt.lean, IsQp, Away, Above, Props, and Row0. https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Development/AutomorphicArithmetic/Foundations/GaloisRepresentations/TypeConditions/WeightsConjAlt.lean#L20-L89

import Definitions.Def_AlpoGeB008

/-!
The stronger compatibility interface from WeightsConjAlt.lean in Alpöge's
November 2026 GRH release. The local predicates and arithmetic objects shared
with Row0b come from the existing Prove2Me bundles.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual
  ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc
  Formalism.MainNotions.N Polynomial
open GlobalTheory GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst
  GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.GalStar

open UpperTheory.GalS (TmW)

def IsQp {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) : Prop :=
  ∃ (p : ℕ) (_ : Fact p.Prime) (iso : ℚ_[p] ≃+* w.adicCompletion E), Continuous iso

section Local

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

structure Away (x y : WD h) : Prop where
  dim : x.lpDim = y.lpDim
  tor : Tor y → y.mono0 → x = y
  tame0 : IsQp w → TmW y → Sqf y → y.mono0 →
    x.mono0 ∧ ∀ g : ↥(Weil h), deg g = 0 → x.charPol g = y.charPol g

end Local

variable (Rc : RecNotion) {E Ω : Type} [Field E] [NumberField E] [Field Ω]
  [Algebra E Ω] {l : ℕ} [Fact l.Prime] {a : ℕ} [IsAlgClosure E Ω] [IsCMField E]

structure Above (π : CuspSub E a) (ι : Qbar l ≃+* ℂ) (r : G E Ω →* GL (Fin a) (Qbar l))
    (HT : (E →+* Qbar l) → Multiset ℤ) (P : LocPrime l)
    {w : HeightOneSpectrum (𝓞 E)} {A : ValuationSubring Ω}
    (h : IsPlaceOver A w) {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
    (Bw : LocBridge l E Ω (Dec (F := E) A) O) (hj : Pst.Induces Bw) : Prop where
  crys : ∀ σ, π.IsLocComp w σ → SmGL.IsSpherical σ.ρ →
    IsCrysAt P Bw (r.comp (Dec (F := E) A).subtype) ∧
    IsdRAt P Bw (r.comp (Dec (F := E) A).subtype) ∧
    ∀ (τ : E →+* Qbar l) (LL' : FinExt l) (τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1),
      IsInduced Bw τ τ' → IsJumpsAt P Bw (r.comp (Dec (F := E) A).subtype) τ (HT τ)
  nice : ∀ σ, π.IsLocComp w σ → ∀ rc, Rc h rc →
    ((IsQp w ∧ TmW (rc (algNorm σ)) ∧ Sqf (rc (algNorm σ))) ∨ Tor (rc (algNorm σ))) →
    (rc (algNorm σ)).mono0 →
    IsdRAt P Bw (r.comp (Dec (F := E) A).subtype) ∧
    IsPstAt P Bw (r.comp (Dec (F := E) A).subtype) ∧
    (∀ (τ : E →+* Qbar l) (LL' : FinExt l) (τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1),
      IsInduced Bw τ τ' → IsJumpsAt P Bw (r.comp (Dec (F := E) A).subtype) τ (HT τ)) ∧
    Away (wdAt P ι Bw h hj (r.comp (Dec (F := E) A).subtype)) (rc (algNorm σ))

structure Props (π : CuspSub E a) (ι : Qbar l ≃+* ℂ)
    (r : G E Ω →* GL (Fin a) (Qbar l)) (wt : ℤ)
    (HT : (E →+* Qbar l) → Multiset ℤ) : Prop where
  cont : Continuous r
  ss : IsSSRep r
  away : ∀ (w : HeightOneSpectrum (𝓞 E)) (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal)
    (A : ValuationSubring Ω) (h : IsPlaceOver A w)
    (rc : IrrGL (w.adicCompletion E) → WD h), Rc h rc →
    ∀ σ, π.IsLocComp w σ → Away (wdOf h hl ι r) (rc (algNorm σ))
  weights : ∀ τ : E →+* Qbar l, (HT τ).map (fun n : ℤ => (n : ℂ)) =
    ((CG.mk π).infChar (ι.toRingHom.comp τ)).map (fun z => ((a : ℂ) - 1) / 2 - z)
  weights_conj : ∀ τ : E →+* Qbar l,
    HT (τ.comp (IsCMField.complexConj E).toRingEquiv.toRingHom) = (HT τ).map (wt - ·)
  above : ∀ (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) →
    ∀ (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (h : IsPlaceOver A w)
      (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
      (Bw : LocBridge l E Ω (Dec (F := E) A) O) (hj : Pst.Induces Bw),
        Above Rc π ι r HT P h Bw hj

def Row0 : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ), 1 ≤ a →
    ∀ (π : CuspSub E a) (χ : HChar (maximalRealSubfield E)),
      (CG.mk π).IsRegAlg → GlobalTheory.ContraPair.PolarizedPair π χ →
      ∃ (r : G E Ω →* GL (Fin a) (Qbar l)) (wt : ℤ)
        (HT : (E →+* Qbar l) → Multiset ℤ), Props Rc π ι r wt HT

end UpperTheory.GalStar


