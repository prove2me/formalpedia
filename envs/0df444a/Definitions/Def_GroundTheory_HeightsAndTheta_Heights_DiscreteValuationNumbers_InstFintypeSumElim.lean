-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_InstFintypeSumElim
-- name    : GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_InstFintypeSumElim
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:30:40.103023+00:00
-- url     : https://prove2.me/theorems/78add076-3480-4c7f-b060-bc31faee9e52
-- title:
--   Inst Fintype Sum Elim
-- statement:
--   Definitions and structural lemmas for Inst Fintype Sum Elim, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/DiscreteValuationNumbers/InstFintypeSumElim.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_IsFieldIntersection
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_Bundle
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1
instance instFintypeSumElim {K K' : Type} (ι : K → Type) (ι' : K' → Type) [∀ k, Fintype (ι k)]
    [∀ k, Fintype (ι' k)] : ∀ k, Fintype (Sum.elim ι ι' k)
  | .inl k => inferInstanceAs (Fintype (ι k))
  | .inr k => inferInstanceAs (Fintype (ι' k))
section Coord
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
def mcMap (R : Type*) [CommRing R] {Ω : Type*} [CommRing Ω] [Algebra R Ω] (x : (Σ k, ι k) → Ω) :
    MRingOver R ι →ₐ[R] MvPolynomial K Ω :=
  aeval fun p => MvPolynomial.C (x p) * MvPolynomial.X p.1
def mcIdeal (R : Type*) [CommRing R] {Ω : Type*} [CommRing Ω] [Algebra R Ω]
    (x : (Σ k, ι k) → Ω) : Ideal (MRingOver R ι) :=
  RingHom.ker (mcMap R x)
def mseg {Ω : Type*} [CommMonoid Ω] (x : (Σ k, ι k) → Ω) : (∀ k, ι k) → Ω :=
  fun s => ∏ k, x ⟨k, s k⟩
def chartMon {Ω : Type*} [Field Ω] (x : (Σ k, ι k) → Ω) (s : ∀ k, ι k) (a : K → ℤ) : Ω :=
  ∏ k, x ⟨k, s k⟩ ^ a k
def joinCoord {K' : Type} {ι' : K' → Type} {Ω : Type*} (x : (Σ k, ι k) → Ω)
    (z : (Σ k, ι' k) → Ω) : (Σ k : K ⊕ K', Sum.elim ι ι' k) → Ω
  | ⟨.inl k, i⟩ => x ⟨k, i⟩
  | ⟨.inr k, i⟩ => z ⟨k, i⟩
def liftVar {K' : Type} (ι' : K' → Type) : (Σ k, ι k) → (Σ k : K ⊕ K', Sum.elim ι ι' k) :=
  fun p => ⟨.inl p.1, p.2⟩
def pullDeg {K' : Type} (a : K → ℤ) : K ⊕ K' → ℤ :=
  Sum.elim a 0
def restrictChart {K' : Type} {ι' : K' → Type} (s : ∀ k : K ⊕ K', Sum.elim ι ι' k) : ∀ k, ι k :=
  fun k => s (.inl k)
end Coord
section Numbers
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
def monoList {r : ℕ} {A : Type*} (deg : Fin r → A) (μ : Fin r →₀ ℕ) : List A :=
  (List.finRange r).flatMap fun s => List.replicate (μ s) (deg s)
def polyNum {F : Type*} [Field F] (I : IFamily F ι) (V : Ideal (MRingOver F ι)) (n : ℕ) {r : ℕ}
    (deg : Fin r → K → ℤ) (Q : MvPolynomial (Fin r) ℤ) : ℤ :=
  ∑ μ ∈ Q.support, Q.coeff μ * if h : (monoList deg μ).length = n then
    I V n (fun j => (monoList deg μ).get (Fin.cast h.symm j)) else 0
def fieldNum (F : Type*) [Field F] (κ : K → Type) [∀ k, Fintype (κ k)] : IFamily F κ :=
  Classical.epsilon fun I => IsFieldIntersection I
def divDiff {r : ℕ} (l : Fin r) (G : MvPolynomial (Fin r) ℤ) : MvPolynomial (Fin (r + r)) ℤ :=
  ∑ μ ∈ G.support, MvPolynomial.C (G.coeff μ) *
    (∏ j ∈ Finset.univ.filter (fun j => j < l), X (Fin.natAdd r j) ^ μ j) *
    (∑ a ∈ Finset.range (μ l), X (Fin.castAdd r l) ^ a * X (Fin.natAdd r l) ^ (μ l - 1 - a)) *
    (∏ j ∈ Finset.univ.filter (fun j => l < j), X (Fin.castAdd r j) ^ μ j)
def hNeg (N n c : ℕ) : MvPolynomial (Fin (N + n)) ℤ :=
  aeval (fun i : Fin N => -X (Fin.castAdd n i)) (hsymm (Fin N) ℤ c)
def segrePoly (N m n : ℕ) : MvPolynomial (Fin (N + n)) ℤ :=
  (if N ≤ m + 1 then hNeg N n (m + 1 - N) else 0) * ∏ j : Fin n, X (Fin.natAdd N j)
def zetaDeg (tw : K → ℤ) : K ⊕ Unit → ℤ :=
  Sum.elim (fun k => -tw k) fun _ => 1
end Numbers
section DVR
variable (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
abbrev kap := IsLocalRing.ResidueField O
def IsModelOver (P : Ideal (MRingOver O ι)) (d : ℕ) : Prop :=
  Nonempty K ∧ IsMultiProjPrime P ∧ P.comap (C : O →+* MRingOver O ι) = ⊥ ∧
    ringKrullDim (MRingOver O ι ⧸ P) = ((d + 1 + Fintype.card K : ℕ) : WithBot ℕ∞)
def redIdeal (G : Ideal (MRingOver O ι)) : Ideal (MRingOver (kap O) ι) :=
  G.map (MvPolynomial.map (IsLocalRing.residue O))
def IsVertDiv (P : Ideal (MRingOver O ι)) (b : K → ℤ) (f g : MRingOver O ι) : Prop :=
  (∃ α β : K → ℕ, IsMultiHomog f α ∧ IsMultiHomog g β ∧ ∀ k, (α k : ℤ) - β k = b k) ∧
    f ∉ P ∧ g ∉ P ∧
    ∀ Q : Ideal (MRingOver O ι), IsMultiProjPrime Q → P ≤ Q →
      Q.comap (C : O →+* MRingOver O ι) = ⊥ →
      ∃ u v : MRingOver O ι, (∃ γ, IsMultiHomog u γ) ∧ (∃ δ, IsMultiHomog v δ) ∧ u ∉ Q ∧ v ∉ Q ∧
        u * f - v * g ∈ P
def ratCyc (P : Ideal (MRingOver O ι)) (f g : MRingOver O ι) : Ideal (MRingOver O ι) →₀ ℤ :=
  Finsupp.mapRange (fun n : ℕ => (n : ℤ)) Nat.cast_zero (divCycle P f) -
    Finsupp.mapRange (fun n : ℕ => (n : ℤ)) Nat.cast_zero (divCycle P g)
def vEval (J : Ideal (MRingOver (kap O) ι) → ℤ) (Z : Ideal (MRingOver O ι) →₀ ℤ) : ℤ :=
  Z.sum fun G m => m * J (redIdeal O G)
def pairNum (I : IFamily (kap O) ι) (P : Ideal (MRingOver O ι)) (d : ℕ) {r : ℕ}
    (y y' : Fin r → K → ℤ) (f g : Fin r → MRingOver O ι) (G : MvPolynomial (Fin r) ℤ) : ℤ :=
  ∑ l, vEval O (fun W => polyNum I W d (Fin.append y y') (divDiff l G)) (ratCyc O P (f l) (g l))
end DVR
section Flags
variable (o : Type*) [CommRing o] {Ω : Type*} [Field Ω] [Algebra o Ω]
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
def IsUnitOn {σ : Type*} (y : σ → Ω) (s : σ) (f w : Ω) : Prop :=
  w ≠ 0 ∧ (∃ n : ℕ, f ^ n * w ∈ chartRing o y s) ∧ ∃ n : ℕ, f ^ n * w⁻¹ ∈ chartRing o y s
def IsGradedFrame (x : (Σ k, ι k) → Ω) {N : ℕ} {E : Type*} [AddCommGroup E] [Module Ω E]
    (B : ChartBundle o (mseg x) N E) (Vs : Fin (N + 1) → Submodule Ω E) (m : Fin N → K → ℤ)
    (gen : Fin N → E) : Prop :=
  ∀ s, mseg x s ≠ 0 → ∃ (k : ℕ) (f c : Fin k → Ω), (∀ l, f l ∈ chartRing o (mseg x) s) ∧
    (∀ l, c l ∈ chartRing o (mseg x) s) ∧ ∑ l, c l * f l = 1 ∧
    ∀ l, ∃ b : Fin N → E, LinearIndependent Ω b ∧ Submodule.span Ω (Set.range b) = ⊤ ∧
      (∀ e, (∃ n : ℕ, f l ^ n • e ∈ B.lat s) ↔
        ∃ a : Fin N → Ω, (∀ q, ∃ n : ℕ, f l ^ n * a q ∈ chartRing o (mseg x) s) ∧
          e = ∑ q, a q • b q) ∧
      ∀ i, ∃ w : Ω, IsUnitOn o (mseg x) s (f l) w ∧
        b i - (w * chartMon x s (m i)) • gen i ∈ Vs i.castSucc
structure FullFlag (x : (Σ k, ι k) → Ω) {N : ℕ} {E : Type*} [AddCommGroup E] [Module Ω E]
    (B : ChartBundle o (mseg x) N E) where

  Vs : Fin (N + 1) → Submodule Ω E
  mono : Monotone Vs
  dim : ∀ i, Module.finrank Ω (Vs i) = (i : ℕ)
  top : Vs (Fin.last N) = ⊤

  deg : Fin N → K → ℤ

  gen : Fin N → E
  gen_mem : ∀ i, gen i ∈ Vs i.succ
  frame : IsGradedFrame o x B Vs deg gen
def IsDualGen (x : (Σ k, ι k) → Ω) {N : ℕ} {E : Type*} [AddCommGroup E] [Module Ω E]
    (B : ChartBundle o (mseg x) N E) (tw : K → ℤ) {M : ℕ} (φ : Fin M → Module.Dual Ω E) : Prop :=
  ∀ s, mseg x s ≠ 0 →
    (∀ j, ∀ e ∈ B.lat s, ∃ a ∈ chartRing o (mseg x) s, φ j e = a * chartMon x s tw) ∧
    ∀ ψ : Module.Dual Ω E, (∀ e ∈ B.lat s, ψ e ∈ chartRing o (mseg x) s) →
      ∃ c : Fin M → Ω, (∀ j, c j ∈ chartRing o (mseg x) s) ∧
        ψ = ∑ j, (c j * (chartMon x s tw)⁻¹) • φ j
def peCoord (x : (Σ k, ι k) → Ω) {N : ℕ} {E : Type*} [AddCommGroup E] [Module Ω E]
    (bas : Module.Basis (Fin N) Ω E) {M : ℕ} (φ : Fin M → Module.Dual Ω E) :
    (Σ k : K ⊕ Unit, Sum.elim ι (fun _ : Unit => Fin M) k) → FractionRing (MvPolynomial (Fin N) Ω) :=
  joinCoord (fun p => algebraMap Ω (FractionRing (MvPolynomial (Fin N) Ω)) (x p))
    fun p : (Σ _ : Unit, Fin M) => algebraMap (MvPolynomial (Fin N) Ω) (FractionRing (MvPolynomial (Fin N) Ω))
      (∑ q, MvPolynomial.C (φ p.2 (bas q)) * MvPolynomial.X q)
end Flags
section Bundles
universe uΩ uV uV₁
variable (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable {Ω : Type uΩ} [Field Ω] [Algebra O Ω]
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
def SameGeneric (x : (Σ k, ι k) → Ω) {N : ℕ} {V : Type*} [AddCommGroup V] [Module Ω V]
    (E E' : ChartBundle O (mseg x) N V) : Prop :=
  ∀ s, mseg x s ≠ 0 →
    (∀ v ∈ E.lat s, ∃ c : O, c ≠ 0 ∧ algebraMap O Ω c • v ∈ E'.lat s) ∧
    ∀ v ∈ E'.lat s, ∃ c : O, c ≠ 0 ∧ algebraMap O Ω c • v ∈ E.lat s
def LatLE (x : (Σ k, ι k) → Ω) {N : ℕ} {V : Type*} [AddCommGroup V] [Module Ω V]
    (E E' : ChartBundle O (mseg x) N V) : Prop :=
  ∀ s, mseg x s ≠ 0 → E.lat s ≤ E'.lat s
structure FlagPair (x : (Σ k, ι k) → Ω) {N : ℕ} {V : Type*} [AddCommGroup V] [Module Ω V]
    (E E' : ChartBundle O (mseg x) N V) extends FullFlag O x E where

  deg' : Fin N → K → ℤ

  gen' : Fin N → V
  gen'_mem : ∀ i, gen' i ∈ Vs i.succ
  frame' : IsGradedFrame O x E' Vs deg' gen'

  f : Fin N → MRingOver O ι

  g : Fin N → MRingOver O ι
  rel : ∀ i, gen' i - (aeval x (f i) / aeval x (g i)) • gen i ∈ Vs i.castSucc
  vert : ∀ i, IsVertDiv O (mcIdeal O x) (deg i - deg' i) (f i) (g i)
def IsPull {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]
    (x : (Σ k, ι k) → Ω) (z : (Σ k, ι' k) → Ω) {N : ℕ} {V : Type*} [AddCommGroup V] [Module Ω V]
    (E : ChartBundle O (mseg x) N V) (EB : ChartBundle O (mseg (joinCoord x z)) N V) : Prop :=
  ∀ s, mseg (joinCoord x z) s ≠ 0 → EB.lat s = AddSubgroup.closure
    {v | ∃ a ∈ chartRing O (mseg (joinCoord x z)) s, ∃ e ∈ E.lat (restrictChart s), v = a • e}
def fnField {Ω₁ : Type*} [Field Ω₁] [Algebra O Ω₁] {K₀ : Type} {κ : K₀ → Type}
    (y : (Σ k, κ k) → Ω₁) : Subfield Ω₁ :=
  Subfield.closure (Set.range (algebraMap O Ω₁) ∪
    Set.range fun q : (Σ k, κ k × κ k) => y ⟨q.1, q.2.1⟩ / y ⟨q.1, q.2.2⟩)
structure FlagModel (x : (Σ k, ι k) → Ω) (d N : ℕ) {V : Type*} [AddCommGroup V] [Module Ω V]
    (E E' : ChartBundle O (mseg x) N V) where

  K' : Type
  [finK : Fintype K']

  ι' : K' → Type
  [finι : ∀ k, Fintype (ι' k)]

  z : (Σ k, ι' k) → Ω
  model : IsModelOver O (mcIdeal O (joinCoord x z)) d

  birat : fnField O (joinCoord x z) = fnField O x

  EB : ChartBundle O (mseg (joinCoord x z)) N V

  E'B : ChartBundle O (mseg (joinCoord x z)) N V
  pull : IsPull O x z E EB
  pull' : IsPull O x z E' E'B
  flag : FlagPair O (joinCoord x z) EB E'B
attribute [instance] FlagModel.finK FlagModel.finι
def FlagModel.value {x : (Σ k, ι k) → Ω} {d N : ℕ} {V : Type*} [AddCommGroup V] [Module Ω V]
    {E E' : ChartBundle O (mseg x) N V} (F : FlagModel O x d N E E')
    (I : IFamily (kap O) (Sum.elim ι F.ι')) (G : MvPolynomial (Fin N) ℤ) {r : ℕ}
    (y y' : Fin r → K → ℤ) (f g : Fin r → MRingOver O ι) (Q : MvPolynomial (Fin r) ℤ) : ℤ :=
  pairNum O I (mcIdeal O (joinCoord x F.z)) d
    (Fin.append F.flag.deg fun l => pullDeg (K' := F.K') (y l))
    (Fin.append F.flag.deg' fun l => pullDeg (K' := F.K') (y' l))
    (Fin.append F.flag.f fun l => rename (liftVar F.ι') (f l))
    (Fin.append F.flag.g fun l => rename (liftVar F.ι') (g l))
    (rename (Fin.castAdd r) G * rename (Fin.natAdd N) Q)
open Classical in

def ck (x : (Σ k, ι k) → Ω) (d N : ℕ) {V : Type*} [AddCommGroup V] [Module Ω V]
    (E E' : ChartBundle O (mseg x) N V) (k : ℕ) {q : ℕ} (L : Fin q → K → ℤ)
    (Q : MvPolynomial (Fin q) ℤ) : ℤ :=
  if h : Nonempty (FlagModel O x d N E E') then
    (Classical.choice h).value O (fieldNum (kap O) _) (psum (Fin N) ℤ k) L L (fun _ => 1)
      (fun _ => 1) Q
  else 0
open Classical in

def rootNum (x : (Σ k, ι k) → Ω) (d N : ℕ) {V : Type*} [AddCommGroup V] [Module Ω V]
    (E : ChartBundle O (mseg x) N V) (G : MvPolynomial (Fin N) ℤ) {q : ℕ} (L : Fin q → K → ℤ)
    (Q : MvPolynomial (Fin q) ℤ) (c : O) : ℤ :=
  if h : Nonempty (FlagModel O x d N E E) then
    vEval O (fun W => polyNum (fieldNum (kap O) (Sum.elim ι (Classical.choice h).ι')) W d
        (Fin.append (Classical.choice h).flag.deg fun l => pullDeg (K' := (Classical.choice h).K') (L l))
        (rename (Fin.castAdd q) G * rename (Fin.natAdd N) Q))
      (Finsupp.mapRange (fun n : ℕ => (n : ℤ)) Nat.cast_zero
        (divCycle (mcIdeal O (joinCoord x (Classical.choice h).z)) (MvPolynomial.C c)))
  else 0
def IsSubQuot (x : (Σ k, ι k) → Ω) {N N₁ N₂ : ℕ} {V V₁ V₂ : Type*} [AddCommGroup V] [Module Ω V]
    [AddCommGroup V₁] [Module Ω V₁] [AddCommGroup V₂] [Module Ω V₂]
    (E : ChartBundle O (mseg x) N V) (i : V₁ →ₗ[Ω] V) (q : V →ₗ[Ω] V₂)
    (E₁ : ChartBundle O (mseg x) N₁ V₁) (E₂ : ChartBundle O (mseg x) N₂ V₂) : Prop :=
  Function.Injective i ∧ Function.Surjective q ∧ LinearMap.range i = LinearMap.ker q ∧
    ∀ s, mseg x s ≠ 0 → E₁.lat s = (E.lat s).comap i.toAddMonoidHom ∧
      E₂.lat s = (E.lat s).map q.toAddMonoidHom
def QuotIso (x : (Σ k, ι k) → Ω) {N N₁ : ℕ} {V V₁ : Type*} [AddCommGroup V] [Module Ω V]
    [AddCommGroup V₁] [Module Ω V₁] (E E' : ChartBundle O (mseg x) N V)
    (E₁ E₁' : ChartBundle O (mseg x) N₁ V₁) : Prop :=
  ∃ Pb : ChartBundle O (mseg x) (N + N₁) (V × V₁), ∀ s, mseg x s ≠ 0 →
    (∀ v, (v, 0) ∈ Pb.lat s ↔ v ∈ E'.lat s) ∧ (∀ v, (∃ w, (v, w) ∈ Pb.lat s) ↔ v ∈ E.lat s) ∧
    (∀ w, (0, w) ∈ Pb.lat s ↔ w ∈ E₁'.lat s) ∧ (∀ w, (∃ v, (v, w) ∈ Pb.lat s) ↔ w ∈ E₁.lat s)
def IsQuotLin (x : (Σ k, ι k) → Ω) {N₁ : ℕ} {V₁ : Type*} [AddCommGroup V₁] [Module Ω V₁]
    (E₁ E₁' : ChartBundle O (mseg x) N₁ V₁) (s : ∀ k, ι k) {Nm : Type*} [AddCommGroup Nm]
    [Module (chartRing O (mseg x) s) Nm] (lam : V₁ → Nm) : Prop :=
  (∀ v ∈ E₁.lat s, ∀ w ∈ E₁.lat s, lam (v + w) = lam v + lam w) ∧ (∀ v ∈ E₁'.lat s, lam v = 0) ∧
    ∀ a : chartRing O (mseg x) s, ∀ v ∈ E₁.lat s, lam ((a : Ω) • v) = a • lam v
def IsFrobPres (p : ℕ) (x : (Σ k, ι k) → Ω) {N N₁ : ℕ} {V : Type uV} {V₁ : Type uV₁} [AddCommGroup V]
    [Module Ω V] [AddCommGroup V₁] [Module Ω V₁] (E E' : ChartBundle O (mseg x) N V)
    (E₁ E₁' : ChartBundle O (mseg x) N₁ V₁) (ψ : (∀ k, ι k) → V → V₁) : Prop :=
  (∀ s, mseg x s ≠ 0 →
    (∀ v ∈ E.lat s, ψ s v ∈ E₁.lat s) ∧ (∀ v ∈ E'.lat s, ψ s v ∈ E₁'.lat s) ∧
    (∀ v ∈ E.lat s, ∀ w ∈ E.lat s, ψ s (v + w) - ψ s v - ψ s w ∈ E₁'.lat s) ∧
    (∀ a ∈ chartRing O (mseg x) s, ∀ v ∈ E.lat s, ψ s (a • v) - a ^ p • ψ s v ∈ E₁'.lat s) ∧
    (∀ v ∈ E₁.lat s, (p : Ω) • v ∈ E₁'.lat s) ∧
    ∀ (Nm : Type (max uΩ uV uV₁)) [AddCommGroup Nm] [Module (chartRing O (mseg x) s) Nm],
      (∀ n : Nm, (p : chartRing O (mseg x) s) • n = 0) →
      ∀ χ : V → Nm, (∀ v ∈ E.lat s, ∀ w ∈ E.lat s, χ (v + w) = χ v + χ w) →
        (∀ v ∈ E'.lat s, χ v = 0) →
        (∀ a : chartRing O (mseg x) s, ∀ v ∈ E.lat s, χ ((a : Ω) • v) = a ^ p • χ v) →
        ∃ lam : V₁ → Nm, IsQuotLin O x E₁ E₁' s lam ∧ (∀ v ∈ E.lat s, lam (ψ s v) = χ v) ∧
          ∀ lam' : V₁ → Nm, IsQuotLin O x E₁ E₁' s lam' → (∀ v ∈ E.lat s, lam' (ψ s v) = χ v) →
            ∀ v ∈ E₁.lat s, lam' v = lam v) ∧
  ∀ s t, mseg x s ≠ 0 → mseg x t ≠ 0 → ∀ v ∈ E.lat s, ∀ m : ℕ,
    (mseg x s / mseg x t) ^ m • v ∈ E.lat t → ∃ n : ℕ, (mseg x s / mseg x t) ^ n •
      (ψ t ((mseg x s / mseg x t) ^ m • v) - (mseg x s / mseg x t) ^ (p * m) • ψ s v) ∈ E₁'.lat t
def bcCoord {Ω₁ : Type*} [Field Ω₁] [Algebra Ω Ω₁] {K' : Type} {ι' : K' → Type}
    (x : (Σ k, ι k) → Ω) (z : (Σ k, ι' k) → Ω₁) : (Σ k : K ⊕ K', Sum.elim ι ι' k) → Ω₁ :=
  joinCoord (fun p => algebraMap Ω Ω₁ (x p)) z
def IsPullBC {Ω₁ : Type*} [Field Ω₁] [Algebra O Ω₁] [Algebra Ω Ω₁] {K' : Type} [Fintype K']
    {ι' : K' → Type} [∀ k, Fintype (ι' k)] (x : (Σ k, ι k) → Ω) (z : (Σ k, ι' k) → Ω₁) {N : ℕ}
    {V V₁ : Type*} [AddCommGroup V] [Module Ω V] [AddCommGroup V₁] [Module Ω₁ V₁] [Module Ω V₁]
    (bc : V →ₗ[Ω] V₁) (E : ChartBundle O (mseg x) N V)
    (E₁ : ChartBundle O (mseg (bcCoord x z)) N V₁) : Prop :=
  ∀ s, mseg (bcCoord x z) s ≠ 0 → E₁.lat s = AddSubgroup.closure
    {v | ∃ a ∈ chartRing O (mseg (bcCoord x z)) s, ∃ e ∈ E.lat (restrictChart s), v = a • bc e}
def modelDeg {Ω₁ : Type*} [Field Ω₁] [Algebra O Ω₁] [Algebra Ω Ω₁] {K' : Type} {ι' : K' → Type}
    (x : (Σ k, ι k) → Ω) (z : (Σ k, ι' k) → Ω₁) : ℕ :=
  Module.finrank (fnField O (fun p => algebraMap Ω Ω₁ (x p)))
    (IntermediateField.adjoin (fnField O (fun p => algebraMap Ω Ω₁ (x p)))
      (fnField O (bcCoord x z) : Set Ω₁))
end Bundles
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles


