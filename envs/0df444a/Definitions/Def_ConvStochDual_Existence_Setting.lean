-- Prove2me | Definitions.Def_ConvStochDual_Existence_Setting
-- name    : ConvStochDual_Existence_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T00:30:04.797977+00:00
-- url     : https://prove2.me/theorems/cc91be36-c0da-4f90-b3ac-fb989494bee7
-- title:
--   Sections 1–4: probability spaces, random-variable duality and stochastic primal/dual objectives
-- statement:
--   Let $(\Omega,\mathcal F,P)$ be a probability space with a finite filtration. The spaces $\mathcal X$ and $\mathcal U$ are Fréchet spaces embedded in almost-everywhere classes of finite-dimensional random variables; $\mathcal V$ and $\mathcal Y$ are their separating random-variable dual partners. Each space is solid and decomposable. Both strong topological duals split uniquely into a random-variable component and a singular component.
--
--   A convex normal integrand $f$ defines the extended-real integral functional $Ef$ using the paper's positive-part convention. The adaptive primal values are
--
--   $$\inf(SP)=\inf_{x\in\mathcal N} Ef(x,\bar u),\qquad \inf(SP_{\mathcal X})=\varphi(0,\bar u).$$
--
--   The ordinary dual ranges over $(p,y)\in\mathcal X_a^\perp\times\mathcal Y$ and has objective $\langle\bar u,y\rangle-Ef^*(p,y)$. The strong dual ranges over $\mathcal X^*\times\mathcal U^*$ and uses the conjugate $\varphi^*$.
--
--   These definitions give the common model for the existence and optimality results. The random variables are represented modulo almost-everywhere equality, and a coordinate time stamp records the paper's finite process blocks.
-- source:
--   Pennanen & Perkkiö, Dual solutions in convex stochastic optimization, arXiv:2205.15825v1, pp. 1–3, 5, 8–9, 11–14, 18 and 38, §§1–4 and Appendix

import Mathlib
import Definitions.Def_DupacovaWets_Consistency_expect

open MeasureTheory Filter
open scoped BigOperators Classical

namespace ConvStochDual.Existence

abbrev RV (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) (k : ℕ) :=
  Ω →ₘ[P] (Fin k → ℝ)

def dot {k : ℕ} (a b : Fin k → ℝ) : ℝ := ∑ i, a i * b i

noncomputable def pair {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {k : ℕ}
    (a b : RV Ω P k) : ℝ := ∫ ω, dot (a ω) (b ω) ∂P

def IsEssentiallyBounded {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {k : ℕ}
    (x : RV Ω P k) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ᵐ ω ∂P, ∀ i, |x ω i| ≤ C

def IsDecomposable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {k : ℕ}
    {A : Type*} [AddCommGroup A] [Module ℝ A] (ι : A →ₗ[ℝ] RV Ω P k) : Prop :=
  ∀ x : A, ∀ w : RV Ω P k, IsEssentiallyBounded P w →
    ∀ B : Set Ω, MeasurableSet B → ∃ z : A,
      ∀ᵐ ω ∂P, ι z ω = if ω ∈ B then ι x ω else w ω

def IsSolid {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {k : ℕ}
    {A : Type*} [AddCommGroup A] [Module ℝ A] (ι : A →ₗ[ℝ] RV Ω P k) : Prop :=
  ∀ x : A, ∀ w : RV Ω P k,
    (∀ᵐ ω ∂P, ∀ i, |w ω i| ≤ |ι x ω i|) → ∃ z : A, ι z = w

def IsSingular {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {k : ℕ}
    {A : Type*} [AddCommGroup A] [Module ℝ A] [TopologicalSpace A]
    (ι : A →ₗ[ℝ] RV Ω P k) (ℓ : A →L[ℝ] ℝ) : Prop :=
  ∀ u : A, ∃ B : ℕ → Set Ω,
    (∀ j, MeasurableSet (B j)) ∧ Antitone B ∧
    Tendsto (fun j => P (B j)) atTop (nhds 0) ∧
    ∀ j (w : A), (∀ᵐ ω ∂P, ι w ω = if ω ∈ B j then 0 else ι u ω) → ℓ w = 0

def IsDecomp {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {k : ℕ}
    {A : Type*} [AddCommGroup A] [Module ℝ A] [TopologicalSpace A]
    (ι : A →ₗ[ℝ] RV Ω P k) (V : Submodule ℝ (RV Ω P k))
    (ℓ : A →L[ℝ] ℝ) (yc : V) (ys : A →L[ℝ] ℝ) : Prop :=
  IsSingular P ι ys ∧ ∀ u : A, ℓ u = pair P (ι u) (yc : RV Ω P k) + ys u

def IsNormalIntegrand {Ω : Type*} [MeasurableSpace Ω] {n m : ℕ}
    (f : Ω → (Fin n → ℝ) → (Fin m → ℝ) → EReal) : Prop :=
  (∀ ω, Convex ℝ {q : (Fin n → ℝ) × (Fin m → ℝ) × ℝ |
      (f ω q.1 q.2.1) ≤ (q.2.2 : EReal)}) ∧
  (∀ ω, LowerSemicontinuous (fun q : (Fin n → ℝ) × (Fin m → ℝ) => f ω q.1 q.2)) ∧
  (∀ ω, (∃ x u, f ω x u = ⊥) → ∀ x u, f ω x u = ⊥) ∧
  (∀ O : Set ((Fin n → ℝ) × (Fin m → ℝ) × ℝ), IsOpen O →
    MeasurableSet {ω | ∃ q ∈ O, f ω q.1 q.2.1 ≤ (q.2.2 : EReal)})

def pos {A : Type*} [AddCommGroup A] [Module ℝ A] (C : Set A) : Set A :=
  {z | ∃ α : ℝ, 0 < α ∧ ∃ c ∈ C, z = α • c}

def LinClosed {A : Type*} [AddCommGroup A] [Module ℝ A] [TopologicalSpace A]
    (C : Set A) : Prop :=
  (∃ L : Submodule ℝ A, (L : Set A) = C) ∧ IsClosed C

variable {Ω X U : Type*} [MeasurableSpace Ω]
  [AddCommGroup X] [Module ℝ X] [UniformSpace X]
  [IsUniformAddGroup X] [ContinuousSMul ℝ X]
  [AddCommGroup U] [Module ℝ U] [UniformSpace U]
  [IsUniformAddGroup U] [ContinuousSMul ℝ U]
  {T n m : ℕ}

structure Setting (P : Measure Ω) [IsProbabilityMeasure P] (τ : Fin n → Fin (T + 1))
    (𝔽 : Fin (T + 1) → MeasurableSpace Ω)
    (ιX : X →ₗ[ℝ] RV Ω P n) (ιU : U →ₗ[ℝ] RV Ω P m)
    (V : Submodule ℝ (RV Ω P n)) (Y : Submodule ℝ (RV Ω P m)) where
  f : Ω → (Fin n → ℝ) → (Fin m → ℝ) → EReal
  ubar : U

variable {P : Measure Ω} [IsProbabilityMeasure P] {τ : Fin n → Fin (T + 1)}
  {𝔽 : Fin (T + 1) → MeasurableSpace Ω}
  {ιX : X →ₗ[ℝ] RV Ω P n} {ιU : U →ₗ[ℝ] RV Ω P m}
  {V : Submodule ℝ (RV Ω P n)} {Y : Submodule ℝ (RV Ω P m)}

def Adapted (τ : Fin n → Fin (T + 1)) (𝔽 : Fin (T + 1) → MeasurableSpace Ω)
    (P : Measure Ω) (x : RV Ω P n) : Prop :=
  ∀ i, ∃ g : Ω → ℝ, StronglyMeasurable[𝔽 (τ i)] g ∧
    (fun ω => x ω i) =ᵐ[P] g

noncomputable def Ef (s : Setting P τ 𝔽 ιX ιU V Y)
    (x : RV Ω P n) (u : RV Ω P m) : EReal :=
  DupacovaWets.Consistency.expect P (fun ω => s.f ω (x ω) (u ω))

noncomputable def fstar (s : Setting P τ 𝔽 ιX ιU V Y)
    (ω : Ω) (p : Fin n → ℝ) (y : Fin m → ℝ) : EReal :=
  ⨆ x : Fin n → ℝ, ⨆ u : Fin m → ℝ,
    ((dot x p + dot u y : ℝ) : EReal) - s.f ω x u

noncomputable def EfStar (s : Setting P τ 𝔽 ιX ιU V Y)
    (p : RV Ω P n) (y : RV Ω P m) : EReal :=
  DupacovaWets.Consistency.expect P (fun ω => fstar s ω (p ω) (y ω))

def Xa (s : Setting P τ 𝔽 ιX ιU V Y) : Set X :=
  {x | Adapted τ 𝔽 P (ιX x)}

noncomputable def XaPerp (s : Setting P τ 𝔽 ιX ιU V Y) : Set V :=
  {p | ∀ x ∈ Xa s, pair P (ιX x) (p : RV Ω P n) = 0}

def XaCirc (s : Setting P τ 𝔽 ιX ιU V Y) : Set (X →L[ℝ] ℝ) :=
  {p | ∀ x ∈ Xa s, p x = 0}

noncomputable def phi (s : Setting P τ 𝔽 ιX ιU V Y) (z : X) (u : U) : EReal :=
  ⨅ x : X, ⨅ (_ : Adapted τ 𝔽 P (ιX x - ιX z)), Ef s (ιX x) (ιU u)

def domEf (s : Setting P τ 𝔽 ιX ιU V Y) : Set (X × U) :=
  {q | Ef s (ιX q.1) (ιU q.2) < ⊤}

def domuEf (s : Setting P τ 𝔽 ιX ιU V Y) : Set U :=
  {u | ∃ x : X, (x, u) ∈ domEf s}

def domPhi (s : Setting P τ 𝔽 ιX ιU V Y) : Set (X × U) :=
  {q | phi s q.1 q.2 < ⊤}

noncomputable def sigmaDomEf (s : Setting P τ 𝔽 ιX ιU V Y)
    (p : X →L[ℝ] ℝ) (y : U →L[ℝ] ℝ) : EReal :=
  ⨆ q : X × U, ⨆ (_ : q ∈ domEf s), ((p q.1 + y q.2 : ℝ) : EReal)

noncomputable def phiStar (s : Setting P τ 𝔽 ιX ιU V Y)
    (p : X →L[ℝ] ℝ) (y : U →L[ℝ] ℝ) : EReal :=
  ⨆ z : X, ⨆ u : U, ((p z + y u : ℝ) : EReal) - phi s z u

noncomputable def phiStarV (s : Setting P τ 𝔽 ιX ιU V Y)
    (p : V) (y : Y) : EReal :=
  ⨆ z : X, ⨆ u : U,
    ((pair P (ιX z) (p : RV Ω P n) + pair P (ιU u) (y : RV Ω P m) : ℝ) : EReal) - phi s z u

noncomputable def valSP (s : Setting P τ 𝔽 ιX ιU V Y) : EReal :=
  ⨅ x : RV Ω P n, ⨅ (_ : Adapted τ 𝔽 P x), Ef s x (ιU s.ubar)

noncomputable def valSPX (s : Setting P τ 𝔽 ιX ιU V Y) : EReal := phi s 0 s.ubar

noncomputable def dualObj (s : Setting P τ 𝔽 ιX ιU V Y) (p : V) (y : Y) : EReal :=
  ((pair P (ιU s.ubar) (y : RV Ω P m) : ℝ) : EReal) -
    EfStar s (p : RV Ω P n) (y : RV Ω P m)

noncomputable def valD (s : Setting P τ 𝔽 ιX ιU V Y) : EReal :=
  ⨆ p : V, ⨆ (_ : p ∈ XaPerp s), ⨆ y : Y, dualObj s p y

noncomputable def valDs (s : Setting P τ 𝔽 ιX ιU V Y) : EReal :=
  ⨆ p : X →L[ℝ] ℝ, ⨆ y : U →L[ℝ] ℝ,
    ((y s.ubar : ℝ) : EReal) - phiStar s p y

def IsSubgradAt (g : (Fin n → ℝ) → (Fin m → ℝ) → EReal)
    (x : Fin n → ℝ) (u : Fin m → ℝ) (p : Fin n → ℝ) (y : Fin m → ℝ) : Prop :=
  g x u ≠ ⊤ ∧ g x u ≠ ⊥ ∧
    ∀ x' u', g x u + ((dot (x' - x) p + dot (u' - u) y : ℝ) : EReal) ≤ g x' u'

def EfProperLsc (s : Setting P τ 𝔽 ιX ιU V Y) : Prop :=
  (∀ q : X × U, Ef s (ιX q.1) (ιU q.2) ≠ ⊥) ∧
  (∃ q : X × U, Ef s (ιX q.1) (ιU q.2) < ⊤) ∧
  LowerSemicontinuous (fun q : X × U => Ef s (ιX q.1) (ιU q.2))

def IsCondExpT (s : Setting P τ 𝔽 ιX ιU V Y) (t : Fin (T + 1)) (x x' : X) : Prop :=
  ∀ i, (fun ω => ιX x' ω i) =ᵐ[P] MeasureTheory.condExp (𝔽 t) P (fun ω => ιX x ω i)

def CondExpClosed (s : Setting P τ 𝔽 ιX ιU V Y) : Prop :=
  ∀ t (x : X), ∃ x' : X, IsCondExpT s t x x'

def Assumption23_1 (s : Setting P τ 𝔽 ιX ιU V Y) : Prop :=
  LinClosed (pos ((fun u : U => u - s.ubar) '' domuEf s))

def Assumption23_2 (s : Setting P τ 𝔽 ιX ιU V Y) : Prop :=
  ∀ t (z : X), (z, s.ubar) ∈ domEf s →
    ∃ zbar : X, (zbar, s.ubar) ∈ domEf s ∧
      ∀ i, τ i ≤ t →
        (fun ω => ιX zbar ω i) =ᵐ[P]
          MeasureTheory.condExp (𝔽 t) P (fun ω => ιX z ω i)

def HasPastSupport (s : Setting P τ 𝔽 ιX ιU V Y)
    (t : Fin (T + 1)) (p : X →L[ℝ] ℝ) : Prop :=
  ∀ z : X, (∀ᵐ ω ∂P, ∀ i, τ i ≤ t → ιX z ω i = 0) → p z = 0

structure Standing (s : Setting P τ 𝔽 ιX ιU V Y) : Prop where
  frechetX : LocallyConvexSpace ℝ X ∧ TopologicalSpace.MetrizableSpace X ∧ CompleteSpace X
  frechetU : LocallyConvexSpace ℝ U ∧ TopologicalSpace.MetrizableSpace U ∧ CompleteSpace U
  injectiveX : Function.Injective ιX
  injectiveU : Function.Injective ιU
  filtration_le : ∀ t, 𝔽 t ≤ (inferInstance : MeasurableSpace Ω)
  filtration_mono : Monotone 𝔽
  normal : IsNormalIntegrand s.f
  decomposableX : IsDecomposable P ιX
  decomposableU : IsDecomposable P ιU
  decomposableV : IsDecomposable P V.subtype
  decomposableY : IsDecomposable P Y.subtype
  solidX : IsSolid P ιX
  solidU : IsSolid P ιU
  solidV : IsSolid P V.subtype
  solidY : IsSolid P Y.subtype
  pair_integrableX : ∀ x : X, ∀ v : V, Integrable (fun ω => dot (ιX x ω) (v.1 ω)) P
  pair_integrableU : ∀ u : U, ∀ y : Y, Integrable (fun ω => dot (ιU u ω) (y.1 ω)) P
  separatesX : (∀ x : X, (∀ v : V, pair P (ιX x) v.1 = 0) → x = 0) ∧
    (∀ v : V, (∀ x : X, pair P (ιX x) v.1 = 0) → v = 0)
  separatesU : (∀ u : U, (∀ y : Y, pair P (ιU u) y.1 = 0) → u = 0) ∧
    (∀ y : Y, (∀ u : U, pair P (ιU u) y.1 = 0) → y = 0)
  pair_continuousX : ∀ v : V, Continuous (fun x : X => pair P (ιX x) v.1)
  pair_continuousU : ∀ y : Y, Continuous (fun u : U => pair P (ιU u) y.1)
  splitsX : ∀ ℓ : X →L[ℝ] ℝ, ∃! q : V × (X →L[ℝ] ℝ), IsDecomp P ιX V ℓ q.1 q.2
  splitsU : ∀ ℓ : U →L[ℝ] ℝ, ∃! q : Y × (U →L[ℝ] ℝ), IsDecomp P ιU Y ℓ q.1 q.2
  integrableX : ∀ x : X, ∀ i, Integrable (fun ω => ιX x ω i) P

def IsNormalIntegrand1 {k : ℕ}
    (h : Ω → (Fin k → ℝ) → EReal) : Prop :=
  (∀ ω, Convex ℝ {q : (Fin k → ℝ) × ℝ | h ω q.1 ≤ (q.2 : EReal)}) ∧
  (∀ ω, LowerSemicontinuous (h ω)) ∧
  (∀ ω, (∃ u, h ω u = ⊥) → ∀ u, h ω u = ⊥) ∧
  (∀ O : Set ((Fin k → ℝ) × ℝ), IsOpen O →
    MeasurableSet {ω | ∃ q ∈ O, h ω q.1 ≤ (q.2 : EReal)})

noncomputable def Eh {k : ℕ} (h : Ω → (Fin k → ℝ) → EReal)
    (u : RV Ω P k) : EReal :=
  DupacovaWets.Consistency.expect P (fun ω => h ω (u ω))

noncomputable def hstar {k : ℕ} (h : Ω → (Fin k → ℝ) → EReal)
    (ω : Ω) (y : Fin k → ℝ) : EReal :=
  ⨆ u : Fin k → ℝ, ((dot u y : ℝ) : EReal) - h ω u

noncomputable def EhStar {k : ℕ} (h : Ω → (Fin k → ℝ) → EReal)
    (y : RV Ω P k) : EReal :=
  DupacovaWets.Consistency.expect P (fun ω => hstar h ω (y ω))

def domEh {k : ℕ} (h : Ω → (Fin k → ℝ) → EReal)
    (ι : U →ₗ[ℝ] RV Ω P k) : Set U :=
  {u | Eh h (ι u) < ⊤}

def EhProper {k : ℕ} (h : Ω → (Fin k → ℝ) → EReal)
    (ι : U →ₗ[ℝ] RV Ω P k) : Prop :=
  (∀ u : U, Eh h (ι u) ≠ ⊥) ∧ (domEh h ι).Nonempty

noncomputable def EhConj {k : ℕ} (h : Ω → (Fin k → ℝ) → EReal)
    (ι : U →ₗ[ℝ] RV Ω P k) (y : U →L[ℝ] ℝ) : EReal :=
  ⨆ u : U, ((y u : ℝ) : EReal) - Eh h (ι u)

noncomputable def sigmaDomEh {k : ℕ} (h : Ω → (Fin k → ℝ) → EReal)
    (ι : U →ₗ[ℝ] RV Ω P k) (y : U →L[ℝ] ℝ) : EReal :=
  ⨆ u : U, ⨆ (_ : u ∈ domEh h ι), ((y u : ℝ) : EReal)

def IsSubgradStrong {k : ℕ} (h : Ω → (Fin k → ℝ) → EReal)
    (ι : U →ₗ[ℝ] RV Ω P k) (ubar : U) (y : U →L[ℝ] ℝ) : Prop :=
  Eh h (ι ubar) ≠ ⊤ ∧ Eh h (ι ubar) ≠ ⊥ ∧
    ∀ u : U, Eh h (ι ubar) + ((y (u - ubar) : ℝ) : EReal) ≤ Eh h (ι u)

def IsSubgradRegular {k : ℕ} (h : Ω → (Fin k → ℝ) → EReal)
    (ι : U →ₗ[ℝ] RV Ω P k) (ubar : U)
    (Y₀ : Submodule ℝ (RV Ω P k)) (yc : Y₀) : Prop :=
  Eh h (ι ubar) ≠ ⊤ ∧ Eh h (ι ubar) ≠ ⊥ ∧
    ∀ u : U, Eh h (ι ubar) +
      ((pair P (ι (u - ubar)) (yc : RV Ω P k) : ℝ) : EReal) ≤ Eh h (ι u)

def IsNormalAt {k : ℕ} (h : Ω → (Fin k → ℝ) → EReal)
    (ι : U →ₗ[ℝ] RV Ω P k) (ubar : U) (ys : U →L[ℝ] ℝ) : Prop :=
  ∀ u ∈ domEh h ι, ys (u - ubar) ≤ 0

structure IntegralStanding {k : ℕ} (h : Ω → (Fin k → ℝ) → EReal)
    (ι : U →ₗ[ℝ] RV Ω P k) (Y₀ : Submodule ℝ (RV Ω P k)) : Prop where
  frechet : LocallyConvexSpace ℝ U ∧ TopologicalSpace.MetrizableSpace U ∧ CompleteSpace U
  injective : Function.Injective ι
  normal : IsNormalIntegrand1 h
  decomposableU : IsDecomposable P ι
  decomposableY : IsDecomposable P Y₀.subtype
  solidU : IsSolid P ι
  solidY : IsSolid P Y₀.subtype
  pair_integrable : ∀ u : U, ∀ y : Y₀, Integrable (fun ω => dot (ι u ω) (y.1 ω)) P
  separates : (∀ u : U, (∀ y : Y₀, pair P (ι u) y.1 = 0) → u = 0) ∧
    (∀ y : Y₀, (∀ u : U, pair P (ι u) y.1 = 0) → y = 0)
  pair_continuous : ∀ y : Y₀, Continuous (fun u : U => pair P (ι u) y.1)
  splits : ∀ ℓ : U →L[ℝ] ℝ,
    ∃! q : Y₀ × (U →L[ℝ] ℝ), IsDecomp P ι Y₀ ℓ q.1 q.2

end ConvStochDual.Existence


