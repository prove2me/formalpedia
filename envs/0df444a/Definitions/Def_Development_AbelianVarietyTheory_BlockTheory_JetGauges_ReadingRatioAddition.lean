-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_ReadingRatioAddition
-- name    : Development_AbelianVarietyTheory_BlockTheory_JetGauges_ReadingRatioAddition
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T01:18:15.70991+00:00
-- url     : https://prove2.me/theorems/2c2d2192-f588-48a8-8385-6d136e3deaf5
-- title:
--   Reading Ratio Addition
-- statement:
--   Definitions and structural lemmas for Reading Ratio Addition, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/JetGauges/ReadingRatioAddition.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_BasePsiLeviLowerBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_NormOrderStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GlobalTheory.IndefiniteRowSideFullHecke.GenericFrameParameters
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.T0 ReciprocityTheory.ChartRestriction.G.AR.Inst
  ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates
noncomputable section
section Defs
variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
def IsGenFrame {c : ι} (X : FD.Data E r) (Rd : ℕ → Submodule K (A c))
    (rd : ℕ → A c → Frame X.Ψ r → ℂ) (x : Frame X.Ψ r) : Prop :=
  x ∈ X.dom ∧ ∀ k, ∀ g ∈ Rd k, g ≠ 0 → rd k g x ≠ 0
def IsEvalAt {c : ι} (X : FD.Data E r) (Rd : ℕ → Submodule K (A c))
    (rd : ℕ → A c → Frame X.Ψ r → ℂ) (x : Frame X.Ψ r) (P : Ω c →+* ℂ) : Prop :=
  ∀ k, ∀ f ∈ Rd k, ∀ g ∈ Rd k, ∀ a : Ω c, f = a • g → rd k f x = P a * rd k g x
structure IsReading (𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)) (d : T0.Data K ι Ω WT A) (c : ι)
    (sg : K →+* ℂ) (X : FD.Data E r) (L : Wt X.Ψ r)
    (Rd : ℕ → Submodule K (A c)) (rd : ℕ → A c → Frame X.Ψ r → ℂ) : Prop where

  mem : ∀ k, ∀ f ∈ Rd k, f ∈ 𝒜 c (k • d.wL)

  mul_mem : ∀ k l, ∀ f ∈ Rd k, ∀ g ∈ Rd l, f * g ∈ Rd (k + l)

  ratio : ∀ a : Ω c, ∃ k, ∃ f ∈ Rd k, ∃ g ∈ Rd k, g ≠ 0 ∧ f = a • g

  sec : ∀ k, ∀ f ∈ Rd k, X.IsSec (k • L) (rd k f)
  add : ∀ k, ∀ f ∈ Rd k, ∀ g ∈ Rd k, ∀ x ∈ X.dom, rd k (f + g) x = rd k f x + rd k g x
  smul : ∀ k, ∀ f ∈ Rd k, ∀ a : K, ∀ x ∈ X.dom, rd k (a • f) x = sg a * rd k f x
  mul : ∀ k l, ∀ f ∈ Rd k, ∀ g ∈ Rd l, ∀ x ∈ X.dom, rd (k + l) (f * g) x = rd k f x * rd l g x

  onto : ∀ P ∈ PT (Ω := Ω c) sg, ∃ x, IsGenFrame X Rd rd x ∧ IsEvalAt X Rd rd x P

  unram : ∀ x, IsGenFrame X Rd rd x → ∀ v : V (nd X), v ≠ 0 →
    ∃ k, ∃ f ∈ Rd k, ∃ g ∈ Rd k, g ≠ 0 ∧
      fderiv ℂ (fun z : V (nd X) => rd k f (cpt X x z) / rd k g (cpt X x z)) 0 v ≠ 0
def IsGenParam {D N : ℕ} (sg : K →+* ℂ) (t : TVar D N → ℂ) : Prop :=
  Function.Injective (MvPolynomial.eval₂Hom sg t : KTp K D N →+* ℂ)
def genSec {D N : ℕ} {X : FD.Data E r} (Xa : ArchInM X) (hN : N + 1 = Xa.N) (t : TVar D N → ℂ)
    (i : Fin (D + 1)) (x : Frame X.Ψ r) : ℂ :=
  ∑ j : Fin (N + 1), t (i, j) * Xa.w (Fin.cast hN j) x
def w0F {D N : ℕ} {X : FD.Data E r} (Xa : ArchInM X) (hN : N + 1 = Xa.N) (t : TVar D N → ℂ) :
    Frame X.Ψ r → ℂ :=
  genSec Xa hN t 0
def sF {D N : ℕ} {X : FD.Data E r} (Xa : ArchInM X) (hD : nd X = D) (hN : N + 1 = Xa.N)
    (t : TVar D N → ℂ) (k : Fin (nd X)) : Frame X.Ψ r → ℂ :=
  genSec Xa hN t (Fin.cast hD k).succ
def beAlg (d : T0.Data K ι Ω WT A) (c : ι) : A c := d.et c ^ 2 * d.ta1 c ^ d.n1
structure Common (𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)) (d : T0.Data K ι Ω WT A) (c : ι)
    (sg : K →+* ℂ) (X : FD.Data E r) (Xa : ArchInM X) (hN : d.N + 1 = Xa.N)
    (Rd : ℕ → Submodule K (A c)) (rd : ℕ → A c → Frame X.Ψ r → ℂ) (t : TVar d.D d.N → ℂ) : Prop where
  evidence : IsReading 𝒜 d c sg X Xa.L Rd rd
  w_mem : ∀ j, d.w j c ∈ Rd 1
  w_rd : ∀ j, ∀ x ∈ X.dom, rd 1 (d.w j c) x = Xa.w (Fin.cast hN j) x
  n_eq : d.n1 = Xa.i * Xa.g0
  be_mem : beAlg d c ∈ Rd (2 * d.n1)
  be_rd : ∀ x ∈ X.dom, rd (2 * d.n1) (beAlg d c) x = Xa.et x ^ 2 * Xa.th1 x ^ d.n1
  param : IsGenParam sg t
def wSq {X : FD.Data E r} (Xa : ArchInM X) (x : Frame X.Ψ r) : ℝ :=
  ∑ j, X.pnorm Xa.L (Xa.w j) x ^ 2
def sSq {D N : ℕ} {X : FD.Data E r} (Xa : ArchInM X) (hD : nd X = D) (hN : N + 1 = Xa.N)
    (t : TVar D N → ℂ) (x : Frame X.Ψ r) : ℝ :=
  ∑ k, X.pnorm Xa.L (sF Xa hD hN t k) x ^ 2
example {D N : ℕ} (sg : K →+* ℂ) (e : KTf K D N →+* ℂ)
    (he : ∀ a : K, e (algebraMap (KTp K D N) (KTf K D N) (MvPolynomial.C a)) = sg a) :
    IsGenParam sg fun p : TVar D N => e (algebraMap (KTp K D N) (KTf K D N) (MvPolynomial.X p)) := by
  have h : (MvPolynomial.eval₂Hom sg fun p : TVar D N =>
      e (algebraMap (KTp K D N) (KTf K D N) (MvPolynomial.X p))) =
      e.comp (algebraMap (KTp K D N) (KTf K D N)) := by
    apply MvPolynomial.ringHom_ext
    · intro a; simp [he]
    · intro p; simp
  unfold IsGenParam
  rw [h]
  exact e.injective.comp (IsFractionRing.injective (KTp K D N) (KTf K D N))
end Defs
def CoordStatement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (ι : Type) [Fintype ι]
    (Ω : ι → Type) [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
    (WT : Type) [AddCommGroup WT]
    (A : ι → Type) [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
    [∀ c, Algebra (𝓞 K) (A c)]
    (𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)) (d : T0.Data K ι Ω WT A) (c : ι) (sg : K →+* ℂ)
    (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : FD.Data E r) (Xa : ArchInM X)
    (hD : nd X = d.D) (hN : d.N + 1 = Xa.N)
    (Rd : ℕ → Submodule K (A c)) (rd : ℕ → A c → Frame X.Ψ r → ℂ) (t : TVar d.D d.N → ℂ),
    d.Ax 𝒜 → Common 𝒜 d c sg X Xa hN Rd rd t →
    ∀ x, IsGenFrame X Rd rd x → (∀ k, sF Xa hD hN t k x = 0) → w0F Xa hN t x ≠ 0 →
      (fderiv ℂ (fun z : V (nd X) => (WithLp.toLp 2 fun k =>
        sF Xa hD hN t k (cpt X x z) / w0F Xa hN t (cpt X x z) : V (nd X))) 0).det ≠ 0
def NormAllStatement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (ι : Type) [Fintype ι]
    (Ω : ι → Type) [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
    (WT : Type) [AddCommGroup WT]
    (A : ι → Type) [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
    [∀ c, Algebra (𝓞 K) (A c)]
    (𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)) (d : T0.Data K ι Ω WT A) (c : ι) (sg : K →+* ℂ)
    (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : FD.Data E r) (Xa : ArchInM X)
    (hD : nd X = d.D) (hN : d.N + 1 = Xa.N)
    (Rd : ℕ → Submodule K (A c)) (rd : ℕ → A c → Frame X.Ψ r → ℂ) (t : TVar d.D d.N → ℂ),
    d.Ax 𝒜 → Common 𝒜 d c sg X Xa hN Rd rd t →
    ∃ C : ℝ, ∀ x ∈ X.dom,
      wSq Xa x ≤ C * (X.pnorm Xa.L (w0F Xa hN t) x ^ 2 + sSq Xa hD hN t x)
def NormOffStatement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (ι : Type) [Fintype ι]
    (Ω : ι → Type) [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
    (WT : Type) [AddCommGroup WT]
    (A : ι → Type) [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
    [∀ c, Algebra (𝓞 K) (A c)]
    (𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)) (d : T0.Data K ι Ω WT A) (c : ι) (sg : K →+* ℂ)
    (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : FD.Data E r) (Xa : ArchInM X)
    (hD : nd X = d.D) (hN : d.N + 1 = Xa.N)
    (Rd : ℕ → Submodule K (A c)) (rd : ℕ → A c → Frame X.Ψ r → ℂ) (t : TVar d.D d.N → ℂ),
    d.Ax 𝒜 → Common 𝒜 d c sg X Xa hN Rd rd t →
    ∀ U : Set (Frame X.Ψ r), IsOpen U →
      (∀ x ∈ X.dom, (∀ k, sF Xa hD hN t k x = 0) → x ∈ U) →
      (∀ x ∈ U, ∀ γ ∈ X.Γ, ∀ b ∈ Bor X.Ψ r, lact γ (rmul x b) ∈ U) →
      ∃ C : ℝ, ∀ x ∈ X.dom, x ∉ U → wSq Xa x ≤ C * sSq Xa hD hN t x
def FlatLeavesStatement : Prop := CoordStatement ∧ NormAllStatement ∧ NormOffStatement
end
end GlobalTheory.IndefiniteRowSideFullHecke.GenericFrameParameters


