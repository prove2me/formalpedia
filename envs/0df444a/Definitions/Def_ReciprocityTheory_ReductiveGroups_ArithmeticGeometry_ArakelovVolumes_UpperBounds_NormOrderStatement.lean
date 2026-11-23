-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_NormOrderStatement
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_NormOrderStatement
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T12:46:42.374595+00:00
-- url     : https://prove2.me/theorems/0c52ec06-8cb5-46cb-b6ee-f13c5f19d733
-- title:
--   Norm Order Statement
-- statement:
--   Definitions and structural lemmas for Norm Order Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ArakelovVolumes/UpperBounds/NormOrderStatement.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_LaTIsPrime
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FiniteGenOfWeakAxioms
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.AR.Up
open NumberField ReciprocityTheory.ChartRestriction.G.T0
noncomputable section
variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}
namespace AlgT
variable (d : Data K ι Ω WT A)
abbrev OmT (c : ι) : Type := FractionRing (MvPolynomial (TVar d.D d.N) (Ω c))
def iKp (c : ι) : KTp K d.D d.N →+* OmT d c :=
  (algebraMap (MvPolynomial (TVar d.D d.N) (Ω c)) (OmT d c)).comp
    (MvPolynomial.map (algebraMap K (Ω c)))
theorem iKp_injective (c : ι) : Function.Injective (iKp d c) :=
  (IsFractionRing.injective (MvPolynomial (TVar d.D d.N) (Ω c)) (OmT d c)).comp
    (MvPolynomial.map_injective _ (algebraMap K (Ω c)).injective)
def iK (c : ι) : KTf K d.D d.N →+* OmT d c :=
  IsFractionRing.lift (A := KTp K d.D d.N) (g := iKp d c) (iKp_injective d c)
def iΩ (c : ι) : Ω c →+* OmT d c :=
  (algebraMap (MvPolynomial (TVar d.D d.N) (Ω c)) (OmT d c)).comp MvPolynomial.C
def xT (c : ι) (j : Fin (d.N + 1)) : OmT d c :=
  iΩ d c (ratio (Ω := Ω c) (d.w j c) (d.w (d.jc c) c))
def sT (c : ι) (i : Fin (d.D + 1)) : OmT d c :=
  ∑ j, algebraMap (MvPolynomial (TVar d.D d.N) (Ω c)) (OmT d c) (MvPolynomial.X (i, j)) * xT d c j
def yT (c : ι) (k : Fin d.D) : OmT d c := sT d c k.succ / sT d c 0
def A0 (c : ι) : Subring (OmT d c) := Subring.closure (Set.range (iK d c) ∪ Set.range (yT d c))
def Fy (c : ι) : Subfield (OmT d c) := Subfield.closure (Set.range (iK d c) ∪ Set.range (yT d c))
def evY (c : ι) : MvPolynomial (Fin d.D) (KTf K d.D d.N) →+* OmT d c :=
  MvPolynomial.eval₂Hom (iK d c) (yT d c)
def uT (c : ι) (e : ℕ) (f : A c) : OmT d c :=
  iΩ d c (ratio (Ω := Ω c) f (d.w (d.jc c) c ^ e)) / sT d c 0 ^ e
def combP (c : ι) (e m : ℕ) (q : Fin m → KTp K d.D d.N) (f : Fin m → A c) :
    MvPolynomial (TVar d.D d.N) (Ω c) :=
  ∑ i, MvPolynomial.map (algebraMap K (Ω c)) (q i) *
    MvPolynomial.C (ratio (Ω := Ω c) (f i) (d.w (d.jc c) c ^ e))
def uC (c : ι) (e m : ℕ) (q : Fin m → KTp K d.D d.N) (f : Fin m → A c) : OmT d c :=
  algebraMap (MvPolynomial (TVar d.D d.N) (Ω c)) (OmT d c) (combP d c e m q f) / sT d c 0 ^ e
def phiS (c : ι) : MvPolynomial (TVar d.D d.N) (Ω c) →+* OmS (Ω c) d.D d.N :=
  (MvPolynomial.aeval (R := Ω c) (sImg (D := d.D) (d.jc c) (d.x c))).toRingHom
def pS (c : ι) : Ideal (MvPolynomial (TVar d.D d.N) (Ω c)) := RingHom.ker (phiS d c)
instance pS_isPrime (c : ι) : (pS d c).IsPrime := RingHom.ker_isPrime _
abbrev RS (c : ι) : Type := Localization.AtPrime (pS d c)
abbrev mmS (c : ι) : Ideal (RS d c) := IsLocalRing.maximalIdeal (RS d c)
end AlgT
open AlgT
def TrdegD (d : Data K ι Ω WT A) (c : ι) : Prop :=
  Algebra.trdeg K (IntermediateField.adjoin K (Set.range fun j =>
    ratio (Ω := Ω c) (d.w j c) (d.w (d.jc c) c))) = d.D
def GrowthOne (d : Data K ι Ω WT A) (c : ι) (sg : K →+* ℂ) (G : WT) (e : ℕ) (f : A c) : Prop :=
  ∃ C : ℝ, ∀ P ∈ PT (Ω := Ω c) sg, d.nrm c G f P ≤ C * d.be c P ^ e
def IntegralStatement : Prop :=
  ∀ (d : Data K ι Ω WT A), d.AxW 𝒜 → ∀ c : ι, TrdegD d c → ∀ j,
    ∃ (m : ℕ) (a : Fin (m + 1) → MvPolynomial (Fin d.D) (KTf K d.D d.N)),
      a 0 = 1 ∧ (∀ k, (a k).totalDegree ≤ k) ∧
      ∑ k : Fin (m + 1), evY d c (a k) * (xT d c j / sT d c 0) ^ (m - (k : ℕ)) = 0
def CharPolyStatement : Prop :=
  ∀ (d : Data K ι Ω WT A), d.AxW 𝒜 → ∀ c : ι, TrdegD d c →
    ∀ [FiniteDimensional (Fy d c) (OmT d c)] [Module.Free (Fy d c) (OmT d c)],
    ∀ (sg : K →+* ℂ) (e m : ℕ) (q : Fin m → KTp K d.D d.N) (f : Fin m → A c),
    (∀ i, f i ∈ 𝒜 c (e • d.wL)) → (∀ i, GrowthOne d c sg (e • d.wL) e (f i)) →
    ∀ k : ℕ, k ≤ Module.finrank (Fy d c) (OmT d c) →
      ∃ Q : MvPolynomial (Fin d.D) (KTf K d.D d.N), Q.totalDegree ≤ e * k ∧
        ((LinearMap.mulLeft (Fy d c) (uC d c e m q f)).charpoly.coeff
          (Module.finrank (Fy d c) (OmT d c) - k) : OmT d c) = evY d c Q
def NormStatement : Prop :=
  ∀ (d : Data K ι Ω WT A), d.AxW 𝒜 → ∀ c : ι, TrdegD d c →
    ∀ [FiniteDimensional (Fy d c) (OmT d c)],
    ∀ (sg : K →+* ℂ) (k : ℕ) (b : A c), b ∈ 𝒜 c (k • d.wL) → b ≠ 0 → GrowthOne d c sg (k • d.wL) k b →
    ∃ Q : MvPolynomial (Fin d.D) (KTf K d.D d.N), MvPolynomial.constantCoeff Q ≠ 0 ∧
      ((Algebra.norm (Fy d c) (uT d c k b) : Fy d c) : OmT d c) = evY d c Q
def OrderStatement : Prop :=
  ∀ (d : Data K ι Ω WT A), d.AxW 𝒜 → ∀ c : ι, TrdegD d c →
    ∀ [FiniteDimensional (Fy d c) (OmT d c)],
    ∀ (sg : K →+* ℂ) (e m : ℕ) (q : Fin m → KTp K d.D d.N) (f : Fin m → A c),
    (∀ i, f i ∈ 𝒜 c (e • d.wL)) → (∀ i, GrowthOne d c sg (e • d.wL) e (f i)) →
    algebraMap (MvPolynomial (TVar d.D d.N) (Ω c)) (RS d c) (combP d c e m q f) ∈ mmS d c ^ (e + 1) →
    combP d c e m q f = 0
def NormOrderStatement : Prop :=
  ∀ (d : Data K ι Ω WT A), d.AxW 𝒜 → ∀ c : ι, TrdegD d c →
    ∀ [FiniteDimensional (Fy d c) (OmT d c)],
    ∀ (e n : ℕ) (g : MvPolynomial (TVar d.D d.N) (Ω c)),
    algebraMap (MvPolynomial (TVar d.D d.N) (Ω c)) (RS d c) g ∈ mmS d c ^ n →
    ∀ Q : MvPolynomial (Fin d.D) (KTf K d.D d.N),
      ((Algebra.norm (Fy d c) (algebraMap (MvPolynomial (TVar d.D d.N) (Ω c)) (OmT d c) g /
        sT d c 0 ^ e) : Fy d c) : OmT d c) = evY d c Q →
      ∀ α ∈ Q.support, n * Module.finrank (Fy d c) (OmT d c) ≤ α.sum fun _ k => k
def OmSFinStatement : Prop :=
  ∀ (d : Data K ι Ω WT A), d.AxW 𝒜 → ∀ c : ι, d.S1 →
    FiniteDimensional (d.KT c) (OmS (Ω c) d.D d.N)
end
end ReciprocityTheory.ChartRestriction.G.AR.Up


