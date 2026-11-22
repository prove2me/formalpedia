-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_LaTIsPrime
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_LaTIsPrime
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:22:49.632057+00:00
-- url     : https://prove2.me/theorems/62dd8117-da84-49bd-b410-96b5cb11b98b
-- title:
--   La TIs Prime
-- statement:
--   Definitions and structural lemmas for La TIs Prime, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/LaTIsPrime.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_TheoremA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace ReciprocityTheory.ChartRestriction.G.T0
open NumberField
abbrev OT (K : Type) [Field K] [NumberField K] (D N : ℕ) : Type :=
  MvPolynomial (TVar D N) (𝓞 K)
abbrev KTp (K : Type) [Field K] (D N : ℕ) : Type := MvPolynomial (TVar D N) K
abbrev KTf (K : Type) [Field K] (D N : ℕ) : Type := FractionRing (KTp K D N)
noncomputable def laT {K : Type} [Field K] [NumberField K] (D N : ℕ)
    (la : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) : Ideal (OT K D N) :=
  Ideal.map (MvPolynomial.C : 𝓞 K →+* OT K D N) la.asIdeal
instance laT_isPrime {K : Type} [Field K] [NumberField K] (D N : ℕ)
    (la : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) : (laT D N la).IsPrime := by
  have e := MvPolynomial.quotientEquivQuotientMvPolynomial (σ := TVar D N) la.asIdeal
  have : IsDomain (OT K D N ⧸ laT D N la) := MulEquiv.isDomain _ e.toRingEquiv.symm.toMulEquiv
  exact (Ideal.Quotient.isDomain_iff_prime _).mp this
abbrev Op {K : Type} [Field K] [NumberField K] (D N : ℕ)
    (la : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) : Type :=
  Localization.AtPrime (laT D N la)
noncomputable def OTtoKT (K : Type) [Field K] [NumberField K] (D N : ℕ) : OT K D N →+* KTp K D N :=
  MvPolynomial.map (algebraMap (𝓞 K) K)
noncomputable def OpToKT {K : Type} [Field K] [NumberField K] (D N : ℕ)
    (la : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) : Op D N la →+* KTf K D N :=
  IsLocalization.lift (M := (laT D N la).primeCompl) (S := Op D N la)
    (g := (algebraMap (KTp K D N) (KTf K D N)).comp (OTtoKT K D N)) (by
      intro y
      apply isUnit_iff_ne_zero.mpr
      intro h
      have hy : (y : OT K D N) ≠ 0 := fun h0 => y.2 (by rw [h0]; exact (laT D N la).zero_mem)
      apply hy
      have h2 : OTtoKT K D N (y : OT K D N) = 0 :=
        (IsFractionRing.injective (KTp K D N) (KTf K D N)) (by simpa using h)
      exact MvPolynomial.map_injective _ (IsFractionRing.injective (𝓞 K) K)
        (by simpa [OTtoKT] using h2))
variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}
namespace Data
variable (d : Data K ι Ω WT A)
def S1 : Prop := ∀ c, Function.Injective (d.sH c)
noncomputable def KTtoS (h : d.S1) (c : ι) : KTf K d.D d.N →+* OmS (Ω c) d.D d.N :=
  IsFractionRing.lift (A := KTp K d.D d.N) (g := (d.sH c).toRingHom) (h c)
noncomputable def OpToS (h : d.S1) (la : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (c : ι) :
    Op d.D d.N la →+* OmS (Ω c) d.D d.N :=
  (d.KTtoS h c).comp (OpToKT d.D d.N la)
noncomputable def OTtoS (c : ι) : OT K d.D d.N →+* OmS (Ω c) d.D d.N :=
  (d.sH c).toRingHom.comp (OTtoKT K d.D d.N)
def PlOver (la : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (c : ι) :
    Set (AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ)) :=
  {w | IsNormDiscrete w ∧ ∀ x : OT K d.D d.N, 0 ≤ w (d.OTtoS c x) ∧
    (0 < w (d.OTtoS c x) ↔ x ∈ laT d.D d.N la)}
noncomputable def Wres (c : ι) (w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ)) :
    AddValuation (Ω c) (WithTop ℤ) :=
  w.comap (algebraMap (Ω c) (OmS (Ω c) d.D d.N))
noncomputable def fze (h : d.S1) (c : ι) (w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ)) : ℕ :=
  letI : Algebra (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := (d.KTtoS h c).toAlgebra
  letI := resAlg (F := KTf K d.D d.N) w
  Module.finrank (IsLocalRing.ResidueField ((vRing w).comap (algebraMap (KTf K d.D d.N)
    (OmS (Ω c) d.D d.N)))) (IsLocalRing.ResidueField (vRing w))
end Data
namespace Data
variable (d : Data K ι Ω WT A)
open scoped TensorProduct
def Rb : ℕ := (d.T - 1).choose d.D
noncomputable def lenA (la : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (e : ℕ) : ℕ∞ :=
  let R := (la.valuationSubringAtPrime K).toSubring
  letI : Module R (∀ c, A c) := Module.compHom _ R.subtype
  let Θ := Submodule.span R (d.Theta : Set (∀ c, A c))
  let X := Submodule.span R
    ((la.asIdeal ^ e • d.M : Submodule (𝓞 K) (∀ c, A c)) : Set (∀ c, A c))
  Module.length R (↥(X ⊔ Θ) ⧸ Θ.comap (X ⊔ Θ).subtype)
def Vamb : Type := KTf K d.D d.N ⊗[K] (∀ c, A c)
noncomputable instance : AddCommGroup d.Vamb :=
  inferInstanceAs (AddCommGroup (KTf K d.D d.N ⊗[K] (∀ c, A c)))
noncomputable instance : Module (KTf K d.D d.N) d.Vamb :=
  inferInstanceAs (Module (KTf K d.D d.N) (KTf K d.D d.N ⊗[K] (∀ c, A c)))
noncomputable def tv (x : KTf K d.D d.N) (a : ∀ c, A c) : d.Vamb := (x ⊗ₜ[K] a : KTf K d.D d.N ⊗[K] (∀ c, A c))
noncomputable def polyToV (p : MvPolynomial (TVar d.D d.N) (∀ c, A c)) : d.Vamb :=
  ∑ β ∈ p.support,
    d.tv (algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (MvPolynomial.monomial β 1)) (p.coeff β)
noncomputable abbrev modOpV (la : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    Module (Op d.D d.N la) d.Vamb :=
  Module.compHom _ (OpToKT d.D d.N la)
noncomputable def genZV : {α : Fin d.D → Fin (d.T + 1) // d.absα α = d.a0} × Fin d.n0 → d.Vamb :=
  fun p => d.polyToV (d.genZ p.1.1 p.2)
noncomputable def ZK : Submodule (KTf K d.D d.N) d.Vamb :=
  Submodule.span (KTf K d.D d.N) (Set.range d.genZV)
noncomputable def rho : ℕ := Module.finrank (KTf K d.D d.N) d.ZK
noncomputable def lenOp (la : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (e : ℕ) : ℕ∞ :=
  letI := d.modOpV la
  let Θ : Submodule (Op d.D d.N la) d.Vamb := Submodule.span (Op d.D d.N la)
    ((fun a => d.tv 1 a) '' (d.Theta : Set (∀ c, A c)))
  let X : Submodule (Op d.D d.N la) d.Vamb :=
    Submodule.span (Op d.D d.N la) ((fun a => d.tv 1 a) ''
    ((la.asIdeal ^ e • d.M : Submodule (𝓞 K) (∀ c, A c)) : Set (∀ c, A c)))
  Module.length (Op d.D d.N la) (↥(X ⊔ Θ) ⧸ Θ.comap (X ⊔ Θ).subtype)
noncomputable def cl (la : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) : ℝ :=
  letI := d.modOpV la
  let Zla : Submodule (Op d.D d.N la) d.Vamb := Submodule.span (Op d.D d.N la) (Set.range d.genZV)
  let Mla : Submodule (Op d.D d.N la) d.Vamb := Submodule.span (Op d.D d.N la)
    ((fun a => d.tv 1 a) '' (d.M : Set (∀ c, A c)))
  let Zsat : Submodule (Op d.D d.N la) d.Vamb := Mla ⊓ Submodule.span (Op d.D d.N la) (d.ZK : Set d.Vamb)
  ((Module.length (Op d.D d.N la) (Zsat ⧸ Zla.comap Zsat.subtype)).toNat : ℝ)
noncomputable abbrev algOp (h : d.S1) (la : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (c : ι) :
    Algebra (Op d.D d.N la) (OmS (Ω c) d.D d.N) :=
  (d.OpToS h la c).toAlgebra
noncomputable def eF (hd : d.Ax 𝒜) : ∀ c, A c := hd.a4.choose
noncomputable def bvecG (sel : Fin d.del → Fin d.np) (e : ∀ c, A c) (k : Fin d.del) :
    ∀ c, OmS (Ω c) d.D d.N :=
  fun c => algebraMap (Ω c) (OmS (Ω c) d.D d.N) (ratio (Ω := Ω c) (d.thp (sel k) c) (e c))
def AdmissibleOmegaFamiliesAtPrimeOfSection (e : ∀ c, A c) (la : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    Set (∀ c, OmS (Ω c) d.D d.N) :=
  {y | ∀ c, ∀ w ∈ d.PlOver la c,
    0 ≤ w (y c) + ((d.ord c (d.Wres c w) d.wF (e c) : ℤ) : WithTop ℤ)}
noncomputable def IL (h : d.S1) (sel : Fin d.del → Fin d.np) (e : ∀ c, A c)
    (la : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) : ℝ :=
  letI : ∀ c, Algebra (Op d.D d.N la) (OmS (Ω c) d.D d.N) := fun c => d.algOp h la c
  let A0 := Submodule.span (Op d.D d.N la) (d.AdmissibleOmegaFamiliesAtPrimeOfSection e la)
  let B := Submodule.span (Op d.D d.N la) (Set.range (d.bvecG sel e))
  ((Module.length (Op d.D d.N la) (A0 ⧸ B.comap A0.subtype)).toNat : ℝ)
noncomputable def bvec (hd : d.Ax 𝒜) : Fin d.del → ∀ c, OmS (Ω c) d.D d.N :=
  d.bvecG hd.sel (d.eF hd)
def AdmissibleOmegaFamiliesAtPrime (hd : d.Ax 𝒜) (la : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    Set (∀ c, OmS (Ω c) d.D d.N) :=
  d.AdmissibleOmegaFamiliesAtPrimeOfSection (d.eF hd) la
noncomputable def Iterm (h : d.S1) (hd : d.Ax 𝒜) (la : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    ℝ :=
  d.IL h hd.sel (d.eF hd) la
noncomputable def Nl (h : d.S1) (la : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) : ℝ :=
  ∑ c, ∑ᶠ (w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ)) (_ : w ∈ d.PlOver la c),
    (d.fze h c w : ℝ) * (d.ord c (d.Wres c w) (d.n1 • d.wde) (d.et c) : ℝ)
noncomputable def ql (hd : d.Ax 𝒜) (la : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) : ℝ :=
  letI := hd.twistedCentralTestFunction; letI := hd.numberFieldDegreeOne; letI := hd.fieldDegreeAxiom
  ∑ᶠ (la1 : IsDedekindDomain.HeightOneSpectrum (𝓞 hd.K1))
    (_ : la1.asIdeal.comap (algebraMap (𝓞 K) (𝓞 hd.K1)) = la.asIdeal),
    ((la1.asIdeal.ramificationIdx (𝓞 K) * la1.asIdeal.inertiaDeg (𝓞 K) : ℕ) : ℝ) /
      (Module.finrank K hd.K1 : ℝ) * hd.q la1
noncomputable def rhoP (hd : d.Ax 𝒜) : ℕ :=
  letI := hd.twistedCentralTestFunction; letI := hd.fieldDegreeAxiom
  d.rk - Module.finrank hd.K1 hd.MD
end Data
end ReciprocityTheory.ChartRestriction.G.T0


