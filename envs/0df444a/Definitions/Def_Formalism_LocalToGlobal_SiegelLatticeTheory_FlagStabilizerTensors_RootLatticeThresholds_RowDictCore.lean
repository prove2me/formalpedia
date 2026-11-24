-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_RowDictCore
-- name    : Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_RowDictCore
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-24T17:54:34.903293+00:00
-- url     : https://prove2.me/theorems/10eb7fed-b956-4678-bde6-c34361c91b2b
-- title:
--   Row Dict Core
-- statement:
--   Definitions and structural lemmas for Row Dict Core, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/FlagStabilizerTensors/RootLatticeThresholds/RowDictCore.lean

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_GlobAut
import Definitions.Def_Formalism_LocalToGlobal_NormalizedHeckeFactors_TypesDefs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory NumberField Polynomial
open scoped InnerProductSpace TensorProduct
open Matrix
namespace Formalism.L2.SG.Pf.RowDictPf
open Formalism.MainNotions.S
def RConvFExists : Prop :=
  ∀ (I : AutInst) (μf : Measure I.Gf) [SigmaFinite μf] [μf.IsHaarMeasure], μf.IsMulRightInvariant →
    SecondCountableTopology I.GA → BorelSpace I.GA →
    ∀ (fund : Set I.GA), I.IsFundDom (I.muA μf) fund →
    ∀ R : I.GA → (I.L2 μf fund →L[ℂ] I.L2 μf fund), I.IsRightReg μf fund R →
    ∀ f : I.Gf → ℂ, Integrable f μf → ∃ T : I.L2 μf fund →L[ℂ] I.L2 μf fund, I.IsRConvF μf fund R f T
def recipN {g : ℕ} (f : (ZMod g)[X]) : (ZMod g)[X] := C (f.coeff 0)⁻¹ * f.reverse
def SeriesConj : Prop :=
  ∀ (g : ℕ) [Fact g.Prime] (teich : Formalism.CyclotomicNorms.Fbar g →* ℂ) (ζ : ℕ → Formalism.CyclotomicNorms.Fbar g), Formalism.L2.NT.IsGenSys ζ →
    ∀ (r : ℕ) (f : (ZMod g)[X]), f.Monic → ∀ x : GL (Fin r) (ZMod g),
      star ((Formalism.L2.NT.eSerC teich ζ r f).coeff x) = (Formalism.L2.NT.eSerC teich ζ r (recipN f)).coeff x
def GoodRecip : Prop :=
  ∀ (N g : ℕ) [Fact g.Prime] {PP J : Type} (f : PP → (ZMod g)[X]) (χ : PP → J → (ZMod g)ˣ),
    Formalism.CyclotomicNorms.IsGood N g f χ → Formalism.CyclotomicNorms.IsGood N g (fun v => recipN (f v)) (fun v j => (χ v j)⁻¹)
section Red
variable (I : AutInst)
def wLat0 (w : IsDedekindDomain.HeightOneSpectrum (𝓞 I.E)) : Submodule (𝓞 I.E) (Fin I.n → I.E) :=
  Submodule.span (𝓞 I.E) {z | ∃ a ∈ w.asIdeal, ∃ y ∈ I.L, z = ((a : 𝓞 I.E) : I.E) • y}
def IsRedBasis0 (w : IsDedekindDomain.HeightOneSpectrum (𝓞 I.E)) {m : ℕ} (b : Fin m → (Fin I.n → I.E)) : Prop :=
  (∀ i, b i ∈ I.L) ∧ ∀ y ∈ I.L, ∃ c : Fin m → ℤ, y - ∑ i, (c i : I.E) • b i ∈ wLat0 I w
def RedMat0 (w : IsDedekindDomain.HeightOneSpectrum (𝓞 I.E)) (p : ℕ) {m : ℕ} (x : I.Gf)
    (M : Matrix (Fin m) (Fin m) (ZMod p)) : Prop :=
  ∃ b : Fin m → (Fin I.n → I.E), IsRedBasis0 I w b ∧ ∀ i,
    I.fmat x *ᵥ (fun k => Formalism.UG.inclE (F := I.F) (Af I.F) (b i k)) -
      ∑ j, (((M j i).val : ℕ) : I.E ⊗[I.F] Af I.F) • (fun k => Formalism.UG.inclE (F := I.F) (Af I.F) (b j k)) ∈
      lamAf (F := I.F) (wLat0 I w)
end Red
def RedExists0 : Prop :=
  ∀ (I : AutInst) (w : IsDedekindDomain.HeightOneSpectrum (𝓞 I.E)) (p : ℕ), p.Prime →
    Nat.card (𝓞 I.E ⧸ w.asIdeal) = p →
    ∀ m : ℕ, m = I.n → ∀ x ∈ I.Kset, ∃ M : GL (Fin m) (ZMod p), RedMat0 I w p x (M : Matrix (Fin m) (Fin m) (ZMod p))
def RedConj0 : Prop :=
  ∀ (I : AutInst) (w : IsDedekindDomain.HeightOneSpectrum (𝓞 I.E)) (p : ℕ), p.Prime →
    Nat.card (𝓞 I.E ⧸ w.asIdeal) = p →
    ∀ m : ℕ, m = I.n → ∀ (x : I.Gf) (M M' : GL (Fin m) (ZMod p)),
      RedMat0 I w p x (M : Matrix (Fin m) (Fin m) (ZMod p)) →
      RedMat0 I w p x (M' : Matrix (Fin m) (Fin m) (ZMod p)) → ∃ P : GL (Fin m) (ZMod p), M' = P⁻¹ * M * P
end Formalism.L2.SG.Pf.RowDictPf


