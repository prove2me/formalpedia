-- Prove2me | Definitions.Def_Formalism_LocalRingCardinality_DataHost
-- name    : Formalism_LocalRingCardinality_DataHost
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-24T17:57:08.623878+00:00
-- url     : https://prove2.me/theorems/ea43a402-b608-4da2-9a91-9b43534932a9
-- title:
--   Data Host
-- statement:
--   Definitions and structural lemmas for Data Host, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalRingCardinality/DataHost.lean

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_Params
import Definitions.Def_Formalism_FrobeniusOrbits_RealSubfieldLeCompositum
import Definitions.Def_Formalism_FrobeniusOrbits_DiscrMaximalRealCyclotomic
import Definitions.Def_Formalism_FrobeniusOrbits_HostOrbitsPlaces
import Definitions.Def_Formalism_FrobeniusOrbits_HostDiffSupport
import Definitions.Def_Formalism_FrobeniusOrbits_HostThickExists
import Definitions.Def_Formalism_FrobeniusOrbits_HostOrbitCountSg
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ConjEMemHostFIff
import Theorems.Thm_Formalism_FrobeniusOrbits_isCMField_hostE
import Theorems.Thm_Formalism_HC_HostAx_isCMField_hostE

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition
open scoped Pointwise
namespace Formalism.BasicNotions
noncomputable def iotaH (e : ℕ) (i : ZMod (2 ^ e)) : HGrp e := hcl e (u5 (e + 2)) ^ i.val
noncomputable def iotaHInv (e : ℕ) (h : HGrp e) : ZMod (2 ^ e) := Function.invFun (iotaH e) h
inductive PrimeClass
  |   splitK
  |   signal
  |   inertClass
  |   ram2
  |   ramQ
  |   ramD
  deriving DecidableEq
noncomputable def primeClass {φ : Formalism.HC.Frame} (H : Formalism.HC.HostRaw φ) (p : ℕ) : PrimeClass :=
  if p ∈ H.small then .ram2 else if p = H.q then .ramQ else if p = H.d then .ramD
  else if jacobiSym (-(H.d : ℤ)) p = 1 then .splitK
  else if H.psAt p = 1 then .signal
  else .inertClass
structure Host (R : Ranks) extends Formalism.HC.HostAx R.toFrame where

  flPS : toHostRaw.PsQ
  sqq : E
  sqq_sq : sqq ^ 2 = -(q : E)
  gal_sqq : ∀ σ : E ≃ₐ[ℚ] E, σ sqq = ((((gal σ).1.1 : ℤˣ) : ℤ) : E) * sqq

  QS_exact : toHostRaw.Exact

  QS_le : QS ≤ R.n ^ 2

  o_pow : R.toFrame.o ^ 64 ≤ 2 ^ R.e

  q_ne_three : q ≠ 3

  qd_big : 4 * R.t * R.r + 1 < q ∧ 4 * R.t * R.r + 1 < d

  splitBound : ℕ
  split_small : ∀ p : ℕ, p.Prime → p ≠ 2 → p ≤ splitBound → jacobiSym (-(d : ℤ)) p = 1

  small_le : ∀ l : ℕ, l.Prime → l ≠ 2 → l ∣ QS → 4 * l ≤ splitBound

  φ₀ : E →+* ℂ
  φ₀_mem : φ₀ ∈ toHostRaw.cmType

  𝔟 : Ideal (𝓞 E)
  𝔟_spec : differentIdeal (𝓞 toHostRaw.K) (𝓞 E) = 𝔟 * (toHostRaw.conj • 𝔟) ∧ 𝔟 ⊔ toHostRaw.conj • 𝔟 = ⊤

  𝔟_stable : ∀ σ : E ≃ₐ[ℚ] E, gal σ ∈ R.Psi → σ • 𝔟 = 𝔟

  levelPrimes : Finset ℕ

  g : Fin 2 → ℕ
  g_prime : ∀ i, (g i).Prime
  g_ne : g 0 ≠ g 1
  g_level : ∀ i, g i ∈ levelPrimes

  pde : ℕ
  pde' : ℕ
  pde_prime : pde.Prime
  pde'_prime : pde'.Prime
  pde_ne : pde ≠ pde'
  pde_level : pde ∈ levelPrimes ∧ pde' ∈ levelPrimes

  pde_mod : pde % 15 = 1 ∧ pde' % 15 = 1
  pde_ne_g : ∀ i, pde ≠ g i ∧ pde' ≠ g i

  ccK : Ideal (𝓞 toHostRaw.K)
  ccK_ne_bot : ccK ≠ ⊥

  ccK_primitive : ∀ m : ℕ, 1 < m → ¬ ccK ≤ Ideal.span {(m : 𝓞 toHostRaw.K)}

  ccK_split : ∀ P : Ideal (𝓞 toHostRaw.K), P.IsPrime → ccK ≤ P →
    (Ideal.absNorm P).Prime ∧ jacobiSym (-(d : ℤ)) (Ideal.absNorm P) = 1

  ccK_coprime : ∀ p ∈ insert 2 (insert 3 (insert 5 (insert q (insert d levelPrimes)))), Nat.Coprime (Ideal.absNorm ccK) p

  ccK_coprimeS : Nat.Coprime (Ideal.absNorm ccK) QS

  level_coprimeS : ∀ p ∈ levelPrimes, Nat.Coprime p QS

  TT : Finset R.A

  T2 : Finset ℕ
  u0 : R.A
  Lw : ℕ
  two_le_Lw : 2 ≤ Lw
  second_set_range : ∀ s ∈ T2, 4 * Lw * s < R.n0
  second_set_no_relation : NoRel T2 Lw

  CT2 : ℝ
namespace Host
variable {R : Ranks} (H : Host R)
@[instance_reducible] noncomputable def cmStar : StarRing H.E :=
  @NumberField.IsCMField.starRing H.E _ _ H.isCMField_hostE _
noncomputable def sigmaOf (g : R.GG) : H.E ≃ₐ[ℚ] H.E := H.gal.symm g
noncomputable def emb (g : R.GG) : H.E →+* ℂ := H.φ₀.comp (H.sigmaOf g : H.E →+* H.E)
def MuCond {ι : Type} [Fintype ι] (g : ι → R.GG) (e : ι → ℚ) : Prop :=
  ∀ ζ : H.E, (∃ n : ℕ, 0 < n ∧ ζ ^ n = 1) → ∏ τ, H.emb (g τ) ζ ^ (e τ).num = 1
open Classical in

noncomputable def topPlaces : Finset R.GG := H.TT.image R.tau1
open Classical in

noncomputable def thickPlaces : Finset R.GG :=
  H.T2.image (fun s => R.tau2 (R.dig s + H.u0))
def IsThin (g : R.GG) : Prop := g ∈ R.Psi ∧ g ∉ H.topPlaces ∧ g ∉ H.thickPlaces
noncomputable def cls (p : ℕ) : PrimeClass := primeClass H.toHostRaw p
noncomputable def rdE : ℝ :=
  |(discr H.E : ℝ)| ^ ((1 : ℝ) / (Module.finrank ℚ H.E : ℝ))
noncomputable def v : ℝ := H.rdE / 2
noncomputable def ka : ℝ := Real.pi / H.v
def sqrtMinusD : H.E := H.sqd
noncomputable def xi0 : H.E := -1 / ((Ideal.absNorm H.ccK : H.E) * H.sqrtMinusD)
noncomputable def ccE : Ideal (𝓞 H.E) := Ideal.map (algebraMap (𝓞 H.K) (𝓞 H.E)) H.ccK
noncomputable def AA0 : FractionalIdeal (nonZeroDivisors (𝓞 H.E)) H.E :=
  ((H.𝔟 : FractionalIdeal (nonZeroDivisors (𝓞 H.E)) H.E))⁻¹
noncomputable def AA : FractionalIdeal (nonZeroDivisors (𝓞 H.E)) H.E :=
  (H.ccE : FractionalIdeal (nonZeroDivisors (𝓞 H.E)) H.E) * H.AA0
noncomputable def AAbar : FractionalIdeal (nonZeroDivisors (𝓞 H.E)) H.E :=
  ((H.conj • H.ccE : Ideal (𝓞 H.E)) : FractionalIdeal (nonZeroDivisors (𝓞 H.E)) H.E) *
    ((H.conj • H.𝔟 : Ideal (𝓞 H.E)) : FractionalIdeal (nonZeroDivisors (𝓞 H.E)) H.E)⁻¹
noncomputable def ddE : Ideal (𝓞 H.E) := differentIdeal ℤ (𝓞 H.E)
def secondSet_card_lower_bound : Prop :=
  (R.n0 : ℝ) * Real.exp (-(H.CT2 * Real.sqrt (Real.log (R.n0 : ℝ) * Real.log H.Lw))) / H.Lw ≤ H.T2.card
end Host
def FactIota : Prop := ∀ e : ℕ,
  Function.Bijective (iotaH e) ∧
  (∀ i j : ZMod (2 ^ e), iotaH e (i + j) = iotaH e i * iotaH e j) ∧
  iotaH e 1 = hcl e (u5 (e + 2))
def bridge_iota : Prop := ∀ e : ℕ, ∀ ι : Multiplicative (ZMod (2 ^ e)) ≃* HGrp e,
  ι (Multiplicative.ofAdd 1) = hcl e (u5 (e + 2)) →
  ∀ i : ZMod (2 ^ e), ι (Multiplicative.ofAdd i) = iotaH e i
def bridge_star : Prop := ∀ (R : Ranks) (H : Host R) (x : H.E),
  (@star H.E (@InvolutiveStar.toStar _ (@StarMul.toInvolutiveStar _ _
    (@StarRing.toStarMul _ _ H.cmStar))) x) = H.conj x
def FactCardPsi : Prop := ∀ (R : Ranks) (H : Host R),
  Nat.card R.Psi = R.f ∧ H.cmType.ncard = R.f
def FactEmb : Prop := ∀ (R : Ranks) (H : Host R),
  Function.Bijective H.emb ∧ ∀ g : R.GG, H.emb g ∈ H.cmType ↔ g ∈ R.Psi
def FactPlaces : Prop := ∀ φ : Formalism.HC.Frame,
  (∀ g : φ.GG, g ∈ φ.Psi ↔ (∃ t, g = φ.tau1 t) ∨ (∃ t, g = φ.tau2 t)) ∧
  ∀ t t' : φ.A, φ.tau1 t ≠ φ.tau2 t'
def FactTopsThick : Prop := ∀ (R : Ranks) (H : Host R),
  (∀ g ∈ H.topPlaces, g ∈ R.Psi) ∧ (∀ g ∈ H.thickPlaces, g ∈ R.Psi) ∧
  Disjoint H.topPlaces H.thickPlaces ∧
  H.topPlaces.card = H.TT.card ∧ H.thickPlaces.card = H.T2.card
def HNeZero {R : Ranks} (H : Host R) (p : ℕ) : Prop :=
  ∀ (P : Ideal (𝓞 H.E)) [P.IsPrime] [P.LiesOver (Ideal.span {(p : ℤ)})] (σ : H.E ≃ₐ[ℚ] H.E),
    IsArithFrobAt ℤ σ P → Even (orderOf (H.galE σ).2)
def FactRd : Prop := ∀ (R : Ranks) (H : Host R),
  (2 : ℝ) ^ ((R.e : ℝ) + 1 - (2 : ℝ) ^ (-(R.e : ℝ))) * Real.sqrt H.d ≤ H.rdE ∧
  H.rdE ≤ (H.QS : ℝ) / 2 * Real.sqrt ((H.q : ℝ) * H.d) ∧ (2 * R.f : ℝ) ≤ H.rdE ^ 2
def FactPrincipalDatum : Prop := ∀ (R : Ranks) (H : Host R),
  FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 H.E)) H.xi0 * H.AA * H.AAbar *
    ((H.ddE : Ideal (𝓞 H.E)) : FractionalIdeal (nonZeroDivisors (𝓞 H.E)) H.E) = 1
def FactMMUnimodular : Prop := ∀ (R : Ranks) (H : Host R), ∀ x : H.E,
  x ∈ H.AA0 ↔ ∀ y ∈ H.AA0,
    Algebra.trace H.K H.E (x * H.conj y) ∈ (algebraMap (𝓞 H.K) H.K).range
def FactClassFrob : Prop := ∀ (R : Ranks) (H : Host R),
  ∀ (p : ℕ) [Fact p.Prime], ¬ p ∣ H.condN →
  ∀ (P : Ideal (𝓞 H.E)) [P.IsPrime] [P.LiesOver (Ideal.span {(p : ℤ)})]
    (σ : H.E ≃ₐ[ℚ] H.E), IsArithFrobAt ℤ σ P →
    (H.cls p = .splitK ↔ ((H.galE σ).1 = 1 ∨ (H.galE σ).1 = (-1, 1))) ∧
    (H.cls p = .signal ↔ (H.galE σ).1 = (1, -1)) ∧
    (H.cls p = .inertClass ↔ (H.galE σ).1 = c0)
def FactFrobGeom : Prop := ∀ (R : Ranks) (H : Host R) (σ : H.E ≃ₐ[ℚ] H.E),
  H.galE σ⁻¹ = (H.galE σ)⁻¹ ∧
  R.iotaInv (H.galE σ⁻¹).2 = - R.iotaInv (H.galE σ).2
end Formalism.BasicNotions


