-- Prove2me | Definitions.Def_ReciprocityTheory_DualLattices_CyclicRecursionStatement
-- name    : ReciprocityTheory_DualLattices_CyclicRecursionStatement
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T04:15:09.785444+00:00
-- url     : https://prove2.me/theorems/22e8c96c-8109-4f67-8cfb-ef72326860ea
-- title:
--   Cyclic Recursion Statement
-- statement:
--   Definitions and structural lemmas for Cyclic Recursion Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/CyclicRecursionStatement.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open WittVector Ideal
namespace ReciprocityTheory.PGsh
section Ainf
variable (p : ℕ) [Fact p.Prime] (C : Type) [Field C] (v : Valuation C NNReal)
  (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (span {(p : O)}) O]
def KerThetaStatement : Prop :=
  ∀ pflat : PreTilt O p, pflat.untilt = (p : O) →
    RingHom.ker (fontaineTheta O p) =
        span {(p : WittVector p (PreTilt O p)) - teichmuller p pflat} ∧
      ((p : WittVector p (PreTilt O p)) - teichmuller p pflat) ∈
        nonZeroDivisors (WittVector p (PreTilt O p)) ∧
      RingHom.ker ((Ideal.Quotient.mk (span {(p : O)})).comp (fontaineTheta O p)) =
        span {(p : WittVector p (PreTilt O p)), teichmuller p pflat}
def XiNuStatement : Prop :=
  ∀ ε : PreTilt O p, v.Integers O →
    IsPrimitiveRoot (((frobeniusEquiv (PreTilt O p) p).symm ε).untilt) p →
      teichmuller p ε - 1 =
          (∑ i ∈ Finset.range p, teichmuller p ((frobeniusEquiv (PreTilt O p) p).symm ε) ^ i) *
            (teichmuller p ((frobeniusEquiv (PreTilt O p) p).symm ε) - 1) ∧
        fontaineTheta O p (teichmuller p ((frobeniusEquiv (PreTilt O p) p).symm ε) - 1) =
          ((frobeniusEquiv (PreTilt O p) p).symm ε).untilt - 1 ∧
        v (algebraMap O C (fontaineTheta O p
            (teichmuller p ((frobeniusEquiv (PreTilt O p) p).symm ε) - 1))) ^ (p - 1) =
          v (p : C) ∧
        ∀ pflat : PreTilt O p, pflat.untilt = (p : O) →
          RingHom.ker (fontaineTheta O p) =
              span {∑ i ∈ Finset.range p,
                teichmuller p ((frobeniusEquiv (PreTilt O p) p).symm ε) ^ i} ∧
            ∃ u : (WittVector p (PreTilt O p))ˣ,
              ∑ i ∈ Finset.range p, teichmuller p ((frobeniusEquiv (PreTilt O p) p).symm ε) ^ i =
                u * ((p : WittVector p (PreTilt O p)) - teichmuller p pflat)
def RegularStatement : Prop :=
  ∀ pflat : PreTilt O p, pflat.untilt = (p : O) →
    (p : WittVector p (PreTilt O p)) ∈ nonZeroDivisors (WittVector p (PreTilt O p)) ∧
      (∀ x : WittVector p (PreTilt O p),
          teichmuller p pflat * x ∈ span {(p : WittVector p (PreTilt O p))} →
            x ∈ span {(p : WittVector p (PreTilt O p))}) ∧
      span {(p : WittVector p (PreTilt O p)), teichmuller p pflat} ≠ ⊤
def FlatW'Statement : Prop :=
  ∀ pflat : PreTilt O p, pflat.untilt = (p : O) →
    span {(p : WittVector p (PreTilt O p)) ^ 2, teichmuller p pflat} =
        span {((p : WittVector p (PreTilt O p)) - teichmuller p pflat) ^ 2, teichmuller p pflat} ∧
      ((p : WittVector p (PreTilt O p) ⧸
          span {(p : WittVector p (PreTilt O p)) ^ 2, teichmuller p pflat}) ^ 2 = 0) ∧
      (∀ x : WittVector p (PreTilt O p) ⧸
            span {(p : WittVector p (PreTilt O p)) ^ 2, teichmuller p pflat},
          (p : WittVector p (PreTilt O p) ⧸
              span {(p : WittVector p (PreTilt O p)) ^ 2, teichmuller p pflat}) * x = 0 →
            ∃ y, x = (p : WittVector p (PreTilt O p) ⧸
              span {(p : WittVector p (PreTilt O p)) ^ 2, teichmuller p pflat}) * y) ∧
      ∀ [Algebra (ZMod (p ^ 2)) (WittVector p (PreTilt O p) ⧸
          span {(p : WittVector p (PreTilt O p)) ^ 2, teichmuller p pflat})],
        Module.Flat (ZMod (p ^ 2)) (WittVector p (PreTilt O p) ⧸
          span {(p : WittVector p (PreTilt O p)) ^ 2, teichmuller p pflat})
end Ainf
def TiltStructureStatement (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal)
    (O : Type) [CommRing O] [Algebra O C], v.Integers O →
    ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (span {(p : O)}) O],
      (∃ pflat : PreTilt O p, pflat.untilt = (p : O)) ∧
      (∃ ε : PreTilt O p, IsPrimitiveRoot (((frobeniusEquiv (PreTilt O p) p).symm ε).untilt) p) ∧
      KerThetaStatement p O ∧ XiNuStatement p C v O ∧ RegularStatement p O ∧
      FlatW'Statement p O
def TeichSumStatement (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ (ι : Type) (s : Finset ι),
    (∃ S : MvPolynomial ι ℤ, (p : MvPolynomial ι ℤ) * S =
      ∑ i ∈ s, MvPolynomial.X i ^ p - (∑ i ∈ s, MvPolynomial.X i) ^ p) ∧
    ∀ (K : Type) [CommRing K] [CharP K p] [PerfectRing K p] (X : ι → K) (S : MvPolynomial ι ℤ),
      (p : MvPolynomial ι ℤ) * S =
          ∑ i ∈ s, MvPolynomial.X i ^ p - (∑ i ∈ s, MvPolynomial.X i) ^ p →
        (∃ w : WittVector p K,
          ∑ i ∈ s, teichmuller p (X i) =
            teichmuller p (∑ i ∈ s, X i) + (p : WittVector p K) *
              teichmuller p (MvPolynomial.aeval (fun i => (frobeniusEquiv K p).symm (X i)) S) +
              (p : WittVector p K) ^ 2 * w) ∧
        ∀ (y : K) (t : WittVector p K), ∃ w : WittVector p K,
          (teichmuller p y + (p : WittVector p K) * t) ^ p =
            teichmuller p (y ^ p) + (p : WittVector p K) ^ 2 * w
def CyclicRecursionStatement : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℚ V] (o : ℕ) [NeZero o] (P : ℚ), 1 < P →
    ∀ La s : ZMod o → V,
      (∀ i, P • s i = s (i + 1) + La (i + 1)) ↔
        (∀ i, s i = (1 - P⁻¹ ^ o)⁻¹ •
          ∑ n ∈ Finset.range o, P⁻¹ ^ (n + 1) • La (i + ((n + 1 : ℕ) : ZMod o)))
def CyclicSeriesStatement : Prop :=
  ∀ (o : ℕ) [NeZero o] (P : ℝ), 1 < P → ∀ (La : ZMod o → ℝ) (i : ZMod o),
    HasSum (fun n : ℕ => P⁻¹ ^ (n + 1) * La (i + ((n + 1 : ℕ) : ZMod o)))
      ((1 - P⁻¹ ^ o)⁻¹ * ∑ n ∈ Finset.range o, P⁻¹ ^ (n + 1) * La (i + ((n + 1 : ℕ) : ZMod o)))
def CyclicOneTypeStatement : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℚ V] (p k : ℕ), 2 ≤ p → 1 ≤ k → ∀ La s : V,
    (((p : ℚ) ^ k) • s = s + La ↔ s = ((p : ℚ) ^ k - 1)⁻¹ • La) ∧
    (s = ((p : ℚ) ^ k - 1)⁻¹ • La →
      s - ((p : ℚ) - 1)⁻¹ • La = (((p : ℚ) ^ k - 1)⁻¹ - ((p : ℚ) - 1)⁻¹) • La ∧
      (k = 1 → s - ((p : ℚ) - 1)⁻¹ • La = 0))
end ReciprocityTheory.PGsh


