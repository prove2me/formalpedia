-- Prove2me | Definitions.Def_UnaryParityLifting_Exact_Supplement_resolution
-- name    : UnaryParityLifting_Exact_Supplement_resolution
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T19:45:53.087876+00:00
-- url     : https://prove2.me/theorems/eb532358-0b23-459b-a6c7-64c6d21b85aa
-- title:
--   Ordinary Resolution sequences and polynomial simulation
-- statement:
--   A Resolution refutation of F is a finite sequence ending with the empty clause. Every line is an input clause, a weakening of an earlier line, or the resolvent of two earlier lines on complementary literals. Size is sequence length; width is maximum line cardinality. No minimum over a potentially empty proof set is used.
--
--   $$\operatorname{size}(\pi)=\#\text{lines of }\pi,\qquad \operatorname{width}(\pi)=\max_{C\in\pi}|C|.$$
--
--   Polynomial simulation quantifies one positive constant C and natural exponent K before every finite input formula and every source proof: a target refutation must exist with size at most C(s+|F|+1)^K, where s is the source proof size. The two predicates distinguish Resolution simulating parity certificates and parity certificates simulating Resolution. Source formulas omit tautologies as in §2. These are proof syntax and size comparisons, with no assumed separation.
-- source:
--   Yaroslav Alekseev, Lifting to Unary Sherali–Adams over Parities, STOC 2027 submission #567 (October 2026), canonical source.pdf SHA256 088f9b64d3926dd700996884111b97c94806141880e07004f529211a40c0619b; citation_basis: published (submission artifact, no acceptance claim), p.18, §6 Resolution rule and weakening; pp.19–20, Corollary 6.3

import Definitions.Def_UnaryParityLifting_Exact_Supplement_encoding

noncomputable section
open Classical
open scoped BigOperators

namespace UnaryParityLifting.Exact.Supplement

/-- Ordinary Resolution with weakening, exactly the sequence convention of §6. -/
def Resolution {V : Type} (F : LiftSAParity.CNF V)
    (p : List (LiftSAParity.Clause V)) : Prop :=
  p.getLast? = some ∅ ∧ ∀ k (hk : k < p.length),
    p[k] ∈ F ∨
    (∃ i, ∃ (hi : i < k), p[i]'(lt_trans hi hk) ⊆ p[k]) ∨
    (∃ i j, ∃ (hi : i < k) (hj : j < k) (v : V),
      (v,true) ∈ p[i]'(lt_trans hi hk) ∧ (v,false) ∈ p[j]'(lt_trans hj hk) ∧
      p[k] = (p[i]'(lt_trans hi hk)).erase (v,true) ∪ (p[j]'(lt_trans hj hk)).erase (v,false))
def resolutionWidth {V : Type} (p : List (LiftSAParity.Clause V)) : ℕ :=
  (p.map Finset.card).foldr max 0
/-- One polynomial, uniform over formulas and source proofs, with the input length included. -/
def ResolutionSimulatesParity : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ K : ℕ, ∀ (v : ℕ) (F : LiftSAParity.CNF (Fin v))
    (q : CertificateSyntax F), SourceCNF F → q.Valid →
      ∃ p, Resolution F p ∧ (p.length : ℝ) ≤
        C * ((chargedSize (binaryCharge (Fin v)) q + cnfBits F + 1 : ℕ) : ℝ) ^ K
def ParitySimulatesResolution : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ K : ℕ, ∀ (v : ℕ) (F : LiftSAParity.CNF (Fin v))
    (p : List (LiftSAParity.Clause (Fin v))), SourceCNF F → Resolution F p →
      ∃ q : CertificateSyntax F, q.Valid ∧ (chargedSize (binaryCharge (Fin v)) q : ℝ) ≤
        C * ((p.length + cnfBits F + 1 : ℕ) : ℝ) ^ K

end UnaryParityLifting.Exact.Supplement


