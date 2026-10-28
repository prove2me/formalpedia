-- Prove2me | Definitions.Def_TaoFivePrimes_RHExtendedMomentRule
-- name    : TaoFivePrimes_RHExtendedMomentRule
-- status  : Definition
-- author  : @Johan Mercedes
-- created : 2026-10-27T18:51:58.383513+00:00
-- url     : https://prove2.me/theorems/756fe037-1e62-4977-816c-02c36c5dc6d2
-- title:
--   Rational Mellin quadrature rule for arbitrary moment order
-- statement:
--   For every nonnegative integer $j$, let $Q_j$ be the rational number obtained by applying the published sixteen-panel, 184-jet theta quadrature data to the scaled even moment of order $2j$.
--
--   $$
--   Q_j=\sum_{i=0}^{15} Q_{i,2j}.
--   $$
--
--   Each panel value is a finite rational sum formed from the stored theta-jet coefficients, integration weights, and factorials. The rule is defined at every nonnegative index. This definition alone asserts no numerical accuracy or zero-location conclusion.
-- source:
--   Extension of sometik179’s published 16-panel Mellin and theta-jet certificate, Prove2Me submission c9908072-d99a-4431-aad8-a72c6352619a, https://prove2.me/submissions/c9908072-d99a-4431-aad8-a72c6352619a, with theta/Mellin foundations by Gabewhigham. The present definition makes the rational rule available at arbitrary nonnegative moment indices.

/- Rational 16-panel rule for the scaled even Mellin moments of xi.
The theta-jet data and original quadrature framework are due to sometik179,
with theta/Mellin foundations by Gabewhigham. This definition asserts no
accuracy bound and no zero-location statement. -/
import Definitions.Def_TaoFivePrimes_RH14To100MomentCertificateDataNC
import Mathlib.Data.Rat.Cast.Defs
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset

set_option autoImplicit false
open Finset

namespace RHNextMomentRule

noncomputable def centers (i : ℕ) : List ℤ :=
  if hi : i<16 then RH14MomentEnclosureProof.CertifiedGlobalJetCenters.centerNumerators ⟨i,hi⟩ else []

noncomputable def jet (i j : ℕ) : ℚ :=
  (centers i |>.getD j 0 : ℚ)/CertifiedFixedPoint.scale310

noncomputable def weight (j : ℕ) : ℚ := (1-(-1:ℚ)^(j+1))/(j+1)

noncomputable def correlation (q : ℕ → ℚ) (m : ℕ) : ℚ :=
  ∑ l ∈ range (184-m), q l * weight (m+l)

noncomputable def scalarPanel (q : ℕ → ℚ) (a c h : ℚ) (k : ℕ) : ℚ :=
  h * ∑ m ∈ range (k+1),
    (if m<184 then (a*h)^m/(m.factorial:ℚ)*correlation q m else 0)*
      ((a*c)^(k-m)/((k-m).factorial:ℚ))

noncomputable def panelCenter (i : ℕ) : ℚ := 3*(2*(i:ℚ)+1)/16

end RHNextMomentRule

noncomputable def TaoFivePrimes_RHExtendedMomentRule (j : ℕ) : ℚ :=
  ∑ i ∈ Finset.range 16,
    RHNextMomentRule.scalarPanel (RHNextMomentRule.jet i) 64
      (RHNextMomentRule.panelCenter i) (3/16) (2*j)


