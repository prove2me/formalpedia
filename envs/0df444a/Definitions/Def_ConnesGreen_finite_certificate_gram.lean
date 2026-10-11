-- Prove2me | Definitions.Def_ConnesGreen_finite_certificate_gram
-- name    : ConnesGreen_finite_certificate_gram
-- status  : Definition
-- author  : @waitingintime
-- created : 2026-10-08T21:09:23.669794+00:00
-- url     : https://prove2.me/theorems/ec1f5411-3870-473f-b284-dc0377dd518d
-- title:
--   Finite certificate operator and Gram matrix for the original Connes–Weil actors
-- statement:
--   On the original completed Dirichlet energy carrier at window t, define D = δI + sum of positive rank-one columns over F minus sum of negative rank-one columns over the unchanged selected packet S. The finite index is the tagged union of positive F and negative S columns. The certificate matrix has entries inner(u_i,D u_j). Actual zeta zeros, multiplicities and Green-source normalization are inherited without modification. Dependent and repeated columns are allowed; no inverse or basis is defined. This is an auxiliary finite compression, not a replacement for the original full actors.
-- source:
--   monocap-tech/weil, WeilDefect/Connes/FiniteCertificateGram.lean at df7cd5371e1778aa18f13856f32247a971f62d6b
--
--   Literature/source audit addendum (2026-10-11; COR-19): Exact native software custody, independently verified from retained local Git objects: monocap-tech/weil df7cd5371e1778aa18f13856f32247a971f62d6b, WeilDefect/Connes/FiniteCertificateGram.lean, SHA256 d91cdc289ef38252ddeedb92bde07040b6362cb7f444f50a5cfaa6f6438cbdfc. Public availability of these historical pins has not been checked; this addendum verifies local source bytes and preserves the original source ancestry. The unchanged graph RHS values were checked against native definitions by Lean rfl. This is source/value custody, not an assertion that contextual literature supplies the whole definition bundle.

import Definitions.Def_ConnesGreen_RG0_original_actors
import Definitions.Def_ConnesGreen_RG0_original_inner_marker
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Complex ConnesRZ ConnesRZFrontier ConnesGreen WeilDefect WeilDefect.ConnesNative
open scoped BigOperators InnerProductSpace lp ENNReal Classical ComplexOrder Topology
noncomputable section
namespace ConnesGreen
/-- Finite auxiliary certificate operator on the ORIGINAL physical carrier.
This does not replace either original full actor or the selected packet. -/
def canonicalFiniteCertificateOperator (t : ℝ) (S F : Finset CriticalZeros) (δ : ℝ) :
    Physical t →L[ℂ] Physical t :=
  δ • 1 + (∑ ρ ∈ F, InnerProductSpace.rankOne ℂ
    (positiveGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ)
    (positiveGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ)) -
  (∑ ρ ∈ S, InnerProductSpace.rankOne ℂ
    (negativeGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ)
    (negativeGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ))

/-- Tagged ORIGINAL positive and selected negative columns; repetitions and
linear dependencies are permitted, with no change of basis assumed. -/
def canonicalFiniteActorFamily (t : ℝ) (S F : Finset CriticalZeros) :
    ({ρ : CriticalZeros // ρ ∈ F} ⊕ {ρ : CriticalZeros // ρ ∈ S}) → Physical t :=
  Sum.elim (fun ρ => positiveGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ.1)
    (fun ρ => negativeGreenColumn (fun τ => sourceEmbed t (actualGreenSource τ)) ρ.1)

/-- Exact finite Gram compression of the error-paid certificate operator. -/
def canonicalFiniteCertificateGram (t : ℝ) (S F : Finset CriticalZeros) (δ : ℝ) :
    Matrix ({ρ : CriticalZeros // ρ ∈ F} ⊕ {ρ : CriticalZeros // ρ ∈ S})
      ({ρ : CriticalZeros // ρ ∈ F} ⊕ {ρ : CriticalZeros // ρ ∈ S}) ℂ :=
  fun i j => ⟪canonicalFiniteActorFamily t S F i,
    canonicalFiniteCertificateOperator t S F δ (canonicalFiniteActorFamily t S F j)⟫_ℂ


end ConnesGreen


