-- Prove2me | Definitions.Def_HlawkaCodex84_SOSPolynomialData
-- name    : HlawkaCodex84_SOSPolynomialData
-- status  : Definition
-- author  : @moona3k
-- created : 2026-10-06T07:23:42.351101+00:00
-- url     : https://prove2.me/theorems/8968729f-fe6a-4832-8124-9a52b0610aaf
-- title:
--   Polynomial reconstruction expressions for Hlawka cutoff 84
-- statement:
--   These thirteen pure definitions specify the original cutoff-84 SOS matrix and radial comparison matrix, using the already published exact rational certificate data. Equality of these matrices is a separate theorem, not an assumption in the definitions. Both expressions agree definitionally with the locally verified original cutoff-84 construction.
-- source:
--   https://prove2.me/campaigns/sharp-diagonal-hlawka-constant; Codex cutoff84 continuation: Hlawka84_QuadraticSOSBridge. Both original matrix expressions have exact Lean rfl equivalence checks.

import Definitions.Def_HlawkaCodex84_SOSCertificateData
import Mathlib
set_option autoImplicit false
namespace HlawkaCodex84SOSPolynomialData
open HlawkaCodex84SOSCache
open scoped BigOperators
def rho : ℚ := 1953/10000

def pairLeft : Fin 3 → Fin 3 := ![1,0,0]

def pairRight : Fin 3 → Fin 3 := ![2,2,1]

def pairVector (p : Fin 3) : Fin 3 → ℚ :=
  fun i => (if i = pairLeft p then 1 else 0) - (if i = pairRight p then 1 else 0)

def graph (k : Fin 9) : Matrix (Fin 3) (Fin 3) ℚ :=
  ∑ p : Fin 3, if (k.val/3 = (pairLeft p).val ∨ k.val/3 = (pairRight p).val) ∧
      k.val%3 ≠ p.val then
    ((1+rho)/2) • Matrix.vecMulVec (pairVector p) (pairVector p) else 0


def realGram : Matrix (Fin 30) (Fin 30) ℝ := gram.map (fun q : ℚ => (q : ℝ))


def realMultiplier (k : Fin 9) : Matrix (Fin 3) (Fin 3) ℝ :=
  (![multiplier0, multiplier1, multiplier2, multiplier3, multiplier4,
    multiplier5, multiplier6, multiplier7, multiplier8] k).map (fun q : ℚ => (q : ℝ))


def blockWeights (e : Fin 9 → ℝ) : Fin 10 → ℝ :=
  ![1,e 0,e 1,e 2,e 3,e 4,e 5,e 6,e 7,e 8]

def tensorLift (e : Fin 9 → ℝ) : Matrix (Fin 30) (Fin 3) ℝ :=
  fun j i => if j.val%3 = i.val then blockWeights e ⟨j.val/3, by omega⟩ else 0


noncomputable def certificateMatrix (e : Fin 9 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  (tensorLift e).transpose * realGram * tensorLift e +
    ∑ k : Fin 9, ((1953/10000 : ℝ)^2 - (e k)^2) • realMultiplier k

/-- The reconstructed SOS expression is nonnegative on the continuous box.
Identification with the original radial comparison is a separate obligation. -/

def boxMatrix (e : Fin 9 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![-1+e 0,1+e 1,1+e 2; 1+e 3,-1+e 4,1+e 5; 1+e 6,1+e 7,-1+e 8]


def realGraph (k : Fin 9) : Matrix (Fin 3) (Fin 3) ℝ :=
  (graph k).map (fun q : ℚ => (q : ℝ))


noncomputable def comparisonMatrix (e : Fin 9 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  (14/5 : ℝ) • (boxMatrix e * (boxMatrix e).transpose) -
    ∑ k : Fin 9, (boxMatrix e ⟨k.val/3, by omega⟩ ⟨k.val%3, by omega⟩)^2 • realGraph k

end HlawkaCodex84SOSPolynomialData


