-- Prove2me | Definitions.Def_ReciprocityTheory_DualLattices_WtGtRowSubstXSub
-- name    : ReciprocityTheory_DualLattices_WtGtRowSubstXSub
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:21:55.647869+00:00
-- url     : https://prove2.me/theorems/263983b9-ccb7-4659-81c9-1bbd5907c402
-- title:
--   Wt Gt Row Subst XSub
-- statement:
--   Definitions and structural lemmas for Wt Gt Row Subst XSub, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/WtGtRowSubstXSub.lean

import Definitions.Def_ReciprocityTheory_DualLattices_ConstantCoeffRowSubst
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Matrix Finset
open scoped Classical
namespace ReciprocityTheory.PGsh
variable {ν : ℕ} {ι : Type*}
def vw (p : Fin ν × ι) : ℕ := 2 ^ (ν - 1 - (p.1 : ℕ))
def wt (A : Fin ν × ι →₀ ℕ) : ℕ := A.sum fun p e => e * vw p
def tor (s : ℂ) : Matrix (Fin ν) (Fin ν) ℂ := Matrix.diagonal fun k => s ^ (2 ^ (ν - 1 - (k : ℕ)))
def comp (d : ℕ) (P : MvPolynomial (Fin ν × ι) ℂ) : MvPolynomial (Fin ν × ι) ℂ :=
  ∑ A ∈ P.support.filter (fun A => wt A = d), monomial A (coeff A P)
def WtGe (d : ℕ) (P : MvPolynomial (Fin ν × ι) ℂ) : Prop := ∀ A ∈ P.support, d ≤ wt A
def WtGt (d : ℕ) (P : MvPolynomial (Fin ν × ι) ℂ) : Prop := ∀ A ∈ P.support, d < wt A
end ReciprocityTheory.PGsh


