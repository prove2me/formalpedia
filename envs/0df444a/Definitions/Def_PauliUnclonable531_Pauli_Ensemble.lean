-- Prove2me | Definitions.Def_PauliUnclonable531_Pauli_Ensemble
-- name    : PauliUnclonable531_Pauli_Ensemble
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:08:12.405227+00:00
-- url     : https://prove2.me/theorems/66960499-354b-4f53-8ca5-398adeeaaf16
-- title:
--   Product-state ensemble with the prescribed parity
-- statement:
--   At each position define the basis change Uⱼ as I when xⱼ=0, H when (xⱼ,zⱼ)=(1,0), and SH when (xⱼ,zⱼ)=(1,1). Let Uₖ be their tensor product and qⱼ the active mask. The constrained ensemble is
--
--   $$2^{-(n-1)}\sum_{r:\,\bigoplus_jq_jr_j=m}U_k|r\rangle\langle r|U_k^\dagger.$$
--
--   The sum includes every n-bit string satisfying the weighted parity. Identity positions are unconstrained and become maximally mixed after averaging. The construction statements require n≥1 and a supported key, so n−1 never truncates improperly. Proposition 3.2 identifies this ensemble with the ciphertext matrix; that equality is not built into the definition.
-- source:
--   Prabhanjan Ananth, Seyoon Ragavan, Amit Sahai, STOC 2027 submission #531 (October 2026), §3.1, p.16, Proposition 3.2, Eq. (15)

import Mathlib
import Definitions.Def_PauliUnclonable531_Pauli_Instructions

open scoped Matrix Matrix.Norms.L2Operator ComplexOrder
set_option autoImplicit false

namespace PauliUnclonable531.Pauli

/-- Local basis changes I,H,SH and their tensor product (§3.1, p.16). -/
noncomputable def basisChange (x z : Fin 2) : Op (Fin 2) :=
  if x = 0 then 1 else if z = 0 then gateMatrix .H else gateMatrix .S * gateMatrix .H

noncomputable def basisUnitary {n : ℕ} (k : Key n) : Op (Bits n) :=
  fun r s => ∏ j, basisChange (k.val.1 j) (k.val.2 j) (r j) (s j)

def weightedParity {n : ℕ} (k : Key n) (r : Bits n) : Fin 2 :=
  ∑ j, if active k.val j then r j else 0

/-- The constrained ensemble, not one individual pure ciphertext (Proposition 3.2). -/
noncomputable def parityEnsemble {n : ℕ} (k : Key n) (m : Fin 2) : Op (Bits n) :=
  ((2 : ℂ)^(n-1))⁻¹ • ∑ r : Bits n,
    if weightedParity k r = m then
      basisUnitary k * basisDensity r * (basisUnitary k).conjTranspose else 0

end PauliUnclonable531.Pauli


