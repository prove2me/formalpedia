-- Prove2me | Definitions.Def_MantriCVQ_reducedDNF
-- name    : MantriCVQ_reducedDNF
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:13:42.589629+00:00
-- url     : https://prove2.me/theorems/3aff995d-8aa3-40a2-95a9-10ec18a063dc
-- title:
--   The DNF $\Phi^-_\rho$ of Claim 6.4
-- statement:
--   $\Phi^-_\rho$ is the DNF on the free variables obtained from $\Phi$ by deleting every term for which more than $J$ blocks are light, and then projecting and normalizing the remaining terms. It is a function of $\Phi$ and the seeds, and does not depend on $z$.
-- source:
--   Mantri, Classical Verification of Quantum Computation Beyond the Polynomial Hierarchy, arXiv:2610.37635 (PDF sha256 d1fab777…1d0b33), Claim 6.4, p. 25 (PDF p. 27)

import Mathlib
import Definitions.Def_MantriCVQ_Light
import Definitions.Def_MantriCVQ_Projection

open QAlgorithms.Complexity SamplingAC0

namespace MantriCVQ

open Classical in
/-- The DNF `Φ⁻_ρ` of Claim 6.4 (Mantri, arXiv:2610.37635 (PDF sha256 d1fab777…1d0b33), Claim 6.4, p. 25
(PDF p. 27)): delete every term for which more than `J` blocks are light, and project and normalize
the remaining terms. It is a function of `Φ` and the seeds, not of `z`. -/
noncomputable def reducedDNF (C : (m : ℕ) → Bits m → Bits m → Bool) {ι : Type} [Fintype ι]
    [DecidableEq ι] {m : ℕ} (t J : ℕ) (Φ : DNF (ι × Addr [m])) (s : ι → Seed [m]) : DNF ι :=
  projDNF (forestProj C [m] s) (Φ.filter fun T => decide ((lightBlocks t T s).card ≤ J))

end MantriCVQ


