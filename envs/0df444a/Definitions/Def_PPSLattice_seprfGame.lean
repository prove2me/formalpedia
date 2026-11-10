-- Prove2me | Definitions.Def_PPSLattice_seprfGame
-- name    : PPSLattice_seprfGame
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T22:33:42.605245+00:00
-- url     : https://prove2.me/theorems/c06be24a-f077-498c-a70a-6e998aeaf9ca
-- title:
--   The SEPRF security experiment
-- statement:
--   The adversary outputs $(1^{\ell_{\mathrm{out}}},x^*)$ with $\ell_{\mathrm{out}}\ge1$ and $x^*\in\{0,1\}^\lambda$ (otherwise the output is a uniform bit). Then $b\leftarrow\{0,1\}$; $\mathrm{key}_0\leftarrow\mathrm{Setup}(1^\lambda,1^{\ell_{\mathrm{out}}})$, or $\mathrm{eqKey}\leftarrow\mathrm{Sim1}(1^\lambda,1^{\ell_{\mathrm{out}}},x^*)$, $y^*\leftarrow\{0,1\}^{\ell_{\mathrm{out}}}$, $\mathrm{key}_1\leftarrow\mathrm{Sim2}(\mathrm{eqKey},y^*)$. The adversary receives $\mathrm{key}_b$ and guesses; the output is $1$ iff the guess is $b$.
-- source:
--   Goyal–Yadugiri, New Results in Adaptively-Secure Broadcast Encryption and Succinct Computational Secret Sharing from Standard Lattices, STOC 2027 submission (manuscript sha256 7f9c493f…), Definition 4.2, Security, p.19

import Mathlib
import Definitions.Def_RestrictedDec_Adversary
import Definitions.Def_PPSLattice_SEPRF
import Definitions.Def_AvgPHETH_uniformDist
open QAlgorithms.Complexity
set_option autoImplicit false

namespace PPSLattice

/-- The **SEPRF security experiment** (Definition 4.2), with output `1` iff the guess equals `b`:
the adversary's first move `tup [1^{ℓ_out}, x*]` must have `ℓ_out ≥ 1` and `x* ∈ {0,1}^λ` (otherwise
the output is a uniform bit); then `b ← {0,1}`; `key₀ ← Setup(1^λ, 1^{ℓ_out})`, or
`eqKey ← Sim1(1^λ, 1^{ℓ_out}, x*)`, `y* ← {0,1}^{ℓ_out}`, `key₁ ← Sim2(eqKey, y*)`; the adversary
receives `key_b` and its next move's first bit is the guess.
Goyal–Yadugiri, *New Results in Adaptively-Secure Broadcast Encryption and Succinct Computational Secret Sharing from Standard Lattices*, STOC 2027 submission (manuscript sha256 7f9c493f…), Definition 4.2, Security, p.19. -/
noncomputable def seprfGame (F : SEPRF) (A : RestrictedDec.Adversary) (lam : ℕ) : PMF Bool :=
  (A.activate lam [] (BeyondDS.tup [])).bind fun r0 =>
    let fs := BeyondDS.untup r0.2
    let lo := BeyondDS.decNat (fs.getD 0 [])
    let xs := fs.getD 1 []
    if 1 ≤ lo ∧ xs.length = lam then
      (PMF.uniformOfFintype Bool).bind fun b =>
        (if b then (F.sim1 lam lo xs).bind fun ek => (AvgPHETH.uniformDist lo).bind fun ys => F.sim2 ek ys
          else F.setup lam lo).bind fun key =>
          (A.activate lam r0.1 key).map fun r1 => decide (r1.2.headD false = b)
    else PMF.uniformOfFintype Bool

end PPSLattice


