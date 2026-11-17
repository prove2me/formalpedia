-- Prove2me | Definitions.Def_RestrictedDec_Supplement_Sampler
-- name    : RestrictedDec_Supplement_Sampler
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T13:26:50.836317+00:00
-- url     : https://prove2.me/theorems/a18753d9-5c5f-414e-80af-88922c582e3f
-- title:
--   Message-pair samplers run independently of the keys
-- statement:
--   A **message-pair sampler** is a machine run on $1^\lambda$ and its own uniform coins $\rho$ (it receives no key), whose output is read as a pair $(u,v)$. It is **uniform PPT** when its number of coins is polynomially bounded and the machine is polynomial-time. For a property $\mathrm{Good}_\lambda(u,v)$, its **success probability** is $\Pr_\rho[\mathrm{Good}_\lambda(u,v)]$.
--
--   Theorems 5 and 7 require the property on every output; Theorems 9 and 11 require non-negligible success probability on infinitely many security parameters.
-- source:
--   Nguyen–Susilo, Between CPA and CCA: Security Hierarchies for Restricted Decryption, STOC 2027 submission (manuscript sha256 6aeac40c…), Theorem 5, p.25; Theorem 7, p.27; Theorem 9, p.38; Theorem 11, p.43

import Mathlib
import Definitions.Def_BeyondDS_tup
import Definitions.Def_NoisyOWMPC_Negligible
import Definitions.Def_RestrictedDec_Supplement_interact
open QAlgorithms.Complexity
set_option autoImplicit false

namespace RestrictedDec

namespace Supplement

/-- A **message-pair sampler**: a machine `f` run on `tup [1^λ, ρ]` with `coins λ` uniform coins
`ρ`, whose output `tup [u, v]` is read as the pair `(u, v)`. It sees no key: it is "run
independently of the generated keys".
Nguyen–Susilo, STOC 2027 submission (manuscript sha256 6aeac40c…), Theorem 5, p.25 ("two
efficiently found valid equal-length messages u0, u1, sampled independently of the generated
keys"); Theorem 9, p.38 ("a PPT witness sampler"); Theorem 11, p.43 ("a uniform PPT sampler, run
independently of the generated keys"). -/
structure Sampler where
  coins : ℕ → ℕ
  f : Str → Str

/-- The sampler is **uniform PPT**: polynomially many coins and a polynomial-time machine. -/
def Sampler.IsEfficient (W : Sampler) : Prop :=
  NoisyOWMPC.PolyBounded W.coins ∧ PolyTimeComputable W.f

/-- The pair output by the sampler on coins `ρ`. -/
def Sampler.out (W : Sampler) (lam : ℕ) (ρ : Fin (W.coins lam) → Bool) : Str × Str :=
  (fld (W.f (BeyondDS.tup [encNat lam, List.ofFn ρ])) 0,
    fld (W.f (BeyondDS.tup [encNat lam, List.ofFn ρ])) 1)

open Classical in
/-- The probability that the sampler's pair satisfies `Good λ u v`. -/
noncomputable def Sampler.succ (W : Sampler) (Good : ℕ → Str → Str → Prop) (lam : ℕ) : ℝ :=
  (((PMF.uniformOfFintype (Fin (W.coins lam) → Bool)).map fun ρ =>
    decide (Good lam (W.out lam ρ).1 (W.out lam ρ).2)) true).toReal

end Supplement

end RestrictedDec


