-- Prove2me | Definitions.Def_LaconicBarrier_WEScheme_source
-- name    : LaconicBarrier_WEScheme_source
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:42:51.723508+00:00
-- url     : https://prove2.me/theorems/fb58a62f-ded5-4368-8f96-3e2cc3e63ee1
-- title:
--   The fixed-message witness-encryption game
-- statement:
--   For one-bit messages the witness-encryption game with the message pair fixed to $(0,1)$ is a family of two-message games indexed by the statement $x$: the challenger samples $b \leftarrow \{0,1\}$, sends $\mathrm{Enc}(1^\lambda, x, b)$, receives a bit $b'$ and wins if $b' = b$. Its baseline is $1/2$ and its index set is the false statements $x \notin L$. A reduction's query count refers to calls to this stateless ciphertext-to-bit oracle.
-- source:
--   Jain, Mathialagan, Roy, From Succinct Arguments to Proofs: Lower Bounds for Obfuscation and SNARGs, STOC 2027 submission (manuscript sha256 1af78662…), §4.1.4, p.18

import Mathlib
import Definitions.Def_LaconicBarrier_WEScheme
import Definitions.Def_LaconicBarrier_TwoMsg

namespace LaconicBarrier

/-- The **fixed-message witness-encryption game** as a family of two-message games indexed by the
statement (Jain, Mathialagan, Roy, STOC 2027 submission (manuscript sha256 1af78662…), §4.1.4, p.18:
"The challenger samples `b ← {0, 1}`, sends `Enc(1^λ, x, b)`, receives a bit `b′`, and wins if
`b′ = b`; its baseline is `1/2`"; "Our query count refers to calls to this stateless
ciphertext-to-bit oracle"). The first coin is `b`, the others are `Enc`'s coins; a response other than
the one-bit string `[b]` loses. Its index set is the false statements `x ∉ L`. -/
noncomputable def WEScheme.source (E : WEScheme) : TwoMsg where
  coins lam x := E.ecoins lam x + 1
  chal lam x ρ := E.Enc lam x (ρ 0) (fun i => ρ i.succ)
  wins lam x ρ a := decide (a = [ρ 0])
  c₀ := 1 / 2
  c₀_nonneg := by norm_num
  c₀_lt_one := by norm_num

end LaconicBarrier


