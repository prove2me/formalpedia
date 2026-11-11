-- Prove2me | Definitions.Def_TrapdoorHCF_CCA2_Constructions
-- name    : TrapdoorHCF_CCA2_Constructions
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T19:38:08.838999+00:00
-- url     : https://prove2.me/theorems/b404387f-01ae-4583-af80-5c0bbf01d328
-- title:
--   The three fixed black-box constructions
-- statement:
--   The **projection** keeps key generation, input sampling and evaluation, and replaces a designated string and a successful partial-inversion result by its first bit. Failure stays failure; the forward theorems require $l(\lambda)\ge1$ for all sufficiently large $\lambda$.
--
--   For a one-bit TDHF, the **CCA2 construction** uses its keys. To encrypt the one-bit string $m$, it samples exactly $\lambda$ independent candidate inputs and chooses the first whose designated value equals $m$. It returns the selected evaluation with flag 0, or $(m,1)$ if none matches. Decryption of flag 0 uses partial inversion; flag 1 returns its payload only when that payload has length 1. A ciphertext is the flag bit followed by its payload; the empty string is malformed and decrypts to failure. Decryption uses only the secret key.
--
--   The reverse construction for PKE $P$ over $\{0,1\}^{l(\lambda)}$ samples a uniform concatenation $x=m\mathbin\Vert r$ of a message and an encryption tape, and sets
--
--   $$\operatorname{Eval}(pk,m\mathbin\Vert r)=\operatorname{Enc}(pk,m;r),\qquad \operatorname{hEval}(pk,m\mathbin\Vert r)=m,\qquad\operatorname{pInv}(sk,y)=\operatorname{Dec}(sk,y).$$
--
--   These are actual algorithm definitions, without correctness or security conclusions embedded in them. Every construction calls the input algorithms as subroutines: this is the mission's reading of black-box construction. Missing bits on inputs outside the sampler range have a fixed false default; no source instance uses that default.
-- source:
--   Kanad Chakravarti, Shreyas Gupta, Bhavana Kanukurthi, Girisha Shankar, Trapdoors Beyond Inversion: Recoverable Information in Public-Key Cryptography, STOC 2027 submission #571 (October 2026; unrefereed), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/571.pdf, Theorem 7 construction, pp.36–37; Lemma 5 construction, pp.45–46; Section A.2, pp.34–35

import Mathlib
import Definitions.Def_TrapdoorHCF_CCA2_Games
open QAlgorithms.Complexity
set_option autoImplicit false

namespace TrapdoorHCF.CCA2

/-- First-bit projection in Lemma 5, pp.45–46. The default on the empty string
is irrelevant whenever the source's l >= 1 assumption is satisfied. -/
def firstBit (z : Str) : Str := [z.headD false]

def proj (T : TDHF) : TDHF :=
  { T with
    hEval := fun lam pk x => firstBit (T.hEval lam pk x)
    pInv := fun lam sk y => (T.pInv lam sk y).map firstBit }

/-- A ciphertext is flag :: payload. Thus [] alone is malformed, and a flag-one
ciphertext is well formed only if its payload is one bit. This code is injective. -/
def cipher (payload : Str) (flag : Bool) : Str := flag :: payload

/-- The pp.36–37 deterministic decryption rule, with no public-key argument. -/
def ccaDec (T : TDHF) (lam : ℕ) (sk : Str) : Str → Option Str
  | false :: c => T.pInv lam sk c
  | true :: c => if c.length = 1 then some c else none
  | [] => none

/-- Read a fixed-length coin vector. Outside the specified domain, missing bits
are false. All construction calls on sampled inputs have exactly the right length. -/
def coinsFrom (k : ℕ) (w : Str) : Fin k → Bool := fun i => w.getD i.val false

/-- Ordered candidates, with no injectivity assumption on their evaluations. -/
def candidatePairs (T : TDHF) (lam : ℕ) (pk : Str) (xs : List Str) : List (Str × Str) :=
  xs.map fun x => (T.eval lam pk x, T.hEval lam pk x)

/-- First matching candidate, or the printed fallback (m,1). -/
def chooseCipher (m : Str) (pairs : List (Str × Str)) : Str :=
  match pairs.find? (fun yz => decide (yz.2 = m)) with
  | some yz => cipher yz.1 false
  | none => cipher m true

/-- Theorem 7 construction, pp.36–37. Exactly lambda independent sampler blocks
are available; computing every candidate before selecting has the same output law
as stopping at the first match. No security property is assumed in this definition. -/
def cca2Scheme (T : TDHF) : RestrictedDec.PKE where
  keyCoins := T.keyCoins
  keyGen := T.keyGen
  encCoins := fun lam => lam * T.sampCoins lam
  enc := fun lam pk m r =>
    let tape := List.ofFn r
    let xs := (List.range lam).map fun i =>
      T.samp lam (coinsFrom (T.sampCoins lam) (tape.drop (i * T.sampCoins lam)))
    chooseCipher m (candidatePairs T lam pk xs)
  dec := ccaDec T

/-- Section A.2, pp.34–35. x = m || r uses a fixed l(lambda)-bit prefix.
The sampler is the identity on l + encCoins uniform bits. Outside its range,
missing encryption coins are false; correctness is asserted on the range only. -/
def ofPKE (l : ℕ → ℕ) (P : RestrictedDec.PKE) : TDHF where
  keyCoins := P.keyCoins
  keyGen := P.keyGen
  sampCoins := fun lam => l lam + P.encCoins lam
  samp := fun _ r => List.ofFn r
  eval := fun lam pk x =>
    P.enc lam pk (x.take (l lam)) (coinsFrom (P.encCoins lam) (x.drop (l lam)))
  hEval := fun lam _ x => x.take (l lam)
  pInv := P.dec

end TrapdoorHCF.CCA2


