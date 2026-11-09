-- Prove2me | Definitions.Def_GenericGroupWE_Main_PrimeSampling
-- name    : GenericGroupWE_Main_PrimeSampling
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:55:57.5992+00:00
-- url     : https://prove2.me/theorems/2b53008b-eb5a-4b37-ba61-3f5b3dcdbce5
-- title:
--   The bounded dyadic prime-sampling experiment
-- statement:
--   For integers $m\ge1$ and a trial budget $T$, sample independent uniform integers from $[2^m,2^{m+1})$. Stop at the first prime, or return the common failure symbol after $T$ unsuccessful trials.
--
--   $$p=2^m+a,\qquad a\ \text{uniform in }\{0,\ldots,2^m-1\}.$$
--
--   Primality is the actual arithmetic predicate, not an assumed test certificate. The polynomial-time implementation remains a conclusion of the prime-sampling theorem. Input lengths charge $m$ and the security parameter in unary. The experiment has no message-bit parameter and therefore cannot correlate failure with the encrypted bit.
-- source:
--   Hair and Sahai, Witness Encryption via Prime-Order Generic Groups, STOC 2027 submission #47 (PDF built 2026-11-02; SHA-256 0b7f14e2db9bb3e199883ab907f854b7b5884c7c9f3d1e4c306bb71e89b659cb), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/47.pdf, §7, Choosing the Prime, PDF p. 30 (printed p. 29).

import Definitions.Def_GenericGroupWE_Main_Scheme

namespace GenericGroupWE.Main

noncomputable def dyadicPrimeSampler (m : ℕ) : ℕ → PMF (Option PrimeOrder)
  | 0 => pure none
  | attempts+1 => (PMF.uniformOfFintype (Fin (2^m))).bind fun a =>
      let p := 2^m + a.val
      if hp : p.Prime then pure (some ⟨p,hp⟩) else dyadicPrimeSampler m attempts

def primeSamplingInput (m n : ℕ) : Bits :=
  pack [List.replicate m true, List.replicate n true]

def primeSamplingOutput (out : Option PrimeOrder) : Ciphertext :=
  ⟨none, out.map fun p => p.val.bits⟩

end GenericGroupWE.Main


