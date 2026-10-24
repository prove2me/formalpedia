-- Prove2me | Definitions.Def_HILL_PRG_InversionCheck
-- name    : HILL_PRG_InversionCheck
-- status  : Definition
-- author  : @Victorized
-- created : 2026-10-24T04:53:53.670747+00:00
-- url     : https://prove2.me/theorems/d7b3a57e-2fa5-4df1-afd0-306097446df9
-- title:
--   Explicit inversion-checking distinguisher
-- statement:
--   The inversion-checking program receives a security parameter, a target image, and inverter coins. It runs the inverter, verifies the candidate seed length, evaluates the generator at that candidate, and accepts exactly when the computed image equals the target.
--
--   The four component programs compute the unary seed length, the unary output length, generator evaluation, and inversion. The image is separated from the random coins using the computed output length. All inputs, including malformed encodings, have a defined output.
--
--   **Formalization Note** This definition specifies the program but does not assert its running-time bound. Polynomial-time closure and correctness are proved separately.
--
--   **Formalization credit:** **Wentao Li (Victor)**, under the Prove2Me account **Victorized**, with assistance from OpenAI Codex.
-- source:
--   Håstad, Impagliazzo, Levin, Luby, A Pseudorandom Generator from Any One-Way Function, SIAM J. Comput. 28(4), 1999, p. 1387, Theorem 6.3, reverse implication attributed to Levin (1987); https://www.cs.bu.edu/fac/lnd/pdf/hill.pdf. The checking algorithm and quantitative counting bound are an explicit formalization of the standard inverter-to-distinguisher reduction.

import Definitions.Def_HILL_PRG_Model

namespace HILL.PRG

/-- Check the output of an inverter, retaining the security parameter and target image.
`T` and `L` compute the unary seed and image lengths, `E` evaluates the generator,
and `I` is the inverter. Malformed inputs are assigned a total, deterministic result. -/
def inversionChecker (T L E I : Bits → Bits) (w : Bits) : Bits :=
  let n := (w.takeWhile id).length
  let payload := w.drop (n + 2)
  let y := payload.take ((L (List.replicate n true)).length)
  let out := I (enc n payload)
  if out.length = (T (List.replicate n true)).length ∧
      E (encAdvice n 0 out) = y then [true] else []

end HILL.PRG


