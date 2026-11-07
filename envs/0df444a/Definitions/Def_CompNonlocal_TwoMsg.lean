-- Prove2me | Definitions.Def_CompNonlocal_TwoMsg
-- name    : CompNonlocal_TwoMsg
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:43:05.204492+00:00
-- url     : https://prove2.me/theorems/edccaf6c-aba4-4632-82be-6746397f96fe
-- title:
--   Sender-first two-message QCCC protocols
-- statement:
--   A protocol of the form
--   $$(\mathrm{msg}_S,\mathrm{st}_S)\leftarrow\mathrm{Sen}_1(1^\kappa),\quad(\mathrm{msg}_R,\mathrm{out}_R)\leftarrow\mathrm{Rec}(\mathrm{msg}_S),\quad \mathrm{out}_S\leftarrow\mathrm{Sen}_2(\mathrm{st}_S,\mathrm{msg}_S,\mathrm{msg}_R),$$
--   with classical messages and a possibly quantum retained state $\mathrm{st}_S$. Derived: the law of $(\mathrm{msg}_S,\mathrm{msg}_R,\mathrm{out}_R,\mathrm{out}_S)$ and expectations under it.
-- source:
--   Głuch, Morimae, From Computational Nonlocality to Public-Key Encryption and Commitments, manuscript (STOC 2027 submission, sha256 e245edd7…), Definition 4, p.21

import Mathlib
import Definitions.Def_CompNonlocal_Family
import Definitions.Def_CompNonlocal_ICirc_branchOn
import Definitions.Def_CompNonlocal_ICirc_effectOn

set_option autoImplicit false

namespace CompNonlocal

open QAlgorithms.Complexity

/-- Sender-first two-message QCCC protocols. Głuch, Morimae, *From Computational Nonlocality to
Public-Key Encryption and Commitments*, manuscript (STOC 2027 submission, sha256 e245edd7…),
Definition 4, p.21: "We call key agreement sender-first two-message when it has the form
(msg_S, st_S) ← KA.Sen1(1^κ), (msg_R, K_R) ← KA.Rec(msg_S), K_S ← KA.Sen2(st_S, msg_S, msg_R). The
retained state st_S may be quantum." Lemma 18 (p.45) uses the same shape with general outputs.

The derived functions in this module, at security parameter `κ`: `st κ mS`, the sender's
unnormalized retained state after sending `mS`; `prob κ mS r sO`, the probability that the sender
sends `mS`, the receiver's classical output is `r` (its reply `msg_R = r.take (lR κ)` followed by its
private output `r.drop (lR κ)`), and the sender's final output is `sO`; and `expect κ f`, the
expectation of `f(msg_S, msg_R, out_R, out_S)` in an honest execution.

**Formalization Note** `Sen1` has no input; `Rec` reads `msg_S` classically (no quantum input);
`Sen2` reads `msg_S ++ msg_R` and `st_S`. There is no shared setup: every circuit starts from its own
inputs and `|0⟩` ancillas. -/
structure TwoMsg where
  /-- `Sen1(1^κ) → (msg_S, st_S)`. -/
  Sen1 : Family
  /-- `Rec(msg_S) → (msg_R, out_R)`. -/
  Rec : Family
  /-- `Sen2(st_S, msg_S, msg_R) → out_S`. -/
  Sen2 : Family
  /-- The length of the reply `msg_R` inside the receiver's classical output. -/
  lR : ℕ → ℕ

namespace TwoMsg

/-- The sender's unnormalized retained state after sending `mS`. -/
noncomputable def st (P : TwoMsg) (κ : ℕ) (mS : Str) :
    Matrix (Bits (P.Sen1 κ).outQ.length) (Bits (P.Sen1 κ).outQ.length) ℂ :=
  (P.Sen1 κ).branchOn 0 [] 1 (fun t => decide (t = mS))

/-- The probability of the honest execution `(msg_S, receiver output, sender output) = (mS, r, sO)`. -/
noncomputable def prob (P : TwoMsg) (κ : ℕ) (mS r sO : Str) : ℝ :=
  ((P.Rec κ).effectOn 0 mS (fun t => decide (t = r))).trace.re *
    ((P.Sen2 κ).effectOn (P.Sen1 κ).outQ.length (mS ++ r.take (P.lR κ))
        (fun t => decide (t = sO)) * P.st κ mS).trace.re

/-- The expectation of `f(msg_S, msg_R, out_R, out_S)` in an honest execution. -/
noncomputable def expect (P : TwoMsg) (κ : ℕ) (f : Str → Str → Str → Str → ℝ) : ℝ :=
  ∑ mS : Bits (P.Sen1 κ).outC.length, ∑ r : Bits (P.Rec κ).outC.length,
    ∑ sO : Bits (P.Sen2 κ).outC.length,
      P.prob κ (List.ofFn mS) (List.ofFn r) (List.ofFn sO) *
        f (List.ofFn mS) ((List.ofFn r).take (P.lR κ)) ((List.ofFn r).drop (P.lR κ)) (List.ofFn sO)

end TwoMsg

end CompNonlocal


