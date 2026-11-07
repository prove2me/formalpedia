-- Prove2me | Definitions.Def_MultiSelectPandora_resv
-- name    : MultiSelectPandora_resv
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:02:45.294554+00:00
-- url     : https://prove2.me/theorems/7cd55596-8398-4760-a1d5-4220628e4df4
-- title:
--   The reservation value $\sigma_i$
-- statement:
--   The reservation value of box $i$ is the least solution $\sigma_i$ of
--   $$E[(v_i-\sigma_i)_+]=c_i.$$
--   It can be negative: if $c_i>E[v_i]$ then $\sigma_i=E[v_i]-c_i<0$.
--
--   **Formalization Note** The paper says "the solution". It is not unique when $c_i=0$, since every $\sigma$ at or above the largest value of positive probability solves the equation, so this is the least one. The capped value is the same for every choice, but `MaxV` is not. It is written as an `sInf`; the verification file proves that for a valid instance the solution set has a least element, so the junk value of `sInf` is never met.
-- source:
--   Beyhaghi–Han–Luqman, Multi-Selection Pandora's Box with Nonobligatory Inspection: A PTAS and a Structural Separation, manuscript (STOC 2027 submission; held artifact sha256 0c3a8a501c28a4d26cc0a9898ecfcee9283823c4b2a6aaa221463bce48e9cea8), §2.3, p.6 (PDF p.7); p.31 (PDF p.32)

import Mathlib
import Definitions.Def_MultiSelectPandora_Inst

namespace MultiSelectPandora

/-- **The reservation value `σ_i`.** Beyhaghi–Han–Luqman manuscript, §2.3, p.6 (PDF p.7): "the solution of
`E[(v_i − σ_i)_+] = c_i`".

**Formalization Note.** The solution is not unique when `c_i = 0`: every `σ` at or above the largest value of positive
probability solves the equation. This is the **least** solution, as an `sInf`. For a valid instance the solution set is
nonempty, closed and bounded below, so `sInf` is its minimum (verification file), and `sInf`'s junk value is never met.
`σ_i` can be negative: p.31 (PDF p.32) "if `c_i > E[v_i]`, then `σ_i = E[v_i] − c_i < 0`". -/
noncomputable def resv (I : Inst) (i : Fin I.n) : ℝ :=
  sInf {σ : ℝ | ∑ j, I.prob i j * max (I.val i j - σ) 0 = I.c i}

end MultiSelectPandora


