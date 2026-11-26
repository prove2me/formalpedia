-- Prove2me | Definitions.Def_FirstPassageLinearTransport_RankScaledLoss
-- name    : FirstPassageLinearTransport_RankScaledLoss
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T11:04:24.224828+00:00
-- url     : https://prove2.me/theorems/08bbf87d-17b7-495d-8b5a-90b9cf644fa6
-- title:
--   Rank Scaled Loss
-- statement:
--   Definitions and structural lemmas for Rank Scaled Loss, from Idris Ali Shaik (shaikidris/FirstPassageLinearTransport-Palomar; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Polylogarithmic descent for almost all Collatz orbits in natural density development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/RankScaledLoss.lean

import Definitions.Def_FirstPassageLinearTransport_NestedRecertification
set_option autoImplicit true
namespace FirstPassageLinearTransport
noncomputable section
inductive CertifiedRankChain (r : ℚ) (n : ℕ) : ℕ → ℕ → Prop
  | first {q m h : ℕ}
      (hfp : IsFirstPassage (2 ^ q) n h)
      (hhm : h ≤ m)
      (hm : (m : ℚ) ≤ ((q + 1 : ℕ) : ℚ) / r) :
      CertifiedRankChain r n h q
  | next {t qprev q m h : ℕ}
      (hchain : CertifiedRankChain r n t qprev)
      (hgap : q < qprev)
      (hfp : IsFirstPassage (2 ^ q) (orbit t n) h)
      (hhm : h ≤ m)
      (hm : (m : ℚ) ≤ ((q + 1 : ℕ) : ℚ) / r) :
      CertifiedRankChain r n (t + h) q
end
end FirstPassageLinearTransport


