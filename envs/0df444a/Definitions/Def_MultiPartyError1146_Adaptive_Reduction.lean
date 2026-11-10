-- Prove2me | Definitions.Def_MultiPartyError1146_Adaptive_Reduction
-- name    : MultiPartyError1146_Adaptive_Reduction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T18:33:29.767711+00:00
-- url     : https://prove2.me/theorems/6a7c0755-c8c4-4955-ad7c-e82f29e67b7c
-- title:
--   Algorithm 2: outer encoding and decoded-column composition
-- statement:
--   Each $m$-bit input is encoded by a binary outer code of length $\ell$. A fixed $T$-round one-bit protocol runs separately on each encoded column. Each receiver reconstructs every party's length-$\ell$ codeword from those column outputs, then decodes it. Thus
--   $$T'=\ell T.$$
--   This is the actual causal protocol of Algorithm 2, rather than an assumption that arbitrary uncoded repetition preserves resilience. Failed outer decoding has a fixed all-zero output, making the protocol total.
-- source:
--   Klim Efremenko, Gillat Kol, Raghuvansh Saxena, Zhijun Zhang, STOC 2027 submission #1146 (October 2026), Algorithm 2; Lemma 4.13, printed p.30, PDF p.32

import Mathlib
import Definitions.Def_MultiPartyError1146_Adaptive_Protocol
import Definitions.Def_MultiPartyError1146_Adaptive_Codes

set_option autoImplicit false

namespace MultiPartyError1146.Adaptive

/-- Algorithm 2, including outer encoding, one execution per encoded column, and outer decoding. -/
noncomputable def algorithm2 {n m T : ℕ} (P : Protocol n 1 T)
    (C : BinaryCode (Fin m → Bool)) : Protocol n m (C.length * T) where
  send t i own h :=
    if hT : 0 < T then
      if hq : t.val / T < C.length then
        P.send ⟨t.val % T, Nat.mod_lt _ hT⟩ i (fun _ => C.encode own ⟨t.val / T,hq⟩)
          (fun s => h ⟨T * (t.val / T) + s.val, by
            have hs : s.val < t.val % T := s.isLt
            have he := Nat.div_add_mod t.val T
            omega⟩)
      else none
    else none
  output i own h :=
    if hT : 0 < T then
      let recovered := fun (k : Fin n) (q : Fin C.length) =>
        P.output i (fun _ => C.encode own q)
          (fun s => h ⟨q.val * T + s.val, by
            have hq : q.val + 1 ≤ C.length := q.isLt
            have hm := Nat.mul_le_mul_right T hq
            have hs : s.val < T := s.isLt
            have he : (q.val + 1) * T = q.val * T + T := by simp [Nat.add_mul]
            omega⟩) k 0
      fun k => ((C.decode (fun q => some (recovered k q))).getD (fun _ => false))
    else fun _ _ => false

end MultiPartyError1146.Adaptive


