-- Prove2me | Definitions.Def_DetDLP_D2_TerminalLabeling
-- name    : DetDLP_D2_TerminalLabeling
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T05:12:42.083085+00:00
-- url     : https://prove2.me/theorems/463076b3-1d4f-4ac8-95ef-3bc2de9b3f01
-- title:
--   Encoded interface for boundary-balanced Appendix D.4 vertex labels
-- statement:
--   The input records the graph, the dimension, the unary palette, and the boundary hosts. The output is the coordinate-major label table used as the final field of the one-step query. Correctness requires this same table to satisfy both the padded cell bound and the boundary load bound in each coordinate.
-- source:
--   Liu–Zhang–Ren, Deterministic Discrete Logarithms (revised), Section 5.1, Lemma 5.1; Appendix D.4 caller-supplied labeling interface.

import Definitions.Def_DetDLP_OpenAIAppendixD
import Definitions.Def_DetDLP_PolyTBridge

set_option autoImplicit false

namespace DetDLP.D2
open AppendixD4
open OAI.Algorithms.SubexponentialSAT
open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace

/-- The unary palette gives an input-size bound for candidate enumeration even on malformed inputs. -/
def input (G : Graph) (a : ℕ) {b : ℕ} (host : Fin b → Fin G.nV) : Bits :=
  Encoding.encodeList id [G.encode, countWord a, List.replicate (64^a) true,
    encodeNatListBin (List.ofFn fun j => (host j).val)]

/-- Exactly the last field of `AppendixD4.stepInput`. -/
def output {G : Graph} {a : ℕ} (lbl : Label a G) : Bits :=
  encodeNatListBin ((List.finRange a).flatMap fun i => List.ofFn fun v => (lbl i v).val)

def Balanced {G : Graph} {a b : ℕ} (host : Fin b → Fin G.nV) (τ : ℕ) (lbl : Label a G) : Prop :=
  ∀ (i : Fin a) (g : Fin 64),
    32 * (Finset.univ.filter fun j : Fin b => lbl i (host j) = g).card ≤ b + 512 * (a + 2) * τ

/-- Uniform correctness contract. The multiplicity cap is not advice to the machine. -/
def Correct (f : Bits → Bits) : Prop := ∀ (G : Graph) (a b : ℕ) (host : Fin b → Fin G.nV) (τ : ℕ),
  1 ≤ G.nE → (a+2) * 64^(4*a) * max 1 G.maxDeg ≤ G.nE → 1 ≤ τ →
  (∀ x, (Finset.univ.filter fun y => host x = host y).card ≤ τ) →
  ∃ lbl : Label a G, f (input G a host) = output lbl ∧ Padded lbl ∧ Balanced host τ lbl

end DetDLP.D2


