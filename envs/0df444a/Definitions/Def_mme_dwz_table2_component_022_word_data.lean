-- Prove2me | Definitions.Def_mme_dwz_table2_component_022_word_data
-- name    : mme_dwz_table2_component_022_word_data
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-08-26T03:30:53.456301+00:00
-- url     : https://prove2.me/theorems/df2f0100-8b9c-47a3-a17e-6ae4f298ffc1
-- title:
--   DWZ Table-2 022/202 prescribed split-word data
-- statement:
--   Defines the finite split-word data used by the q=6 Table-2 analysis of the coarse 022 and 202 Coppersmith--Winograd square constituents. A word records a three-class pattern with multiplicities L,G,L and a pair of q-valued labels at every middle position. The module also records the exact Table-2 integer scaling m=100000000t, L=3477403t, and G=93045194t. It contains data only and makes no tensor-restriction or asymptotic-value claim.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, Section 6.3 and Table 2, https://arxiv.org/abs/2210.10173

import Mathlib

namespace MME.DWZTable2Component022

def Fine022Channel (q : ℕ) :=
  Fin 1 ⊕ ((Fin q × Fin q) ⊕ Fin 1)

instance fine022ChannelFinite (q : ℕ) : Finite (Fine022Channel q) := by
  unfold Fine022Channel
  infer_instance

def splitMultiplicity (L G : ℕ) : Fin 3 → ℕ := ![L, G, L]

def SplitPattern (m L G : ℕ) :=
  {p : Fin m → Fin 3 // ∀ c,
    Fintype.card {r : Fin m // p r = c} = splitMultiplicity L G c}

instance splitPatternFinite (m L G : ℕ) : Finite (SplitPattern m L G) := by
  unfold SplitPattern
  infer_instance

def Restricted022Word (q m L G : ℕ) :=
  Σ p : SplitPattern m L G,
    ({r : Fin m // p.1 r = (1 : Fin 3)} → Fin q × Fin q)

instance restricted022WordFinite (q m L G : ℕ) :
    Finite (Restricted022Word q m L G) := by
  unfold Restricted022Word
  infer_instance

def splitWordCount (m L : ℕ) : ℕ :=
  Nat.choose m L * Nat.choose (m - L) L

def table2Power022 (t : ℕ) : ℕ := 100000000 * t

def table2OuterCount022 (t : ℕ) : ℕ := 3477403 * t

def table2MiddleCount022 (t : ℕ) : ℕ := 93045194 * t

end MME.DWZTable2Component022


