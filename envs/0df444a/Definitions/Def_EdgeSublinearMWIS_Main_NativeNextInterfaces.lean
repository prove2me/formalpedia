-- Prove2me | Definitions.Def_EdgeSublinearMWIS_Main_NativeNextInterfaces
-- name    : EdgeSublinearMWIS_Main_NativeNextInterfaces
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-18T16:36:38.60809+00:00
-- url     : https://prove2.me/theorems/079210ef-856b-49da-8aeb-4d94b795610b
-- title:
--   Moment and recovery selector data interfaces
-- statement:
--   These declarations define the moment-constructor size and word-height parameters, moment-vector values, enumerated subsets and their next-element relation, and the coordinate-recovery matrix and bound entries.
--
--   For a moment encoding of a graph with order $n$, target $k$ and relaxation level $r$, the shared height parameter is
--   $$H(n,k,r)=100\,s(n,k,r)^3+10.$$
--   The remaining interfaces describe stored values and query entries. They contain no algorithm correctness or execution assumptions; those are proved by the separate operational theorems.
-- source:
--   https://github.com/EdouardBonnet/lax-109476/blob/0a042604c7ae1ef4cd9a4c7d82eb902f313d4864/proofs/Lax109476Proofs/RamRecoveryData.lean (definitions and structure interfaces, starting at lines 16)
--   https://github.com/EdouardBonnet/lax-109476/blob/0a042604c7ae1ef4cd9a4c7d82eb902f313d4864/proofs/Lax109476Proofs/RecoveryQueryEntries.lean (definitions and structure interfaces, starting at lines 12, 21)
--   https://github.com/EdouardBonnet/lax-263307/blob/68b2d26aa2075e2ef80fd9d355ea748d2a818fd1/proofs/Lax263307Proofs/NativeCombinations.lean (definitions and structure interfaces, starting at lines 52, 278)
--   https://github.com/EdouardBonnet/lax-263307/blob/68b2d26aa2075e2ef80fd9d355ea748d2a818fd1/proofs/Lax263307Proofs/NativeMomentEncodingHeight.lean (definitions and structure interfaces, starting at lines 14)
--   https://github.com/EdouardBonnet/lax-263307/blob/68b2d26aa2075e2ef80fd9d355ea748d2a818fd1/proofs/Lax263307Proofs/NativeMomentProduce.lean (definitions and structure interfaces, starting at lines 13)
--   https://github.com/EdouardBonnet/lax-263307/blob/68b2d26aa2075e2ef80fd9d355ea748d2a818fd1/proofs/Lax263307Proofs/NativeMomentProgram.lean (definitions and structure interfaces, starting at lines 17, 104)
--   https://github.com/EdouardBonnet/lax-263307/blob/68b2d26aa2075e2ef80fd9d355ea748d2a818fd1/proofs/Lax263307Proofs/NativeMomentVectors.lean (definitions and structure interfaces, starting at lines 16)

import Definitions.Def_EdgeSublinearMWIS_Main_NativeBoundsInterfaces

-- Solutions.RAM_Lax109476Proofs_RecoveryQueryEntries
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax109476Proofs.RecoveryQueryEntries

open Lax109476.LinearProgram CoordinateOptimization LexicographicMinima RationalArithmeticBounds

def entry {m n : ℕ} (P : Program ℚ m n) (k : ℕ)
    (i : Fin ((m + (n + n)) + 1)) (j : Fin n) : ℚ :=
  if hi : i.val < m then P.A ⟨i.val, hi⟩ j
  else if i.val < m + n then
    if i.val - m < k ∧ j.val = i.val - m then 1 else 0
  else if i.val < m + n + n then
    if i.val - m - n < k ∧ j.val = i.val - m - n then -1 else 0
  else if j.val = k then 1 else 0

def bound {m n : ℕ} (P : Program ℚ m n) (x : Fin n → ℚ) (k : ℕ) (t : ℚ)
    (i : Fin ((m + (n + n)) + 1)) : ℚ :=
  if hi : i.val < m then P.b ⟨i.val, hi⟩
  else if hi : i.val < m + n then
    if i.val - m < k then x ⟨i.val - m, by omega⟩ else 0
  else if hi : i.val < m + n + n then
    if i.val - m - n < k then -x ⟨i.val - m - n, by omega⟩ else 0
  else t









end Lax109476Proofs.RecoveryQueryEntries

end

-- Solutions.RAM_Lax109476Proofs_RamRecoveryData
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax109476Proofs.RamRecoveryData

open Lax109476.LinearProgram
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRationalArrays RamRationalScalars





def Data {m n : ℕ} (P : Program ℚ m n) (x : Fin n → ℚ) (k : ℕ) (t : ℚ) (σ : Env) : Prop :=
  Represents "point.A" (RamMatrixStorage.flatten P.A) σ ∧ Represents "point.b" (List.ofFn P.b) σ ∧
    Represents "point.x" (List.ofFn x) σ ∧ σ.vars "point.m" = m ∧ σ.vars "point.n" = n ∧
    σ.vars "point.k" = k ∧ Value "bisect.mid" t σ







end Lax109476Proofs.RamRecoveryData

end

-- Solutions.RAM_Lax263307Proofs_NativeCombinations
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

namespace Lax263307Proofs.NativeCombinations

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState





def table (n k : ℕ) : List ℕ :=
  (List.ofFn fun i : Fin (n+1) => List.ofFn fun j : Fin (k+1) => i.val.choose j.val).flatten

































def advance (remaining need rank : ℕ) : ℕ × ℕ × ℕ :=
  if need=0 then (0,need,rank)
  else if rank<(remaining-1).choose need then (0,need,rank)
  else (1,need-1,rank-(remaining-1).choose need)



























end Lax263307Proofs.NativeCombinations

end

-- Solutions.RAM_Lax263307Proofs_NativeMomentProduce
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

namespace Lax263307Proofs.NativeMomentProduce

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open NativeMasks NativeMomentRows

def Value (B : ℕ) (q : ℚ) (σ : Env) : Prop :=
  σ.vars "coefficient.positive"< B ∧ σ.vars "coefficient.negative"< B ∧
  ((σ.vars "coefficient.positive" : ℕ) : ℚ)-σ.vars "coefficient.negative"=q





















end Lax263307Proofs.NativeMomentProduce

end

-- Solutions.RAM_Lax263307Proofs_NativeMomentVectors
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


set_option maxHeartbeats 200000
set_option maxRecDepth 10000

namespace Lax263307Proofs.NativeMomentVectors

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState
open Lax263307 MomentLP NativeMomentFamily NativeMomentProduce



def value (N q : ℕ) : ℚ := if q=1 then -1 else if q < N+2 then 1 else 0























end Lax263307Proofs.NativeMomentVectors

end

-- Solutions.RAM_Lax263307Proofs_NativeMomentProgram
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


set_option maxHeartbeats 200000
set_option maxRecDepth 10000

namespace Lax263307Proofs.NativeMomentProgram

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState Lax455465Proofs
open Lax263307 MomentLP
open Lax109476.RationalEncoding

abbrev N (n r : ℕ) := dimension n r


















open Lax109476Proofs





def size (n k r : ℕ) : ℕ := n+k+r+N n r+2




end Lax263307Proofs.NativeMomentProgram

end

-- Solutions.RAM_Lax263307Proofs_NativeMomentEncodingHeight
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax263307Proofs.NativeMomentEncodingHeight

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax263307 MomentLP NativeCatalogMetadata
open Lax109476.RationalEncoding
open Lax455465Proofs

def height (n k r : ℕ) : ℕ := 100*(NativeMomentProgram.size n k r)^3+10



end Lax263307Proofs.NativeMomentEncodingHeight

end


