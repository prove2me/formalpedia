-- Prove2me | Definitions.Def_EdgeSublinearMWIS_Main_NativePhaseInterfaces
-- name    : EdgeSublinearMWIS_Main_NativePhaseInterfaces
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-18T14:57:53.716091+00:00
-- url     : https://prove2.me/theorems/bff94ed6-ebc8-4248-a0de-b820a6d76614
-- title:
--   Phase state interfaces for weighted preprocessing and exact point recovery
-- statement:
--   These data declarations expose the exact interfaces used by weighted preprocessing, root resource computation, flow compilation and rational point initialization. They define finite matrix/list encodings, input predicates and stored program parameters.
--
--   For a graph $G$ with rounded nonnegative copy counts $c_v$, the encoding includes the adjacency matrix of its independent blow-up, of order
--   $$N=\sum_{v\in V(G)}c_v.$$
--   The bundle also exposes the real interpretation of rational vectors and the fixed flow-system dimensions. Every operational correctness and resource bound remains a separate theorem obligation.
-- source:
--   https://github.com/EdouardBonnet/lax-109476/blob/0a042604c7ae1ef4cd9a4c7d82eb902f313d4864/concepts/Lax109476/RationalCertificates.lean (definitions and structure interfaces, starting at lines 41)
--   https://github.com/EdouardBonnet/lax-263307/blob/68b2d26aa2075e2ef80fd9d355ea748d2a818fd1/proofs/Lax263307Proofs/NativeBlowUp.lean (definitions and structure interfaces, starting at lines 20, 23, 242, 320)
--   https://github.com/EdouardBonnet/lax-263307/blob/68b2d26aa2075e2ef80fd9d355ea748d2a818fd1/proofs/Lax263307Proofs/NativeFrontend.lean (definitions and structure interfaces, starting at lines 18)
--   https://github.com/EdouardBonnet/lax-455465/blob/9988b9c5399185cfb3ca2129ca7c807fd80c2885/proofs/Lax455465Proofs/RamFlowData.lean (definitions and structure interfaces, starting at lines 10, 11)
--   https://github.com/EdouardBonnet/lax-455465/blob/9988b9c5399185cfb3ca2129ca7c807fd80c2885/proofs/Lax455465Proofs/RamFlowLp.lean (definitions and structure interfaces, starting at lines 38)

import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic
import Mathlib.Data.Fin.Tuple.Take
import Definitions.Def_EdgeSublinearMWIS_Main_NativeDetailedInterfaces

-- Solutions.RAM_Lax109476_RationalCertificates
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.

/-!
---
title: Exact rational solution certificates
type: definition
---
A rational linear program is a linear program with rational coefficients,
still optimized over real variables. Its outcomes have three certificate forms:

* an optimal primal point and matching dual multipliers;
* nonnegative Farkas multipliers certifying infeasibility;
* a feasible primal point and an improving recession direction certifying
  unboundedness.

Every coordinate in these certificates is rational, and all certificate
conditions can be checked by exact rational arithmetic.

# Formalization notes

The three constructors carry precisely the witnesses needed for their
claims. The predicates use the same row, column, and objective formulas
as the real program. The real interpretation casts the coefficient data
and witness coordinates exactly. No outcome or correctness proof is
assumed as part of the input.
-/

namespace Lax109476.RationalCertificates

open Lax109476.LinearProgram Lax109476.FarkasCertificate Lax109476.RecessionDirection



/-- The exact real interpretation of a rational vector. -/
def realVector {n : ℕ} (x : Fin n → ℚ) : Fin n → ℝ := fun j => x j







end Lax109476.RationalCertificates

end

-- Solutions.RAM_Lax455465Proofs_RamFlowData
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax455465Proofs.RamFlowData

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState DirectedFlowLP
open scoped NNRat

abbrev rows (n : ℕ) := n*n+2*((n*n)*n)
abbrev columns (n : ℕ) := 1+(n*n)*(n*n)









end Lax455465Proofs.RamFlowData

end

-- Solutions.RAM_Lax455465Proofs_RamFlowLp
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax455465Proofs.RamFlowLp

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational RamVirtualState DirectedFlowLP
open RamFlowData Lax109476.RationalEncoding
open scoped NNRat





abbrev wordLength (n : ℕ) := 2+3*(rows n*columns n+rows n+columns n)







end Lax455465Proofs.RamFlowLp

end

-- Solutions.RAM_Lax263307Proofs_NativeFrontend
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


namespace Lax263307Proofs.NativeFrontend

open Lax263307.IndependentSetEncoding

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax263307.WeightedIndependentSet

def tailInput {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (w : Fin n → ℚ) (ε : ℚ) : List ℕ :=
  (List.ofFn fun u => List.ofFn fun v => if G.Adj u v then 1 else 0).flatten ++ encodeParameters w ε


















































end Lax263307Proofs.NativeFrontend

end

-- Solutions.RAM_Lax263307Proofs_NativeBlowUp
section
-- Adapted from the pinned Apache-2.0 Lax native MWIS and RAM sources.


set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

namespace Lax263307Proofs.NativeBlowUp

open Lax263307.IndependentSetEncoding

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState
open Lax263307.WeightedAlgorithm

def blocks {n : ℕ} (copies : Fin n → ℕ) : List (List ℕ) :=
  List.ofFn fun v => List.replicate (copies v) v.val

def owners {n : ℕ} (copies : Fin n → ℕ) : List ℕ := (blocks copies).flatten







































def matrix {n : ℕ} (f : Fin n → Fin n → ℕ) : List ℕ :=
  (List.ofFn fun i => List.ofFn (f i)).flatten

















def numberedMatrix {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (copies : Fin n → ℕ) : List ℕ := matrix (fun i j => if (numbered G copies).Adj i j then 1 else 0)















open Lax263307.WeightRounding Lax263307.WeightedIndependentSet NativeFrontend













open Lax109476Proofs





end Lax263307Proofs.NativeBlowUp

end


