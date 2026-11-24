-- Prove2me | Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_StandardValuations_SplitProd
-- name    : Development_WeilBound_ThetaLifts_LocalTheory_StandardValuations_SplitProd
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T05:57:36.696982+00:00
-- url     : https://prove2.me/theorems/595f5176-3708-4156-8ca1-64491ad3e3d2
-- title:
--   Split Prod
-- statement:
--   Definitions and structural lemmas for Split Prod, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LocalTheory/StandardValuations/SplitProd.lean

import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_StandardValuations_IntIndPow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open Matrix MeasureTheory ValuativeRel Topology GlobalTheory.SplitFlip GlobalTheory.SplitWeil
namespace PositivityTheory.ThKG.Std
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n d n₁ d₁ : ℕ} {ν : kˣ →* ℂˣ} {ϖ : kˣ} {c : ℕ}
def mid {b : ℕ} (i : Fin b) : Fin (b + 2) := i.castSucc.succ
open Classical in

def rad (ϖ : kˣ) (c : ℕ) (e : Fin n → Fin d) (j : Fin d) : k := if j ∈ Set.range e then 1 else (ϖ : k) ^ c
def std (ν : kˣ →* ℂˣ) (ϖ : kˣ) (c : ℕ) (e : Fin n → Fin d) (Y : Matrix (Fin n) (Fin d) k) : ℂ :=
  (∏ p : Fin n × Fin d, ind (rad ϖ c e p.2) (Y p.1 p.2)) * dl ν (Y.submatrix id e).det
def tm (Z : Fin n × Fin d → k) : Matrix (Fin n) (Fin d) k := Matrix.of fun i j => Z (i, j)
def emb (R : Type) [Zero R] [One R] (j : Fin n₁ → Fin n) : Matrix (Fin n) (Fin n₁) R := Matrix.of fun i i' => if i = j i' then 1 else 0
def ext (jr : Fin n₁ → Fin n) (jc : Fin d₁ → Fin d) (y : Matrix (Fin n₁) (Fin d₁) k) : Matrix (Fin n) (Fin d) k :=
  emb k jr * y * (emb k jc)ᵀ
variable {jr : Fin n₁ → Fin n} {jc : Fin d₁ → Fin d}
variable [SecondCountableTopology k] [MeasurableSpace k] [BorelSpace k] {m : Measure k} {ψ : AddChar k ℂ}
end PositivityTheory.ThKG.Std


