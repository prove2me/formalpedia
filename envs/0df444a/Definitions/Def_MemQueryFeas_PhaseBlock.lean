-- Prove2me | Definitions.Def_MemQueryFeas_PhaseBlock
-- name    : MemQueryFeas_PhaseBlock
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:40:19.23619+00:00
-- url     : https://prove2.me/theorems/ba46c4ec-b1bf-47a7-a12d-f1b5b3562865
-- title:
--   The Block property of a phase region
-- statement:
--   For a phase $v$ of layer $p$: the region $R_v$ is $\Delta$-$\mathrm{Block}_k(q\mid \mathrm{Mem}_v,C_v,E_{>p})$, in the skeleton model with the fixed deterministic learner and final oracle. For a leaf ($p=P$) the context is $(\mathrm{Mem}_\ell,C_\ell)$.
-- source:
--   Yu–Blanchard, Exponential memory/query-complexity tradeoffs in high-accuracy feasibility problems, preprint (Nov. 3, 2026), Theorem 2, Proposition 1, Corollary 1, p.11 (PDF p.12)

import Mathlib
import Definitions.Def_MemQueryFeas_IsBlock
import Definitions.Def_MemQueryFeas_memV
import Definitions.Def_MemQueryFeas_memCode
import Definitions.Def_MemQueryFeas_regionV
import Definitions.Def_MemQueryFeas_ctxV
import Definitions.Def_MemQueryFeas_EgtV

open MeasureTheory

namespace MemQueryFeas

/-- **The Block property of a phase region, `R_v` is `∆-Block_k(q | Mem_v, C_v, E_{>p})`.** Yu–Blanchard, *Exponential memory/query-complexity tradeoffs in high-accuracy feasibility problems*, preprint (Nov. 3, 2026),
Theorem 2, p.11 (PDF p.12): "`R_v` is `∆-Block_k(q | Mem_v, C_v, E_{>p−1})`" for `v ∈ V_{p−1}`;
Proposition 1 and Corollary 1, p.11.

For a phase `v` of layer `p = |v|` in the skeleton model `(μ, Eb, ch)` with the fixed deterministic
learner `alg` and final oracle `fin`: the random region `R_v` (`regionV`) is `∆-Block_k(q | ·)` with
context `(Mem_v, C_v, E_{>p})` (`memV` encoded by `memCode`, `ctxV`, `EgtV`).

**Formalization Note.** For a leaf (`p = P`), `E_{>P}` is the constant `0`, which adds nothing to the
context (Corollary 1 conditions on `(Mem_ℓ, C_ℓ)` only). The final oracle receives the realized base
subspaces `(E_p)_p`. -/
def PhaseBlock {Ω : Type*} [MeasurableSpace Ω] {d M : ℕ} (ε : ℝ) (P : ℕ) (alg : DetMemAlg d M)
    (fin : (ℕ → Op d) → List (Vec d) → Vec d → Option (Vec d)) (μ : Measure Ω)
    (Eb : ℕ → Ω → Op d) (ch : ℕ → List ℕ → ℕ → Ω → Op d) (k : ℕ) (Δ q : ℝ) (v : List ℕ) :
    Prop :=
  IsBlock μ k Δ q (fun ω => regionV (delta d ε P) (fun p u i => ch p u i ω) v)
    (fun ω => (memCode (memV ε P alg (fun p u i => ch p u i ω) (fin (fun p => Eb p ω)) v),
      ctxV (fun p u i => ch p u i ω) v, EgtV (fun p => Eb p ω) P v.length))

end MemQueryFeas


