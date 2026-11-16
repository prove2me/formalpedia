-- Prove2me | Definitions.Def_DoublyEffIP_Supplement_bitAugLang
-- name    : DoublyEffIP_Supplement_bitAugLang
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:42:20.594856+00:00
-- url     : https://prove2.me/theorems/90bc252b-d631-472e-a441-4d481ba478b8
-- title:
--   The augmented language $L^k_t[\Phi]$ on bit strings
-- statement:
--   For a splitting parameter $\lambda$ and a predicate $\Phi$ on $k\times(\lambda+1)$ matrices of configurations given by a description $\langle\Phi\rangle$ (via the generator $T_\Phi$), the **augmented language** is
--
--   $$
--   L^k_t[\Phi]=\big\{x=\mathrm{bits}(y) : y\in L^k_t\ \wedge\ (t\ge\lambda\Rightarrow\Phi(M_y)=1)\big\},
--   $$
--
--   where $M_y$ is the midpoint matrix of $y$ (its $(i,j)$ entry is the configuration reached from $y_{i,\mathrm{start}}$ after $(t/\lambda)\cdot j$ steps) and $\Phi(M_y)$ is evaluated by the implementation circuit of $\langle\Phi\rangle$ on the bits of $M_y$, row by row. It is built on the published `DoublyEffIP.augLang`.
--
--   **Formalization Note** $\Phi:\{0,1\}^{k\times(S(\lambda+1))}\to\{0,1\}$ is defined before the protocol chooses its binary field, so its circuit is evaluated over $\mathrm{GF}(2)$: on bit inputs, an ADD/MULT circuit with constants $0,1$ takes the same values over every binary field. Its generator gate is read as $0$.
-- source:
--   Chen–Hong–Kalai–Xi, Towards a Doubly Efficient IP = PSPACE, arXiv:2606.21799 (version of 2026-11-02, sha256 14d170db…), Section 5.1, p.19, Definition 10; Theorem 7

import Mathlib
import Definitions.Def_DoublyEffIP_Supplement_WinCfg
import Definitions.Def_DoublyEffIP_Supplement_winStep
import Definitions.Def_DoublyEffIP_Supplement_winEnc
import Definitions.Def_DoublyEffIP_Supplement_batchBits
import Definitions.Def_DoublyEffIP_Supplement_flatMat
import Definitions.Def_DoublyEffIP_Supplement_bitsIn
import Definitions.Def_DoublyEffIP_Supplement_PredHolds
import Definitions.Def_DoublyEffIP_augLang
import Definitions.Def_TreeEdgeRankPC_Transducer
import Definitions.Def_SubexponentialSAT

set_option autoImplicit false

open OAI.Algorithms.SubexponentialSAT.Computation
open TreeEdgeRankPC

namespace DoublyEffIP.Supplement

/-- **The augmented language `L^k_t[Φ]` on bit strings** — Definition 10 of Chen–Hong–Kalai–Xi, *Towards a Doubly Efficient IP = PSPACE*, arXiv:2606.21799
(version of 2026-11-02, sha256 14d170db…), p.19:
`L^k_t[Φ] := {x ∈ {0,1}^{k×2S} | x ∈ L^k_t ∧ (t ≥ λ ⟹ Φ(M_x) = 1)}`, where `M_x ∈
{0,1}^{k×(S(λ+1))}` is the midpoint matrix and `Φ` a predicate given by a description `⟨Φ⟩`
with implementation circuit `C` (Theorem 7, p.19).

The bit strings `batchBits y` of the batches `y` in the published `DoublyEffIP.augLang` for the step
`winStep M S`, where `Φ` holds on a `k × (λ + 1)` matrix of configurations when the circuit that
`TΦ` outputs, applied to the matrix's bits (row by row, each entry `winEnc`) and `⟨Φ⟩`, gives `1`.

**Formalization Note.** `Φ : {0,1}^{k×(S(λ+1))} → {0,1}` is defined before the protocol picks
its binary field, so its circuit is evaluated over `GF(2)`: on bit inputs an ADD/MULT circuit with
constants `0`, `1` takes the same values over every binary field. Its `gen` gate is read as `0`. -/
def bitAugLang (M : PrimitiveMachine) (S t lam : ℕ) (TΦ : Transducer) (descΦ : List Bool)
    (k : ℕ) : Set (List Bool) :=
  {x | ∃ y : Fin k → WinCfg M S × WinCfg M S,
    y ∈ DoublyEffIP.augLang (winStep M S) t lam
      (fun Mm => PredHolds (0 : ZMod 2) TΦ
        (bitsIn (ZMod 2) (flatMat fun i j => winEnc (Mm i j)).flatten) descΦ) ∧
    x = batchBits y}

end DoublyEffIP.Supplement


