-- Prove2me | Definitions.Def_FlexRigidity_Hist
-- name    : FlexRigidity_Hist
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:15:03.564472+00:00
-- url     : https://prove2.me/theorems/f26fc20a-d317-4a25-bbf7-8424f893de8b
-- title:
--   Protected classical records of a sequential process
-- statement:
--   After $k$ rounds of a sequential process the protected registers are $C_1O_1\cdots C_kO_k$. Their joint index set is built round by round, $\mathrm{Hist}_{k+1}=\mathrm{Hist}_k\times(C\times O_k)$, and from a history one reads off the record string $\mathbf c=(c_1,\dots,c_k)\in C^k$ and, when $O$ does not depend on the round, the list of round records $((c_i,o_i))_{i\le k}$.
--
--   **Formalization Note** Rounds are numbered from $0$ (the paper's round $i$ is Lean's $i-1$).
-- source:
--   Arqand, Kundu, Tan, Flexible rigidity: Compiling generic trusted-preparation protocols into sequential device-independent protocols, arXiv:2610.00444 (artifact sha256 8c67699d…), Postulate Set 4.1, p. 28

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P35

set_option autoImplicit false

open scoped Matrix ComplexOrder ENNReal
open Filter Topology
open QAlgorithms (Superop IsChannel krausApply idTensorSuperop piSuperop)
open QAlgorithms.Papers.Independent.Dependency50.P35 (tr Density Dominates divergence rawTrace spectralPower maxRelative POVM leftMarginal rightMarginal)

noncomputable section

namespace FlexRigidity

/-- **Protected classical records of a sequential process** (Arqand–Kundu–Tan, *Flexible
rigidity*, arXiv:2610.00444, artifact sha256 8c67699d…, Postulate Set 4.1, p. 28): after `k`
rounds the protected registers are `C_1 O_1 ⋯ C_k O_k`; `Hist C O k` is their joint index set,
built as `Hist C O (k+1) = Hist C O k × (C × O k)`. `Hist.cs` reads off the record string
`c = (c_1, …, c_k) ∈ C^k`.

**Formalization Note** The protected registers `C_i O_i` are indexed by the computational basis of
`C × O i` (the paper's states are classical on `C_i`; `O_i` is a finite register whose basis is
used only to index the tensor product). Rounds are numbered `0, 1, …` (the paper's `1, 2, …`). -/
def Hist (C : Type) (O : ℕ → Type) : ℕ → Type
  | 0 => Unit
  | k + 1 => Hist C O k × (C × O k)

instance Hist.instFintype (C : Type) (O : ℕ → Type) [Fintype C] [∀ k, Fintype (O k)] :
    ∀ k, Fintype (Hist C O k)
  | 0 => inferInstanceAs (Fintype Unit)
  | k + 1 => by
    letI := Hist.instFintype C O k
    exact inferInstanceAs (Fintype (Hist C O k × (C × O k)))

instance Hist.instDecEq (C : Type) (O : ℕ → Type) [DecidableEq C] [∀ k, DecidableEq (O k)] :
    ∀ k, DecidableEq (Hist C O k)
  | 0 => inferInstanceAs (DecidableEq Unit)
  | k + 1 => by
    letI := Hist.instDecEq C O k
    exact inferInstanceAs (DecidableEq (Hist C O k × (C × O k)))

/-- The record string `(c_1, …, c_k)` of a history. -/
def Hist.cs {C : Type} {O : ℕ → Type} : (k : ℕ) → Hist C O k → Fin k → C
  | 0, _ => Fin.elim0
  | k + 1, h => Fin.snoc (α := fun _ => C) (Hist.cs k (h : Hist C O k × (C × O k)).1)
      (h : Hist C O k × (C × O k)).2.1

/-- For a constant output register `O`, the list of round records `((c_i, o_i))_{i<k}`. -/
def Hist.ent {C O : Type} : (k : ℕ) → Hist C (fun _ => O) k → Fin k → C × O
  | 0, _ => Fin.elim0
  | k + 1, h => Fin.snoc (α := fun _ => C × O)
      (Hist.ent k (h : Hist C (fun _ => O) k × (C × O)).1) (h : Hist C (fun _ => O) k × (C × O)).2

end FlexRigidity


