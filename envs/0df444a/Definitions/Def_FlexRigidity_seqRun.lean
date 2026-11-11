-- Prove2me | Definitions.Def_FlexRigidity_seqRun
-- name    : FlexRigidity_seqRun
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:16:28.513575+00:00
-- url     : https://prove2.me/theorems/e33ace90-e698-4f8d-861a-7cf0ce29751c
-- title:
--   The sequential process $\mathcal E_n\circ\cdots\circ\mathcal E_1[\rho^0]$
-- statement:
--   Given round channels $\mathcal E_i\in\mathrm{CPTP}(M_i,C_iO_iM_{i+1})$ and an initial state $\rho^0_{M_1R}$, the state after $k$ rounds is
--   $$(\mathcal E_k\circ\cdots\circ\mathcal E_1)[\rho^0],$$
--   where each $\mathcal E_i$ acts on the current memory, with the identity on the earlier protected outputs $C_{<i}O_{<i}$ and on the external side information $R$. It defines $\rho^{\mathrm{real}}=\mathcal E[\rho^0]$ and $\rho^{\mathrm{ideal}}=\mathcal F[\rho^0]$ of Theorem 4.4 and the states of the DI protocol.
-- source:
--   Arqand, Kundu, Tan, Flexible rigidity: Compiling generic trusted-preparation protocols into sequential device-independent protocols, arXiv:2610.00444 (artifact sha256 8c67699d…), Postulate Set 4.1, p. 28; §4.2, p. 33

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P35
import Definitions.Def_FlexRigidity_Hist
set_option autoImplicit false

open scoped Matrix ComplexOrder ENNReal
open Filter Topology
open QAlgorithms (Superop IsChannel krausApply idTensorSuperop piSuperop)
open QAlgorithms.Papers.Independent.Dependency50.P35 (tr Density Dominates divergence rawTrace spectralPower maxRelative POVM leftMarginal rightMarginal)

noncomputable section

namespace FlexRigidity

/-- **The sequential process** `E = E_n ∘ ⋯ ∘ E_1` applied to `ρ⁰_{M_1 R}` (Arqand–Kundu–Tan,
*Flexible rigidity*, arXiv:2610.00444, artifact sha256 8c67699d…, Postulate Set 4.1, p. 28, and
§4.2, p. 33): round `k` applies `E_k ∈ CPTP(M_k, C_k O_k M_{k+1})` to the memory, with the
identity on the earlier protected outputs `C_{<k} O_{<k}` and on the external side information
`R`. `seqRun E ρ⁰ k` is the state after `k` rounds, on `C_{≤k} O_{≤k} ⊗ R ⊗ M_{k+1}`.

**Formalization Note** The state is a matrix indexed by `Hist C O k × (R × M k)`; the reference
`R` is placed before the memory, and `idTensorSuperop` applies `E_k` to the memory block. -/
def seqRun {C : Type} {O M : ℕ → Type} {R : Type}
    (E : (k : ℕ) → Superop (M k) ((C × O k) × M (k + 1)))
    (ρ0 : Matrix (R × M 0) (R × M 0) ℂ) :
    (k : ℕ) → Matrix (Hist C O k × (R × M k)) (Hist C O k × (R × M k)) ℂ
  | 0 => Matrix.of fun i j => ρ0 i.2 j.2
  | k + 1 =>
    let ρ := seqRun E ρ0 k
    let ρ' : Matrix ((Hist C O k × R) × M k) ((Hist C O k × R) × M k) ℂ :=
      Matrix.of fun i j => ρ (i.1.1, i.1.2, i.2) (j.1.1, j.1.2, j.2)
    let σ := idTensorSuperop (R := Hist C O k × R) (E k) ρ'
    Matrix.of fun (i j : Hist C O (k + 1) × (R × M (k + 1))) =>
      σ (((i.1 : Hist C O k × (C × O k)).1, i.2.1), ((i.1 : Hist C O k × (C × O k)).2, i.2.2))
        (((j.1 : Hist C O k × (C × O k)).1, j.2.1), ((j.1 : Hist C O k × (C × O k)).2, j.2.2))

end FlexRigidity


