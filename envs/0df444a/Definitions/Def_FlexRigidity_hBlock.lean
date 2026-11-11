-- Prove2me | Definitions.Def_FlexRigidity_hBlock
-- name    : FlexRigidity_hBlock
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:18:44.948339+00:00
-- url     : https://prove2.me/theorems/2a321510-20b9-4265-906b-a36225a286e8
-- title:
--   The block function $h_{i,c}$, eq. (21)
-- statement:
--   For a normalized pure input $|\sigma^i\rangle_{M_iR_i}$,
--   $$h_{i,c}(|\sigma^i\rangle)=Q_\alpha\big(\sigma^{i,\mathcal G_i}_{\wedge(C_i=c)}\big\|\sigma^{i,\mathcal P_i\circ\mathcal G_i}_{\wedge(C_i=c)}\big).$$
--   `hBlock` takes the pure input on any finite reference; `hMarg` evaluates $h_{i,c}$ on the canonical purification of a state $\sigma_{M_i}$, which is $h_{i,c}(\sigma^i_{M_i})$ of Lemma 4.3(i).
-- source:
--   Arqand, Kundu, Tan, Flexible rigidity: Compiling generic trusted-preparation protocols into sequential device-independent protocols, arXiv:2610.00444 (artifact sha256 8c67699d…), Lemma 4.3, eq. (21), p. 30

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P35
import Definitions.Def_FlexRigidity_SeqData
import Definitions.Def_FlexRigidity_blockC
import Definitions.Def_ObliviousRSP_pureState
import Definitions.Def_FlexRigidity_sandQ
import Definitions.Def_FlexRigidity_canonPurif
set_option autoImplicit false

open scoped Matrix ComplexOrder ENNReal
open Filter Topology
open QAlgorithms (Superop IsChannel krausApply idTensorSuperop piSuperop)
open QAlgorithms.Papers.Independent.Dependency50.P35 (tr Density Dominates divergence rawTrace spectralPower maxRelative POVM leftMarginal rightMarginal)

noncomputable section

namespace FlexRigidity

/-- **The block function `h_{i,c}`, eq. (21)** (Arqand–Kundu–Tan, *Flexible rigidity*,
arXiv:2610.00444, artifact sha256 8c67699d…, Lemma 4.3, p. 30): for a normalized pure input
`|σ^i⟩_{M_i R_i}`, `h_{i,c}(|σ^i⟩) = Q_α(σ^{i,G_i}_{∧(C_i=c)} ‖ σ^{i,P_i∘G_i}_{∧(C_i=c)})`.
`hBlock` takes the pure input on an arbitrary reference `Rf` (placed first); `hMarg` evaluates it
on the canonical purification of a state `σ_{M_i}`, the function `h_{i,c}(σ^i_{M_i})` of
Lemma 4.3(i). -/
def hBlock {C : Type} {O M Z S J : ℕ → Type} [DecidableEq C]
    [∀ k, Fintype (M k)] [∀ k, DecidableEq (M k)] [∀ k, Fintype (Z k)] [∀ k, DecidableEq (Z k)]
    [∀ k, Fintype (S k)] [∀ k, DecidableEq (S k)] [∀ k, Fintype (J k)] [∀ k, DecidableEq (J k)]
    (D : SeqData C O M Z S J) (i : ℕ) (c : C) (a : ℝ) {Rf : Type} [Fintype Rf] [DecidableEq Rf]
    (σ : Rf × M i → ℂ) : ℝ≥0∞ :=
  sandQ a (blockC (D.cOf i) c (idTensorSuperop (R := Rf) (D.G i) (ObliviousRSP.pureState σ)))
    (blockC (D.cOf i) c (idTensorSuperop (R := Rf) (fun X => D.P i (D.G i X)) (ObliviousRSP.pureState σ)))

/-- `h_{i,c}` as a function of the input marginal `σ_{M_i}` (Lemma 4.3(i)), evaluated on the
canonical purification with reference `R_i ≅ M_i`. -/
def hMarg {C : Type} {O M Z S J : ℕ → Type} [DecidableEq C]
    [∀ k, Fintype (M k)] [∀ k, DecidableEq (M k)] [∀ k, Fintype (Z k)] [∀ k, DecidableEq (Z k)]
    [∀ k, Fintype (S k)] [∀ k, DecidableEq (S k)] [∀ k, Fintype (J k)] [∀ k, DecidableEq (J k)]
    (D : SeqData C O M Z S J) (i : ℕ) (c : C) (a : ℝ) (ρ : Matrix (M i) (M i) ℂ) : ℝ≥0∞ :=
  hBlock D i c a (Rf := M i) (canonPurif ρ)

end FlexRigidity


