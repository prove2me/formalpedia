-- Prove2me | Definitions.Def_FlexRigidity_Rterm
-- name    : FlexRigidity_Rterm
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:18:24.539785+00:00
-- url     : https://prove2.me/theorems/e0cb380a-8d70-419b-8379-101688513801
-- title:
--   Stabilized round divergence $R_{\alpha,\mathcal G_i,\mathcal P_i\circ\mathcal G_i}(f)$, eq. (18)
-- statement:
--   $$R_{\alpha,\mathcal G_i,\mathcal P_i\circ\mathcal G_i}(f)=D_\alpha\big(\mathcal G_i\otimes\mathrm{id}_{R_i}\big\|(\mathcal P^f_i\circ\mathcal G_i)\otimes\mathrm{id}_{R_i}\big),$$
--   the channel divergence of Definition 2.10, where $\mathcal P^f_i$ multiplies the $C_i=c$ block of $\mathcal P_i$ by $2^{f(c)}$.
--
--   **Formalization Note** $R_i\cong M_i$ (the paper allows any $|R_i|\ge|M_i|$; by Lemma 4.3(i) the value is the same).
-- source:
--   Arqand, Kundu, Tan, Flexible rigidity: Compiling generic trusted-preparation protocols into sequential device-independent protocols, arXiv:2610.00444 (artifact sha256 8c67699d…), eq. (18), p. 29

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P35
import Definitions.Def_FlexRigidity_SeqData
import Definitions.Def_FlexRigidity_chanDiv
import Definitions.Def_FlexRigidity_weightBlocks
set_option autoImplicit false

open scoped Matrix ComplexOrder ENNReal
open Filter Topology
open QAlgorithms (Superop IsChannel krausApply idTensorSuperop piSuperop)
open QAlgorithms.Papers.Independent.Dependency50.P35 (tr Density Dominates divergence rawTrace spectralPower maxRelative POVM leftMarginal rightMarginal)

noncomputable section

namespace FlexRigidity

/-- **The stabilized single-round divergence `R_{α,G_i,P_i∘G_i}(f)`, eq. (18)**
(Arqand–Kundu–Tan, *Flexible rigidity*, arXiv:2610.00444, artifact sha256 8c67699d…, p. 29):
`R_{α,G_i,P_i∘G_i}(f) = D_α(G_i ⊗ id_{R_i} ‖ (P^f_i ∘ G_i) ⊗ id_{R_i})`, the channel divergence of
Definition 2.10, where `P^f_i` multiplies the `C_i = c` block of `P_i` by `2^{f(c)}`.

**Formalization Note** The reference is `R_i ≅ M_i` (`|R_i| ≥ |M_i|` in the paper; by Lemma
4.3(i) the value does not depend on that choice). -/
def Rterm {C : Type} {O M Z S J : ℕ → Type} [Fintype C] [DecidableEq C]
    [∀ k, Fintype (M k)] [∀ k, DecidableEq (M k)] [∀ k, Fintype (Z k)] [∀ k, DecidableEq (Z k)]
    [∀ k, Fintype (S k)] [∀ k, DecidableEq (S k)] [∀ k, Fintype (J k)] [∀ k, DecidableEq (J k)]
    (D : SeqData C O M Z S J) (i : ℕ) (a : ℝ) (f : C → ℝ) : EReal :=
  chanDiv a (idTensorSuperop (R := M i) (D.G i))
    (idTensorSuperop (R := M i) (fun X => weightBlocks (D.cOf i) f (D.P i (D.G i X))))

end FlexRigidity


