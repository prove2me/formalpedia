-- Prove2me | Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_AssemblyT
-- name    : Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_AssemblyT
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T12:09:09.275684+00:00
-- url     : https://prove2.me/theorems/49635548-98bc-54b0-b921-c6dcb6c8ad43
-- title:
--   Assembly T
-- statement:
--   Definitions and structural lemmas for Assembly T, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/RepresentationTheoryGL/SiegelWeilProof/HolomorphicContinuation/GaussianPlaneIntegrals/AssemblyT.lean

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_GaussianPlaneIntegrals_AssemblyTB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory MvPolynomial
open scoped ComplexOrder
namespace PositivityTheory.Rg.Sw.FFTSteps.AsmT
open AsmA
variable {ι A B : Type} [Fintype ι] [DecidableEq ι] [Fintype A] [Fintype B]
variable (ι A B) in

abbrev NN : ℕ := Fintype.card ι + (Fintype.card A + Fintype.card B)
def emb (i : ι) : Fin (NN ι A B) := Fin.castAdd _ (Fintype.equivFin ι i)
variable (A B) in

def invE (j : Fin (NN ι A B)) : Option ι :=
  if h : (j : ℕ) < Fintype.card ι then some ((Fintype.equivFin ι).symm ⟨j, h⟩) else none
variable (ι) in

def resφ : (Fin (NN ι A B) × A) ⊕ (Fin (NN ι A B) × B) → PV ι A B :=
  Sum.elim (fun x => (invE A B x.1).elim 0 fun i => X (Sum.inl (i, x.2)))
    (fun y => (invE A B y.1).elim 0 fun i => X (Sum.inr (i, y.2)))
def res : PV (Fin (NN ι A B)) A B →ₐ[ℂ] PV ι A B := aeval (resφ ι)
def ren : (ι × A) ⊕ (ι × B) → (Fin (NN ι A B) × A) ⊕ (Fin (NN ι A B) × B) :=
  Sum.map (Prod.map emb id) (Prod.map emb id)
def blk (u : Matrix (Fin (NN ι A B)) (Fin (NN ι A B)) ℂ) : Matrix ι ι ℂ := fun i i' => u (emb i) (emb i')
def Tf (hA : Avg) (q : PV ι A B) : PV ι A B := res (Classical.choose (hA (NN ι A B) A B (rename ren q)))
end PositivityTheory.Rg.Sw.FFTSteps.AsmT


