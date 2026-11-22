-- Prove2me | Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_HtGram
-- name    : Formalism_HarderNarasimhan_HarderNarasimhanProofs_HtGram
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T17:25:19.910803+00:00
-- url     : https://prove2.me/theorems/18f87f57-cefb-4f97-ac2a-3ba8322ce27c
-- title:
--   Ht Gram
-- statement:
--   Definitions and structural lemmas for Ht Gram, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HarderNarasimhan/HarderNarasimhanProofs/HtGram.lean

import Definitions.Def_Formalism_HarderNarasimhan_StatementPl
import Definitions.Def_Formalism_LatticeSlopes_ExistsSaturatedSlopeEqMuMax
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DegSupermodZ
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField Matrix
noncomputable section
namespace Formalism.HN
namespace HeightGram
section Basic
variable {K : Type} [Field K] [NumberField K] [StarRing K]
  {V ι : Type} [AddCommGroup V] [Module K V] [Fintype ι] [DecidableEq ι]
end Basic
section LinAlg
variable {n : Type} [Fintype n] [DecidableEq n]
def realif (G : Matrix n n ℂ) : Matrix (Fin 2 × n) (Fin 2 × n) ℝ :=
  Matrix.of fun p q => if p.1 = 0 then (if q.1 = 0 then (G p.2 q.2).re else -(G p.2 q.2).im)
    else (if q.1 = 0 then (G p.2 q.2).im else (G p.2 q.2).re)
end LinAlg
section Fact
variable {P S : Type} [Fintype P] [DecidableEq P] [Fintype S] [DecidableEq S] {j : ℕ}
def gmat (lam : P → S → ℂ) (G : P → Matrix (Fin j) (Fin j) ℂ) :
    Matrix (S × Fin j) (S × Fin j) ℝ :=
  Matrix.of fun p q => ∑ v, (star (lam v p.1) * lam v q.1 * G v p.2 q.2).re
def amat (lam : P → S → ℂ) (eS : S ≃ P × Fin 2) : Matrix (P × Fin 2) (P × Fin 2) ℝ :=
  Matrix.of fun x q => if x.2 = 0 then (lam x.1 (eS.symm q)).re else (lam x.1 (eS.symm q)).im
def bmat (G : P → Matrix (Fin j) (Fin j) ℂ) :
    Matrix ((P × Fin 2) × Fin j) ((P × Fin 2) × Fin j) ℝ :=
  Matrix.of fun x y => if x.1.1 = y.1.1 then realif (G x.1.1) (x.1.2, x.2) (y.1.2, y.2) else 0
end Fact
section DetG
variable {P S : Type} [Fintype P] [DecidableEq P] [Fintype S] [DecidableEq S] {j : ℕ}
end DetG
section NT
variable (K : Type) [Field K] [NumberField K] [IsTotallyComplex K]
theorem isEmpty_real : IsEmpty {w : InfinitePlace K // w.IsReal} := ⟨fun w => (InfinitePlace.not_isReal_iff_isComplex.mpr (IsTotallyComplex.isComplex w.1)) w.2⟩
attribute [local instance] isEmpty_real
def idxE : mixedEmbedding.index K ≃ InfinitePlace K × Fin 2 :=
  (Equiv.emptySum _ _).trans
    (Equiv.prodCongr (Equiv.subtypeUnivEquiv fun w => IsTotallyComplex.isComplex w) (Equiv.refl _))
def lamK (v : InfinitePlace K) (m : Free.ChooseBasisIndex ℤ (𝓞 K)) : ℂ :=
  v.embedding (integralBasis K m)
end NT
section Main
variable {K : Type} [Field K] [NumberField K]
  {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
end Main
end HeightGram
end Formalism.HN


