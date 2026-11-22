-- Prove2me | Definitions.Def_LeanPool_Copula_Rectangle
-- name    : LeanPool_Copula_Rectangle
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T18:42:20.925383+00:00
-- url     : https://prove2.me/theorems/32e532cb-901f-45f0-8b1c-ec429638b14e
-- title:
--   Rectangle
-- statement:
--   Definitions and structural lemmas for Rectangle, from Marcus Rockel; Gaëtan Serré; Rémy Degenne; LeanPool contributors's pinned Finite-dimensional copulas and Sklar’s theorem development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Copula/Rectangle.lean

module
public import Definitions.Def_LeanPool_Copula_CDF
set_option autoImplicit true
@[expose] public section
public section
@[expose] section
open MeasureTheory Set
open scoped unitInterval BigOperators
namespace ProbabilityTheory.Copula
variable {d : ℕ}
@[expose]
def corner (a b : Fin d → I) (s : Finset (Fin d)) (i : Fin d) : I :=
  if i ∈ s then a i else b i
@[expose]
def partialIncrement (F : (Fin d → I) → ℝ) (a b : Fin d → I)
    (s : Finset (Fin d)) : ℝ :=
  ∑ t ∈ s.powerset, (-1 : ℝ) ^ t.card * F (corner a b t)
@[expose]
def rectangleIncrement (F : (Fin d → I) → ℝ) (a b : Fin d → I) : ℝ :=
  partialIncrement F a b Finset.univ
end ProbabilityTheory.Copula


