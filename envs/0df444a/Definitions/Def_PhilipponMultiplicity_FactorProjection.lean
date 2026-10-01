-- Prove2me | Definitions.Def_PhilipponMultiplicity_FactorProjection
-- name    : PhilipponMultiplicity_FactorProjection
-- status  : Definition
-- author  : @tomasz
-- created : 2026-10-01T09:54:20.687856+00:00
-- url     : https://prove2.me/theorems/631b763e-b930-4a98-a1eb-5b8193cd03b1
-- title:
--   Nonempty selections of group factors and their coordinate projections
-- statement:
--   For an embedded product $G=\prod_iG_i$, a factor selection is a nonempty finite subset $I$ of the original factor indices. The selected product $G_I$ keeps the original factors and embeddings. This bundle defines a finite enumeration of $I$, the coordinate projection $\pi:G\to G_I$, the inclusion of homogeneous coordinate variables, and extension of exponent tuples by zero outside $I$.
--
--   These are concrete constructions from the original product. The bundle contains no assumptions about analytic contact, dimensions, ranks, or multiplicity estimates. Their geometric compatibility remains a separate theorem.
-- source:
--   Supporting definitions for the coordinate-projection reduction of Philippon (1986), Corollary 2.3, pp.360–361. https://numdam.org/articles/10.24033/bsmf.2060/

import Definitions.Def_PhilipponMultiplicity_Corollaries

set_option autoImplicit false
open scoped BigOperators Topology
noncomputable section

namespace PhilipponMultiplicity
universe u
variable {K : Type u} [Field K]

/-- A nonempty collection of the original factors, with no change of embedding. -/
abbrev GroupFactorSelection (G : EmbeddedGroupProduct K) :=
  {s : Finset G.FactorIndex // s.Nonempty}

namespace GroupFactorSelection
variable {G : EmbeddedGroupProduct K} (s : GroupFactorSelection G)

def indexEquiv : Fin (Fintype.card s.val) ≃ s.val := (Fintype.equivFin s.val).symm

def index (i : Fin (Fintype.card s.val)) : G.FactorIndex := (s.indexEquiv i).val

def group : EmbeddedGroupProduct K where
  factorCount := Fintype.card s.val
  positive := Fintype.card_pos_iff.mpr (by
    obtain ⟨i,hi⟩ := s.property
    exact ⟨⟨i,hi⟩⟩)
  factor := fun i => G.factor (s.index i)

def project : G.Point →+ s.group.Point where
  toFun x i := x (s.index i)
  map_zero' := rfl
  map_add' _ _ := rfl

def coordinateIndex (v : s.group.ambient.Variable) : G.ambient.Variable := ⟨s.index v.1,v.2⟩

def extendExponent (r : s.group.FactorIndex → ℕ) (i : G.FactorIndex) : ℕ :=
  if hi : i ∈ s.val then r (s.indexEquiv.symm ⟨i,hi⟩) else 0

end GroupFactorSelection
end PhilipponMultiplicity


