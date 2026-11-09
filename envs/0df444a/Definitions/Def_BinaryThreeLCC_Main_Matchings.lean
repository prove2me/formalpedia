-- Prove2me | Definitions.Def_BinaryThreeLCC_Main_Matchings
-- name    : BinaryThreeLCC_Main_Matchings
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T13:01:47.961206+00:00
-- url     : https://prove2.me/theorems/816b98bf-a6cd-43da-b83f-1742689e7b78
-- title:
--   Three-uniform recovery matchings and span dimension
-- statement:
--   For a finite vertex set $[N]$ and a target $u$, a recovery matching is a finite family of three-element subsets excluding $u$, pairwise disjoint across distinct hyperedges. It imposes no vector equation by itself. For vector labels $v$ in a vector space over $\mathbb F_2$, define
--
--   $$\operatorname{spanDimension}(v)=\dim_{\mathbb F_2}\operatorname{span}\{v_u\}.$$
--
--   This separates the matching combinatorics from the linear parity equations supplied by theorems. The finite-indexed spans used in the mission are finite dimensional even when the ambient space is not.
-- source:
--   Oliver Janzer, Peter Manohar, STOC 2027 submission #732 (October 2026), Fact 2.1, printed pp.2–3, PDF pp.4–5; finite span in Lemma 4.1, printed p.10, PDF p.12; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/732.pdf

import Definitions.Def_BinaryThreeLCC_Main_CodeModel

set_option autoImplicit false

namespace BinaryThreeLCC.Main

/-- The triples exclude u and distinct triples are disjoint. -/
def IsRecoveryMatching {N : ℕ} (u : Fin N) (H : Finset (Finset (Fin N))) : Prop :=
  (∀ e ∈ H, e.card = 3 ∧ u ∉ e) ∧
    ∀ e ∈ H, ∀ f ∈ H, e ≠ f → Disjoint e f

noncomputable def spanDimension {ι W : Type*} [AddCommGroup W] [Module Bit W]
    (v : ι → W) : ℕ := Module.finrank Bit (Submodule.span Bit (Set.range v))

end BinaryThreeLCC.Main


