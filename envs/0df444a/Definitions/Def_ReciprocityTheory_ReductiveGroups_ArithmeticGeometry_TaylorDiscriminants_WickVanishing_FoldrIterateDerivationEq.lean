-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_FoldrIterateDerivationEq
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_FoldrIterateDerivationEq
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T13:37:27.249202+00:00
-- url     : https://prove2.me/theorems/8f48f49f-7c35-4a7a-926f-b5c8a82258f6
-- title:
--   Foldr Iterate Derivation Eq
-- statement:
--   Definitions and structural lemmas for Foldr Iterate Derivation Eq, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/WickVanishing/FoldrIterateDerivationEq.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_SumSplitsEvalTwoWord
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
namespace ReciprocityTheory.ChartRestriction.G.TB.G2
variable {k : Type} [CommRing k] {d : ℕ}
section Mon
variable (F : Fin d → PS k 2 d) {ι : Type} (u : ι → Fin d → k)
end Mon
section abelian₂
variable {ι : Type} [Fintype ι] [DecidableEq ι] (ψ : List ι → k)
def lamW (P : MvPolynomial ι k) : k :=
  (AddMonoidAlgebra.coeff P).sum (fun n a => a * ψ (word (Finset.univ : Finset ι).toList n))
def rW (c : ι → ι → k) (n : ι →₀ ℕ) : k :=
  ((Finset.univ : Finset ι).toList.map (fun x => ((Finset.univ : Finset ι).toList.map (fun y =>
    c x y * ((n y * (n - Finsupp.single y 1 : ι →₀ ℕ) x : ℕ) : k) *
      ψ (word (Finset.univ : Finset ι).toList (n - Finsupp.single y 1 - Finsupp.single x 1)))).sum)).sum
end abelian₂
end ReciprocityTheory.ChartRestriction.G.TB.G2


