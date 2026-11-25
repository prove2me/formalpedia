-- Prove2me | Definitions.Def_DetDLP_S8L_FpPairTiles
-- name    : DetDLP_S8L_FpPairTiles
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T06:37:19.507265+00:00
-- url     : https://prove2.me/theorems/11583019-f20c-4a70-9e3e-17c68e2dc3d0
-- title:
--   Tiling the finite-field pair query
-- statement:
--   For two tuples of length $m$, combine $2m$ hash tiles with $2m-1$ modular product tiles. Before and after identifying shared bit vertices, all tests accept exactly when every tile accepts its local assignment. The number of subdivided arithmetic edges is at most $40000m(b+3)$ at internal width $b+1$.

import Definitions.Def_DetDLP_S8J_HashGateLayout
import Definitions.Def_DetDLP_S8G_FpMomentLayout

set_option autoImplicit false
namespace DetDLP.S8L.FpPair
open S8J S8G.FpMoment

/-- Two independent raw multiplications and the quotient-remainder column equation. -/
def stage (d : ℕ) (hd : 1 ≤ d) :=
  join (join (w3_fpMulLayout d hd) (w3_fpMulLayout d hd)) (S8C.AddLayout.layout (2*d))

theorem stage_edges {d : ℕ} (hd : 1 ≤ d) : (stage d hd).ne < 5000*(d+2) := by
  have h := (w3_fpMulIncidenceBounds hd).1
  change _ + _ + (2*d*5) < _
  omega

/-- Concatenate the atom tiles and the shortened product chain before bus identification. -/
def bank (m : ℕ) (atom product : w3_FactorLayout) := join (tiles (2*m) atom) (tiles (2*m-1) product)

def bankTest {m : ℕ} {atom product : w3_FactorLayout}
    (a : Fin (2*m) → w3_factorTest atom) (s : Fin (2*m-1) → w3_factorTest product) :
    w3_factorTest (bank m atom product) := joinTest (tileTests a) (tileTests s)

theorem bank_iff {m : ℕ} {atom product : w3_FactorLayout}
    (a : Fin (2*m) → w3_factorTest atom) (s : Fin (2*m-1) → w3_factorTest product)
    (x : Fin (bank m atom product).nb → Bool) :
    Accept _ (bankTest a s) x ↔
    (∀ i, Accept atom (a i) (atTile (x ∘ Fin.castAdd ((2*m-1)*product.nb)) i)) ∧
    (∀ j, Accept product (s j) (atTile (x ∘ Fin.natAdd (2*m*atom.nb)) j)) :=
  (join_iff _ _ x).trans (and_congr (tileTests_iff a _) (tileTests_iff s _))

theorem identified_iff {m : ℕ} {atom product : w3_FactorLayout}
    (a : Fin (2*m) → w3_factorTest atom) (s : Fin (2*m-1) → w3_factorTest product)
    {k : ℕ} (f : Fin (bank m atom product).nb → Fin k) (rep : Fin k → Fin (bank m atom product).nb)
    (hr : Function.RightInverse rep f) (y : Fin k → Bool) :
    Accept (Gluing.identify _ f rep hr) (bankTest a s) y ↔
    (∀ i, Accept atom (a i) (atTile ((y ∘ f) ∘ Fin.castAdd ((2*m-1)*product.nb)) i)) ∧
    (∀ j, Accept product (s j) (atTile ((y ∘ f) ∘ Fin.natAdd (2*m*atom.nb)) j)) :=
  bank_iff a s (y ∘ f)

theorem arithmetic_edges (m b : ℕ) :
    2*(bank m (HashGateLayout.layout (b+1) (Nat.succ_pos _)) (stage (b+1) (Nat.succ_pos _))).ne ≤
    40000*m*(b+3) := by
  let A := HashGateLayout.layout (b+1) (Nat.succ_pos _)
  let B := stage (b+1) (Nat.succ_pos _)
  change 2*(2*m*A.ne + (2*m-1)*B.ne) ≤ _
  have ha : A.ne ≤ 5000*(b+3) := (HashGateLayout.edges (Nat.succ_pos b)).le
  have hs : B.ne ≤ 5000*(b+3) := (stage_edges (Nat.succ_pos b)).le
  calc _ ≤ 2*(2*m*(5000*(b+3)) + (2*m)*(5000*(b+3))) := by gcongr <;> omega
       _ = _ := by ring

end DetDLP.S8L.FpPair


