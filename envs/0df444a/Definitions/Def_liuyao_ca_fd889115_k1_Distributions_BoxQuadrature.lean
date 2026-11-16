-- Prove2me | Definitions.Def_liuyao_ca_fd889115_k1_Distributions_BoxQuadrature
-- name    : liuyao_ca_fd889115_k1_Distributions_BoxQuadrature
-- status  : Definition
-- author  : @liuyao
-- created : 2026-11-15T17:58:04.620489+00:00
-- url     : https://prove2.me/theorems/cb2274e8-e58c-40f2-853d-64ec9fbeda5f
-- title:
--   Computable analysis · BoxQuadrature · fd889115 k1
-- statement:
--   Private dependency for the Distribution Theory mission. Module ComputableDistributions/BoxQuadrature.lean from the frozen computable-analysis foundation with kernel-checked rational decision proofs.

import Definitions.Def_liuyao_ca_fd889115_k1_Distributions_Goals

set_option autoImplicit true

/-! A box quadrature for a single represented integrand. -/

open ComputableAnalysis
open ComputableDistributions (sumRaw sumRaw_valid)

namespace ComputableAnalysis.RationalBox

/-- Center tag of a cell in the uniform dyadic subdivision of a rational box.
At level `n`, each coordinate interval has `2^n` equal cells. -/
def dyadicCellCenter {dimension : Nat} (B : RationalBox dimension)
    (level : Nat) (cell : Fin dimension → Fin (2 ^ level)) :
    QPoint dimension := fun i =>
  let fraction : Rat :=
    ((2 * (cell i).val + 1 : Nat) : Rat) /
      ((2 * 2 ^ level : Nat) : Rat)
  B.lower i + (B.upper i - B.lower i) * fraction

abbrev CellIndex (dimension level : Nat) := Fin dimension → Fin (2 ^ level)

/-- The base digits enumerate the cells, one coordinate at a time. -/
def taggedSum {dimension : Nat} (B : RationalBox dimension)
    (f : QPoint dimension → RealCompute) (level : Nat)
    (tag : CellIndex dimension level → QPoint dimension) : RealCompute :=
  let cellsPerAxis := 2 ^ level
  let cellsPerAxisPositive : 0 < cellsPerAxis := Nat.pow_pos (by decide : 0 < 2)
  RealCompute.scaleRat (B.dyadicCellVolume level) <|
    sumRaw (cellsPerAxis ^ dimension) fun code =>
      let cell : Fin dimension → Fin cellsPerAxis := fun i =>
        ⟨(code.val / cellsPerAxis ^ i.val) % cellsPerAxis,
          Nat.mod_lt _ cellsPerAxisPositive⟩
      f (tag cell)

def midpointSum {dimension : Nat} (B : RationalBox dimension)
    (f : QPoint dimension → RealCompute) (level : Nat) : RealCompute :=
  B.taggedSum f level (B.dyadicCellCenter level)

def TagsInCells {dimension : Nat} (B : RationalBox dimension) (level : Nat)
    (tag : CellIndex dimension level → QPoint dimension) : Prop :=
  ∀ cell i,
    let step := (B.upper i - B.lower i) / ((2 ^ level : Nat) : Rat)
    let left := B.lower i + step * ((cell i).val : Rat)
    left ≤ tag cell i ∧ tag cell i ≤ left + step

theorem midpointSum_valid {dimension : Nat} (B : RationalBox dimension)
    (f : QPoint dimension → RealCompute) (hf : ∀ x, (f x).Valid) (level : Nat) :
    (B.midpointSum f level).Valid := by
  apply RealCompute.scaleRat_valid
  apply sumRaw_valid
  intro _
  exact hf _

end ComputableAnalysis.RationalBox

namespace ComputableDistributions

/-- Midpoints and all other rational tags in the same dyadic cells yield
the same value. The accuracy threshold is uniform in the tags. -/
def HasBoxIntegral {dimension : Nat} (B : RationalBox dimension)
    (f : QPoint dimension → RealCompute) (value : RealCompute) : Prop :=
  (∀ x, (f x).Valid) ∧ RawLimit.TendsTo (B.midpointSum f) value ∧
    ∀ m (eps : QPos), ∃ N, ∀ n, N ≤ n → ∀ tags,
      B.TagsInCells n tags →
      RawLimit.InInterval (B.taggedSum f n tags) (QInterval.expand (value.compute m) eps.val)

theorem HasBoxIntegral.unique {dimension : Nat} {B : RationalBox dimension}
    {f : QPoint dimension → RealCompute} {v w : RealCompute}
    (hv : HasBoxIntegral B f v) (hw : HasBoxIntegral B f w) : v.Equiv w :=
  RawLimit.unique hv.2.1 hw.2.1

private def leftBox {d : Nat} (B : RationalBox d) (i : Fin d) (cut : Rat)
    (h : B.lower i ≤ cut) : RationalBox d where
  lower := B.lower
  upper := replaceCoordinate B.upper i cut
  ordered j := by
    by_cases hj : j = i
    · simpa [replaceCoordinate, hj] using h
    · simpa [replaceCoordinate, hj] using B.ordered j

private def rightBox {d : Nat} (B : RationalBox d) (i : Fin d) (cut : Rat)
    (h : cut ≤ B.upper i) : RationalBox d where
  lower := replaceCoordinate B.lower i cut
  upper := B.upper
  ordered j := by
    by_cases hj : j = i
    · simpa [replaceCoordinate, hj] using h
    · simpa [replaceCoordinate, hj] using B.ordered j

/-- The elementary laws needed for ordinary kernel pairings. Splitting one
coordinate recovers rectangular step sums by finite iteration. A bounded
change on a coordinate plane has no effect on the integral. -/
def BoxIntegralLawsTarget : Prop :=
  (∀ d (B : RationalBox d) c, c.Valid → HasBoxIntegral B (fun _ => c)
    (RealCompute.scaleRat (B.dyadicCellVolume 0) c)) ∧
  (∀ d (B : RationalBox d) (f g : QPoint d → RealCompute) v w c, c.Valid →
    HasBoxIntegral B f v → HasBoxIntegral B g w →
    HasBoxIntegral B (fun x => RealCompute.add (f x) (RealCompute.mul c (g x)))
      (RealCompute.add v (RealCompute.mul c w))) ∧
  (∀ d (B : RationalBox d) (f : QPoint d → RealCompute) (i : Fin d) cut
    (hl : B.lower i ≤ cut) (hr : cut ≤ B.upper i) v w,
    HasBoxIntegral (leftBox B i cut hl) f v → HasBoxIntegral (rightBox B i cut hr) f w →
    HasBoxIntegral B f (RealCompute.add v w)) ∧
  (∀ d (B : RationalBox d) (f g : QPoint d → RealCompute) (i : Fin d) cut v bound,
    HasBoxIntegral B f v → (∀ x, (g x).Valid) →
    (∀ x, x i ≠ cut → (f x).Equiv (g x)) →
    (∀ x, x i = cut → RawLimit.InInterval (RealCompute.sub (f x) (g x)) ⟨-bound, bound⟩) →
    HasBoxIntegral B g v)

end ComputableDistributions


