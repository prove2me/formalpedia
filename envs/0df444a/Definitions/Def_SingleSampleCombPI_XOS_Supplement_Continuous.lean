-- Prove2me | Definitions.Def_SingleSampleCombPI_XOS_Supplement_Continuous
-- name    : SingleSampleCombPI_XOS_Supplement_Continuous
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T17:36:42.651531+00:00
-- url     : https://prove2.me/theorems/6e96fc43-eb42-48b9-8864-1c75e1760073
-- title:
--   Capped-XOS clauses, frozen free-disposal histories and continuous configurations
-- statement:
--   A capped-additive clause has nonnegative coefficients $a_j$ and caps $c_j\in[0,1]$. Its value is
--   $$h_{a,c}(x)=\sum_j a_j\min\{x_j,c_j\}.$$
--   A valuation is capped-XOS if an arbitrary family of such clauses is dominated by the valuation and has a tight clause at each point of the cube; the family may be infinite. The zero function is represented by a zero clause.
--
--   A provisional record stores an amount in the cube and the supporting prices frozen at that amount. For a finite history $H$ of these records, the truncated free-disposal value at nonnegative capacity $c$ is
--   $$\mathrm{FD}_c(H)=\sum_j\int_0^\infty\min\{c_j,\sum_{e\in H}x_{e,j}\mathbf1[q_{e,j}\ge w]\}\,dw.$$
--   The surrogate for the next buyer is $\Phi(x)=v(x)+\mathrm{FD}_{1-x}(H)$. History and configuration free-disposal values invoke the published objective after reindexing each entry separately. Configurations permit several allocations from the same buyer.
--
--   These definitions support Proposition 2.1, Lemma 4.8 and Claim 4.9. They impose no concavity, finite-clause restriction, price-map continuity, optimizer existence, competitive guarantee, or cost certificate.
-- source:
--   Shuchi Chawla, Trung Dang, STOC 2027 submission #30 (October 2026), Definition 5, printed p. 8 / PDF p. 10; §4.2.1, printed pp. 21–23 / PDF pp. 23–25.

import Mathlib
import Definitions.Def_SingleSampleCombPI_XOS_Online
import Definitions.Def_SubsamplingSM_Offline_IsSubmodular

open scoped ENNReal

namespace SingleSampleCombPI.XOS.Supplement

/-! Chawla–Dang, STOC 2027 submission #30 (October 2026), Definition 5,
printed p. 8 / PDF p. 10; §4.2.1, printed pp. 21–23 / PDF pp. 23–25.
The supporting map is the published one-sided interface. No continuity of that
map, finite clause family, concavity, or oracle cost is included in capped-XOS. -/

abbrev Cube (m : ℕ) := AVec .divisible m

/-- One capped-additive clause: nonnegative slopes and caps in the cube. -/
structure CappedClause (m : ℕ) where
  slope : Vec m
  nonneg : ∀ j, 0 ≤ slope j
  cap : Cube m

/-- `h_{a,c}(x) = Σ_j a_j min(x_j,c_j)`. -/
noncomputable def CappedClause.value {m : ℕ} (h : CappedClause m) (x : Vec m) : ℝ :=
  ∑ j, h.slope j * min (x j) (h.cap.1 j)

/-- Definition 5. An arbitrary set of clauses, all dominated by `v`, with a
tight clause at every cube point. This is an attained supremum, including
infinite clause families. The zero valuation can use the zero clause. -/
def IsCappedXOS {m : ℕ} (v : Vec m → ℝ) : Prop :=
  ∃ L : Set (CappedClause m), ∀ x, InDom .divisible x →
    (∀ h ∈ L, h.value x ≤ v x) ∧ ∃ h ∈ L, h.value x = v x

/-- A provisional record stores the amount and the prices frozen at that
amount. Subsequent trimming never reevaluates a supporting-price map. -/
structure Frozen (m : ℕ) where
  amount : Cube m
  price : Vec m

/-- The list of previous provisional records; supply conflicts are allowed. -/
abbrev FrozenHistory (m : ℕ) := List (Frozen m)

/-- Nonnegative frozen prices. Amounts already belong to the cube. -/
def FrozenHistory.Valid {m : ℕ} (H : FrozenHistory m) : Prop :=
  ∀ e ∈ H, ∀ j, 0 ≤ e.price j

/-- Layer mass before imposing a capacity. -/
noncomputable def layerMass {m : ℕ} (H : FrozenHistory m) (j : Fin m) (w : ℝ) : ℝ :=
  (H.map fun e => e.amount.1 j * (if w ≤ e.price j then 1 else 0)).sum

/-- The truncated free-disposal value, §4.2.1. Finite step functions, compactly
supported on `[0,max price]`, are integrated over the positive half-line.
The empty history has value zero at every nonnegative capacity. -/
noncomputable def truncatedFD {m : ℕ} (H : FrozenHistory m) (c : Vec m) : ℝ :=
  ∑ j, ∫ w in Set.Ioi (0 : ℝ), min (c j) (layerMass H j w)

/-- A linear buyer representing one frozen record, solely for invoking the
published free-disposal objective. No new optimization benchmark is introduced. -/
def Frozen.linearBuyer {m : ℕ} (e : Frozen m) : Buyer m :=
  ⟨fun x => dot e.price x, fun _ => e.price, fun _ => ∅⟩

/-- Free disposal of a list: reindex every entry separately, even if two
records originally came from the same buyer. -/
noncomputable def historyFD {m : ℕ} (H : FrozenHistory m) : ℝ :=
  FD .divisible (fun k : Fin H.length => (H.get k).linearBuyer)
    (fun k : Fin H.length => (H.get k).amount.1)

/-- Freeze the source supporting prices at a selected allocation. -/
def freeze {m : ℕ} (b : Buyer m) (x : Cube m) : Frozen m := ⟨x, b.q x.1⟩

/-- `Φ_i(x) = v_i(x) + FD_{1-x}(previous allocations)`. -/
noncomputable def surrogate {m : ℕ} (H : FrozenHistory m) (b : Buyer m) (x : Vec m) : ℝ :=
  b.v x + truncatedFD H (fun j => 1 - x j)

/-- All maximizers on the entire cube, not on a finite grid. -/
def CubeMaximizer {m : ℕ} (f : Vec m → ℝ) (x : Vec m) : Prop :=
  InDom .divisible x ∧ ∀ y, InDom .divisible y → f y ≤ f x

/-- Configurations may repeat a buyer with different allocation vectors. -/
abbrev DivConfig (n m : ℕ) := Fin n × Cube m

/-- Reindex a finite set of configurations as separate provisional entries,
and evaluate the published free-disposal value on all of them. -/
noncomputable def divisibleConfigObj {n m : ℕ} (b : Fin n → Buyer m)
    (I : Finset (DivConfig n m)) : ℝ := by
  classical
  let L := I.toList
  exact FD .divisible (fun k : Fin L.length => b (L.get k).1)
    (fun k : Fin L.length => (L.get k).2.1)

end SingleSampleCombPI.XOS.Supplement


