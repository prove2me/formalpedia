-- Prove2me | Definitions.Def_DetDLP_S8N_MomentPhysicalRows
-- name    : DetDLP_S8N_MomentPhysicalRows
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-25T12:00:17.220595+00:00
-- url     : https://prove2.me/theorems/eedc3494-b76d-50a6-b8f9-615cf8503297
-- title:
--   Physical incidence counts in the elliptic-curve moment circuit
-- statement:
--   Counts each physical incidence in seeds, atom slots, map rows, point additions, fold blocks and their targets.
-- source:
--   S. Liu, B. Zhang, and K. Ren, "A Deterministic Subexponential-time Algorithm for the Discrete Logarithm Problem", Zhejiang University Preprint, 23 November 2026, Section 2.4, Section 3 & Section 4, Lemma 2.4, Theorem 3.1 & Theorem 1.1 (pp. 9–19)

import Definitions.Def_DetDLP_S8N_Routes_v3

set_option autoImplicit false

namespace DetDLP.S8N.MomentIncidences

open S8H0 RegisterMap NamedBlocks GateRoutes RangeRows HashRows
open S8G.SeedAndAtomBank S8M
open private fixed from Definitions.Def_DetDLP_S8M_ECAtomSlot
open private ranges maskEq from Definitions.Def_DetDLP_S8M_ECMapRows
open private invRows selectRows from Definitions.Def_DetDLP_S8N_ECAddRoutes
open private foldStep from Definitions.Def_DetDLP_S8M_ECFoldRoutes

private abbrev hashIncidences (d e : ℕ) := 4*e + 36*d + 10
private abbrev atomIncidences (d e : ℕ) := 85*(d+1) + 7*hashIncidences d e + 12*d + 1
private abbrev mapIncidences (d e : ℕ) := 50*(d+1) + 4*hashIncidences d e + 2 + 6*d
private abbrev stepIncidences (d e : ℕ) := 170*(d+1) + 15*hashIncidences d e + 31*d + 5
private abbrev foldIncidences (n d e : ℕ) := 2 + 4*d + n*stepIncidences d e
private abbrev targetIncidences (d : ℕ) := 10*(d+1) + 3*d

abbrev count {k : ℕ} (b : B k) := b.core.A.ne
abbrev mulEdges {d : ℕ} (hd : 1 ≤ d) := (w4_M5GraphBounds.graph d hd).nE

theorem join_count {k : ℕ} (u v : B k) :
    count (joinB u v) = count u + count v := rfl

private theorem row_count {s : Shape} (n k : ℕ) (r : Fin n → Fin k → Ref s)
    (t : Fin n → (Fin k → Bool) → Bool) : count (rows n k r t) = n*k := rfl

private theorem checker_count {s : Shape} {d : ℕ} (p : ℕ) (z : Path (triple d) s) :
    count (checker p z) = (d+1)*5 := rfl

private theorem add_count {s : Shape} {n : ℕ} (b : Bool) (a x z c : Fin n → Ref s) :
    count (NamedBlocks.add b a x z c) = n*5 := rfl

private theorem rename_count {k l : ℕ} (u : B k) (f : Fin u.core.A.ne → Fin l) :
    count (⟨u.core, f⟩ : B l) = count u := rfl

private theorem many_count {k r : ℕ} (n : ℕ) (u : Fin (n+1) → B k)
    (h : ∀ i, count (u i) = r) : count (many n u) = (n+1)*r := by
  induction n with
  | zero => simpa [many] using h 0
  | succ n ih =>
    rw [many, join_count, h 0, ih (fun i => u i.succ) (fun i => h i.succ)]
    ring

theorem all_count {s : Shape} {r : ℕ} (n : ℕ) (u : Fin n → B (s.size+1))
    (h : ∀ i, count (u i) = r) : count (allRows n u) = n*r := by
  cases n with
  | zero => simp [allRows, row_count]
  | succ n => exact many_count n u h

theorem hash_count {s : Shape} {d : ℕ} (hd : 1 ≤ d) (p : ℕ) (w : Wires d hd s) :
    count (HashRows.block p w) = hashIncidences d (mulEdges hd) := by
  simp only [hashIncidences, HashRows.block, HashRows.product, HashRows.sumRows, eqs, join_count,
    row_count, add_count, count, mapped, w3_fpMulLayout, w3_m5Layout, w3_forgetSides, mulEdges]
  omega

theorem seed_count {s : Shape} {m d : ℕ} (p : ℕ) (η : List Bool)
    (q : Path (ECSeedBank.ecSeedShape m d) s) :
    count (RoutesV2.ecSeedBlockV2 p m η q) = m*(30*(d+1)) + η.length := by
  unfold RoutesV2.ecSeedBlockV2
  rw [join_count, row_count]
  simp only [Nat.mul_one]
  congr 1
  apply all_count
  intro i
  simp only [ECSeedBank.ecSeedSlotBlock, seedSlotBlock, join_count, checker_count,
    HashRows.sumRows, add_count]
  omega

theorem atom_count {s : Shape} {d : ℕ} (hd : 1 ≤ d) (p T : ℕ) (c : Coeff)
    (a b x y : Word s) (q : Path (ECAtomSlot.slotShape d (mulEdges hd)) s) :
    count (ECAtomSlot.slotBlock hd p T c a b x y q) = atomIncidences d (mulEdges hd) := by
  simp only [atomIncidences, ECAtomSlot.slotBlock, fixed, rename_count, RangeRows.block, many,
    CurveRows.block, join_count, checker_count, hash_count, row_count, add_count]
  omega

theorem map_count {s : Shape} {d e : ℕ} (hd : 1 ≤ d) (p b a c : ℕ) (f : Ref s)
    (x y : Word s) (q : Path (ECMapRows.mapShape d e) s) :
    count (ECMapRows.mapBlock hd p b a c f x y q) = mapIncidences d (mulEdges hd) := by
  simp only [mapIncidences, ECMapRows.mapBlock, ranges, maskEq, eqs, many, join_count,
    checker_count, hash_count, row_count]
  omega

theorem step_count {s : Shape} {d e : ℕ} (hd : 1 ≤ d) (p neg1 three c4 : ℕ)
    (f : Ref s) (x y : Word s) (g : Ref s) (X Y : Word s) (q : Path (ECAddRoutes.addShape d e) s) :
    count (ECAddRoutes.addBlock hd p neg1 three c4 f x y g X Y q) = stepIncidences d (mulEdges hd) := by
  simp only [stepIncidences, ECAddRoutes.addBlock, invRows, selectRows, many, join_count,
    checker_count, hash_count, row_count]
  omega

theorem fold_count {s : Shape} {n d e : ℕ} (hd : 1 ≤ d) (p neg1 three c4 : ℕ)
    (f : Ref s) (x y : Word s) (flags : Fin n → Ref s) (xs ys : Fin n → Word s)
    (z : Ref s) (X Y : Word s) (q : Path (ECFoldRoutes.foldShape n d e) s) :
    count (ECFoldRoutes.foldBlock hd p neg1 three c4 f x y flags xs ys z X Y q) =
      foldIncidences n d (mulEdges hd) := by
  have hs := all_count (r := stepIncidences d (mulEdges hd)) n
    (foldStep hd p neg1 three c4 f x y flags xs ys q) (fun _ => step_count ..)
  simp only [foldIncidences, ECFoldRoutes.foldBlock, join_count, row_count, hs]
  omega

theorem target_count {s : Shape} {d : ℕ} (p : ℕ) (q : Path (RoutesV2.targetShape d) s) :
    count (RoutesV2.targetBlock p q) = targetIncidences d := by
  simp only [targetIncidences, RoutesV2.targetBlock, join_count, checker_count, row_count]
  omega

end DetDLP.S8N.MomentIncidences


