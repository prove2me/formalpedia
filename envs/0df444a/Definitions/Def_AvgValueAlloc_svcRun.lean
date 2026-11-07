-- Prove2me | Definitions.Def_AvgValueAlloc_svcRun
-- name    : AvgValueAlloc_svcRun
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:37:22.406203+00:00
-- url     : https://prove2.me/theorems/4e258e4e-f7b5-4136-a171-76138b6ba94a
-- title:
--   Service kernel: private ledgers and physical winners
-- statement:
--   On a fixed order of the service items and a fixed set of proposals at each position, the kernel keeps private ledgers $L$ (starting at the earned bank $B$) and physical surplus $C$ (starting at $C_0\ge B$). A proposal of buyer $j$ on a negative edge **fits** if its deficit is at most $L_j$; it then debits $L_j$ even if it loses the item. The physical winner is a maximum-original-value buyer among fitting proposals and positive edges (or none); a winner changes $C_j$ by $v_j-\rho_j$, so a negative winner is debited and a positive winner credited. The physical service welfare $R$ adds the winner's original value.
-- source:
--   Mahboub, Rahgoshay, Online Average-Value Allocation: A Sharp Information Frontier, manuscript of Oct. 30, 2026, STOC 2027 submission (sha256 ce4bd89e8ec2cb75817047a84264f190c9dcd024a67ae681e2d9f90a6881c8fb), §2.2, p.5

import Mathlib
import Definitions.Def_AvgValueAlloc_Vec

namespace AvgValueAlloc

/-- The service state: private ledgers `L`, physical surplus `C`, physical service welfare `R`. -/
structure SvcState (n : ℕ) where
  /-- private residual ledgers -/
  L : Fin n → ℝ
  /-- physical surplus -/
  C : Fin n → ℝ
  /-- original physical service welfare so far -/
  R : ℝ

open scoped Classical in
/-- One service position: item `u`, proposed buyers `pr`. A proposal fits when it is a negative
edge whose deficit is at most the current private ledger, and then debits that ledger (even if it
loses the item). The physical winner is a maximum-original-value buyer among private acceptances
and positive edges (least index on ties), or none. A winner changes physical surplus by
`v_j − ρ_j`: a negative winner is debited, a positive winner credited; ledgers never gain. -/
noncomputable def svcStep {n : ℕ} (ρ : Fin n → ℚ) (u : Vec n) (pr : Fin n → Bool)
    (st : SvcState n) : SvcState n :=
  let acc : Fin n → Prop := fun j =>
    pr j = true ∧ (u j : ℚ) < ρ j ∧ (ρ j : ℝ) - ((u j : ℚ≥0) : ℝ) ≤ st.L j
  let cand := Finset.univ.filter fun j => acc j ∨ ρ j ≤ (u j : ℚ)
  let best := cand.filter fun j => ∀ k ∈ cand, u k ≤ u j
  let w : Option (Fin n) := if h : best.Nonempty then some (best.min' h) else none
  { L := fun j => if acc j then st.L j - ((ρ j : ℝ) - ((u j : ℚ≥0) : ℝ)) else st.L j
    C := fun j => if w = some j then st.C j + (((u j : ℚ≥0) : ℝ) - ρ j) else st.C j
    R := st.R + w.elim 0 (fun j => ((u j : ℚ≥0) : ℝ)) }

/-- **The service kernel's ledgers and physical winners on a fixed order and proposal profile.**
Mahboub–Rahgoshay, *Online Average-Value Allocation: A Sharp Information Frontier*,
manuscript of Oct. 30, 2026 (sha256 ce4bd89e…), §2.2, p.5: "Freeze the actually earned bank B.
Distinguish private residual ledgers L from physical surplus C: at service start L_j = B_j ≤ C_j.
… A fitting proposal debits its private ledger even if it loses the item. Choose one
maximum-original-value physical winner among private acceptances and positive edges, or reject. A
negative winner also debits physical surplus; a positive winner increases only physical surplus,
never a private ledger."

`svcRun ρ Z τ prop B C₀ a` is the state after the first `a` service positions, when position `i`
holds `Z (τ i)`, the buyers proposed there are `prop i`, the ledgers start at `B` and the physical
surplus at `C₀`.

**Formalization Note.** The winner's identity on ties does not change `R` (its value is the
maximum either way). -/
noncomputable def svcRun {n z : ℕ} (ρ : Fin n → ℚ) (Z : Fin z → Vec n) (τ : Equiv.Perm (Fin z))
    (prop : Fin z → Fin n → Bool) (B C₀ : Fin n → ℝ) : ℕ → SvcState n
  | 0 => ⟨B, C₀, 0⟩
  | a + 1 =>
    if h : a < z then svcStep ρ (Z (τ ⟨a, h⟩)) (prop ⟨a, h⟩) (svcRun ρ Z τ prop B C₀ a)
    else svcRun ρ Z τ prop B C₀ a

end AvgValueAlloc


