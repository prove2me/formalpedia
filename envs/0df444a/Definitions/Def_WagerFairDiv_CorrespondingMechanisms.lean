-- Prove2me | Definitions.Def_WagerFairDiv_CorrespondingMechanisms
-- name    : WagerFairDiv_CorrespondingMechanisms
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T09:14:59.791246+00:00
-- url     : https://prove2.me/theorems/6d608080-6a0f-49fe-aeb0-daf1b1e5d365
-- title:
--   Corresponding allocation and wagering mechanisms: $\mathcal B = W\mathcal A$, $\mathcal A = \mathcal B/E$ (Definition 10)
-- statement:
--   **Definition 10** (Corresponding mechanisms, p.4). An allocation mechanism $\mathcal A$ and a wagering mechanism $\mathcal B$ are **corresponding mechanisms** if for all $\hat{\mathbf p}$, $\mathbf w$, $i\in[n]$ and $j\in[m]$,
--   $$\mathcal B_{i,j}(\hat{\mathbf p},\mathbf w)=W\,\mathcal A_{i,j}(\hat{\mathbf p},\mathbf w),\qquad W=\sum_{i=1}^n w_i.$$
--   The paper adds "or equivalently, $\mathcal A_{i,j}(\hat{\mathbf v},\mathbf e)=\mathcal B_{i,j}(\hat{\mathbf v},\mathbf e)/E$"; that equivalence is a clause of the mission's goal.
--
--   The file also defines the two maps: $\mathcal A\mapsto W\mathcal A$ (the wagering mechanism corresponding to $\mathcal A$) and $\mathcal B\mapsto\mathcal B/E$ (the allocation mechanism corresponding to $\mathcal B$). The correspondence identifies a share of good $j$ with a share of the $W$ type-$j$ securities.
--
--   **Formalization Note** `Corresponding A B` is the first printed form. `toWager A` and `toAlloc B` are the two maps; weights and wagers are the same positive vector, so $E$ and $W$ are both `PosVec.total`.
-- source:
--   Freeman, Pennock & Vaughan, An Equivalence Between Wagering and Fair-Division Mechanisms (preprint, 2018), Definition 10 (Corresponding mechanisms), §3, p.4. PDF sha256 02e3d24f0ced18523a243feb31fc3e2f28997a9d5a723a0137ed0d2320230580

import Mathlib
import Definitions.Def_WagerFairDiv_Model

namespace WagerFairDiv

variable {n m : ℕ}

/-- The wagering mechanism **corresponding** to an allocation mechanism `A` (Definition 10, p.4):
`Bᵢ,ⱼ(p̂, w) = W Aᵢ,ⱼ(p̂, w)`, with `W = Σᵢ wᵢ`. -/
def toWager (A : Mech n m) : Mech n m := fun p w i j => w.total * A p w i j

/-- The allocation mechanism **corresponding** to a wagering mechanism `B` (Definition 10, p.4):
`Aᵢ,ⱼ(v̂, e) = Bᵢ,ⱼ(v̂, e) / E`, with `E = Σᵢ eᵢ`. -/
noncomputable def toAlloc (B : Mech n m) : Mech n m := fun v e i j => B v e i j / e.total

/-- **Corresponding mechanisms** (Definition 10, p.4): `A` and `B` correspond if for all `p̂`, `w`,
`i ∈ [n]` and `j ∈ [m]`, `Bᵢ,ⱼ(p̂, w) = W Aᵢ,ⱼ(p̂, w)`.

**Formalization Note.** This is the first of the two forms printed in Definition 10; that it is
equivalent to the second form `Aᵢ,ⱼ(v̂, e) = Bᵢ,ⱼ(v̂, e) / E` is part of the mission's goal. -/
def Corresponding (A B : Mech n m) : Prop :=
  ∀ (p : Profile n m) (w : PosVec n) (i : Fin n) (j : Fin m), B p w i j = w.total * A p w i j

end WagerFairDiv


