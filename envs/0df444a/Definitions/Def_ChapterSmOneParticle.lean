-- Prove2me | Definitions.Def_ChapterSmOneParticle
-- name    : ChapterSmOneParticle
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-01T04:55:09.052985+00:00
-- url     : https://prove2.me/theorems/0fb1243f-a3fa-42d5-a562-481e4a73c1a4
-- title:
--   Chapter SmOneParticle
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterSmOneParticle.lean`): generated def bundle for ChapterSmOneParticle. See BookProof/ChapterSmOneParticle.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterSmOneParticle.lean

import Mathlib


/-!
# The Standard Model one-particle coordinates, and the CKM / PMNS mixing algebra

This module is step 1 of the Standard-Model work order of `CONSOLIDATED_PLAN.md`
(§“State of the project — 2026-09-22d”, D6b-SM.1 and D6b-SM.4): the *bookkeeping* layer of
the temporal-gauge (`A₀ = W₀ = B₀ = 0`) Standard-Model one-particle operator, and the
matrix algebra of the two mixing matrices.

## The collective coordinates and the number `D_B`

The plan records the single-particle collective coordinate as

```
xi = ( x , {G^a_i, G^a_{i,j}} , {W^k_i, W^k_{i,j}} , {B_i, B_{i,j}} , {phi_a, phi_{a,j}} , zeta_F )
```

with `D_B = 163` *bosonic* real coordinates.  The plan explicitly asks for the number to be
**recounted and pinned as a theorem** rather than trusted.  That is `card_smCoord`:

```
 3   spatial x_i
 24  gluon fields      G^a_i          (8 colours × 3 directions)
 72  gluon derivatives G^a_{i,j}      (8 × 3 × 3)
 9   weak fields       W^k_i          (3 × 3)
 27  weak derivatives  W^k_{i,j}      (3 × 3 × 3)
 3   hypercharge field B_i
 9   hypercharge derivatives B_{i,j}
 4   Higgs             phi_a          (the complex doublet as four real components)
 12  Higgs derivatives phi_{a,j}
 ---
 163
```

`SmCoord` is that list of blocks as a type, `card_smCoord : Fintype.card SmCoord = 163` is
the recount, and `smIdx : SmCoord ≃ Fin 163` is the resulting labelling of the field-space
directions of `L²(ℝ¹⁶³)`.  Because the labelling is an equivalence, the named coordinate
functions `smX`, `smG`, `smDG`, `smW`, `smDW`, `smB`, `smDB`, `smPhi`, `smDPhi` are
injective and pairwise disjoint by construction — no index arithmetic is done by hand.

The Grassmann factor `zeta_F` is **not** part of `SmCoord`: the fermionic coordinates are
not bosonic coordinates, and the CAR algebra is a stated open boundary of the plan.

## The mixing matrices

The Cadabra module verifies the CKM sector in CHECK 17–20 and the PMNS sector in
CHECK 25–28.  Their Lean counterparts are here, stated once for an arbitrary unitary
`3 × 3` matrix and instantiated to the two physical cases by name:

* `unitary_row_sum_normSq`, `unitary_entry_norm_le_one` — row unitarity and the entry
  bound `|V_ij| ≤ 1` (CHECK 19 for CKM, CHECK 27 for PMNS);
* `unitary_transpose_of_real` — the Cabibbo identity `V Vᵀ = I` for a real unitary
  (CHECK 17 for CKM, CHECK 25 for PMNS);
* `biunitary_massSq` — the biunitary mass identity
  `M = U_L V† D U_R†  ⟹  M† M = U_R (D† D) U_R†` (CHECK 18 for CKM, CHECK 26 for PMNS);
* `norm_mulVec_le_sum`, `yukawa_bound` — the mixing-bounded Yukawa domination: a mixing
  matrix cannot amplify a Yukawa coupling by more than the number of generations
  (CHECK 20 for CKM, CHECK 28 for PMNS).

Only the *unitarity identities* are formalized.  The measured Wolfenstein/PMNS parameters
are experimental input and are not claimed here.

Everything is `sorry`-free and `axiom`-free.
-/

namespace BookProof.SmOneParticle

/-! ## 1. The bosonic collective coordinates, and the recount of `D_B` -/

/-- The bosonic collective coordinate of one Standard-Model excitation, as the disjoint
union of its nine blocks: the three spatial coordinates, the gluon field and its spatial
derivatives, the weak field and its derivatives, the hypercharge field and its derivatives,
and the four real Higgs components with their derivatives. -/
abbrev SmCoord : Type :=
  Fin 3 ⊕ (Fin 8 × Fin 3) ⊕ (Fin 8 × Fin 3 × Fin 3) ⊕ (Fin 3 × Fin 3) ⊕ (Fin 3 × Fin 3 × Fin 3)
    ⊕ Fin 3 ⊕ (Fin 3 × Fin 3) ⊕ Fin 4 ⊕ (Fin 4 × Fin 3)

/-- **The recount of `D_B`.**  The nine blocks of `SmCoord` carry
`3 + 24 + 72 + 9 + 27 + 3 + 9 + 4 + 12 = 163` real bosonic coordinates: the number `D_B` of
the plan, proved rather than quoted. -/
theorem card_smCoord : Fintype.card SmCoord = 163 := by simp

/-- The number of bosonic coordinates of one excitation. -/
def smDimB : ℕ := 163



noncomputable section

/-- The labelling of the `163` field-space directions of `L²(ℝ¹⁶³)` by the collective
coordinates.  Being an equivalence, it makes all the named coordinates below injective and
pairwise distinct. -/
def smIdx : SmCoord ≃ Fin 163 := Fintype.equivFinOfCardEq card_smCoord

/-- The `i`-th spatial coordinate `x_i`. -/
def smX (i : Fin 3) : Fin 163 := smIdx (Sum.inl i)

/-- The gluon field `G^a_i`. -/
def smG (a : Fin 8) (i : Fin 3) : Fin 163 := smIdx (Sum.inr (Sum.inl (a, i)))

/-- The gluon derivative coordinate `G^a_{i,j} = ∂_j G^a_i`. -/
def smDG (a : Fin 8) (i j : Fin 3) : Fin 163 := smIdx (Sum.inr (Sum.inr (Sum.inl (a, i, j))))

/-- The weak field `W^k_i`. -/
def smW (k i : Fin 3) : Fin 163 :=
  smIdx (Sum.inr (Sum.inr (Sum.inr (Sum.inl (k, i)))))

/-- The weak derivative coordinate `W^k_{i,j}`. -/
def smDW (k i j : Fin 3) : Fin 163 :=
  smIdx (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl (k, i, j))))))

/-- The hypercharge field `B_i`. -/
def smB (i : Fin 3) : Fin 163 :=
  smIdx (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl i))))))

/-- The hypercharge derivative coordinate `B_{i,j}`. -/
def smDB (i j : Fin 3) : Fin 163 :=
  smIdx (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl (i, j))))))))

/-- The `a`-th real component of the Higgs doublet `φ_a`. -/
def smPhi (a : Fin 4) : Fin 163 :=
  smIdx (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl a))))))))

/-- The Higgs derivative coordinate `φ_{a,j}`. -/
def smDPhi (a : Fin 4) (j : Fin 3) : Fin 163 :=
  smIdx (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (a, j)))))))))











/-! ## 2. The mixing matrices: CKM (CHECK 17–20) and PMNS (CHECK 25–28) -/

open Matrix

variable {V U : Matrix (Fin 3) (Fin 3) ℂ}

/-- A `3 × 3` mixing matrix is unitary when `V V† = 1`.  This is the Lean form of the CKM
input of CHECK 17–19 and of the PMNS input of CHECK 25–27. -/
def IsMixing (V : Matrix (Fin 3) (Fin 3) ℂ) : Prop := V * Vᴴ = 1















end

end BookProof.SmOneParticle


