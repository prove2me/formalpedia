-- Prove2me | Definitions.Def_KramersHubbard_PartitionFunction_Trotter
-- name    : KramersHubbard_PartitionFunction_Trotter
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T07:04:03.975906+00:00
-- url     : https://prove2.me/theorems/a7108bbe-0bdd-46b7-a8c1-cafa3a9ea682
-- title:
--   Trotter products, insertions and the pairing field
-- statement:
--   For $M\ge1$, set $\delta=\beta/M$, $c_i=\delta U_i/2$, $P_i=n(v_i)n(w_i)$ and
--
--   $$C=e^{-\delta H_0/2}\prod_{i=1}^r(I+c_iP_i),\quad L=CC^\dagger,\quad \Delta_i=a(w_i)a(v_i).$$
--
--   The product is ordered, rather than commutative. Insertions $K=[M]\times[2r]$ are flattened lexicographically with the interaction sequence $(1,\ldots,r,r,\ldots,1)$ in every slice. Their imaginary times are $(M-m+1/2)\delta$. The expansion weight $f(X)$ is computed directly from Eq.(20), using operator products, before any determinant equality is asserted. Replacing each factor by $I+c_iP_i+\sqrt{\lambda c_i}(\Delta_i+\Delta_i^\dagger)$ defines $C_\lambda$ and $L_\lambda=C_\lambda C_\lambda^\dagger$. The mathematical objects may be exponentially sized; evaluating them is not a primitive machine instruction.
-- source:
--   Chaithanya Rayudu, Jun Takahashi, Ojas Parekh, Andrew Zhao, STOC 2027 submission #1325 (October 2026), Efficient classical simulation of Fermi-Hubbard models with Kramers symmetry, Eqs.(17)-(22), (37)-(38), pp.12-13,16; printed page = 1-based PDF page. https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1325.pdf; PDF SHA-256 e3fd3fa7390d8ff9f0f1e2ee07e6ebc5b8d7304e26be9e76959d9587f4564eae. Canonical submitted artifact, citation_basis: published; title-page date November 3, 2026; no assertion of conference acceptance.

import Definitions.Def_KramersHubbard_PartitionFunction_Model

noncomputable section
open scoped BigOperators
open Matrix

namespace KramersHubbard.PartitionFunction

/-- Flat lexicographic index (m,q), m=0,...,M-1 and q=0,...,2r-1. -/
abbrev Insertion (M r : ℕ) := Fin (M * (2 * r))

def interactionIndex {M r} (k : Insertion M r) : Fin r :=
  have hr : 0 < r := by
    by_contra h
    have : r = 0 := by omega
    subst r
    simpa using k.isLt
  let q := k.val % (2 * r)
  have hq : q < 2 * r := Nat.mod_lt _ (by omega)
  ⟨if q < r then q else 2 * r - 1 - q, by split <;> omega⟩

def delta (β : ℝ) (M : ℕ) : ℝ := β / M

def coupling {N r} (D : Data N r) (β : ℝ) (M : ℕ) (i : Fin r) : ℝ :=
  delta β M * D.U i / 2

def halfFree {N r} (D : Data N r) (β : ℝ) (M : ℕ) : FockOp N :=
  NormedSpace.exp ((-delta β M / 2 : ℝ) • freeH D)

/-- Printed order 1,...,r, followed in CC† by r,...,1. -/
def trotterC {N r} (D : Data N r) (β : ℝ) (M : ℕ) : FockOp N :=
  halfFree D β M * ((List.finRange r).map fun i =>
    1 + (coupling D β M i : ℂ) • pairProjector D i).prod

def trotterL {N r} (D : Data N r) (β : ℝ) (M : ℕ) : FockOp N :=
  trotterC D β M * (trotterC D β M).conjTranspose

def trotterZ {N r} (D : Data N r) (β : ℝ) (M : ℕ) : ℂ :=
  ((trotterL D β M) ^ M).trace

def insertionTime {M r} (β : ℝ) (k : Insertion M r) : ℝ :=
  ((M : ℝ) - (k.val / (2 * r) : ℕ) - 1/2) * delta β M

/-- Direct Eq.(20), not defined through a determinant identity. -/
def expansionWeight {N r M} (D : Data N r) (β : ℝ)
    (X : Finset (Insertion M r)) : ℂ :=
  (∏ k ∈ X, (coupling D β M (interactionIndex k) : ℂ)) *
    (((List.finRange M).map fun m =>
      halfFree D β M * ((List.finRange (2 * r)).map fun q =>
        let k : Insertion M r := ⟨m.val * (2*r) + q.val, by have hm := m.isLt; have hq := q.isLt; nlinarith⟩
        if k ∈ X then pairProjector D (interactionIndex k) else 1).prod *
      halfFree D β M).prod).trace

def pairAnnihilator {N r} (D : Data N r) (i : Fin r) : FockOp N :=
  annihilate (partner D i) * annihilate (D.v i)

def pairingC {N r} (D : Data N r) (β : ℝ) (M : ℕ) (lam : ℝ) : FockOp N :=
  halfFree D β M * ((List.finRange r).map fun i =>
    1 + (coupling D β M i : ℂ) • pairProjector D i +
      (Real.sqrt (lam * coupling D β M i) : ℂ) •
        (pairAnnihilator D i + (pairAnnihilator D i).conjTranspose)).prod

def pairingL {N r} (D : Data N r) (β : ℝ) (M : ℕ) (lam : ℝ) : FockOp N :=
  pairingC D β M lam * (pairingC D β M lam).conjTranspose

def pairingZ {N r} (D : Data N r) (β : ℝ) (M : ℕ) (lam : ℝ) : ℂ :=
  ((pairingL D β M lam) ^ M).trace

end KramersHubbard.PartitionFunction


