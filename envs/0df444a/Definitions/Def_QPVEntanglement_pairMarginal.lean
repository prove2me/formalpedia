-- Prove2me | Definitions.Def_QPVEntanglement_pairMarginal
-- name    : QPVEntanglement_pairMarginal
-- status  : Definition
-- author  : @iris
-- created : 2026-11-11T08:27:12.958218+00:00
-- url     : https://prove2.me/theorems/79992696-212f-4fff-a68d-a1795dcfc8d8
-- title:
--   Two-qubit marginals on selected qubit factors
-- statement:
--   For a state on $X\otimes Y$ and identifications $X\cong\mathbb C^2\otimes P$, $Y\cong\mathbb C^2\otimes Q$, the **pair marginal** is the partial trace over everything except the two selected qubits; it gives the recovered states $\tilde\rho_{O_jR_j}$, $\tilde\tau_{O_jW_j}$ of §6. The module also provides regrouping $X(YZ)\to(XY)Z$, the partial trace over a middle factor, the application of a superoperator to a middle factor, the qubit $O_j$ of a $k$-qubit register, and the marginal on $O_jA$ of a state with $O=O_1\cdots O_k$.
-- source:
--   Behera, Goyal, Breaking the Bounded Entanglement Barrier for Quantum Position Verification, arXiv:2609.39234 (sha256 bdf2928d…), Lemma 6, Lemma 7 and Theorem 6, pp.33–34

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P19

set_option autoImplicit false

open scoped Matrix ComplexOrder

namespace QPVEntanglement

/-- Regroup `X × (Y × Z)` as `(X × Y) × Z` (the bipartition `XY : Z`). -/
noncomputable def assocL {X Y Z : Type*} (M : Matrix (X × (Y × Z)) (X × (Y × Z)) ℂ) :
    Matrix ((X × Y) × Z) ((X × Y) × Z) ℂ :=
  Matrix.reindex (Equiv.prodAssoc X Y Z).symm (Equiv.prodAssoc X Y Z).symm M

/-- Trace out the middle factor: the `X × Z` marginal of a state on `X × (Y × Z)`. -/
noncomputable def traceMid {X Y Z : Type*} [Fintype Y] (M : Matrix (X × (Y × Z)) (X × (Y × Z)) ℂ) :
    Matrix (X × Z) (X × Z) ℂ :=
  fun x y => ∑ b, M (x.1, (b, x.2)) (y.1, (b, y.2))

/-- Apply a superoperator to the middle factor: `(id_X ⊗ E ⊗ id_Z)`. -/
noncomputable def applyMid {X Y Y' Z : Type*} (E : QAlgorithms.Superop Y Y')
    (M : Matrix (X × (Y × Z)) (X × (Y × Z)) ℂ) : Matrix (X × (Y' × Z)) (X × (Y' × Z)) ℂ :=
  fun x y => E (fun b b' => M (x.1, (b, x.2.2)) (y.1, (b', y.2.2))) x.2.1 y.2.1

/-- Qubit `j` of an `k`-qubit register, split off: `(Fin k → Fin 2) ≃ Fin 2 × (rest)`. -/
def qubitAt {k : ℕ} (j : Fin k) : (Fin k → Fin 2) ≃ Fin 2 × ({l : Fin k // l ≠ j} → Fin 2) :=
  Equiv.piSplitAt j fun _ => Fin 2

/-- A qubit factor of the first register of `A × B`. -/
def extLeft {A B P : Type*} (e : A ≃ Fin 2 × P) : A × B ≃ Fin 2 × (P × B) :=
  (e.prodCongr (Equiv.refl B)).trans (Equiv.prodAssoc (Fin 2) P B)

/-- A qubit factor of the second register of `A × B`. -/
def extRight {A B P : Type*} (e : B ≃ Fin 2 × P) : A × B ≃ Fin 2 × (A × P) :=
  (Equiv.prodComm A B).trans (extLeft e) |>.trans
    (Equiv.prodCongr (Equiv.refl (Fin 2)) (Equiv.prodComm P A))

/-- A qubit factor of the quantum part `A'` of `C × A'`. -/
def extFlag {C A P : Type*} (e : A ≃ Fin 2 × P) : C × A ≃ Fin 2 × (C × P) :=
  (Equiv.prodComm C A).trans (extLeft e) |>.trans
    (Equiv.prodCongr (Equiv.refl (Fin 2)) (Equiv.prodComm P C))

/-- **The two-qubit marginal on a pair of qubit factors** (`ρ̃_{O_jR_j}`, §6, pp.33–35): for
`M` on `X × Y` and qubit factors `e₁ : X ≃ ℂ² ⊗ P`, `e₂ : Y ≃ ℂ² ⊗ Q`, the partial trace of `M`
over everything except the two selected qubits. Behera–Goyal, arXiv:2609.39234 (sha256
bdf2928d…), Lemma 7 and Theorem 6, pp.33–34. -/
noncomputable def pairMarginal {X Y P Q : Type*} [Fintype P] [Fintype Q] (e₁ : X ≃ Fin 2 × P)
    (e₂ : Y ≃ Fin 2 × Q) (M : Matrix (X × Y) (X × Y) ℂ) :
    Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  fun u v => ∑ p, ∑ q, M (e₁.symm (u.1, p), e₂.symm (u.2, q)) (e₁.symm (v.1, p), e₂.symm (v.2, q))

/-- The marginal on `O_j A` of a state on `O × A`, `O = O₁ ⋯ O_k` with `O_j` of dimension
`dO j` (Lemma 6, p.33): trace out every `O_l`, `l ≠ j`. -/
noncomputable def coordMarginal {k : ℕ} {dO : Fin k → ℕ} {A : Type*} (j : Fin k)
    (ρ : Matrix (((l : Fin k) → Fin (dO l)) × A) (((l : Fin k) → Fin (dO l)) × A) ℂ) :
    Matrix (Fin (dO j) × A) (Fin (dO j) × A) ℂ :=
  fun x y => ∑ r : ((l : {l : Fin k // l ≠ j}) → Fin (dO l.val)),
    ρ ((Equiv.piSplitAt j (fun l => Fin (dO l))).symm (x.1, r), x.2)
      ((Equiv.piSplitAt j (fun l => Fin (dO l))).symm (y.1, r), y.2)

end QPVEntanglement


