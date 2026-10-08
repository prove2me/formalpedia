-- Prove2me | Definitions.Def_CompOT_Assignment_Defs
-- name    : CompOT_Assignment_Defs
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T00:24:43.167531+00:00
-- url     : https://prove2.me/theorems/80abc700-e5fc-4df9-943f-e0a365631d3d
-- title:
--   (2.2), (2.10)–(2.12) — finite couplings, transport cost, and scaled permutation matrices
-- statement:
--   For histograms $a\in\mathbb R^n$ and $b\in\mathbb R^m$, the **transportation polytope** $U(a,b)$ consists of nonnegative matrices whose row sums are $a$ and whose column sums are $b$:
--
--   $$U(a,b)=\{P\in\mathbb R_+^{n\times m}:\sum_j P_{ij}=a_i,\ \sum_iP_{ij}=b_j\}. $$
--
--   For a cost matrix $C$, the pairing is $\langle C,P\rangle=\sum_{i,j}C_{ij}P_{ij}$, and $L_C(a,b)$ is its minimum over $U(a,b)$. An optimal coupling is a member of $U(a,b)$ whose cost is no greater than that of any other member.
--
--   For $n>0$, the uniform histogram $u$ has entries $1/n$. A permutation $\sigma$ gives the **scaled permutation coupling** $(P_\sigma)_{ij}=1/n$ when $j=\sigma(i)$ and $0$ otherwise. Its assignment objective is $A_C(\sigma)=\frac1n\sum_i C_{i,\sigma(i)}$; the minimum of this objective over permutations is also defined.
--
--   These definitions provide the common finite matrix model used by the matching proposition and its supporting claims.
--
--   **Formalization Note** Indices use `Fin n`, so they start at zero in Lean. Consuming theorems use simplex marginals to make $U(a,b)$ nonempty and its objective bounded; $n>0$ guards the normalized assignment formulas.
-- source:
--   Peyré & Cuturi, Computational Optimal Transport (FnT ML 2019), (2.2), p. 365; (2.10), p. 370; (2.11), p. 371; (2.12), p. 372

import Mathlib

namespace CompOT.Assignment

/-- The discrete transport polytope `U(a,b)` of (2.10). -/
def couplings {n m : ℕ} (a : Fin n → ℝ) (b : Fin m → ℝ) :
    Set (Matrix (Fin n) (Fin m) ℝ) :=
  {P | (∀ i j, 0 ≤ P i j) ∧
    (∀ i, ∑ j, P i j = a i) ∧
    (∀ j, ∑ i, P i j = b j)}

/-- The Frobenius pairing `⟨C,P⟩` in (2.11). -/
def frob {n m : ℕ} (C P : Matrix (Fin n) (Fin m) ℝ) : ℝ :=
  ∑ i, ∑ j, C i j * P i j

/-- A minimizer of (2.11), with minimization over all of `U(a,b)`. -/
def IsOptimalCoupling {n m : ℕ} (C : Matrix (Fin n) (Fin m) ℝ)
    (a : Fin n → ℝ) (b : Fin m → ℝ) (P : Matrix (Fin n) (Fin m) ℝ) : Prop :=
  P ∈ couplings a b ∧ ∀ Q ∈ couplings a b, frob C P ≤ frob C Q

/-- The uniform histogram `𝟙ₙ/n`. Used only when `0 < n`. -/
noncomputable def uniform (n : ℕ) : Fin n → ℝ := fun _ => 1 / (n : ℝ)

/-- The scaled permutation matrix `P_σ` of (2.12). -/
noncomputable def permCoupling {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j => if j = σ i then 1 / (n : ℝ) else 0

/-- The objective of the assignment problem (2.2). -/
noncomputable def assignmentCost {n : ℕ} (C : Matrix (Fin n) (Fin n) ℝ)
    (σ : Equiv.Perm (Fin n)) : ℝ :=
  (1 / (n : ℝ)) * ∑ i, C i (σ i)

/-- The value `L_C(a,b)` of (2.11). Statements using this real infimum
assume feasible probability histograms, so its feasible set is nonempty and bounded. -/
noncomputable def otCost {n m : ℕ} (C : Matrix (Fin n) (Fin m) ℝ)
    (a : Fin n → ℝ) (b : Fin m → ℝ) : ℝ :=
  sInf {v : ℝ | ∃ P ∈ couplings a b, v = frob C P}

/-- The minimum assignment value of (2.2), written as a real infimum. -/
noncomputable def assignmentMin {n : ℕ} (C : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  sInf {v : ℝ | ∃ σ : Equiv.Perm (Fin n), v = assignmentCost C σ}

end CompOT.Assignment


