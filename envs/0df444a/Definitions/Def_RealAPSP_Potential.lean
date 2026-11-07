-- Prove2me | Definitions.Def_RealAPSP_Potential
-- name    : RealAPSP_Potential
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T20:57:53.848287+00:00
-- url     : https://prove2.me/theorems/aa4e7b57-a377-4d07-a200-020f56bbb6db
-- title:
--   Potential adjustments, potential-adjusting reductions, and uniform, regular and doubling instances
-- statement:
--   An instance $(A',B',C')$ is a **potential adjustment** of $(A,B,C)$ if there are $u,v,w\in\mathbb R^n$ with
--
--   $$A'[i,k]=A[i,k]-u[i]+v[k],\quad B'[k,j]=B[k,j]-v[k]+w[j],\quad C'[i,j]=C[i,j]+u[i]-w[j],$$
--
--   each entry being allowed to be $\bot$ instead. A surviving triangle keeps its weight. A **$\Delta$-approximate potential-adjusting reduction** outputs a set $I$ of potential adjustments and a set $\mathcal T\subseteq[n]^3$ such that each $\Delta$-approximate triangle of $(A,B,C)$ is in $\mathcal T$ or is a $\Delta$-approximate triangle in an instance of $I$.
--
--   With $X$ the set of non-$\bot$ entries, an instance is **$(D,\Delta)$-uniform** if $|X|_{\pm\Delta}\le D$ and **$(K,\Delta)$-doubling** if $|X+X|_{\pm\Delta}\le K|X|_{\pm\Delta}$. A matrix is **$(\rho,\Delta)$-regular** if no $x$ has more than $\rho n$ entries $x\pm\Delta$ in one row or column, and an instance is regular if all three matrices are.
--
--   These are the input and output contracts of the doubling reduction of §7.
--
--   **Formalization Note** An output instance is stored as flags and potentials, so it is a potential adjustment by construction. The page's potentials are integer combinations of input reals, so they are stored unscaled.
-- source:
--   Fischer, Polak, Schmidt, Real-to-Integer Reduction for All-Pairs Shortest Paths, arXiv:2611.04847 (held file sha256 a3dc0096…), Definitions 4.3, 4.4, p.12 (PDF p.14); p.27 (PDF p.29); p.32 (PDF p.34); p.36 (PDF p.38)

import Mathlib
import Definitions.Def_RealAPSP_Triangles
import Definitions.Def_RealAPSP_Cover

namespace RealAPSP

/-!
# Potential adjustments, potential-adjusting reductions, uniform, regular and doubling instances

Fischer, Polak, Schmidt, arXiv:2611.04847 (held file sha256 a3dc0096…), Definitions 4.3, 4.4, p.12 (PDF p.14); §7.2, p.27 (PDF p.29): "Call
an instance (A, B, C) (D, ∆)-uniform if the set X of all non-⊥ entries of A, B, and C satisfies |X|_{±∆} ≤ D."; §7.3, p.32 (PDF p.34): "Call a
matrix A (ρ, ∆)-regular if there is no x ∈ R such that there are more than ρn entries A[i, k] with A[i, k] = x ± ∆ in the same row or column of A.
We say that an instance is (ρ, ∆)-regular, if all three matrices are (ρ, ∆)-regular."; §7.4, p.36 (PDF p.38): "(K, ∆)-doubling if the set X of edge
weights in A, B, and C satisfies that |X + X|_{±∆} ≤ K|X|_{±∆}."

**Formalization Note.** A reduction's output is stored as follows.
* `outCell 0` is the length `ℓ` of the list of triples and `outCell 1` the number `M` of instances; the triples start at `outCell 2`, three cells each.
* From `outCell (2 + 3ℓ)`: for each instance `q < M` and matrix `mat`, the presence flags, row-major.
* In real cells: the potentials `u, v, w` of each instance, at `routCell (q·3n + pot·n + i)`.

So every output instance is a potential adjustment by construction, which `redInstance` makes literal: an entry is the original entry adjusted by
the stored potentials, or ⊥. The potentials in the page's reductions are integer combinations of input reals (p.26, p.33 proof), so they are stored
unscaled.
-/

/-- `(A', B', C')` is a potential adjustment of `(A, B, C)` (Definition 4.3). -/
def IsPotentialAdjustment {n : ℕ} (A B C A' B' C' : Mat ℝ n) : Prop :=
  ∃ u v w : Fin n → ℝ,
    (∀ i k, A' i k = (A i k).map (fun x => x - u i + v k) ∨ A' i k = none) ∧
    (∀ k j, B' k j = (B k j).map (fun x => x - v k + w j) ∨ B' k j = none) ∧
    (∀ i j, C' i j = (C i j).map (fun x => x + u i - w j) ∨ C' i j = none)

/-- The set `X` of all non-⊥ entries of `A`, `B`, `C`. -/
noncomputable def entrySet {n : ℕ} (A B C : Mat ℝ n) : Finset ℝ :=
  (Finset.univ : Finset (Fin n × Fin n)).biUnion fun p =>
    (A p.1 p.2).toFinset ∪ (B p.1 p.2).toFinset ∪ (C p.1 p.2).toFinset

/-- The instance is `(D, ∆)`-uniform (p.27). -/
def IsUniform {n : ℕ} (D : ℕ) (Δ : ℝ) (A B C : Mat ℝ n) : Prop :=
  coverNumber Δ (entrySet A B C) ≤ D

/-- The instance is `(K, ∆)`-doubling (p.36). -/
def IsDoubling {n : ℕ} (K Δ : ℝ) (A B C : Mat ℝ n) : Prop :=
  HasDoubling K Δ (entrySet A B C)

open Classical in
/-- The matrix is `(ρ, ∆)`-regular (p.32). -/
def IsRegularMat {n : ℕ} (ρ Δ : ℝ) (A : Mat ℝ n) : Prop :=
  ∀ x : ℝ,
    (∀ i, (((Finset.univ.filter fun k => ∃ a, A i k = some a ∧ |a - x| ≤ Δ).card : ℕ) : ℝ) ≤ ρ * n) ∧
    (∀ k, (((Finset.univ.filter fun i => ∃ a, A i k = some a ∧ |a - x| ≤ Δ).card : ℕ) : ℝ) ≤ ρ * n)

/-- The instance is `(ρ, ∆)`-regular (p.32). -/
def IsRegular {n : ℕ} (ρ Δ : ℝ) (A B C : Mat ℝ n) : Prop :=
  IsRegularMat ρ Δ A ∧ IsRegularMat ρ Δ B ∧ IsRegularMat ρ Δ C

/-- The stored presence flag of an entry of instance `q`, matrix `mat`, when the triple list has length `ℓ`. -/
def redFlag (σ : State) (n ℓ q : ℕ) (mat : Fin 3) (x y : Fin n) : Prop :=
  σ.imem (outCell (2 + 3 * ℓ + q * (3 * (n * n)) + (mat : ℕ) * (n * n) + (x : ℕ) * n + y)) = 1

/-- The stored potential number `pot` (`0`, `1`, `2` for `u`, `v`, `w`) of instance `q`. -/
noncomputable def redPot (σ : State) (n q : ℕ) (pot : Fin 3) (x : Fin n) : ℝ :=
  σ.rmem (routCell (q * (3 * n) + (pot : ℕ) * n + x))

open Classical in
/-- Output instance number `q`, as a triple of matrices: each entry is the original entry adjusted by the stored
potentials as in Definition 4.3 when its flag is set, and ⊥ otherwise. -/
noncomputable def redInstance {n : ℕ} (A B C : Mat ℝ n) (σ : State) (ℓ q : ℕ) : Mat ℝ n × Mat ℝ n × Mat ℝ n :=
  (fun i k => if redFlag σ n ℓ q 0 i k then
      (A i k).map (fun x => x - redPot σ n q 0 i + redPot σ n q 1 k) else none,
   fun k j => if redFlag σ n ℓ q 1 k j then
      (B k j).map (fun x => x - redPot σ n q 1 k + redPot σ n q 2 j) else none,
   fun i j => if redFlag σ n ℓ q 2 i j then
      (C i j).map (fun x => x + redPot σ n q 0 i - redPot σ n q 2 j) else none)

/-- The final state holds the output `(I, 𝒯)` of a `∆`-approximate potential-adjusting reduction (Definition 4.4) with `|𝒯| ≤ T`, at most
`Mmax` instances, each with property `Q`: each `∆`-approximate triangle of `(A, B, C)` is in `𝒯` or is a `∆`-approximate triangle in an instance. -/
def HasReductionOutput {n : ℕ} (Δ : ℝ) (A B C : Mat ℝ n) (T Mmax : ℝ) (Q : Mat ℝ n → Mat ℝ n → Mat ℝ n → Prop) (σ : State) : Prop :=
  let ℓ := (σ.imem (outCell 0)).toNat
  let M := (σ.imem (outCell 1)).toNat
  ((reportedTriples n σ 2 ℓ).card : ℝ) ≤ T ∧ (M : ℝ) ≤ Mmax ∧
    (∀ q < M, Q (redInstance A B C σ ℓ q).1 (redInstance A B C σ ℓ q).2.1 (redInstance A B C σ ℓ q).2.2) ∧
    ∀ i k j, IsApproxTri Δ A B C i k j →
      (i, k, j) ∈ reportedTriples n σ 2 ℓ ∨
      ∃ q < M, IsApproxTri Δ (redInstance A B C σ ℓ q).1 (redInstance A B C σ ℓ q).2.1
        (redInstance A B C σ ℓ q).2.2 i k j

/-- The cell of component `comp` of entry `(x, y)` of matrix `mat` of integer instance `q`, in the output of Lemma 4.9: `b + 2` cells per entry. -/
def intEntryCell (n base b q : ℕ) (mat : Fin 3) (x y : Fin n) (comp : ℕ) : ℕ :=
  base + ((q * 3 + (mat : ℕ)) * (n * n) + (x : ℕ) * n + y) * (b + 2) + comp

open Classical in
/-- An entry of an integer output instance of Lemma 4.9: a presence flag, then a sign and `b` bits. -/
noncomputable def intEntry (σ : State) (n base b q : ℕ) (mat : Fin 3) (x y : Fin n) : Option ℤ :=
  if σ.imem (outCell (intEntryCell n base b q mat x y 0)) = 1 then
    some (readSigned σ (intEntryCell n base b q mat x y 1) b)
  else none

end RealAPSP


