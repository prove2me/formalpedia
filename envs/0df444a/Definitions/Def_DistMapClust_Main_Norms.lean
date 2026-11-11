-- Prove2me | Definitions.Def_DistMapClust_Main_Norms
-- name    : DistMapClust_Main_Norms
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T03:04:10.608744+00:00
-- url     : https://prove2.me/theorems/9811f7e2-3e6c-4dce-8eee-31b2f9931cc3
-- title:
--   Monotone and column-symmetric norms on nonnegative matrices, weight vectors, ordered and row-wise ordered norms
-- statement:
--   A **monotone norm** on the nonnegative orthant $\mathbb R^m_{\ge 0}$ is a function $f:\mathbb R^m_{\ge0}\to\mathbb R_{\ge0}$ that is definite ($f(v)=0\Rightarrow v=0$), positively homogeneous ($f(av)=af(v)$ for $a\ge0$), subadditive and monotone ($v\le w$ entrywise implies $f(v)\le f(w)$); only nonnegative arguments are ever used. A norm on $d\times n$ matrices treats a matrix as a $dn$-vector. It is **column-symmetric** if $f(M^{(\pi)})=f(M)$ for every nonnegative $M$ and every permutation $\pi$ of the columns, where $M^{(\pi)}_{i,j}=M_{i,\pi(j)}$.
--
--   A **weight vector** $w\in\mathbb R^n_{\ge0}$ is nonzero with $w_1\ge\dots\ge w_n$. For $v\in\mathbb R^n$, $v^{\downarrow}$ is $v$ sorted non-increasingly, and the **ordered norm** is
--   $$\mathrm{ord}_w(v)=\sum_{i=1}^n w_i\,v^{\downarrow}_i .$$
--   A norm on $d\times n$ matrices is **row-wise ordered** if it is $M\mapsto f'(\mathrm{ord}_{w_1}(M_1),\dots,\mathrm{ord}_{w_d}(M_d))$ for weight vectors $w_1,\dots,w_d$ and a monotone norm $f'$ on $\mathbb R^d_{\ge0}$, $M_i$ the $i$-th row. These are the objectives of the mission's goal.
--
--   **Formalization Note.** `IsMonotoneNorm` (on `ι → ℝ`, `ι` finite), `Mat d n = Fin d → Fin n → ℝ` (row first), `IsMonotoneMatrixNorm`, `IsColumnSymmetric`, `IsWeightVector`, `sortDesc` (via `Tuple.sort` reversed), `ordNorm`, `rowOrdNorm W f'`. No continuity or normalization is required.
-- source:
--   Herold, Spoerhase, Kipouridis, Marx, A Unified Framework for Parameterized Approximation of Clustering Objectives via Distance Mappings, STOC 2027 submission (manuscript sha256 1d00c842…), p. 3 (footnote 4), p. 8 (§1.2), p. 21 (§2.2), p. 46 (§4)

import Mathlib

/-!
# Monotone norms on nonnegative orthants, column symmetry, ordered and row-wise ordered norms

Herold, Spoerhase, Kipouridis, Marx, *A Unified Framework for Parameterized Approximation of
Clustering Objectives via Distance Mappings*, STOC 2027 submission (manuscript sha256 1d00c842…):
§1.1 footnote 4 (p. 3), §1.2 (p. 8), §2.2 (p. 21), §4 (p. 46).

* A norm in the paper is a map `f : ℝ^m_{≥0} → ℝ_{≥0}` (here `m` is a finite index type `ι`): it is
  only ever evaluated on nonnegative vectors, so every clause below quantifies over nonnegative
  arguments only. There is no continuity or normalization requirement.
* A `d × n` matrix is `Mat d n = Fin d → Fin n → ℝ` (row index first, `Fin` indices are 0-based where
  the paper writes `[d]`, `[n]`). The norm of a matrix treats it as a `dn`-vector.
* `sortDesc v` is `v↓`, the vector `v` sorted non-increasingly; `ordNorm w v = ∑ᵢ wᵢ · v↓ᵢ`.
* `rowOrdNorm W f' M = f'(ord_{W 0}(M 0), …, ord_{W (d-1)}(M (d-1)))`, a row-wise ordered norm given by
  its weight vectors `W` and its outer monotone norm `f'` (§4, p. 46).
-/

namespace DistMapClust.Main

/-- `f` is a monotone norm on the nonnegative orthant of `ι → ℝ`: nonnegative, definite,
positively homogeneous, subadditive and monotone, each clause on nonnegative vectors. -/
def IsMonotoneNorm {ι : Type} [Fintype ι] (f : (ι → ℝ) → ℝ) : Prop :=
  (∀ v : ι → ℝ, 0 ≤ v → 0 ≤ f v) ∧
  (∀ v : ι → ℝ, 0 ≤ v → f v = 0 → v = 0) ∧
  (∀ (a : ℝ) (v : ι → ℝ), 0 ≤ a → 0 ≤ v → f (a • v) = a * f v) ∧
  (∀ v w : ι → ℝ, 0 ≤ v → 0 ≤ w → f (v + w) ≤ f v + f w) ∧
  (∀ v w : ι → ℝ, 0 ≤ v → v ≤ w → f v ≤ f w)

/-- Real `d × n` matrices, row index first. -/
abbrev Mat (d n : ℕ) := Fin d → Fin n → ℝ

/-- `f` is a monotone norm on nonnegative `d × n` matrices, viewed as `dn`-vectors. -/
def IsMonotoneMatrixNorm {d n : ℕ} (f : Mat d n → ℝ) : Prop :=
  IsMonotoneNorm (fun v : Fin d × Fin n → ℝ => f (fun i j => v (i, j)))

/-- Column symmetry (§2.2): `f(M) = f(M(π))` for every nonnegative `M` and every permutation `π` of
the columns, where `M(π)_{i,j} = M_{i,π(j)}`. -/
def IsColumnSymmetric {d n : ℕ} (f : Mat d n → ℝ) : Prop :=
  ∀ M : Mat d n, 0 ≤ M → ∀ π : Equiv.Perm (Fin n), f (fun i j => M i (π j)) = f M

/-- A weight vector (§2.2): nonnegative, nonzero, sorted non-increasingly. -/
def IsWeightVector {n : ℕ} (w : Fin n → ℝ) : Prop :=
  0 ≤ w ∧ w ≠ 0 ∧ Antitone w

/-- `v↓`: the coordinates of `v` sorted non-increasingly (`Tuple.sort` sorts increasingly). -/
noncomputable def sortDesc {n : ℕ} (v : Fin n → ℝ) : Fin n → ℝ :=
  fun i => v (Tuple.sort v (Fin.rev i))

/-- The ordered norm `ord_w(v) = ∑ᵢ wᵢ · v↓ᵢ` (§2.2). -/
noncomputable def ordNorm {n : ℕ} (w v : Fin n → ℝ) : ℝ :=
  ∑ i, w i * sortDesc v i

/-- The row-wise ordered norm with weight vectors `W` and outer norm `f'`:
`M ↦ f'((ord_{W i}(row i of M))_{i})` (§1.2 p. 8, §4 p. 46). -/
noncomputable def rowOrdNorm {d n : ℕ} (W : Fin d → Fin n → ℝ) (f' : (Fin d → ℝ) → ℝ)
    (M : Mat d n) : ℝ :=
  f' (fun i => ordNorm (W i) (M i))

end DistMapClust.Main


