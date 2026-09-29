-- Prove2me | Definitions.Def_mme_omega_pos
-- name    : mme_omega_pos
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-05-29T15:39:05.572023+00:00
-- url     : https://prove2.me/theorems/fbce3188-5705-4afd-b204-e2c4dfcb770d
-- statement:
--   **Strict positivity of the matrix-multiplication exponent (Strassen form).**
--
--   `matMulExp_strassen_pos : 0 < \mathrm{matMulExp\_strassen}\,K`, plus the sharper `one_le_matMulExp_strassen : 1 \leq \mathrm{matMulExp\_strassen}\,K`.
--
--   **The lower bound.** For every $n \geq 2$, the matrix-multiplication tensor $\langle n, n, n\rangle = \mathrm{MMTensor}\,n\,n\,n$ admits a restriction *from* the diagonal $I_n = \mathrm{diagObj}\,K\,3\,n$: pick out the diagonal entries of each mode, sending $e_{ii} \otimes e_{ii} \otimes e_{ii}$ to the $i$-th summand of the diagonal. Restrictions in this direction (diagonal $\leq$ MM-tensor) cannot increase the **flattening rank** (`Def_mme_flattening`'s `flatteningRank_mono`), and the flattening rank of $I_n$ is exactly $n$. Hence $\mathrm{strassenRank}(\mathrm{MMTensor}\,n\,n\,n) \geq n$.
--
--   **Combining.** $\log_n(\mathrm{strassenRank}(\mathrm{MMTensor}\,n\,n\,n)) / \log n \geq \log n / \log n = 1$ for $n \geq 2$. The fallback `else 3` branch of $\mathrm{matMulExp\_strassen}$ (the value on $n \leq 1$ that keeps the definition total) is $3 \geq 1$. Hence every term of the defining $\inf$ is $\geq 1$, so $\mathrm{matMulExp\_strassen}\,K \geq 1 > 0$.
--
--   **Where used.** `matMulExp_strassen_pos` is the side condition powering the `Real.zero_rpow` rewrite in the τ-theorem's zero-dimension reduction (`sketch_mme_sum_inequality`): for $i$ with $n_i m_i p_i = 0$, the summand $(n_i m_i p_i)^{\omega/3} = 0$ only when $\omega/3 \neq 0$. Surfaced as a citable Theorem node `mme_matMulExp_strassen_pos`.

import Mathlib.LinearAlgebra.PiTensorProduct.Basic
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.Lattice.Nat
import Mathlib.Order.ConditionallyCompleteLattice.Indexed
import Definitions.Def_mme_omega
import Definitions.Def_mme_omega_strassen
import Definitions.Def_mme_tensor
import Definitions.Def_mme_tensor_rank
import Definitions.Def_mme_flattening

/-! # Positivity of the matrix-multiplication exponent ω (Strassen form)

The main result of this file is

  `matMulExp_strassen_pos : 0 < matMulExp_strassen K`,

the positivity of the matrix-multiplication exponent in its Strassen form.

The clean route is the lower bound `n ≤ strassenRank (MMTensor K n n n)`. The matrix
multiplication tensor `MM(n,n,n)` restricts FROM the diagonal `I_n = diagObj K 3 n`
(extract the diagonal entries of each mode), so its restriction rank dominates `n` by the
flattening lower bound: flattening rank is monotone under restriction and equals `n` on the
diagonal. Then for `n ≥ 2`,

  `log (strassenRank (MM n n n)) / log n ≥ log n / log n = 1`,

and the `else 3` branch is `3 ≥ 1`, so every term of the defining `⨅` is `≥ 1`, whence
`1 ≤ matMulExp_strassen K` and in particular `0 < matMulExp_strassen K`.

We also attempt a normalization lemma relating `matMulExp_strassen K` to a fixed MM tensor's
asymptotic rank; see the note at the end of the file. -/

universe u

open PiTensorProduct TensorProduct BigOperators Module

namespace MME

variable {K : Type u} [Field K]

/-! ## The diagonal restricts from `MM(n,n,n)`

`diagObj K 3 n` is a restriction of `MMObj K n n n`: applying the mode-wise diagonal
projection `v ↦ (l ↦ v (l, l))` to `MM(n,n,n) = ∑_{i,j,k} e_{ij} ⊗ e_{jk} ⊗ e_{ki}` keeps
only the terms with `i = j = k`, producing `∑_l e_l ⊗ e_l ⊗ e_l = (diagObj 3 n).t`. -/

/-- The mode-wise diagonal projection `(Fin n × Fin n → K) →ₗ[K] (Fin n → K)`,
`v ↦ (l ↦ v (l, l))`. -/
private noncomputable def diagProj (n : ℕ) : (Fin n × Fin n → K) →ₗ[K] (Fin n → K) :=
  LinearMap.funLeft K K (fun l : Fin n => (l, l))

/-- The diagonal projection sends the standard basis vector `e_{(a,b)}` to `e_a` if `a = b`
and to `0` otherwise. -/
private theorem diagProj_single (n : ℕ) (a b : Fin n) :
    diagProj (K := K) n (Pi.single (a, b) 1) =
      if a = b then (Pi.single a 1 : Fin n → K) else 0 := by
  funext l
  rw [diagProj, LinearMap.funLeft_apply]
  by_cases hab : a = b
  · subst hab
    rw [if_pos rfl]
    simp only [Pi.single_apply, Prod.mk.injEq, and_self]
  · rw [if_neg hab, Pi.zero_apply]
    rw [Pi.single_apply]
    rw [if_neg]
    intro h
    rw [Prod.mk.injEq] at h
    exact hab (h.1.symm.trans h.2)

/-- `diagObj K 3 n` is a restriction of `MMObj K n n n`. -/
theorem diagObj_restrict_MMObj (n : ℕ) :
    TensorObj.Restrict (TensorObj.diagObj K 3 n) (MMObj K n n n) := by
  -- mode-wise diagonal projection on each of the three modes
  refine ⟨fun (s : Fin 3) =>
    match s with
    | ⟨0, _⟩ => diagProj (K := K) n
    | ⟨1, _⟩ => diagProj (K := K) n
    | ⟨2, _⟩ => diagProj (K := K) n, ?_⟩
  -- restate the goal with the module families spelled out (`MMSpace` / `Fin n → K`) so that
  -- `map_tprod` can fire syntactically on the pure terms
  show PiTensorProduct.map (s := MMSpace K n n n) (t := fun _ : Fin 3 => Fin n → K)
    (fun (s : Fin 3) =>
      match s with
      | ⟨0, _⟩ => diagProj (K := K) n
      | ⟨1, _⟩ => diagProj (K := K) n
      | ⟨2, _⟩ => diagProj (K := K) n) (MMTensor K n n n) =
    ∑ j : Fin n, tprod K (fun _ : Fin 3 => (Pi.single j 1 : Fin n → K))
  rw [MMTensor]
  -- push `map` through the triple sum and apply `map_tprod` to every pure term
  simp only [map_sum, PiTensorProduct.map_tprod]
  -- the pure diagonal tensor `e_l ⊗ e_l ⊗ e_l` of `diagObj K 3 n`
  set e : Fin n → PiTensorProduct K (fun _ : Fin 3 => Fin n → K) :=
    fun l => tprod K (fun _ => (Pi.single l 1 : Fin n → K)) with he
  -- rewrite the body of the triple sum to the collapsed `if` form: each mapped pure term
  -- reduces to `if i = j ∧ j = k then e i else 0` (only `i = j = k` survives, where all
  -- three diagonal projections agree). We work directly on the goal's term via `refine`,
  -- so the `match` motives match definitionally.
  trans (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n, (if i = j ∧ j = k then e i else 0))
  · refine Finset.sum_congr rfl (fun i _ =>
      Finset.sum_congr rfl (fun j _ =>
        Finset.sum_congr rfl (fun k _ => ?_)))
    by_cases hij : i = j
    · by_cases hjk : j = k
      · -- i = j = k: all three factors are `e_i`
        have hki : k = i := by rw [← hjk, ← hij]
        rw [if_pos (show i = j ∧ j = k from ⟨hij, hjk⟩), he]
        congr 1
        funext s
        fin_cases s <;> dsimp only
        · exact (diagProj_single n i j).trans (if_pos hij)
        · exact (diagProj_single n j k).trans ((if_pos hjk).trans (by rw [hij]))
        · exact (diagProj_single n k i).trans ((if_pos hki).trans (by rw [hki, hij, hjk]))
      · -- j ≠ k: the middle factor vanishes
        rw [if_neg (show ¬(i = j ∧ j = k) by rintro ⟨_, h⟩; exact hjk h)]
        refine MultilinearMap.map_coord_zero (tprod K) (1 : Fin 3) ?_
        dsimp only
        exact (diagProj_single n j k).trans (if_neg hjk)
    · -- i ≠ j: the first factor vanishes
      rw [if_neg (show ¬(i = j ∧ j = k) by rintro ⟨h, _⟩; exact hij h)]
      refine MultilinearMap.map_coord_zero (tprod K) (0 : Fin 3) ?_
      dsimp only
      exact (diagProj_single n i j).trans (if_neg hij)
  -- collapse the triple sum: only `i = j = k` terms remain
  have hcollapse : (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
        (if i = j ∧ j = k then e i else 0)) = ∑ l : Fin n, e l := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.sum_eq_single i]
    · rw [Finset.sum_eq_single i]
      · rw [if_pos (show i = i ∧ i = i from ⟨rfl, rfl⟩)]
      · intro k _ hki; rw [if_neg (by rintro ⟨_, h⟩; exact hki h.symm)]
      · intro h; exact absurd (Finset.mem_univ i) h
    · intro j _ hji
      refine Finset.sum_eq_zero (fun k _ => ?_)
      rw [if_neg (by rintro ⟨h, _⟩; exact hji h.symm)]
    · intro h; exact absurd (Finset.mem_univ i) h
  refine hcollapse.trans ?_
  rw [he]

/-! ## The flattening lower bound on `MM(n,n,n)`

Flattening rank is monotone under restriction, and the diagonal `diagObj K 3 n` has
flattening rank `n`. Since `diagObj K 3 n` restricts from `MMObj K n n n`, we get
`n ≤ flatteningRank σ (MMObj K n n n)`. -/

/-- The flattening rank of `MM(n,n,n)` along the split `{0} | {1,2}` is at least `n`. -/
theorem n_le_flatteningRank_MMObj (n : ℕ) :
    n ≤ flatteningRank (diagSplit (d := 3) (by norm_num)) (MMObj K n n n) := by
  have hmono := flatteningRank_mono (diagSplit (d := 3) (by norm_num))
    (diagObj_restrict_MMObj (K := K) n)
  rwa [flatteningRank_diag] at hmono

/-! ## The lower bound `n ≤ strassenRank (MM(n,n,n))`

If `MM(n,n,n)` restricts to the diagonal `diagTensor K 3 r`, then equivalently
`MMObj K n n n` restricts to `diagObj K 3 r` (definitionally the same data), so the
flattening rank cannot increase: `n ≤ flatteningRank (MMObj n n n) ≤ flatteningRank
(diagObj 3 r) = r`. Hence `n` is a lower bound for the `sInf` defining `strassenRank`. -/

/-- Any raw tensor that is a sum of `r` pure tensors restricts from the diagonal
`diagTensor K d r` (the decomposition ⇒ restriction direction; cf. the witness-set
identity used by `tensorRank = strassenRank`). -/
private theorem restrict_diagTensor_of_sum
    {d : ℕ} {V : Fin d → Type u} [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    {T : PiTensorProduct K V} {r : ℕ} (g : Fin r → ∀ i, V i)
    (hT : T = ∑ j, tprod K (g j)) :
    Restrict T (diagTensor K d r) := by
  refine ⟨fun i => ∑ j : Fin r,
    LinearMap.smulRight (LinearMap.proj j : (Fin r → K) →ₗ[K] K) (g j i), ?_⟩
  have hf_eval : ∀ (i : Fin d) (k : Fin r),
      (∑ j : Fin r, LinearMap.smulRight (LinearMap.proj j : (Fin r → K) →ₗ[K] K) (g j i))
        (Pi.single k (1 : K)) = g k i := by
    intro i k
    simp only [LinearMap.coe_sum, Finset.sum_apply, LinearMap.smulRight_apply,
      LinearMap.proj_apply]
    rw [Finset.sum_eq_single_of_mem k (Finset.mem_univ k)
      (fun j _ hjk => by rw [Pi.single_eq_of_ne hjk, zero_smul])]
    simp
  rw [diagTensor, map_sum]
  rw [show (∑ j : Fin r, PiTensorProduct.map
      (fun i => ∑ j' : Fin r, LinearMap.smulRight (LinearMap.proj j' :
        (Fin r → K) →ₗ[K] K) (g j' i)) (tprod K (fun _ => (Pi.single j 1 : Fin r → K))))
      = ∑ j : Fin r, tprod K (g j) from ?_]
  · exact hT.symm
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [PiTensorProduct.map_tprod]
  congr 1
  funext i
  exact hf_eval i j

/-- The Strassen rank of the matrix-multiplication tensor `MM(n,n,n)` is at least `n`. -/
theorem n_le_strassenRank_MMTensor (n : ℕ) :
    n ≤ strassenRank (MMTensor K n n n) := by
  -- it suffices that `n` lower-bounds every member of the defining set
  unfold strassenRank
  refine le_csInf ?_ ?_
  · -- the set is nonempty: `MMTensor n n n` is a sum of `n*n*n` pure tensors.
    -- It suffices to produce *some* `r` with a pure-tensor decomposition; we pick
    -- `r = n*n*n` and the `g` obtained by reindexing the triple sum.
    refine ⟨n * n * n, ?_⟩
    -- the reindexing equiv `Fin (n*n*n) ≃ (Fin n × Fin n) × Fin n` (left-associated, the
    -- shape produced by collapsing `∑ i, ∑ j, ∑ k` via `Finset.sum_product'`)
    let e : Fin (n * n * n) ≃ (Fin n × Fin n) × Fin n :=
      finProdFinEquiv.symm.trans (Equiv.prodCongr finProdFinEquiv.symm (Equiv.refl _))
    -- the family of pure tensors, indexed by `(Fin n × Fin n) × Fin n`
    let F : (Fin n × Fin n) × Fin n → ∀ i : Fin 3, MMSpace K n n n i :=
      fun idx s =>
        match s with
        | ⟨0, _⟩ => (Pi.single (idx.1.1, idx.1.2) 1 : Fin n × Fin n → K)
        | ⟨1, _⟩ => (Pi.single (idx.1.2, idx.2) 1 : Fin n × Fin n → K)
        | ⟨2, _⟩ => (Pi.single (idx.2, idx.1.1) 1 : Fin n × Fin n → K)
    refine restrict_diagTensor_of_sum (fun idx => F (e idx)) ?_
    -- `∑ idx, tprod (F (e idx)) = ∑ p, tprod (F p)` by reindexing, and the latter is `MMTensor`
    rw [Equiv.sum_comp e (fun p => tprod K (F p))]
    rw [MMTensor]
    -- collapse the triple sum into a sum over `(Fin n × Fin n) × Fin n`
    rw [← Finset.sum_product', ← Finset.sum_product', Finset.univ_product_univ,
      Finset.univ_product_univ]
    rfl
  · -- every `r` with `Restrict (MMTensor n n n) (diagTensor 3 r)` satisfies `n ≤ r`
    intro r hr
    -- transfer the raw-tensor restriction to a `TensorObj.Restrict`
    have hr' : TensorObj.Restrict (MMObj K n n n) (TensorObj.diagObj K 3 r) := hr
    -- flattening rank is monotone and pins both ends
    have hmono := flatteningRank_mono (diagSplit (d := 3) (by norm_num)) hr'
    rw [flatteningRank_diag] at hmono
    exact (n_le_flatteningRank_MMObj n).trans hmono

/-! ## Positivity of ω (Strassen form)

For `1 < n`, `log (strassenRank (MM n n n)) / log n ≥ log n / log n = 1`; the `else 3`
branch is `3 ≥ 1`. So every term of the defining `⨅` is `≥ 1`, hence
`1 ≤ matMulExp_strassen K`, in particular `0 < matMulExp_strassen K`. -/

/-- Every term of the family defining `matMulExp_strassen` is at least `1`. -/
private theorem one_le_matMulExp_strassen_term (n : ℕ) :
    (1 : ℝ) ≤ (if 1 < n then
      Real.log (strassenRank (MMTensor K n n n) : ℝ) / Real.log n else 3) := by
  split_ifs with hn
  · -- `1 < n`: `log (strassenRank) / log n ≥ log n / log n = 1`
    have hn1 : (1 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hlogn_pos : 0 < Real.log n := Real.log_pos hn1
    rw [le_div_iff₀ hlogn_pos, one_mul]
    -- `log n ≤ log (strassenRank)` since `n ≤ strassenRank` and `n > 0`
    apply Real.log_le_log (by exact_mod_cast (by omega : 0 < n))
    exact_mod_cast n_le_strassenRank_MMTensor (K := K) n
  · norm_num

/-- **`1 ≤ matMulExp_strassen K`.** The `⨅` of a family bounded below by `1` is `≥ 1`. -/
theorem one_le_matMulExp_strassen : (1 : ℝ) ≤ matMulExp_strassen K := by
  rw [matMulExp_strassen]
  exact le_ciInf (fun n => one_le_matMulExp_strassen_term (K := K) n)

/-- **PRIMARY RESULT.** The Strassen-form matrix-multiplication exponent ω is positive. -/
theorem matMulExp_strassen_pos : 0 < matMulExp_strassen K :=
  lt_of_lt_of_le one_pos (one_le_matMulExp_strassen (K := K))

-- The ω normalization `matMulExp_strassen = log₂ (tensorAsymptoticRank (MMObj 2 2 2))`
-- is proved sorry-free in `Def_mme_omega_normalize.lean` (`matMulExp_strassen_eq_log_AR`),
-- which is import-clean (no `Def_mme_tensor_bridge`). It is not restated here.

end MME


