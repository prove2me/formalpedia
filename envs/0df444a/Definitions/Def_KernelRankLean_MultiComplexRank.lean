-- Prove2me | Definitions.Def_KernelRankLean_MultiComplexRank
-- name    : KernelRankLean_MultiComplexRank
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-23T02:07:16.604714+00:00
-- url     : https://prove2.me/theorems/89ec8232-f2fc-4252-b885-15986a20f6d1
-- title:
--   Multi Complex Rank
-- statement:
--   Definitions and structural lemmas for Multi Complex Rank, from Olli Niemitalo's pinned Finite separable rank of radial kernels development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/MultiComplexRank.lean

import Definitions.Def_KernelRankLean_ComplexRank
set_option autoImplicit true
open Complex Polynomial NNReal
namespace KernelRank
noncomputable def truncExpPoly (k : ℕ) (u : ℂ) : ℂ[X] :=
  ∑ q ∈ Finset.range (k + 1), C (u ^ q / (q.factorial : ℂ)) * X ^ q
noncomputable def revHassePoly (P : ℂ[X]) (k : ℕ) (u : ℂ) : ℂ[X] :=
  ∑ q ∈ Finset.range (k + 1),
    C ((q.factorial : ℂ) * (hasseDeriv q P).eval u) * X ^ (k - q)
abbrev CoeffSpace {ι : Type*} (m₀ : ι → ℕ) : Type _ :=
  ∀ i : ι, Fin (m₀ i) → ℂ
noncomputable def singleCoeff {ι : Type*} [DecidableEq ι] {m₀ : ι → ℕ}
    (i₀ : ι) (q₀ : Fin (m₀ i₀)) (z : ℂ) : CoeffSpace m₀ :=
  fun i q => if h : i = i₀ then if (h ▸ q) = q₀ then z else 0 else 0
noncomputable def truncForm {ι : Type*} [Fintype ι] (d : ℕ) (m₀ c : ι → ℕ)
    (w : ι → ℕ → ℂ) (u : Fin d → ∀ i, Fin (m₀ i) → ℂ) : ℂ :=
  ∑ i : ι, ∑ q ∈ Finset.univ.filter (fun q : Fin d → Fin (m₀ i) => ∑ j, (q j : ℕ) < c i),
    w i (∑ j, (q j : ℕ)) * ∏ j : Fin d, u j i (q j)
def projCoeff {ι : Type*} {m₀ : ι → ℕ} (i : ι) (q : Fin (m₀ i)) : CoeffSpace m₀ →ₗ[ℂ] ℂ where
  toFun x := x i q
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
noncomputable def truncMultilinearMap {ι : Type*} [Fintype ι] (d : ℕ) (m₀ c : ι → ℕ)
    (w : ι → ℕ → ℂ) : MultilinearMap ℂ (fun _ : Fin d => CoeffSpace m₀) ℂ :=
  ∑ i : ι, ∑ q ∈ Finset.univ.filter (fun q : Fin d → Fin (m₀ i) => ∑ j, (q j : ℕ) < c i),
    w i (∑ j, (q j : ℕ)) •
      (MultilinearMap.mkPiAlgebra ℂ (Fin d) ℂ).compLinearMap (fun j => projCoeff i (q j))
end KernelRank


