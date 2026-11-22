-- Prove2me | Definitions.Def_GirvingAKS_MGG_WalkExpansion
-- name    : GirvingAKS_MGG_WalkExpansion
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-22T18:31:23.399369+00:00
-- url     : https://prove2.me/theorems/0d1b5597-e97d-4b1d-abf8-893e5b27f7af
-- title:
--   AKS sorting networks (Seiferas port) — Walk Operator Expansion for MGG
-- statement:
--   Part of a port of the Lean development https://github.com/girving/aks (commit `c7fb62e`), which proves the Ajtai–Komlós–Szemerédi theorem: there are sorting networks of depth $O(\log n)$ and size $O(n\log n)$, following Seiferas's simplified separator-based construction (J. Seiferas, *Sorting networks of logarithmic depth, further simplified*, Algorithmica 53 (2009)). This definition bundle is the module `AKS/MGG/WalkExpansion.lean`; it contains the definitions of that module together with their supporting lemmas, so that later bundles can import them.
--
--   **Contents.** Proves `4⟨f, Wf⟩ = C₁ + C₂` where C₁, C₂ are spatial correlation sums matching the DFT correlation pairs in `DFT.lean`.
--
--   Key results:
--
--   - `sum_reindex_xy`: reindex `∑ Fin(n*n)` as `∑ Fin n × Fin n`
--   - `mgg_sum_invol`: involution pairing for MGG port pairs
--   - `mgg_walkCLM_inner_eq_corr`: the main walk expansion identity
--
--   **Formalization Note** The file was ported from Lean v4.29.0-rc4 to Lean v4.33.1 / Mathlib `0df444a`. The ported text agrees with the upstream file except for small proof repairs needed by the newer toolchain, the removal of the Lean module-system keywords, and the renaming of the upstream structure `Graph` to `HalfEdgeGraph`, which avoids a clash with Mathlib's `Graph`.
-- source:
--   https://github.com/girving/aks/blob/c7fb62ed80a4a610f87f34db0082cadbd7c00c9f/AKS/MGG/WalkExpansion.lean (ported); Seiferas, Sorting networks of logarithmic depth, further simplified, Algorithmica 53 (2009) 374–384; Ajtai, Komlós, Szemerédi, Sorting in c log n parallel steps, Combinatorica 3 (1983) 1–19

import Definitions.Def_GirvingAKS_MGG_Defs

/-! Ported to Lean v4.33.1 / Mathlib 0df444a from `AKS/MGG/WalkExpansion.lean` of
https://github.com/girving/aks (commit c7fb62ed80a4a610f87f34db0082cadbd7c00c9f, Apache-2.0). -/

/-
  # Walk Operator Expansion for MGG

  Proves `4⟨f, Wf⟩ = C₁ + C₂` where C₁, C₂ are spatial correlation sums
  matching the DFT correlation pairs in `DFT.lean`.

  Key results:
  - `sum_reindex_xy`: reindex `∑ Fin(n*n)` as `∑ Fin n × Fin n`
  - `mgg_sum_invol`: involution pairing for MGG port pairs
  - `mgg_walkCLM_inner_eq_corr`: the main walk expansion identity
-/


section

open Matrix BigOperators Finset Real

/-! **Walk operator expansion helpers** -/

/-- Reindexing: `∑ v : Fin(n*n), h v = ∑ x y : Fin n, h ⟨x*n+y, _⟩`.
    Uses `finProdFinEquiv` with a coordinate-order correction. -/
theorem sum_reindex_xy (n : ℕ) (h : Fin (n * n) → ℝ) :
    ∑ v : Fin (n * n), h v =
    ∑ x : Fin n, ∑ y : Fin n, h ⟨x.val * n + y.val, Fin.pair_lt x y⟩ := by
  rw [← finProdFinEquiv.sum_comp h, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => ?_))
  congr 1; ext; simp [finProdFinEquiv]; ring

/-- Involution pairing: for an MGG port pair `(i, j)` where the reverse port of
    `i` is always `j` and vice versa, `∑ f(v)·f(nbr(v,j)) = ∑ f(v)·f(nbr(v,i))`.
    Proof: substitute `v = nbr(u,i)` (a bijection), then `nbr(nbr(u,i),j) = u`. -/
theorem mgg_sum_invol (n : ℕ) (f : Fin (n * n) → ℝ) (i j : Fin 8)
    (hi : ∀ v : Fin (n * n), ((mgg n).rot (v, i)).2 = j)
    (hj : ∀ v : Fin (n * n), ((mgg n).rot (v, j)).2 = i) :
    ∑ v : Fin (n * n), f v * f ((mgg n).neighbor v j) =
    ∑ v : Fin (n * n), f v * f ((mgg n).neighbor v i) := by
  let e : Fin (n * n) ≃ Fin (n * n) := {
    toFun := fun v => (mgg n).neighbor v i
    invFun := fun u => (mgg n).neighbor u j
    left_inv := fun v => by
      show ((mgg n).rot (((mgg n).rot (v, i)).1, j)).1 = v
      rw [show j = ((mgg n).rot (v, i)).2 from (hi v).symm, Prod.mk.eta]
      exact congr_arg Prod.fst ((mgg n).rot_involution (v, i))
    right_inv := fun u => by
      show ((mgg n).rot (((mgg n).rot (u, j)).1, i)).1 = u
      rw [show i = ((mgg n).rot (u, j)).2 from (hj u).symm, Prod.mk.eta]
      exact congr_arg Prod.fst ((mgg n).rot_involution (u, j))
  }
  conv_lhs => rw [show (∑ v, f v * f ((mgg n).neighbor v j)) =
    ∑ v, f (e v) * f ((mgg n).neighbor (e v) j) from (e.sum_comp _).symm]
  congr 1; ext v
  show f ((mgg n).neighbor v i) * f ((mgg n).neighbor ((mgg n).neighbor v i) j) =
       f v * f ((mgg n).neighbor v i)
  have hleft := e.left_inv v
  change (mgg n).neighbor ((mgg n).neighbor v i) j = v at hleft
  rw [hleft]; ring

/-- Walk operator expansion: `4⟨f, Wf⟩ = C₁ + C₂` where C₁, C₂ are the spatial
    correlation sums matching `corr_pair1`/`corr_pair2`.

    Proof: expand `walkCLM`, reindex `Fin(n*n)` → `Fin n × Fin n`,
    expand all 8 MGG neighbors, pair each forward map T with its inverse T⁻¹
    (via `mgg_sum_invol`), giving `∑ g·g∘T + ∑ g·g∘T⁻¹ = 2·∑ g·g∘T`.
    Result: `8⟨f,Wf⟩ = 2(C₁+C₂)`, so `4⟨f,Wf⟩ = C₁+C₂`. -/
theorem mgg_walkCLM_inner_eq_corr (n : ℕ) (hn : 3 ≤ n)
    (f : EuclideanSpace ℝ (Fin (n * n))) :
    let g : Fin n → Fin n → ℝ := fun x y =>
      f ⟨x.val * n + y.val, by nlinarith [x.isLt, y.isLt]⟩
    4 * @inner ℝ _ _ f ((mgg n).walkCLM f) =
    (∑ x : Fin n, ∑ y : Fin n,
      g x y * (g ⟨(x.val + 2 * y.val) % n, Nat.mod_lt _ (by omega)⟩ y +
               g ⟨(x.val + 2 * y.val + 1) % n, Nat.mod_lt _ (by omega)⟩ y)) +
    (∑ x : Fin n, ∑ y : Fin n,
      g x y * (g x ⟨(2 * x.val + y.val) % n, Nat.mod_lt _ (by omega)⟩ +
               g x ⟨(2 * x.val + y.val + 1) % n, Nat.mod_lt _ (by omega)⟩)) := by
  intro g
  have hn0 : 0 < n := by omega
  -- Per-port neighbor sum
  let nb := fun (i : Fin 8) => ∑ v : Fin (n * n), f v * f ((mgg n).neighbor v i)
  -- Step 1: 4*inner = (1/2) * (nb0 + nb1 + ... + nb7)
  have h_lhs : 4 * @inner ℝ _ _ f ((mgg n).walkCLM f) =
      (1 / 2 : ℝ) * (nb ⟨0, by omega⟩ + nb ⟨1, by omega⟩ + nb ⟨2, by omega⟩ +
        nb ⟨3, by omega⟩ + nb ⟨4, by omega⟩ + nb ⟨5, by omega⟩ +
        nb ⟨6, by omega⟩ + nb ⟨7, by omega⟩) := by
    simp only [nb]
    rw [PiLp.inner_apply]
    simp_rw [show ∀ (a b : ℝ), @inner ℝ ℝ _ a b = b * a from fun a b => by
      show RCLike.re (b * starRingEnd ℝ a) = b * a
      simp only [RCLike.conj_to_real, RCLike.re_to_real]]
    simp only [RegularGraph.walkCLM_apply]
    have merge : ∀ (g h : Fin (n * n) → ℝ),
        (∑ v, g v) + (∑ v, h v) = ∑ v, (g v + h v) :=
      fun g h => (Finset.sum_add_distrib).symm
    rw [merge, merge, merge, merge, merge, merge, merge]
    change (4 : ℝ) * ∑ v : Fin (n * n), _ = (1 / 2 : ℝ) * ∑ v : Fin (n * n), _
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun v _ => ?_)
    simp only [Fin.sum_univ_eight, show (0 : Fin 8) = ⟨0, by omega⟩ from rfl,
      show (1 : Fin 8) = ⟨1, by omega⟩ from rfl, show (2 : Fin 8) = ⟨2, by omega⟩ from rfl,
      show (3 : Fin 8) = ⟨3, by omega⟩ from rfl, show (4 : Fin 8) = ⟨4, by omega⟩ from rfl,
      show (5 : Fin 8) = ⟨5, by omega⟩ from rfl, show (6 : Fin 8) = ⟨6, by omega⟩ from rfl,
      show (7 : Fin 8) = ⟨7, by omega⟩ from rfl]
    ring
  -- Step 2: Port pairing via involution
  have hrev : ∀ (k : Fin 4), ∀ v : Fin (n * n),
      ((mgg n).rot (v, ⟨2 * k.val, by omega⟩)).2 = ⟨2 * k.val + 1, by omega⟩ ∧
      ((mgg n).rot (v, ⟨2 * k.val + 1, by omega⟩)).2 = ⟨2 * k.val, by omega⟩ := by
    intro k v; fin_cases k <;>
      exact ⟨by simp [mgg, mgg_rot, mggNbr], by simp [mgg, mgg_rot, mggNbr]⟩
  have h01 : nb ⟨1, by omega⟩ = nb ⟨0, by omega⟩ :=
    mgg_sum_invol n f ⟨0, by omega⟩ ⟨1, by omega⟩
      (fun v => (hrev ⟨0, by omega⟩ v).1) (fun v => (hrev ⟨0, by omega⟩ v).2)
  have h23 : nb ⟨3, by omega⟩ = nb ⟨2, by omega⟩ :=
    mgg_sum_invol n f ⟨2, by omega⟩ ⟨3, by omega⟩
      (fun v => (hrev ⟨1, by omega⟩ v).1) (fun v => (hrev ⟨1, by omega⟩ v).2)
  have h45 : nb ⟨5, by omega⟩ = nb ⟨4, by omega⟩ :=
    mgg_sum_invol n f ⟨4, by omega⟩ ⟨5, by omega⟩
      (fun v => (hrev ⟨2, by omega⟩ v).1) (fun v => (hrev ⟨2, by omega⟩ v).2)
  have h67 : nb ⟨7, by omega⟩ = nb ⟨6, by omega⟩ :=
    mgg_sum_invol n f ⟨6, by omega⟩ ⟨7, by omega⟩
      (fun v => (hrev ⟨3, by omega⟩ v).1) (fun v => (hrev ⟨3, by omega⟩ v).2)
  -- Step 3: Simplify to nb0 + nb2 + nb4 + nb6 = C₁ + C₂
  rw [h_lhs, h01, h23, h45, h67]
  suffices h04 : nb ⟨0, by omega⟩ + nb ⟨4, by omega⟩ =
      ∑ x : Fin n, ∑ y : Fin n,
        g x y * (g ⟨(x.val + 2 * y.val) % n, Nat.mod_lt _ (by omega)⟩ y +
                 g ⟨(x.val + 2 * y.val + 1) % n, Nat.mod_lt _ (by omega)⟩ y) by
    suffices h26 : nb ⟨2, by omega⟩ + nb ⟨6, by omega⟩ =
        ∑ x : Fin n, ∑ y : Fin n,
          g x y * (g x ⟨(2 * x.val + y.val) % n, Nat.mod_lt _ (by omega)⟩ +
                   g x ⟨(2 * x.val + y.val + 1) % n, Nat.mod_lt _ (by omega)⟩) by
      linarith
    -- nb2 + nb6 = C₂: reindex + expand ports 2 and 6
    simp only [nb, ← Finset.sum_add_distrib, sum_reindex_xy n]
    refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => ?_))
    have h2 : (mgg n).neighbor ⟨x.val * n + y.val, Fin.pair_lt x y⟩ ⟨2, by omega⟩ =
        ⟨x.val * n + (2 * x.val + y.val) % n,
         Fin.pair_lt x ⟨_, Nat.mod_lt _ hn0⟩⟩ := by
      ext; simp only [RegularGraph.neighbor, mgg, mgg_rot, mggNbr,
        encode_div x.val y.val n y.isLt, encode_mod x.val y.val n y.isLt]
    have h6 : (mgg n).neighbor ⟨x.val * n + y.val, Fin.pair_lt x y⟩ ⟨6, by omega⟩ =
        ⟨x.val * n + (2 * x.val + y.val + 1) % n,
         Fin.pair_lt x ⟨_, Nat.mod_lt _ hn0⟩⟩ := by
      ext; simp only [RegularGraph.neighbor, mgg, mgg_rot, mggNbr,
        encode_div x.val y.val n y.isLt, encode_mod x.val y.val n y.isLt]
    simp only [h2, h6, mul_add, g]
  -- nb0 + nb4 = C₁: reindex + expand ports 0 and 4
  simp only [nb, ← Finset.sum_add_distrib, sum_reindex_xy n]
  refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => ?_))
  have h0 : (mgg n).neighbor ⟨x.val * n + y.val, Fin.pair_lt x y⟩ ⟨0, by omega⟩ =
      ⟨(x.val + 2 * y.val) % n * n + y.val,
       Fin.pair_lt ⟨_, Nat.mod_lt _ hn0⟩ y⟩ := by
    ext; simp only [RegularGraph.neighbor, mgg, mgg_rot, mggNbr,
      encode_div x.val y.val n y.isLt, encode_mod x.val y.val n y.isLt]
  have h4 : (mgg n).neighbor ⟨x.val * n + y.val, Fin.pair_lt x y⟩ ⟨4, by omega⟩ =
      ⟨(x.val + 2 * y.val + 1) % n * n + y.val,
       Fin.pair_lt ⟨_, Nat.mod_lt _ hn0⟩ y⟩ := by
    ext; simp only [RegularGraph.neighbor, mgg, mgg_rot, mggNbr,
      encode_div x.val y.val n y.isLt, encode_mod x.val y.val n y.isLt]
  simp only [h0, h4, mul_add, g]

end


