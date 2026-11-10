-- Prove2me | Definitions.Def_TensorRankN2M_ThreeTwoM_SkewAugmentation
-- name    : TensorRankN2M_ThreeTwoM_SkewAugmentation
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T04:15:40.071917+00:00
-- url     : https://prove2.me/theorems/bf3f6921-75d0-4670-9e39-b4907860ef64
-- title:
--   Alternating arrays V^{∧d} and the skew augmentation h of a linear map ℓ : V^d → Y (§4)
-- statement:
--   Let $V$ and $Y$ be vector spaces over a field $\mathbb F$ and let $\iota$ be an index set (in the paper $\iota=\{1,\dots,d\}$). The space of **alternating arrays** is
--   $$V^{\wedge\iota}=\{c\in V^{\iota\times\iota}: c_{i,i}=0,\ c_{j,i}=-c_{i,j}\ \ \forall i,j\in\iota\}.$$
--   Both conditions are imposed, so the diagonal vanishes also in characteristic $2$. For a linear map $\ell:V^\iota\to Y$, its **skew augmentation** is the linear map
--   $$h:V^{\wedge\iota}\to Y^\iota,\qquad h(c)=(\ell(c_{i,:}))_{i\in\iota},$$
--   where $c_{i,:}\in V^\iota$ is the $i$-th row of $c$.
--
--   The skew augmentation appears in the $\langle n,2,m\rangle$ lower-bound argument, where the rank of $h$ must be bounded below in terms of the rank of $\ell$ (Lemma 11).
--
--   **Formalization Note.** `SkewArrays 𝔽 V ι` is a submodule of `ι → ι → V`, and `skewAug ℓ : SkewArrays 𝔽 V ι →ₗ[𝔽] (ι → Y)` sends $c$ to $i\mapsto \ell(c\,i)$. Lemma 11 uses $\iota=$ `Fin d` (0-based indices); the $\langle n,2,m\rangle$ maps use $\iota=\{1,\dots,n-1\}$.
-- source:
--   Jason Yang, New lower bounds on tensor rank of (n,2,m) matrix multiplication with GPT-6 Astra, STOC 2027 submission (manuscript of October 2026, sha256 6c1df229…), p. 5, §4 (U^{∧d}, h) and Lemma 11

import Mathlib

/-!
# Alternating arrays `V^{∧d}` and the skew augmentation of a linear map

Jason Yang, *New lower bounds on tensor rank of (n,2,m) matrix multiplication with GPT-6 Astra*,
STOC 2027 submission (manuscript of October 2026), p. 5, §4 and Lemma 11.

* `SkewArrays 𝔽 V ι` is `V^{∧d}` for the index set `ι` (`ι = Fin d` in Lemma 11): the arrays
  `c : ι → ι → V` with `c i i = 0` and `c j i = -c i j` for all `i, j` (both conditions, so the
  arrays are alternating also in characteristic 2).
* `skewAug ℓ` is the skew augmentation `h(c) = (ℓ(c_{1,:}), …, ℓ(c_{d,:}))` of a linear map
  `ℓ : V^ι → Y`, where `c_{i,:} = c i` is the `i`-th row of `c`.
-/

namespace TensorRankN2M.ThreeTwoM

/-- `V^{∧ι}`: the arrays `c ∈ V^{ι×ι}` with `c_{i,i} = 0` and `c_{j,i} = -c_{i,j}` for all
`i, j` (p. 5). -/
def SkewArrays (𝔽 V ι : Type*) [Field 𝔽] [AddCommGroup V] [Module 𝔽 V] :
    Submodule 𝔽 (ι → ι → V) where
  carrier := {c | (∀ i, c i i = 0) ∧ ∀ i j, c j i = -c i j}
  zero_mem' := by simp
  add_mem' := by
    rintro c c' ⟨hc0, hc⟩ ⟨hc0', hc'⟩
    refine ⟨fun i => by simp [hc0, hc0'], fun i j => ?_⟩
    show c j i + c' j i = -(c i j + c' i j)
    rw [hc, hc']
    abel
  smul_mem' := by
    rintro a c ⟨hc0, hc⟩
    refine ⟨fun i => by simp [hc0], fun i j => ?_⟩
    show a • c j i = -(a • c i j)
    rw [hc, smul_neg]

/-- The skew augmentation of `ℓ : V^ι → Y`: `h : V^{∧ι} → Y^ι`, `h(c)_i = ℓ(c_{i,:})` (p. 5). -/
def skewAug {𝔽 V Y ι : Type*} [Field 𝔽] [AddCommGroup V] [Module 𝔽 V] [AddCommGroup Y]
    [Module 𝔽 Y] (ℓ : (ι → V) →ₗ[𝔽] Y) : SkewArrays 𝔽 V ι →ₗ[𝔽] (ι → Y) :=
  LinearMap.pi fun i => ℓ ∘ₗ LinearMap.proj i ∘ₗ (SkewArrays 𝔽 V ι).subtype

end TensorRankN2M.ThreeTwoM


