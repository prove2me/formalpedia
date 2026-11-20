-- Prove2me | Definitions.Def_LatticePrepro_Conversions_Hadamard_Ext
-- name    : LatticePrepro_Conversions_Hadamard_Ext
-- status  : Definition
-- author  : @WizardOfMenlo
-- created : 2026-11-20T00:09:52.247571+00:00
-- url     : https://prove2.me/theorems/e4eecaa1-c741-4275-883e-5c677e9b5bbb
-- title:
--   The blockwise Walsh–Hadamard transform as a linear map (Lemma B.2)
-- statement:
--   Fix $k\ge0$ and a set $\beta$ of blocks. Coordinates are pairs $(s,u)$ of a block $s\in\beta$ and a position $u\in\mathbb F_2^{k}$, and $H_k$ is the $2^{k}\times2^{k}$ Walsh–Hadamard matrix with entries $(-1)^{\langle u,w\rangle}$.
--
--   **The blockwise transform** (`Hadamard.blockHadₗ`) is the $\mathbb Z$-linear map on $\mathbb Z^{\beta\times\mathbb F_2^{k}}$ that applies $H_k$ inside every block:
--   $$(Hv)_{(s,u)}=\sum_{w\in\mathbb F_2^{k}}(-1)^{\langle u,w\rangle}\,v_{(s,w)}.$$
--   It is the function `Hadamard.blockHad` as a linear map.
--
--   The bundle also contains the lemmas that make it one: $|\mathbb F_2^{k}|=2^{k}$ (`card_Idx`), the displayed formula (`blockHad_apply`), additivity and homogeneity (`blockHad_add`, `blockHad_smul`).
--
--   This is the transform of Lemma B.2, which spreads a vector with one nonzero entry per block over its block; Lemma 3.12 applies it to the Construction A lattice when $p>2$.
-- source:
--   G. Fenzi, G. Weissenberg, Nearly Optimal Hardness for CVP and NCP with Preprocessing (STOC 2027 submission #847; IACR ePrint 2026/2634, https://eprint.iacr.org/2026/2634), Lemma B.2 (\label{lem:embeddings}) in Appendix B.2 (\label{subsec:conversion-proof}); Lean: LatticePrepro/Conversions/Hadamard.lean, LatticePrepro.Hadamard.blockHadₗ

import Mathlib
import Definitions.Def_LatticePrepro_Conversions_Hadamard

/-! Further definitions from `LatticePrepro/Conversions/Hadamard.lean`, continuing `Def_LatticePrepro_Conversions_Hadamard`. -/

namespace LatticePrepro

namespace Hadamard

variable (k : ℕ)

lemma card_Idx : Fintype.card (Idx k) = 2 ^ k := by
  simp [ZMod.card]

section Block

variable {β : Type*}

lemma blockHad_apply (v : β × Idx k → ℤ) (su : β × Idx k) :
    blockHad k v su = ∑ w, wh k su.2 w * v (su.1, w) := by
  simp [blockHad, Matrix.mulVec, dotProduct, whMat]

lemma blockHad_add (v w : β × Idx k → ℤ) : blockHad k (v + w) = blockHad k v + blockHad k w := by
  funext su; simp [blockHad_apply, mul_add, Finset.sum_add_distrib]

lemma blockHad_smul (c : ℤ) (v : β × Idx k → ℤ) : blockHad k (c • v) = c • blockHad k v := by
  funext su; simp [blockHad_apply, Finset.mul_sum, mul_left_comm]

/-- The block Hadamard map as a `ℤ`-linear map. -/
def blockHadₗ : (β × Idx k → ℤ) →ₗ[ℤ] (β × Idx k → ℤ) where
  toFun := blockHad k
  map_add' := blockHad_add k
  map_smul' := blockHad_smul k

@[simp] lemma blockHadₗ_apply (v : β × Idx k → ℤ) : blockHadₗ k v = blockHad k v := rfl

end Block

end Hadamard

end LatticePrepro


