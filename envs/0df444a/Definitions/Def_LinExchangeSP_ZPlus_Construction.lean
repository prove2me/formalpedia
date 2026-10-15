-- Prove2me | Definitions.Def_LinExchangeSP_ZPlus_Construction
-- name    : LinExchangeSP_ZPlus_Construction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-15T06:44:37.464729+00:00
-- url     : https://prove2.me/theorems/2cff29d2-3e40-48d3-84f3-effdc53d3fed
-- title:
--   Lemma 7.2 proof, §7.2 — the Gaussian elimination, the digraph H, the sets Dᵢ, T₁, T₂, T₃ and κ(i)
-- statement:
--   This module fixes the objects of the proof of Theorem 6.4 in §7 of Garg and Végh.
--
--   1. **The elimination of Lemma 7.2** (proof, p. 17). For $T \in \mathbb{Q}^{\ell\times t}$ start from $T^{(0)} = T$ and $Y^{(0)} = I_\ell$. At step $k = 1, \dots, \min\{\ell,t\}$: if $T^{(k-1)}_{kk} = 0$, nothing is done; otherwise row $k$ is divided by $T^{(k-1)}_{kk}$ and, for every $i \in [k+1,\ell]$, $-T^{(k-1)}_{ik}/T^{(k-1)}_{kk}$ times the old $k$-th row is added to row $i$. The same row operations applied to $Y^{(k-1)}$ give $Y^{(k)}$. The output is the pair $(Y, T') = (Y^{(m)}, T^{(m)})$, $m = \min\{\ell,t\}$.
--
--   For a square $M \in \mathbb{Q}^{t\times t}$:
--
--   2. **The digraph** $([t], H)$ (§7.2, p. 18): $ij \in H$ if $i \ne j$ and $M_{ij} < 0$.
--
--   3. **$D_i$**, the set of vertices reachable from $i$ in $([t],H)$, including $i$ itself, and $d_i = |D_i|$.
--
--   4. **$M^{(i)}$**, the $d_i \times t$ submatrix of the rows $M_j$, $j \in D_i$, and its rank $\operatorname{rk}(M^{(i)})$.
--
--   5. **The partition** (p. 18)
--   $$T_1 = \{i : |\{j : ij \in H\}| \le 1\},\quad T_2 = \{i \notin T_1 : \operatorname{rk}(M^{(i)}) = d_i\},\quad T_3 = \{i \notin T_1 : \operatorname{rk}(M^{(i)}) < d_i\}.$$
--
--   6. **$\kappa(i)$** for $i \in T_2$: the $i$-th entry of the vector $(M_{D_i,D_i})^{-1}\gamma_{D_i}$, where $M_{D_i,D_i}$ is the principal submatrix of $M$ on $D_i$ and $\gamma_{D_i}$ the restriction of $\gamma$ to $D_i$. Equivalently, $\kappa(i) = r_i$ for the unique $r \in \mathbb{R}^t$ supported on $D_i$ with $M_\ell r = \gamma_\ell$ for all $\ell \in D_i$.
--
--   These objects carry the milestones Lemma 7.2, Claim 7.3(iii), Lemma 7.4 and Claim 7.5.
--
--   **Formalization Note** Indices are 0-based; step $k$ of the paper is step $k-1$ here. The paper's (10) shows that row $i$ receives $-T_{ik}/T_{kk}$ times the row $k$ *before* normalization, which is what is encoded. The paper defines $\kappa(i) := Y^{(ij)}_d\gamma^{(ij)}$ in (12) through the elimination for one arc $ij$ and shows in the proof of Lemma 7.4 that it equals $\hat r_d$, the $i$-th entry of the solution above; the intrinsic form used here is that number, with no arc chosen. For $i \in T_2$ the block $M_{D_i,D_i}$ is invertible, because $D_i$ is closed under arcs, so the rows of $D_i$ vanish outside $D_i$ and have rank $d_i$; for $i \notin T_2$ Mathlib's inverse of a singular matrix is $0$ and `kappa` has no meaning, so it is only used under $i \in T_2$. $D_i$ is defined with classical decidability.
-- source:
--   Garg & Végh, A strongly polynomial algorithm for linear exchange markets, arXiv:1809.06266v3, p. 17 (proof of Lemma 7.2, (10)), p. 18 (§7.2, H, D_i, M^(i), T₁, T₂, T₃), p. 19 ((12), κ(i)), p. 21 (proof of Lemma 7.4(iii), r̂_d = κ(i))

import Mathlib
import Definitions.Def_LinExchangeSP_ZPlus_Setting

namespace LinExchangeSP.ZPlus

open Matrix

/-- The row operations of step `k` of the elimination of Lemma 7.2 (proof, p. 17), applied to a matrix
`A` with the same rows as the current matrix: row `k` is divided by the pivot `piv`, and for every
row `i > k` the multiple `-(c i / piv)` of the old row `k` is added to row `i`, where `c` is the
`k`-th column of the current matrix. Applied to `T^(k-1)` it gives `T^(k)`, applied to `Y^(k-1)` it
gives `Y^(k)`. -/
def rowOps {l : ℕ} {α : Type*} (k : Fin l) (piv : ℚ) (c : Fin l → ℚ)
    (A : Matrix (Fin l) α ℚ) : Matrix (Fin l) α ℚ :=
  fun i j => if i = k then A k j / piv else if k < i then A i j - c i / piv * A k j else A i j

/-- Step `k` (0-based; the paper's step `k + 1`) of the elimination of Lemma 7.2: if `k < min{ℓ, t}`
and the pivot `T^(k)_kk` is nonzero, perform `rowOps` on both `Y` and `T`; otherwise (pivot `0`,
or `k ≥ min{ℓ, t}`) do nothing. -/
def elimStep {l t : ℕ} (k : ℕ)
    (YT : Matrix (Fin l) (Fin l) ℚ × Matrix (Fin l) (Fin t) ℚ) :
    Matrix (Fin l) (Fin l) ℚ × Matrix (Fin l) (Fin t) ℚ :=
  if h : k < l ∧ k < t then
    let kr : Fin l := ⟨k, h.1⟩
    let kc : Fin t := ⟨k, h.2⟩
    let piv := YT.2 kr kc
    if piv = 0 then YT
    else (rowOps kr piv (fun i => YT.2 i kc) YT.1, rowOps kr piv (fun i => YT.2 i kc) YT.2)
  else YT

/-- The pair `(Y^(n), T^(n))` after `n` steps, starting from `(Y^(0), T^(0)) = (I_ℓ, T)`. -/
def elimAux {l t : ℕ} (T : Matrix (Fin l) (Fin t) ℚ) :
    ℕ → Matrix (Fin l) (Fin l) ℚ × Matrix (Fin l) (Fin t) ℚ
  | 0 => (1, T)
  | n + 1 => elimStep n (elimAux T n)

/-- The Gaussian elimination of Lemma 7.2: `(Y, T') = (Y^(m), T^(m))` with `m = min{ℓ, t}`. -/
def gaussElim {l t : ℕ} (T : Matrix (Fin l) (Fin t) ℚ) :
    Matrix (Fin l) (Fin l) ℚ × Matrix (Fin l) (Fin t) ℚ :=
  elimAux T (min l t)

/-- The arcs of the digraph `([t], H)` (§7.2, p. 18): `ij ∈ H` iff `M_ij < 0` (`i ≠ j`). -/
def arcH {t : ℕ} (M : Matrix (Fin t) (Fin t) ℚ) (i j : Fin t) : Prop :=
  i ≠ j ∧ M i j < 0

instance {t : ℕ} (M : Matrix (Fin t) (Fin t) ℚ) (i : Fin t) : DecidablePred (arcH M i) :=
  fun _ => instDecidableAnd

open Classical in
/-- `Dᵢ`, the set of vertices reachable from `i` in `([t], H)`, including `i` itself (§7.2, p. 18). -/
noncomputable def D {t : ℕ} (M : Matrix (Fin t) (Fin t) ℚ) (i : Fin t) : Finset (Fin t) :=
  Finset.univ.filter (fun j => Relation.ReflTransGen (arcH M) i j)

/-- `rk(M^(i))`, the rank of the submatrix of `M` comprising the rows `M_j`, `j ∈ Dᵢ`. -/
noncomputable def rowRank {t : ℕ} (M : Matrix (Fin t) (Fin t) ℚ) (i : Fin t) : ℕ :=
  (M.submatrix (fun r : {j // j ∈ D M i} => (r : Fin t)) id).rank

/-- `i ∈ T₁`: `|{j : ij ∈ H}| ≤ 1` (§7.2, p. 18). -/
def InT1 {t : ℕ} (M : Matrix (Fin t) (Fin t) ℚ) (i : Fin t) : Prop :=
  (Finset.univ.filter (fun j => arcH M i j)).card ≤ 1

/-- `i ∈ T₂`: `i ∉ T₁` and `rk(M^(i)) = dᵢ` (§7.2, p. 18). -/
def InT2 {t : ℕ} (M : Matrix (Fin t) (Fin t) ℚ) (i : Fin t) : Prop :=
  ¬ InT1 M i ∧ rowRank M i = (D M i).card

/-- `i ∈ T₃`: `i ∉ T₁` and `rk(M^(i)) < dᵢ` (§7.2, p. 18). -/
def InT3 {t : ℕ} (M : Matrix (Fin t) (Fin t) ℚ) (i : Fin t) : Prop :=
  ¬ InT1 M i ∧ rowRank M i < (D M i).card

/-- `i ∈ Dᵢ`. -/
theorem self_mem_D {t : ℕ} (M : Matrix (Fin t) (Fin t) ℚ) (i : Fin t) : i ∈ D M i := by
  classical
  simp [D, Relation.ReflTransGen.refl]

/-- `κ(i)` for `i ∈ T₂`, stated intrinsically: the `i`-th entry of the solution `r` of
`M_ℓ r = γ_ℓ` (`ℓ ∈ Dᵢ`) supported on `Dᵢ`, i.e. of `(M_{Dᵢ,Dᵢ})⁻¹ γ_{Dᵢ}`. The block is invertible
exactly when `i ∈ T₂`; elsewhere Mathlib's inverse is `0` and the value carries no meaning. -/
noncomputable def kappa {t : ℕ} (M : Matrix (Fin t) (Fin t) ℚ) (γ : Fin t → ℚ) (i : Fin t) : ℝ :=
  let ι : {j // j ∈ D M i} → Fin t := fun r => r
  ((((M.submatrix ι ι)⁻¹ *ᵥ (γ ∘ ι)) ⟨i, self_mem_D M i⟩ : ℚ) : ℝ)

end LinExchangeSP.ZPlus


