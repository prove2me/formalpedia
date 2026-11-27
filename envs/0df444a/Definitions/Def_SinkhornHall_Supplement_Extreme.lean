-- Prove2me | Definitions.Def_SinkhornHall_Supplement_Extreme
-- name    : SinkhornHall_Supplement_Extreme
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T02:04:13.091977+00:00
-- url     : https://prove2.me/theorems/bdf76ef4-bbcb-507c-94fa-854c78538300
-- title:
--   Extreme stable sets of $\operatorname{Conv}\mathcal S$, the vector $\rho^*$, critical parameters, refined chains, $\oplus$ and the sorted prefixes $U_k$
-- statement:
--   Let $A$ be a real matrix with rows $I$ and columns $J$ (finite), and $r$, $c$ vectors on them. A set $X\sqcup Y$ ($X\subseteq I$, $Y\subseteq J$) is **stable** if $A_{ij}$ is not positive for $i\in X$, $j\in Y$ (base definition).
--
--   1. **$\operatorname{Conv}\mathcal S$** is the convex hull in $\mathbb R^2$ of the points $(r(X),c(Y))$ over all stable sets, where $r(X)=\sum_{i\in X}r_i$. A stable set is **extreme** if its point is a nonzero extreme point of $\operatorname{Conv}\mathcal S$.
--   2. **Ordered extreme stable sets** (`ExtremeChain`): an enumeration $X_0\sqcup Y_0,\dots,X_\theta\sqcup Y_\theta$ of exactly the extreme stable sets with $X_0\supsetneq X_1\supsetneq\dots$ and $Y_0\subsetneq Y_1\subsetneq\dots$; then $I_\kappa=X_{\kappa-1}\setminus X_\kappa$, $J_\kappa=Y_\kappa\setminus Y_{\kappa-1}$, $R_\kappa=r(I_\kappa)$, $C_\kappa=c(J_\kappa)$ ($\kappa=1,\dots,\theta$).
--   3. **The vector (3.7)** $\rho^*_i=(C_\kappa/R_\kappa)\,r_i$ for $i\in I_\kappa$.
--   4. **Parametric problem (3.9)**: the maximizers of $(1-\lambda)r(X)+\lambda c(Y)$ over stable $X\sqcup Y$; $\lambda\in[0,1]$ is **critical** if the maximizer is not unique.
--   5. **Refined chains** (`RefinedChain`): the critical parameters $\lambda_1<\dots<\lambda_\theta$, and in each family $\mathcal S_\kappa$ of maximizers at $\lambda_\kappa$ a maximal chain $X_{\kappa-1}=X_{\kappa,0}\supsetneq\dots\supsetneq X_{\kappa,\alpha_\kappa}=X_\kappa$, $Y_{\kappa-1}=Y_{\kappa,0}\subsetneq\dots\subsetneq Y_{\kappa,\alpha_\kappa}=Y_\kappa$; the refined blocks are $I_{\kappa,\alpha}=X_{\kappa,\alpha-1}\setminus X_{\kappa,\alpha}$, $J_{\kappa,\alpha}=Y_{\kappa,\alpha}\setminus Y_{\kappa,\alpha-1}$ (3.10).
--   6. **Block-diagonal assembly** $\bigoplus_{\kappa,\alpha}s_\kappa B_{\kappa,\alpha}$: the matrix equal to $s_\kappa B_{\kappa,\alpha}$ on $I_{\kappa,\alpha}\times J_{\kappa,\alpha}$ and $0$ elsewhere.
--   7. **Square setting** ($I=J=\{1,\dots,n\}$, $(r,c)=(\mathbf 1,\mathbf 1)$): $X$ is an **extreme subset** if $X\sqcup([n]\setminus\Gamma(X))$ is an extreme stable set; for a permutation $\sigma$ (a sort $p_{i_1}\le\dots\le p_{i_n}$ with $i_t=\sigma(t)$), $U_k=\{i_1,\dots,i_k\}$.
--
--   These objects describe the block structure of the Sinkhorn limit (§3) and the output of the algorithm Sinkhorn & Sorting Marginals (§4.2).
--
--   **Formalization Note** Neither structure presupposes the paper's claims about it (that the extreme stable sets are nested, that there are exactly $\theta$ critical parameters, that $\mathcal S_\kappa$ contains both endpoints): the theorems that use them assert existence or quantify over every instance. Chain indices are `Fin (θ + 1)`, and `k : Fin θ` stands for the block $\kappa=k+1$. Indices in the square setting are 0-based.
-- source:
--   Hayashi–Hirai–Sakabe, Finding Hall blockers by matrix scaling, arXiv:2204.07425v2, §1 Notation p.4 (⊕), §3 p.11 ((3.4), Conv S, extreme), p.12 ((3.5)–(3.7)), pp.13–14 ((3.9), critical parameters, S_κ, maximal chains, (3.10)), §4.2 p.16 (extreme subsets; Algorithm: Sinkhorn & Sorting Marginals, steps 2–3)

import Mathlib
import Definitions.Def_SinkhornHall_Model

open Finset

namespace SinkhornHall.Supplement

/-!
Polymatroidal objects of §3 and §4.2 of Hayashi–Hirai–Sakabe, *Finding Hall blockers by matrix
scaling*, arXiv:2204.07425v2 (pp.11–16): the polygon `Conv S` and extreme stable sets (p.11), the
ordered family of extreme stable sets with its partitions (3.5)–(3.6) (p.12), the vector `ρ*` of
(3.7) (p.12), the parametric problem (3.9), critical parameters, the families `S_κ`, maximal chains
in them and the refined partition (3.10) (pp.13–14), block-diagonal assembly `⊕` (p.4), extreme
subsets and the output of "Sinkhorn & Sorting Marginals" (p.16).
-/

section General

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- **The points `(r(X), c(Y))` of the stable sets**, the image of the map (3.4).
Hayashi–Hirai–Sakabe, arXiv:2204.07425v2, (3.4), p.11: "X ⊔ Y ↦ (r(X), c(Y)) (X ⊔ Y ∈ S)". -/
def stablePoints (A : Matrix ι κ ℝ) (r : ι → ℝ) (c : κ → ℝ) : Set (ℝ × ℝ) :=
  {z | ∃ (X : Finset ι) (Y : Finset κ), SinkhornHall.IsStable A X Y ∧
    z = (∑ i ∈ X, r i, ∑ j ∈ Y, c j)}

/-- **The polygon `Conv S`.**
Hayashi–Hirai–Sakabe, arXiv:2204.07425v2, §3, p.11: "consider the convex hull, denoted by Conv S,
of points (r(X), c(Y)) over all stable sets X ⊔ Y ∈ S". -/
def convS (A : Matrix ι κ ℝ) (r : ι → ℝ) (c : κ → ℝ) : Set (ℝ × ℝ) :=
  convexHull ℝ (stablePoints A r c)

/-- **Extreme stable set.**
Hayashi–Hirai–Sakabe, arXiv:2204.07425v2, §3, p.11: "A stable set X ⊔ Y is called extreme if
(r(X), c(Y)) is a nonzero extreme point of Conv S."

**Formalization Note.** Extreme points are `Set.extremePoints ℝ` of the convex hull in `ℝ × ℝ`. -/
def IsExtremeStable (A : Matrix ι κ ℝ) (r : ι → ℝ) (c : κ → ℝ) (X : Finset ι) (Y : Finset κ) :
    Prop :=
  SinkhornHall.IsStable A X Y ∧ ((∑ i ∈ X, r i, ∑ j ∈ Y, c j) : ℝ × ℝ) ≠ 0 ∧
    ((∑ i ∈ X, r i, ∑ j ∈ Y, c j) : ℝ × ℝ) ∈ (convS A r c).extremePoints ℝ

/-- **The extreme stable sets, ordered as a chain.**
Hayashi–Hirai–Sakabe, arXiv:2204.07425v2, §3, p.12: "Consider all extreme stable sets X_κ ⊔ Y_κ
(κ = 0, 1, 2, …, θ). … By Lemma 3.1, they can be ordered as [n] = X_0 ⊃ X_1 ⊃ ⋯ ⊃ X_θ = ∅,
∅ = Y_0 ⊂ Y_1 ⊂ ⋯ ⊂ Y_θ = [m]."

An `ExtremeChain A r c` is an enumeration `X_0 ⊔ Y_0, …, X_θ ⊔ Y_θ` of exactly the extreme stable
sets with `X` strictly decreasing and `Y` strictly increasing under inclusion.

**Formalization Note.** That such an enumeration exists (and is unique) is the content of Lemma 3.1
and the text after it; the structure does not presuppose it. The theorems that use the chain
either assert that one exists or quantify over every one. Indices `κ` are `Fin (θ + 1)`. -/
structure ExtremeChain (A : Matrix ι κ ℝ) (r : ι → ℝ) (c : κ → ℝ) where
  /-- The last index `θ`. -/
  θ : ℕ
  /-- The row sets `X_0, …, X_θ`. -/
  X : Fin (θ + 1) → Finset ι
  /-- The column sets `Y_0, …, Y_θ`. -/
  Y : Fin (θ + 1) → Finset κ
  extreme : ∀ k, IsExtremeStable A r c (X k) (Y k)
  complete : ∀ (X' : Finset ι) (Y' : Finset κ), IsExtremeStable A r c X' Y' →
    ∃ k, X k = X' ∧ Y k = Y'
  X_anti : StrictAnti X
  Y_mono : StrictMono Y

variable {A : Matrix ι κ ℝ} {r : ι → ℝ} {c : κ → ℝ}

open Classical in
/-- **`I_κ := X_{κ−1} \ X_κ`** of (3.6), for `κ = 1, …, θ`.
Hayashi–Hirai–Sakabe, arXiv:2204.07425v2, (3.6), p.12 (the paper writes `/` for set difference).

**Formalization Note.** `k : Fin θ` stands for `κ = k + 1`, so `I k = X k \ X (k + 1)`. -/
noncomputable def ExtremeChain.I (ch : ExtremeChain A r c) (k : Fin ch.θ) : Finset ι :=
  ch.X k.castSucc \ ch.X k.succ

open Classical in
/-- **`J_κ := Y_κ \ Y_{κ−1}`** of (3.6), for `κ = 1, …, θ` (`k : Fin θ` stands for `κ = k + 1`).
Hayashi–Hirai–Sakabe, arXiv:2204.07425v2, (3.6), p.12. -/
noncomputable def ExtremeChain.J (ch : ExtremeChain A r c) (k : Fin ch.θ) : Finset κ :=
  ch.Y k.succ \ ch.Y k.castSucc

/-- **`R_κ := r(I_κ)`.** Hayashi–Hirai–Sakabe, arXiv:2204.07425v2, §3, p.12. -/
noncomputable def ExtremeChain.Rk (ch : ExtremeChain A r c) (k : Fin ch.θ) : ℝ :=
  ∑ i ∈ ch.I k, r i

/-- **`C_κ := c(J_κ)`.** Hayashi–Hirai–Sakabe, arXiv:2204.07425v2, §3, p.12. -/
noncomputable def ExtremeChain.Ck (ch : ExtremeChain A r c) (k : Fin ch.θ) : ℝ :=
  ∑ j ∈ ch.J k, c j

open Classical in
/-- **The vector `ρ*` of (3.7).**
Hayashi–Hirai–Sakabe, arXiv:2204.07425v2, §3, p.12: "Define ρ* ∈ ℝⁿ by ρ*_i := (C_κ/R_κ) r_i for
i ∈ I_κ."

**Formalization Note.** Written as `Σ_κ [i ∈ I_κ] (C_κ/R_κ) r_i`; the `I_κ` partition the rows
(a consequence of the chain's properties), so exactly one term is nonzero. -/
noncomputable def ExtremeChain.rhoStar (ch : ExtremeChain A r c) : ι → ℝ :=
  fun i => ∑ k : Fin ch.θ, if i ∈ ch.I k then (ch.Ck k / ch.Rk k) * r i else 0

/-- **Maximizers of the parametric problem (3.9).**
Hayashi–Hirai–Sakabe, arXiv:2204.07425v2, (3.9), p.13: "max. (1 − λ)r(X) + λc(Y) s.t. X ⊔ Y ∈ S."

`paramMaximizers A r c t` is the set of stable `X ⊔ Y` maximizing `(1 − t) r(X) + t c(Y)`. -/
def paramMaximizers (A : Matrix ι κ ℝ) (r : ι → ℝ) (c : κ → ℝ) (t : ℝ) :
    Set (Finset ι × Finset κ) :=
  {P | SinkhornHall.IsStable A P.1 P.2 ∧
    ∀ (X' : Finset ι) (Y' : Finset κ), SinkhornHall.IsStable A X' Y' →
      (1 - t) * (∑ i ∈ X', r i) + t * (∑ j ∈ Y', c j) ≤
        (1 - t) * (∑ i ∈ P.1, r i) + t * (∑ j ∈ P.2, c j)}

/-- **Critical parameter of (3.9).**
Hayashi–Hirai–Sakabe, arXiv:2204.07425v2, §3, p.13: "A parameter λ is said to be critical if a
minimizer is not unique."

**Formalization Note.** "minimizer" is read as "maximizer" (problem (3.9) is a maximization; the
paper's "minimizer" refers to the equivalent minimum-cut problem). The parameter ranges over
`[0, 1]` as in (3.9). -/
def IsCritical (A : Matrix ι κ ℝ) (r : ι → ℝ) (c : κ → ℝ) (t : ℝ) : Prop :=
  t ∈ Set.Icc (0 : ℝ) 1 ∧
    ∃ P ∈ paramMaximizers A r c t, ∃ Q ∈ paramMaximizers A r c t, P ≠ Q

/-- **Critical parameters `λ_1 < ⋯ < λ_θ`, the families `S_κ`, and a maximal chain in each.**
Hayashi–Hirai–Sakabe, arXiv:2204.07425v2, §3, pp.13–14: "Let λ_1, λ_2, …, λ_θ be critical
parameters ordered as 0 < λ_1 < λ_2 < ⋯ < λ_θ < 1. Let S_κ denote the family of maximizers of (3.9)
for λ = λ_κ. … Choose a maximal set (chain) {X_{κ,α} ⊔ Y_{κ,α}}_{α=0,1,2,…,α_κ} ⊆ S_κ with the
property: X_{κ−1} = X_{κ,0} ⊃ X_{κ,1} ⊃ ⋯ ⊃ X_{κ,α_κ} = X_κ, Y_{κ−1} = Y_{κ,0} ⊂ Y_{κ,1} ⊂ ⋯ ⊂
Y_{κ,α_κ} = Y_κ."

A `RefinedChain ch` consists of the increasing enumeration `lam` of all critical parameters
(indexed like the blocks of `ch`), and for each `κ` a chain `Xr κ`, `Yr κ` in `S_κ :=
paramMaximizers A r c (lam κ)` from `X_{κ−1} ⊔ Y_{κ−1}` to `X_κ ⊔ Y_κ`, strictly monotone, to which
no member of `S_κ` can be added (maximality: every member of `S_κ` lying between two consecutive
members of the chain, in the order `X ⊇ X'`, `Y ⊆ Y'`, is one of them).

**Formalization Note.** `k : Fin θ` stands for `κ = k + 1`; `α_κ` is `α k` and the chain is indexed
by `Fin (α k + 1)`. That the number of critical parameters equals `θ` and that `S_κ` contains both
endpoints are claims of p.13–14; the structure does not presuppose them, and the theorems that use
it assert that one exists. -/
structure RefinedChain (ch : ExtremeChain A r c) where
  /-- The critical parameters `λ_1 < ⋯ < λ_θ`. -/
  lam : Fin ch.θ → ℝ
  lam_mono : StrictMono lam
  lam_crit : ∀ k, IsCritical A r c (lam k)
  lam_all : ∀ t, IsCritical A r c t → ∃ k, lam k = t
  /-- The chain lengths `α_κ`. -/
  α : Fin ch.θ → ℕ
  /-- The row sets `X_{κ,0}, …, X_{κ,α_κ}`. -/
  Xr : (k : Fin ch.θ) → Fin (α k + 1) → Finset ι
  /-- The column sets `Y_{κ,0}, …, Y_{κ,α_κ}`. -/
  Yr : (k : Fin ch.θ) → Fin (α k + 1) → Finset κ
  mem : ∀ k a, (Xr k a, Yr k a) ∈ paramMaximizers A r c (lam k)
  start_X : ∀ k, Xr k 0 = ch.X k.castSucc
  start_Y : ∀ k, Yr k 0 = ch.Y k.castSucc
  last_X : ∀ k, Xr k (Fin.last (α k)) = ch.X k.succ
  last_Y : ∀ k, Yr k (Fin.last (α k)) = ch.Y k.succ
  X_anti : ∀ k, StrictAnti (Xr k)
  Y_mono : ∀ k, StrictMono (Yr k)
  maximal : ∀ (k : Fin ch.θ) (a : Fin (α k)) (X' : Finset ι) (Y' : Finset κ),
    (X', Y') ∈ paramMaximizers A r c (lam k) →
    X' ⊆ Xr k a.castSucc → Xr k a.succ ⊆ X' → Yr k a.castSucc ⊆ Y' → Y' ⊆ Yr k a.succ →
    (X' = Xr k a.castSucc ∧ Y' = Yr k a.castSucc) ∨ (X' = Xr k a.succ ∧ Y' = Yr k a.succ)

variable {ch : ExtremeChain A r c}

open Classical in
/-- **`I_{κ,α} := X_{κ,α−1} \ X_{κ,α}`** of (3.10), `α = 1, …, α_κ` (`a : Fin (α k)` stands for
`α = a + 1`). Hayashi–Hirai–Sakabe, arXiv:2204.07425v2, (3.10), p.14. -/
noncomputable def RefinedChain.I (rc : RefinedChain ch) (k : Fin ch.θ) (a : Fin (rc.α k)) :
    Finset ι :=
  rc.Xr k a.castSucc \ rc.Xr k a.succ

open Classical in
/-- **`J_{κ,α} := Y_{κ,α} \ Y_{κ,α−1}`** of (3.10).
Hayashi–Hirai–Sakabe, arXiv:2204.07425v2, (3.10), p.14. -/
noncomputable def RefinedChain.J (rc : RefinedChain ch) (k : Fin ch.θ) (a : Fin (rc.α k)) :
    Finset κ :=
  rc.Yr k a.succ \ rc.Yr k a.castSucc

open Classical in
/-- **Block-diagonal assembly `⊕_{κ,α} s_κ B_{κ,α}`** along the refined partition.
Hayashi–Hirai–Sakabe, arXiv:2204.07425v2, §1 Notation, p.4 ("If A is a block diagonal matrix with
diagonals D_1, …, D_k, then A is written as A = ⊕_{i∈[k]} D_i") and (3.11), p.14.

`blockDiag rc s B` has entry `s_κ (B_{κ,α})_ij` at `(i, j) ∈ I_{κ,α} × J_{κ,α}` and `0` outside the
diagonal blocks.

**Formalization Note.** Written as a sum over all blocks of the entry if `(i, j)` lies in that
block; the blocks are disjoint, so at most one term is nonzero. -/
noncomputable def blockDiag (rc : RefinedChain ch) (s : Fin ch.θ → ℝ)
    (B : (k : Fin ch.θ) → (a : Fin (rc.α k)) →
      Matrix {i // i ∈ rc.I k a} {j // j ∈ rc.J k a} ℝ) : Matrix ι κ ℝ :=
  fun i j => ∑ k : Fin ch.θ, ∑ a : Fin (rc.α k),
    if h : i ∈ rc.I k a ∧ j ∈ rc.J k a then s k * B k a ⟨i, h.1⟩ ⟨j, h.2⟩ else 0

end General

section Square

variable {n : ℕ}

/-- **Extreme subset** (in the setting `(r, c) = (1, 1)` of §4).
Hayashi–Hirai–Sakabe, arXiv:2204.07425v2, §4.2, p.16: "Here a subset X is called extreme if
X ⊔ ([n] \ Γ(X)) is an extreme stable set in Section 3."

**Formalization Note.** Rows and columns are both `Fin n`; the second component `[n] \ Γ(X)` is
the set of columns not adjacent to `X`. -/
def IsExtremeSubset (A : Matrix (Fin n) (Fin n) ℝ) (X : Finset (Fin n)) : Prop :=
  IsExtremeStable A 1 1 X (Finset.univ \ SinkhornHall.Gamma A X)

/-- **Prefix `U_k := {i_1, …, i_k}` of a sort.**
Hayashi–Hirai–Sakabe, arXiv:2204.07425v2, §4.2, Algorithm: Sinkhorn & Sorting Marginals, step 3,
p.16: "Output U_k := {i_1, i_2, …, i_k} for k = 0, 1, 2, …, n, where U_0 := ∅."

For a permutation `σ` of `Fin n` (with `i_t = σ (t − 1)`), `sortPrefix σ k` is `σ '' {t | t < k}`.

**Formalization Note.** A sort `p_{i_1} ≤ ⋯ ≤ p_{i_n}` of step 2 is a permutation `σ` with
`p ∘ σ` monotone; every tie-break is such a `σ`. -/
def sortPrefix (σ : Equiv.Perm (Fin n)) (k : ℕ) : Finset (Fin n) :=
  (Finset.univ.filter (fun t : Fin n => (t : ℕ) < k)).image σ

end Square

end SinkhornHall.Supplement


