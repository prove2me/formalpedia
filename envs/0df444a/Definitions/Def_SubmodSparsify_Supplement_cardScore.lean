-- Prove2me | Definitions.Def_SubmodSparsify_Supplement_cardScore
-- name    : SubmodSparsify_Supplement_cardScore
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T00:08:28.440628+00:00
-- url     : https://prove2.me/theorems/51732a0e-52c8-4964-a477-02088371a511
-- title:
--   Algorithm 3 sampling scores (37) with the low-collision partitions of Algorithm 5
-- statement:
--   Let $V = [n]$, let $f_1,\dots,f_m : 2^V \to \mathbb R_{\ge0}$, and let $1 \le k \le n$. Algorithm 5 sets $b = 2^{\lceil \log_2(2k)\rceil}$ and $M = 2^{\lceil \log_2 \max\{n,b\}\rceil}$, works in the field $\mathbb F_M$, assigns distinct labels $x_v \in \mathbb F_M$ to the vertices, fixes a surjective $\mathbb F_2$-linear map $\varphi : \mathbb F_M \to \mathbb F_2^{\log_2 b}$, and forms, for each $a \in \mathbb F_M \setminus\{0\}$, the labeled partition $(X_{a,c})_{c \in \mathbb F_2^{\log_2 b}}$ with
--
--   $$X_{a,c} = \{v \in V : \varphi(a x_v) = c\}.$$
--
--   The family $\mathcal H$ consists of these $M-1$ labeled partitions, counted with multiplicity. The sampling score of component $i$ is (37):
--
--   $$p_i = \sum_{u \in V} s^{(u)}_i + \frac{2}{|\mathcal H|} \sum_{a \ne 0} \sum_{c} t^{(X_{a,c})}_i,$$
--
--   where $s^{(u)}_i$ is the capped share (32), with $K = 2k-1$, of the family $D \mapsto f^{\to}_i(u, D)$ on $V \setminus \{u\}$, and $t^{(X)}_i$ is the share, with $K = |V \setminus X|$ (cap inactive), of the family $C \mapsto f^{\to}_i(C, X)$ on $V \setminus X$; $t^{(V)}_i = 0$. Every occurrence of a labeled block counts, including repeated and empty blocks.
--
--   These are the scores that Algorithm 3 samples with; Theorem 5.1 bounds their total by $10nk$.
--
--   **Formalization Note** $\mathbb F_M$ is Mathlib's `GaloisField 2 (log₂ M)` and $\mathbb F_2^{\log_2 b}$ is `Fin (log₂ b) → ZMod 2`, with $\lceil\log_2 x\rceil$ = `Nat.clog 2 x`. Algorithm 5 leaves the labels and $\varphi$ free, so the score takes them as arguments; statements require the labels injective and $\varphi$ surjective and linear.
-- source:
--   Bao, Cai, Chen, He, Zhang, Nearly Optimal Submodular Sparsification, with and without Cardinality Constraints, arXiv:2606.20777 (version held, sha256 358242d6793d37e5008919a4795e2e18da7fa5049f06ad4d1b929ac6d7fbc634), Algorithm 3, p.28; Algorithm 5 and Claim 5.3, pp.30–31; (37), p.32

import Mathlib
import Definitions.Def_SubmodSparsify_blockMinCut
import Definitions.Def_SubmodSparsify_weights
import Definitions.Def_SubmodSparsify_Supplement_cappedShare

namespace SubmodSparsify.Supplement

/-!
# Algorithm 3's sampling scores (37), with the low-collision partitions of Algorithm 5

Bao, Cai, Chen, He, Zhang, *Nearly Optimal Submodular Sparsification, with and without
Cardinality Constraints*, arXiv:2606.20777 (version held), Algorithm 3 p.28, Algorithm 5 p.31,
Claim 5.3 pp.30–31, (37) p.32.

Algorithm 5: "b ← 2^⌈log₂(2k)⌉; M ← 2^⌈log₂(max{n,b})⌉; Construct F_M and assign distinct labels
x_v ∈ F_M to v ∈ V; Fix a surjective F₂-linear map φ : F_M → F₂^{log₂ b}; […] for all
a ∈ F_M \ {0} do for all c ∈ F₂^{log₂ b} do X_{a,c} ← {v ∈ V : φ(a x_v) = c} […] Append
(X_{a,c})_c to H" (p.31).

(37), p.32: "For each u ∈ V, apply Lemma 5.4 to the functions D ↦ f→ᵢ(u, D) on V \ {u}, with
K = 2k − 1, and denote the resulting share of component i by s⁽ᵘ⁾ᵢ. Similarly, fix a labeled
block X in a partition Π ∈ H. Take E = V \ X and apply the same lemma to the functions
C ↦ f→ᵢ(C, X) on E, with K = |E|. We write t⁽ˣ⁾ᵢ for the share of component i given by (32).
[…] If X = V, the ground set is empty and we set t⁽ⱽ⁾ᵢ = 0. The sampling score is
pᵢ := Σ_{u∈V} s⁽ᵘ⁾ᵢ + (2/|H|) Σ_{Π∈H} Σ_{X∈Π} t⁽ˣ⁾ᵢ. (37) Each occurrence of a labeled block
contributes to this sum, including repeated and empty blocks."

**Formalization Note.**
* `V = [n]` is `Fin n` (paper index = value + 1); components `f : Fin m → Finset (Fin n) → ℝ`.
* `log₂ b = Nat.clog 2 (2k)` and `log₂ M = Nat.clog 2 (max n b)` (`⌈log₂ x⌉` for integers
  `x ≥ 1`). `F_M` is Mathlib's `GaloisField 2 (log₂ M)` (`2^{log₂ M}` elements for `k ≥ 1`), and
  `F₂^{log₂ b}` is `Fin (log₂ b) → ZMod 2`.
* Algorithm 5 leaves the labelling `x_v` and the map `φ` free. The scores are therefore indexed
  by a choice `(x, φ)`; the statements require `x` injective ("distinct labels") and `φ`
  surjective and `ZMod 2`-linear. The partitions are indexed by `a ∈ F_M \ {0}` and their blocks
  by the label `c`, so repeated partitions and repeated or empty blocks are counted with
  multiplicity, and `|H| = |F_M| − 1`.
* `s⁽ᵘ⁾ᵢ` is `cappedShare` with `K = 2k − 1` of the base inside-terminal family
  `inFamily f u` on `[n] \ {u}`; `t⁽ˣ⁾ᵢ` is `cappedShare` with `K = |V \ X|` of the family
  `C ↦ f→ᵢ(C, X)` on `V \ X`. For `X = V` the ground set is empty and `cappedShare` is `0`, the
  paper's `t⁽ⱽ⁾ᵢ = 0`.
-/

variable {n m : ℕ}

/-- `log₂ b` with `b = 2^⌈log₂(2k)⌉` (Algorithm 5, line 2). -/
def blockExp (k : ℕ) : ℕ := Nat.clog 2 (2 * k)

/-- `log₂ M` with `M = 2^⌈log₂(max{n, b})⌉` (Algorithm 5, line 3). -/
def fieldExp (n k : ℕ) : ℕ := Nat.clog 2 (max n (2 ^ blockExp k))

/-- The field `F_M` of Algorithm 5. -/
abbrev LCField (n k : ℕ) : Type := GaloisField 2 (fieldExp n k)

/-- The block labels `F₂^{log₂ b}` of Algorithm 5. -/
abbrev BlockLabel (k : ℕ) : Type := Fin (blockExp k) → ZMod 2

/-- The labeled block `X_{a,c} = {v ∈ V : φ(a x_v) = c}` (Algorithm 5, line 9). -/
noncomputable def lcBlock {k : ℕ} (x : Fin n → LCField n k)
    (φ : LCField n k →ₗ[ZMod 2] BlockLabel k) (a : LCField n k) (c : BlockLabel k) :
    Finset (Fin n) := by
  classical exact Finset.univ.filter (fun v => φ (a * x v) = c)

/-- The outside-block family `(f→ᵢ(·, X))ᵢ` on `V \ X`. -/
noncomputable def blockOutFamily (f : Fin m → Finset (Fin n) → ℝ) (X : Finset (Fin n)) :
    Fin m → Finset (Fin n) → ℝ :=
  fun i C => blockMinCut (f i) C X

/-- `s⁽ᵘ⁾ᵢ`: the capped share (`K = 2k − 1`) of component `i` in the inside-terminal family of
`u` on `[n] \ {u}`. -/
noncomputable def cappedInShare (f : Fin m → Finset (Fin n) → ℝ) (k : ℕ) (u : Fin n)
    (i : Fin m) : ℝ :=
  cappedShare (inFamily f u) (2 * k - 1) (Finset.univ.erase u) i

/-- `t⁽ˣ⁾ᵢ`: the uncapped (`K = |V \ X|`) share of component `i` in the outside-block family of
`X` on `V \ X`. -/
noncomputable def blockShare (f : Fin m → Finset (Fin n) → ℝ) (X : Finset (Fin n))
    (i : Fin m) : ℝ :=
  cappedShare (blockOutFamily f X) (Finset.univ \ X).card (Finset.univ \ X) i

/-- The sampling score (37) of Algorithm 3 for the partition family determined by `(x, φ)`:
`pᵢ = Σ_u s⁽ᵘ⁾ᵢ + (2/|H|) Σ_{a ≠ 0} Σ_c t⁽ˣᵃᶜ⁾ᵢ`. -/
noncomputable def cardScore (f : Fin m → Finset (Fin n) → ℝ) (k : ℕ)
    (x : Fin n → LCField n k) (φ : LCField n k →ₗ[ZMod 2] BlockLabel k) (i : Fin m) : ℝ := by
  classical
  letI : Fintype (LCField n k) := Fintype.ofFinite _
  exact ∑ u, cappedInShare f k u i +
    (2 / (((Finset.univ.filter (fun a : LCField n k => a ≠ 0)).card : ℕ) : ℝ)) *
      ∑ a ∈ Finset.univ.filter (fun a : LCField n k => a ≠ 0),
        ∑ c : BlockLabel k, blockShare f (lcBlock x φ a c) i

end SubmodSparsify.Supplement


