-- Prove2me | Definitions.Def_GabidulinProx_UniqueDecoding_Reconstruction
-- name    : GabidulinProx_UniqueDecoding_Reconstruction
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:46:42.94293+00:00
-- url     : https://prove2.me/theorems/10b9b616-8d29-4e21-9df9-70104be2434b
-- title:
--   Reconstruction equations and global-family interfaces
-- statement:
--   Let $q=|K|$, let $\alpha$ be the evaluation points and let $y$ be a received word. A reconstruction pair $(A,B)$ satisfies
--
--   $$A\in\mathcal L(q,m,t+1),\quad B\in\mathcal L(q,m,k+t),\quad(A,B)\ne(0,0),\quad A(y_r)=B(\alpha_r)\ (r<n).$$
--
--   For coefficient families $a_0,\ldots,a_e$ and $b_0,\ldots,b_{k+e-1}$ in $L[Z]$, the global identity is
--
--   $$\sum_{i=0}^e a_i(Z)(u_{0,r}+Zu_{1,r})^{q^i}
--   +\sum_{j=0}^{k+e-1}b_j(Z)\alpha_r^{q^j}=0.$$
--
--   The separate bound predicate states $a_0\ne0$, $\deg_Za_i\le\sigma_e-q^i$, and $\deg_Zb_j\le\sigma_e$. It asserts no existence. A decoded family on $S$ assigns each $z\in S$ a message $P_z\in\mathcal L(q,m,k)$ whose residual evaluation word has base-field rank at most $e$; values outside $S$ are irrelevant.
--
--   These interfaces name the paper's equations and degree conditions so subsequent theorem statements can accept the full relevant conclusions of earlier lemmas without importing unproved theorem stubs or choosing witnesses from them.
-- source:
--   Songsong Li, Chaoping Xing, Chen Yuan, Ruiqi Zhu, Proximity Gaps for Gabidulin Codes and Applications, STOC 2027 submission #434 (October 2026), Definition 2.6 p.13; Lemma 3.4 p.19 with bounds p.21; §3.2 p.21. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/434.pdf

import Definitions.Def_GabidulinProx_UniqueDecoding_Codes

open scoped BigOperators

namespace GabidulinProx.UniqueDecoding

/-- Equation (6), p.13: the nonzero bounded-degree reconstruction pair. -/
def IsReconstruction {L : Type*} [Field L] {n : ℕ} (q k t : ℕ)
    (α y : Fin n → L) (A B : Polynomial L) : Prop :=
  IsLinearized q (t + 1) A ∧ IsLinearized q (k + t) B ∧
  (A ≠ 0 ∨ B ≠ 0) ∧ ∀ r, A.eval (y r) = B.eval (α r)

/-- The identity of Lemma 3.4 as an identity in L[Z]. -/
def GlobalIdentity {L : Type*} [Field L] {n k e : ℕ} (q : ℕ)
    (α u₀ u₁ : Fin n → L) (a : Fin (e + 1) → Polynomial L)
    (b : Fin (k + e) → Polynomial L) : Prop :=
  ∀ r, (∑ i, a i * (Polynomial.C (u₀ r) + Polynomial.X * Polynomial.C (u₁ r)) ^
    (q ^ i.val)) + (∑ j, b j * Polynomial.C ((α r) ^ (q ^ j.val))) = 0

/-- All nonvanishing and Z-degree conclusions of Lemma 3.4. Zero coefficients are allowed. -/
def GlobalBounds {L : Type*} [Field L] {k e : ℕ} (q : ℕ)
    (a : Fin (e + 1) → Polynomial L) (b : Fin (k + e) → Polynomial L) : Prop :=
  a 0 ≠ 0 ∧ (∀ i, (a i).natDegree ≤ sigma q e - q ^ i.val) ∧
    ∀ j, (b j).natDegree ≤ sigma q e

/-- The family of decoded messages on S; no constraints outside S. -/
noncomputable def DecodedFamily (K : Type*) {L : Type*} [Field K] [Fintype K]
    [Field L] [Algebra K L] {n : ℕ} (α u₀ u₁ : Fin n → L) (k e : ℕ)
    (S : Finset L) (Pz : L → Polynomial L) : Prop :=
  ∀ z ∈ S, IsLinearized (Fintype.card K) k (Pz z) ∧
    wordRank K (linePoint u₀ u₁ z - evaluateWord α (Pz z)) ≤ e

end GabidulinProx.UniqueDecoding


