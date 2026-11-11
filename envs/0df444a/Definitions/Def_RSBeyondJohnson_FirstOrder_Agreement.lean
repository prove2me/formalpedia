-- Prove2me | Definitions.Def_RSBeyondJohnson_FirstOrder_Agreement
-- name    : RSBeyondJohnson_FirstOrder_Agreement
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T16:30:28.707195+00:00
-- url     : https://prove2.me/theorems/52ea3554-06d8-406c-8dd1-33badbedd26f
-- title:
--   Received curves, agreement sets $S_z(P)$, full common-witness agreement and line MCA (Definitions 3.1–3.2)
-- statement:
--   Fix a field $F$, positions $i \in \{1,\dots,n\}$ (in Lean `Fin n`, 0-based) and evaluation points $\alpha_1,\dots,\alpha_n\in F$. A **polynomial received curve** of degree $\ell$ is a tuple of words $w_0,\dots,w_\ell\in F^n$; its $i$-th coordinate at the challenge $z\in F$ is
--   $$w_i(z)=\sum_{t=0}^{\ell} z^t w_{t,i}.$$
--   A **received line** $f+zg$ is the case $\ell=1$, $(w_0,w_1)=(f,g)$.
--
--   For $P\in F[X]$ the **agreement set** is $S_z(P)=\{i : P(\alpha_i)=w_i(z)\}$, and for witnesses $P_0,\dots,P_\ell$ the **common agreement set** is $S(P_0,\dots,P_\ell)=\{i : P_t(\alpha_i)=w_{t,i}\text{ for every }0\le t\le\ell\}$.
--
--   **Definition 3.1.** The pair $(z,P)$ has the **full common-witness property** (message dimension $k$) if there are $P_0,\dots,P_\ell\in F[X]$ of degree $<k$ with
--   $$P=\sum_{t=0}^{\ell} z^t P_t,\qquad S_z(P)=S(P_0,\dots,P_\ell)$$
--   (equality of index sets, not of sizes).
--
--   **Definition 3.2.** $\mathrm{RS}_\alpha[n,k]$ has **line MCA with full agreement sets** at threshold $A$ with exceptional bound $E_{\mathrm{exc}}\in\mathbb R$ if every received line $f+zg$ admits one finite set $\mathcal E\subseteq F$ with $|\mathcal E|\le E_{\mathrm{exc}}$, chosen before the challenge and the candidate, such that every pair $(z,P)$ with $z\notin\mathcal E$, $\deg P<k$ and $|S_z(P)|\ge A$ has the full common-witness property. `HasCurveMCA` is the same notion for curves of degree $\ell$.
--
--   **Formalization Note.** Agreement sets are `Finset (Fin n)`. The exceptional set is a `Finset F`, so it is finite also over infinite fields. Degrees use `Polynomial.degree`, so the zero polynomial has degree $<k$. Distinctness of the $\alpha_i$ is a hypothesis of each theorem.
-- source:
--   Dao, Kominers, Thaler, Reed–Solomon Codes Beyond Johnson: Efficient Decoding and Smaller Cryptographic Proofs, STOC 2027 submission (manuscript of November 2, 2026, sha256 76a38731…), p. 16, (4), Definitions 3.1–3.2

import Mathlib
import Definitions.Def_RSListDecodingCapacity_AllRates_Decoding

open Polynomial

namespace RSBeyondJohnson.FirstOrder

/-!
# Received curves, agreement sets, full common-witness agreement and line MCA

Dao, Kominers, Thaler, *Reed–Solomon Codes Beyond Johnson: Efficient Decoding and Smaller
Cryptographic Proofs*, STOC 2027 submission (manuscript of November 2, 2026), §3.1, p. 16:
(4), Definitions 3.1 and 3.2.

* Positions are `Fin n` (the paper's `[n]`, 0-based). Evaluation points are `α : Fin n → F`;
  their distinctness is a hypothesis of each theorem, not part of these definitions.
* A polynomial received curve of degree `ℓ` is a family of words `w : Fin (ℓ + 1) → Fin n → F`,
  `w t = w_t`; its `i`-th coordinate at the challenge `z` is `w_i(z) = ∑_{t=0}^{ℓ} z^t w_{t,i}`.
  A line `f + z g` is the case `ℓ = 1`, `w = ![f, g]` (`lineCurve f g`).
* Agreement sets are `Finset (Fin n)`; `|S|` is `Finset.card`.
-/

/-- The received curve at the challenge `z`: `w_i(z) = ∑_{t=0}^{ℓ} z^t w_{t,i}` ((4), p. 16). -/
def curveWord {F : Type*} [Field F] {n ℓ : ℕ} (w : Fin (ℓ + 1) → Fin n → F) (z : F) :
    Fin n → F :=
  fun i => ∑ t : Fin (ℓ + 1), z ^ (t : ℕ) * w t i

/-- The received line `f + z g` as the curve of degree one with `(w_0, w_1) = (f, g)`. -/
def lineCurve {F : Type*} [Field F] {n : ℕ} (f g : Fin n → F) : Fin (1 + 1) → Fin n → F :=
  ![f, g]

/-- The agreement set `S_z(P) = {i : P(α_i) = w_i(z)}` (p. 16). -/
noncomputable def agrSet {F : Type*} [Field F] {n ℓ : ℕ} (α : Fin n → F)
    (w : Fin (ℓ + 1) → Fin n → F) (z : F) (P : F[X]) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun i => P.eval (α i) = curveWord w z i

/-- The common agreement set of witnesses `S(P_0, …, P_ℓ) = {i : P_t(α_i) = w_{t,i} for every
0 ≤ t ≤ ℓ}` (p. 16). For a line, `S(F_0, G_0) = {i : F_0(α_i) = f_i and G_0(α_i) = g_i}`. -/
noncomputable def witnessAgrSet {F : Type*} [Field F] {n ℓ : ℕ} (α : Fin n → F)
    (w : Fin (ℓ + 1) → Fin n → F) (Ps : Fin (ℓ + 1) → F[X]) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun i => ∀ t : Fin (ℓ + 1), (Ps t).eval (α i) = w t i

/-- **Definition 3.1 (Full common-witness agreement)**, p. 16. The pair `(z, P)` has the full
common-witness property for the received curve `w`, at message dimension `k`, if there are
polynomials `P_0, …, P_ℓ` of degree `< k` with `P = ∑_t z^t P_t` and `S_z(P) = S(P_0, …, P_ℓ)`
(equality of index sets). -/
def HasFullCommonWitness {F : Type*} [Field F] {n ℓ : ℕ} (k : ℕ) (α : Fin n → F)
    (w : Fin (ℓ + 1) → Fin n → F) (z : F) (P : F[X]) : Prop :=
  ∃ Ps : Fin (ℓ + 1) → F[X], (∀ t, (Ps t).degree < (k : WithBot ℕ)) ∧
    P = ∑ t : Fin (ℓ + 1), Polynomial.C (z ^ (t : ℕ)) * Ps t ∧
    agrSet α w z P = witnessAgrSet α w Ps

/-- **MCA with full agreement sets for polynomial received curves of degree `ℓ`** (Definition 3.2
and its last sentence, p. 16): every received curve `w` of degree `ℓ` admits one finite set
`E ⊆ F` with `|E| ≤ Eexc`, chosen before the challenge and the candidate, such that every pair
`(z, P)` with `z ∉ E`, `deg P < k` and `|S_z(P)| ≥ A` has the full common-witness property. -/
def HasCurveMCA {F : Type*} [Field F] {n : ℕ} (ℓ k : ℕ) (α : Fin n → F) (A : ℕ) (Eexc : ℝ) :
    Prop :=
  ∀ w : Fin (ℓ + 1) → Fin n → F, ∃ E : Finset F, (E.card : ℝ) ≤ Eexc ∧
    ∀ z : F, z ∉ E → ∀ P : F[X], P.degree < (k : WithBot ℕ) → A ≤ (agrSet α w z P).card →
      HasFullCommonWitness k α w z P

/-- **Definition 3.2 (Line MCA with full agreement sets)**, p. 16: `RS_α[n, k]` has line MCA at
agreement threshold `A` with exceptional bound `Eexc` if every received line `f + z g` admits one
finite set `E ⊆ F` with `|E| ≤ Eexc` such that every pair `(z, P)` with `z ∉ E`, `deg P < k` and
`|S_z(P)| ≥ A` admits `F_0, G_0` of degree `< k` with `P = F_0 + z G_0` and
`S_z(P) = S(F_0, G_0)`. -/
def HasLineMCA {F : Type*} [Field F] {n : ℕ} (k : ℕ) (α : Fin n → F) (A : ℕ) (Eexc : ℝ) :
    Prop :=
  ∀ f g : Fin n → F, ∃ E : Finset F, (E.card : ℝ) ≤ Eexc ∧
    ∀ z : F, z ∉ E → ∀ P : F[X], P.degree < (k : WithBot ℕ) →
      A ≤ (agrSet α (lineCurve f g) z P).card → HasFullCommonWitness k α (lineCurve f g) z P

end RSBeyondJohnson.FirstOrder


