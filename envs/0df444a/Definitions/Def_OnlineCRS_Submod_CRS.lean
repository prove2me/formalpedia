-- Prove2me | Definitions.Def_OnlineCRS_Submod_CRS
-- name    : OnlineCRS_Submod_CRS
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T20:21:08.692297+00:00
-- url     : https://prove2.me/theorems/adf9869a-d8d1-4020-aace-bcd7a4c94a6a
-- title:
--   Definitions 3.1–3.2, p. 16 — (offline) CRSs, (b, c)-balanced and monotone CRSs, the characteristic CRS
-- statement:
--   Let $N$ be a finite ground set and $P\subseteq[0,1]^N$.
--
--   1. **CRS.** A (possibly random) *contention resolution scheme* $\pi$ for $P$ depends on an input vector $x$ and returns, for every $S\subseteq N$, a subset $\pi(S)\subseteq S$ that obeys $P$, i.e. $\mathbf 1_{\pi(S)}\in P$. It is encoded by a probability distribution $\rho_x$ over maps $\varphi:2^N\to 2^N$ for each $x$.
--   2. **Balanced.** For $b,c\in[0,1]$, $\pi$ is *$(b,c)$-balanced* if, whenever $x\in bP$ and $x_e>0$,
--   $$\Pr\big[e\in\pi(R(x))\ \big|\ e\in R(x)\big]\ge c .$$
--   3. **Monotone.** $\pi$ is *monotone* if $\Pr[e\in\pi(S_1)]\ge\Pr[e\in\pi(S_2)]$ whenever $e\in S_1\subseteq S_2$.
--   4. **Characteristic CRS.** For a greedy OCRS with family $\mathcal F_x$, the characteristic CRS $\bar\pi$ is
--   $$\bar\pi(A)=\{e\in A \mid I\cup\{e\}\in\mathcal F_x\ \ \forall I\subseteq A,\ I\in\mathcal F_x\};$$
--   for a randomized greedy OCRS, $\mathcal F_x$ is drawn from its distribution, so $\bar\pi$ is a random CRS.
--
--   The characteristic CRS connects online schemes to offline contention resolution: it selects exactly the selectable active elements, which an online greedy OCRS always selects.
--
--   **Formalization Note** The printed Definition 3.1 reads "$\ge c\cdot x_e$"; this is a slip for "$\ge c$" (the proof of Lemma 3.4 concludes balancedness from $\Pr[e\in\bar\pi(A)\mid e\in A]\ge c$, and Definition 4.5 and Chekuri–Vondrák–Zenklusen use "$\ge c$"). Since $\Pr[e\in R(x)]=x_e$, balancedness is stated without division as $\Pr[e\in\pi(R(x)),\,e\in R(x)]\ge c\,x_e$. The distribution and support conditions of a CRS, and monotonicity, are required for every input vector $x$.
-- source:
--   arXiv:1508.00142v2, §3, p. 16: the recalled definition of a CRS, Definition 3.1 (with '≥ c · x_e' read as '≥ c'), Definition 3.2

import Mathlib
import Definitions.Def_OnlineCRS_Matroid_Basics
import Definitions.Def_OnlineCRS_Submod_Model

open scoped Pointwise

namespace OnlineCRS.Submod

/-- §3, p. 16: a (possibly random) CRS `π` for the polytope `P`, encoded by weights `ρ x φ` over maps
`φ : 2^N → 2^N`. For every input `x`, `ρ x` is a probability distribution on maps, and every map in its
support returns, for every `S ⊆ N`, a subset `φ S ⊆ S` that obeys `P`, i.e. `1_{φ S} ∈ P`. -/
def IsCRS {α : Type} [Fintype α] [DecidableEq α] (P : Set (α → ℝ))
    (ρ : (α → ℝ) → (Finset α → Finset α) → ℝ) : Prop :=
  ∀ x, (∀ φ, 0 ≤ ρ x φ) ∧ (∑ φ : Finset α → Finset α, ρ x φ) = 1 ∧
    ∀ φ, ρ x φ ≠ 0 → ∀ S : Finset α, φ S ⊆ S ∧ indicatorVec (φ S) ∈ P

open Classical in
/-- `Pr[e ∈ π(S)]` for the CRS with weights `ρ` on input `x`, for a fixed set `S`. -/
noncomputable def crsProb {α : Type} [Fintype α] [DecidableEq α]
    (ρ : (α → ℝ) → (Finset α → Finset α) → ℝ) (x : α → ℝ) (S : Finset α) (e : α) : ℝ :=
  ∑ φ : Finset α → Finset α, ρ x φ * (if e ∈ φ S then 1 else 0)

open Classical in
/-- Definition 3.1, first bullet (p. 16), with the printed slip `≥ c · x_e` read as `≥ c` (see Lemma 3.4's
proof, p. 17, and Definition 4.5): the CRS `ρ` is `(b, c)`-balanced for `P` if
`Pr[e ∈ π(R(x)) | e ∈ R(x)] ≥ c` whenever `x ∈ bP` and `x_e > 0`. Since `Pr[e ∈ R(x)] = x_e`, this is
written without division as `Pr[e ∈ π(R(x)) ∧ e ∈ R(x)] ≥ c · x_e`. -/
def IsBalanced {α : Type} [Fintype α] [DecidableEq α] (P : Set (α → ℝ)) (b c : ℝ)
    (ρ : (α → ℝ) → (Finset α → Finset α) → ℝ) : Prop :=
  ∀ x ∈ b • P, ∀ e : α, 0 < x e →
    c * x e ≤ ∑ A : Finset α, OnlineCRS.Matroid.activeProb x A *
      ∑ φ : Finset α → Finset α, ρ x φ * (if e ∈ A ∧ e ∈ φ A then 1 else 0)

/-- Definition 3.1, second bullet (p. 16): the CRS `ρ` is monotone if
`Pr[e ∈ π(S₁)] ≥ Pr[e ∈ π(S₂)]` whenever `e ∈ S₁ ⊆ S₂`, for every input `x`. -/
def IsMonotoneCRS {α : Type} [Fintype α] [DecidableEq α]
    (ρ : (α → ℝ) → (Finset α → Finset α) → ℝ) : Prop :=
  ∀ x, ∀ e : α, ∀ S₁ S₂ : Finset α, e ∈ S₁ → S₁ ⊆ S₂ → crsProb ρ x S₂ e ≤ crsProb ρ x S₁ e

open Classical in
/-- Definition 3.2 (p. 16): for a fixed family `F_x = Fam`,
`π̄(A) = {e ∈ A | I ∪ {e} ∈ F_x ∀ I ⊆ A, I ∈ F_x}`. -/
noncomputable def charMap {α : Type} [DecidableEq α] (Fam : Finset (Finset α)) (A : Finset α) :
    Finset α :=
  A.filter (fun e => OnlineCRS.Matroid.Selectable Fam A e)

open Classical in
/-- Definition 3.2 (p. 16): the characteristic CRS `π̄` of the randomized greedy OCRS `w`. On input `x`
it draws `F_x` from `w x` and applies `charMap F_x`, so the weight of a map `φ` is the total weight of the
families `Fam` with `charMap Fam = φ`. -/
noncomputable def charCRS {α : Type} [Fintype α] [DecidableEq α]
    (w : (α → ℝ) → Finset (Finset α) → ℝ) : (α → ℝ) → (Finset α → Finset α) → ℝ :=
  fun x φ => ∑ Fam : Finset (Finset α), w x Fam * (if φ = charMap Fam then 1 else 0)

end OnlineCRS.Submod


