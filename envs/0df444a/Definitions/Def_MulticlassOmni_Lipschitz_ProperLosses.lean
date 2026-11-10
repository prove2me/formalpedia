-- Prove2me | Definitions.Def_MulticlassOmni_Lipschitz_ProperLosses
-- name    : MulticlassOmni_Lipschitz_ProperLosses
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T22:09:00.860932+00:00
-- url     : https://prove2.me/theorems/03faf315-ce01-458a-8936-e35bd9f91238
-- title:
--   Definition 2.1 — proper, bounded proper ($L_{\mathrm{proper}}$) and $\ell_1$-Lipschitz proper ($L_{\mathrm{lip\text{-}proper}}$) losses
-- statement:
--   Labels $[k]=\{1,\dots,k\}$ are encoded as `Fin k` (the source label $y$ is the index $y-1$). Reports are vectors $r\in\mathbb R^k$; $\Delta_k$ is the closed probability simplex `stdSimplex ℝ (Fin k)`. A loss is a real function $\ell(r,y)$; only its values at reports $r\in\Delta_k$ are used.
--
--   - `dot u v` $=\langle u,v\rangle=\sum_y u_yv_y$; `expect q g` $=\mathbb E_{y\sim q}[g(y)]=\sum_y q_y\,g(y)$; `l1dist r r'` $=\|r-r'\|_1=\sum_i|r_i-r'_i|$; `unitVec y` $=e_y$.
--   - **Proper** (`IsProper`): $\mathbb E_{y\sim q}[\ell(q,y)]\le\mathbb E_{y\sim q}[\ell(r,y)]$ for all $q,r\in\Delta_k$. It is stated through the published definition `UCalibDirichlet.IsProperLoss` applied to `toEReal ℓ`, which embeds the real values on $\Delta_k$ into `EReal` and is $0$ off the simplex; for a real-valued loss that predicate's extra clause (never $-\infty$) holds automatically, so this is exactly the weak-inequality properness of Definition 2.1.
--   - $L_{\mathrm{proper}}$ (`IsBoundedProper`, `properFamily`): proper and $\ell(r,y)\in[0,1]$ for all $r\in\Delta_k$, $y\in[k]$.
--   - $L_{\mathrm{lip\text{-}proper}}$ (`IsLipProper`, `lipProperFamily`): in $L_{\mathrm{proper}}$ and $|\ell(r,y)-\ell(r',y)|\le\|r-r'\|_1$ for all $r,r'\in\Delta_k$, $y\in[k]$.
-- source:
--   Hu, Luo, Schneider, Yang (2026), Sample Complexity of Multiclass Omniprediction, supplied PDF (SHA-256 aaa73474…584f0, citation basis published; STOC 2027 submission), §2 (p. 9), Definition 2.1 (p. 10)

import Mathlib
import Definitions.Def_UCalibDirichlet_IsProperLoss

namespace MulticlassOmni.Lipschitz

/-! # Proper, bounded proper and Lipschitz proper losses (Definition 2.1)

Hu, Luo, Schneider, Yang (2026), *Sample Complexity of Multiclass Omniprediction*, supplied PDF,
§2 (p. 9) and Definition 2.1 (p. 10).

**Conventions.** Labels `[k] = {1, …, k}` are `Fin k`: the source label `y` is `⟨y - 1, _⟩`, so
the source's label `1` is the index `0`. A report `r ∈ Δ_k` is a vector `r : Fin k → ℝ` lying in
`stdSimplex ℝ (Fin k)` (the whole closed simplex). A loss `ℓ : Δ_k × [k] → ℝ` is a total function
`(Fin k → ℝ) → Fin k → ℝ`; only its values on the simplex are ever constrained or used. -/

/-- A real-valued loss on reports `r ∈ ℝ^k` and labels `y ∈ Fin k`; only the values at reports in
the simplex `Δ_k` matter. -/
abbrev Loss (k : ℕ) := (Fin k → ℝ) → Fin k → ℝ

/-- Euclidean inner product `⟨u, v⟩ = ∑_y u_y v_y` on `ℝ^k`. -/
def dot {k : ℕ} (u v : Fin k → ℝ) : ℝ := ∑ y, u y * v y

/-- The expectation `E_{y∼q}[g(y)] = ∑_y q_y g(y)` of `g : [k] → ℝ` under a label
distribution `q ∈ Δ_k`. -/
def expect {k : ℕ} (q : Fin k → ℝ) (g : Fin k → ℝ) : ℝ := ∑ y, q y * g y

/-- The `ℓ1` distance `‖r - r'‖₁ = ∑_i |r_i - r'_i|` (Definition 2.1; not Mathlib's sup norm). -/
def l1dist {k : ℕ} (r r' : Fin k → ℝ) : ℝ := ∑ i, |r i - r' i|

/-- The unit vector `e_y` (the point mass on label `y`). -/
def unitVec {k : ℕ} (y : Fin k) : Fin k → ℝ := Pi.single y 1

/-- Real-loss adapter to the published definition `UCalibDirichlet.IsProperLoss`: embed the
real value `ℓ(r, y)` into `EReal` at reports in the simplex and extend by `0` elsewhere (values off
the simplex are never read by that predicate). -/
noncomputable def toEReal {k : ℕ} (ℓ : Loss k) : (Fin k → ℝ) → Fin k → EReal :=
  fun r y => by classical exact if r ∈ stdSimplex ℝ (Fin k) then ((ℓ r y : ℝ) : EReal) else 0

/-- **Proper loss** (Definition 2.1, p. 10): for all `q, r ∈ Δ_k`,
`E_{y∼q}[ℓ(q, y)] ≤ E_{y∼q}[ℓ(r, y)]`. Stated through the published platform definition
`UCalibDirichlet.IsProperLoss` applied to the real-to-`EReal` adapter `toEReal`; for a real-valued
loss its extra clause "never `−∞`" holds automatically. -/
def IsProper {k : ℕ} (ℓ : Loss k) : Prop :=
  UCalibDirichlet.IsProperLoss (toEReal ℓ)

/-- Membership in `L_proper` (Definition 2.1): `ℓ` is proper and `ℓ(r, y) ∈ [0, 1]` for every
`r ∈ Δ_k` and `y ∈ [k]`. -/
def IsBoundedProper {k : ℕ} (ℓ : Loss k) : Prop :=
  IsProper ℓ ∧ ∀ r ∈ stdSimplex ℝ (Fin k), ∀ y, ℓ r y ∈ Set.Icc (0 : ℝ) 1

/-- Membership in `L_lip-proper` (Definition 2.1): `ℓ ∈ L_proper` and `ℓ` is 1-Lipschitz in its
first argument for the `ℓ1` norm: `|ℓ(r, y) - ℓ(r', y)| ≤ ∑_i |r_i - r'_i|` for all
`r, r' ∈ Δ_k`, `y ∈ [k]`. -/
def IsLipProper {k : ℕ} (ℓ : Loss k) : Prop :=
  IsBoundedProper ℓ ∧
    ∀ r ∈ stdSimplex ℝ (Fin k), ∀ r' ∈ stdSimplex ℝ (Fin k), ∀ y,
      |ℓ r y - ℓ r' y| ≤ l1dist r r'

/-- The family `L_proper`. -/
def properFamily (k : ℕ) : Set (Loss k) := {ℓ | IsBoundedProper ℓ}

/-- The family `L_lip-proper`. -/
def lipProperFamily (k : ℕ) : Set (Loss k) := {ℓ | IsLipProper ℓ}

end MulticlassOmni.Lipschitz


