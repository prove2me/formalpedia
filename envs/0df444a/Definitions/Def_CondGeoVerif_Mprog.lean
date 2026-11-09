-- Prove2me | Definitions.Def_CondGeoVerif_Mprog
-- name    : CondGeoVerif_Mprog
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T07:19:28.580098+00:00
-- url     : https://prove2.me/theorems/36362647-3806-4a20-809e-7f119272c2a6
-- title:
--   Conditional error-allocation programs $M_{0,\eta}$ and $M_{1,\eta}$, and the dual objective
-- statement:
--   Let $G\sim N(0,I_r)$ and let $D:\mathbb R^r\to\{0,1\}$ be a Borel disagreement indicator. An **error allocation** is a Borel function $e:\mathbb R^r\to[0,1]$ with $\mathbb E\,e(G)=\eta$; it is **first-moment free** if in addition $\mathbb E[G\,e(G)]=0$. The two **conditional programs** are
--   $$M_{0,\eta}(D)=\sup\{\mathbb E[e(G)D(G)]: 0\le e\le1,\ \mathbb Ee=\eta\},$$
--   $$M_{1,\eta}(D)=\sup\{\mathbb E[e(G)D(G)]: 0\le e\le1,\ \mathbb Ee=\eta,\ \mathbb E[Ge]=0\}.$$
--   The **dual objective** of the first-moment program at $(\alpha,\gamma)\in\mathbb R\times\mathbb R^r$ is
--   $$\eta\alpha+\mathbb E\big(D(G)-\alpha-\gamma\cdot G\big)_+ ,$$
--   and with $\gamma=0$ it is the dual objective of the mass-only program. A pair $(\alpha,\gamma)$ is a **dual minimizer** if it minimizes this objective over all of $\mathbb R\times\mathbb R^r$.
--
--   The programs measure how much disagreement an error budget $\eta$ can capture while keeping its mass, and in $M_1$ also its first moments, fixed.
--
--   **Formalization Note** The program index $j\in\{0,1\}$ is `Fin 2`. Allocations take values in $[0,1]$ everywhere (every $L^2$ class with $0\le e\le1$ has such a representative). For $0\le\eta\le1$ the value set is nonempty (the constant $\eta$ is feasible) and bounded by $1$, so the real supremum is the true one; all statements assume $0<\eta<1/2$. For $r=0$ the value is $\eta D$, the paper's convention.
-- source:
--   T. Y. Chen, The Conditional Geometry of Statistical Verification, manuscript (October 2026, STOC 2027 submission, sha256 07a66d18…), §3, p.4 (PDF p.7); §A.1, p.13 (PDF p.16); Lemma A.2, p.14 (PDF p.17)

import Mathlib
import Definitions.Def_CondGeoVerif_projClass

set_option autoImplicit false

namespace CondGeoVerif

open MeasureTheory

/-- The `{0,1}` indicator of a Boolean, as a real number. -/
def ind (b : Bool) : ℝ := if b then 1 else 0

/-- The feasible error allocations of the conditional programs (Chen, *The Conditional Geometry
of Statistical Verification*, manuscript, October 2026, sha256 07a66d18…, §A.1, p.13 = PDF p.16;
§B.1, p.25): Borel `e : ℝʳ → [0, 1]` with `E e(G) = η`, and, for `j = 1`, also
`E[G e(G)] = 0` (every coordinate), where `G ∼ N(0, I_r)`. -/
def errorAllocs (j : Fin 2) (η : ℝ) (r : ℕ) : Set (Vec r → ℝ) :=
  {e | Measurable e ∧ (∀ z, 0 ≤ e z ∧ e z ≤ 1) ∧ ∫ z, e z ∂(gauss r) = η ∧
    (j = 1 → ∀ i : Fin r, ∫ z, z i * e z ∂(gauss r) = 0)}

/-- **The conditional programs** `M_{0,η}` and `M_{1,η}` (Chen, Oct. 2026, §3, p.4 = PDF p.7;
§A.1, p.13 = PDF p.16): for a Borel disagreement indicator `D : ℝʳ → {0, 1}`,
`M_{0,η}(D) = sup {E[e(G) D(G)] : 0 ≤ e ≤ 1, E e = η}` and
`M_{1,η}(D) = sup {E[e(G) D(G)] : 0 ≤ e ≤ 1, E e = η, E[G e] = 0}`, `G ∼ N(0, I_r)`.

**Formalization Note** `j : Fin 2` selects the program. Allocations are Borel functions with
values in `[0, 1]` everywhere (every `L²` class with `0 ≤ e ≤ 1` has such a representative). For
`0 ≤ η ≤ 1` the value set is nonempty (the constant `η` is feasible, since the Gaussian has mean
zero) and bounded by `1`, so `sSup` is the true supremum; all statements assume `0 < η < 1/2`. For
`r = 0` the space is a point and the value is `η D`, the paper's `r = 0` convention. -/
noncomputable def Mprog (j : Fin 2) (η : ℝ) {r : ℕ} (D : Vec r → Bool) : ℝ :=
  sSup ((fun e => ∫ z, e z * ind (D z) ∂(gauss r)) '' errorAllocs j η r)

/-- The dual objective of the first-moment program (Chen, Oct. 2026, Lemma A.2, p.14):
`ηα + E(D(G) − α − γ·G)₊`. With `γ = 0` it is the dual objective of the mass-only program. -/
noncomputable def dualObj (η : ℝ) {r : ℕ} (D : Vec r → Bool) (α : ℝ) (γ : Vec r) : ℝ :=
  η * α + ∫ z, max (ind (D z) - α - inner ℝ γ z) 0 ∂(gauss r)

/-- `(α, γ)` minimizes the dual objective of the first-moment program for `D`. -/
def IsDualMin (η : ℝ) {r : ℕ} (D : Vec r → Bool) (α : ℝ) (γ : Vec r) : Prop :=
  ∀ α' : ℝ, ∀ γ' : Vec r, dualObj η D α γ ≤ dualObj η D α' γ'

end CondGeoVerif


