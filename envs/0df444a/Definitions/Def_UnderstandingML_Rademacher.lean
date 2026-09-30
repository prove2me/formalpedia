-- Prove2me | Definitions.Def_UnderstandingML_Rademacher
-- name    : UnderstandingML_Rademacher
-- status  : Definition
-- author  : @naimengye
-- created : 2026-09-24T05:37:19.313799+00:00
-- url     : https://prove2.me/theorems/300cdc3c-4436-40c3-b51f-d1544577897f
-- title:
--   Chapter 26: sign vectors, the Rademacher complexity R(A) (26.5), evaluation sets F ∘ S, loss classes ℓ ∘ H, representativeness (26.1), and the linear evaluation sets H₂ ∘ S and H₁ ∘ S
-- statement:
--   Chapter 26 of Shalev-Shwartz and Ben-David. `signVec σ` encodes $\sigma \in \{\pm1\}^m$ by `Bool`. `rademacher A` is the **Rademacher complexity** $R(A) = \frac1m\mathbb{E}_\sigma\big[\sup_{a \in A}\sum_i\sigma_i a_i\big]$ of $A \subseteq \mathbb{R}^m$ (26.5), the expectation over the uniform $\sigma$ being the average over the $2^m$ sign vectors and the supremum the real supremum over $A$. `evalSet F S` is $F \circ S = \{(f(z_1), \dots, f(z_m)) : f \in F\}$, `lossClass loss H` is $\ell \circ H = \{z \mapsto \ell(h, z) : h \in H\}$, so `rademacher (evalSet (lossClass loss H) S)` is $R(\ell \circ H \circ S)$ (26.4). `representativeness loss H D S` is $\operatorname{Rep}_D(\ell \circ H, S) = \sup_{h \in H}(L_D(h) - L_S(h))$ (26.1), with the risks of Chapter 2. `linearEvalSet B x` is $\{(\langle w, x_1\rangle, \dots, \langle w, x_m\rangle) : \|w\|_2 \le B\}$ for vectors in an inner product space ($H_2 \circ S$ for $B = 1$), and `l1EvalSet B x` is the same with $\|w\|_1 \le B$ in $\mathbb{R}^n$ ($H_1 \circ S$).
-- source:
--   Shalev-Shwartz and Ben-David, Understanding Machine Learning: From Theory to Algorithms, Cambridge University Press 2014, doi:10.1017/CBO9781107298019, §26.1 pp. 375-376 (Definition 26.1, Equations (26.1)-(26.5)), §26.2 p. 382 (Equation (26.14), H₂ ∘ S, H₁ ∘ S)

import Definitions.Def_UnderstandingML_Framework
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Topology.Bornology.Basic

/-!
# Shalev-Shwartz and Ben-David, *Understanding Machine Learning*, Chapter 26: Rademacher
# complexities

Shalev-Shwartz and Ben-David, *Understanding Machine Learning: From Theory to Algorithms*,
Cambridge University Press 2014, doi:10.1017/CBO9781107298019, §26.1–§26.4.

**Representativeness and Rademacher complexity (§26.1, pp. 375–376).** For `F = ℓ ∘ H`,
`Rep_D(F, S) = sup_{f ∈ F} (L_D(f) − L_S(f))` (26.1). For a sample `S`, `F ∘ S` is the set of
evaluation vectors `(f(z₁), …, f(z_m))`, `f ∈ F`. For `A ⊆ ℝ^m`, the **Rademacher complexity** is
`R(A) = (1/m) E_σ [sup_{a ∈ A} ∑ᵢ σᵢ aᵢ]` (26.5), the `σᵢ` being i.i.d. uniform on `{±1}`, and
`R(F ∘ S)` is the Rademacher complexity of `F` with respect to `S` (26.4).

**Linear classes (§26.2, p. 382).** `H₂ ∘ S = {(⟨w, x₁⟩, …, ⟨w, x_m⟩) : ‖w‖₂ ≤ 1}` for `xᵢ` in a
Hilbert space, and `H₁ ∘ S` likewise with `‖w‖₁ ≤ 1` in `ℝⁿ` (26.14).

**Losses of the form (26.18) (§26.3–§26.4).** `ℓ(w, (x, y)) = φ(⟨w, x⟩, y)` with `a ↦ φ(a, y)`
`ρ`-Lipschitz for every `y`.

**Conventions.** The expectation over `σ ∈ {±1}^m` is the average over the `2^m` sign vectors,
so `R(A)` is a finite sum; the supremum over `A` is the real supremum over the subtype `A`
(`0` for empty `A`), and the theorems assume `A` nonempty and bounded where a supremum is
taken. Risks and empirical risks are those of Chapter 2 (`risk`, `empRisk`), samples are
`Fin m`-indexed and `S ∼ D^m` is `iidLaw D m`. Expectations of suprema over uncountable classes
require the measurability hypotheses stated with each theorem (Remark 3.1).
-/

open MeasureTheory
open scoped InnerProductSpace

namespace UnderstandingML

/-! ### Rademacher complexity -/

section Complexity

variable {m : ℕ}

/-- A sign vector `σ ∈ {±1}^m`, encoded by `Bool` (`true ↦ +1`). -/
def signVec (σ : Fin m → Bool) : Fin m → ℝ := fun i ↦ if σ i then 1 else -1

/-- The **Rademacher complexity** `R(A) = (1/m) E_σ [sup_{a ∈ A} ∑ᵢ σᵢ aᵢ]` of `A ⊆ ℝ^m` (26.5),
the expectation being the average over all `2^m` sign vectors. -/
noncomputable def rademacher (A : Set (Fin m → ℝ)) : ℝ :=
  (1 / m) * ((1 / 2 ^ m) * ∑ σ : Fin m → Bool, ⨆ a : A, ∑ i, signVec σ i * (a : Fin m → ℝ) i)

/-- `F ∘ S = {(f(z₁), …, f(z_m)) : f ∈ F}` (p. 376). -/
def evalSet {Z : Type*} (F : Set (Z → ℝ)) (S : Fin m → Z) : Set (Fin m → ℝ) :=
  {v | ∃ f ∈ F, v = fun i ↦ f (S i)}

/-- `ℓ ∘ H = {z ↦ ℓ(h, z) : h ∈ H}` (p. 375). -/
def lossClass {Z Hyp : Type*} (loss : Hyp → Z → ℝ) (H : Set Hyp) : Set (Z → ℝ) :=
  {f | ∃ h ∈ H, f = loss h}

/-- The **representativeness** `Rep_D(ℓ ∘ H, S) = sup_{h ∈ H} (L_D(h) − L_S(h))` (26.1). -/
noncomputable def representativeness {Z Hyp : Type*} [MeasurableSpace Z] (loss : Hyp → Z → ℝ)
    (H : Set Hyp) (D : Measure Z) (S : Fin m → Z) : ℝ :=
  ⨆ h : H, (risk loss D h - empRisk loss S h)

/-- `H₂ ∘ S = {(⟨w, x₁⟩, …, ⟨w, x_m⟩) : ‖w‖ ≤ B}` for vectors `xᵢ` in an inner product space
(Lemma 26.10 with `B = 1`; §26.3 with `H = {w : ‖w‖₂ ≤ B}`). -/
def linearEvalSet {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (B : ℝ)
    (x : Fin m → E) : Set (Fin m → ℝ) :=
  {v | ∃ w : E, ‖w‖ ≤ B ∧ v = fun i ↦ ⟪w, x i⟫_ℝ}

/-- `H₁ ∘ S = {(⟨w, x₁⟩, …, ⟨w, x_m⟩) : ‖w‖₁ ≤ B}` for vectors `xᵢ ∈ ℝⁿ` (Lemma 26.11 with
`B = 1`; §26.4). -/
def l1EvalSet {n : ℕ} (B : ℝ) (x : Fin m → Fin n → ℝ) : Set (Fin m → ℝ) :=
  {v | ∃ w : Fin n → ℝ, ∑ j, |w j| ≤ B ∧ v = fun i ↦ dotProduct w (x i)}

end Complexity

end UnderstandingML


