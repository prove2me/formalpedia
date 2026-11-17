-- Prove2me | Definitions.Def_QSDMixing_GU_Supplement_TriangularWalk
-- name    : QSDMixing_GU_Supplement_TriangularWalk
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T04:39:56.648808+00:00
-- url     : https://prove2.me/theorems/70a0d9a9-283f-4812-8aa2-a5d2beab54ad
-- title:
--   Independent triangular feature walk and its conditional Fourier biases
-- statement:
--   A **triangular feature walk** has independent finite coordinates $X_1,\ldots,X_n$, finite abelian target factors $B_1,\ldots,B_n$, and a feature map
--
--   $$
--   \Phi(x)=\bigl(\Phi_1(x_{\le1}),\ldots,\Phi_n(x_{\le n})\bigr).
--   $$
--
--   The $t$-step walk is $Z_t=\sum_{j=1}^t\Phi(X^j)$. For each target factor, $\lambda_i$ is the largest squared conditional Fourier bias from equation (23); $\lambda=\max_i\lambda_i$ and $r=\max_i\log|B_i|$. The file defines the exact walk law, its total variation from uniformity, and its positive-integer mixing time.
--
--   The integer-valued mixing bound takes the ceiling of the real threshold in equation (25), treats $\lambda=0$ by the time-two estimate furnished by equation (24), and returns $\infty$ when $\lambda\ge1$.
-- source:
--   Zhou, Leditzky, A mixing time method for estimating the sample complexity of quantum state discrimination, arXiv:2609.40182 (held version, sha256 62fb68dd…), §4.1, pp.24–25, eqs. (23)–(25), (113)–(119)

import Mathlib
import Definitions.Def_QSDMixing_GU_Supplement_FiniteProbability

set_option autoImplicit false

namespace QSDMixing.GU.Supplement

noncomputable local instance triangularWalkDecidableEq {α : Type} : DecidableEq α :=
  Classical.decEq α

/-- Independent finite coordinates together with a triangular feature map into a product of
finite abelian groups, as in §4.1. -/
structure TriangularWalk (n : ℕ) where
  Source : Fin n → Type
  Target : Fin n → Type
  [sourceFintype : ∀ i, Fintype (Source i)]
  [targetFintype : ∀ i, Fintype (Target i)]
  [targetGroup : ∀ i, AddCommGroup (Target i)]
  marginal : ∀ i, FiniteProbability (Source i)
  feature : (∀ i, Source i) → (∀ i, Target i)
  triangular : ∀ i x y, (∀ j, j.val ≤ i.val → x j = y j) → feature x i = feature y i

attribute [instance] TriangularWalk.sourceFintype TriangularWalk.targetFintype
  TriangularWalk.targetGroup

/-- Product probability of one source vector; its factorization records independence. -/
noncomputable def TriangularWalk.sampleMass {n : ℕ} (W : TriangularWalk n)
    (x : ∀ i, W.Source i) : ℝ :=
  ∏ i, W.marginal i (x i)

/-- Replace coordinate `i` of a dependent vector. -/
def TriangularWalk.replaceCoordinate {n : ℕ} (W : TriangularWalk n) (i : Fin n)
    (x y : ∀ j, W.Source j) : ∀ j, W.Source j :=
  fun j => if h : j = i then by subst j; exact y i else x j

/-- The squared conditional Fourier bias in (23), before maximizing over nontrivial characters. -/
noncomputable def TriangularWalk.biasValue {n : ℕ} (W : TriangularWalk n) (i : Fin n)
    (χ : AddChar (W.Target i) (unitary ℂ)) : ℝ :=
  ∑ x, W.sampleMass x *
    ‖∑ y, W.sampleMass y *
      (((χ (W.feature (W.replaceCoordinate i x y) i) : unitary ℂ) : ℂ))‖ ^ 2

/-- The number `λᵢ` from (23). If the factor `Bᵢ` is trivial, the maximum is over the empty
set and is assigned the harmless value zero. -/
noncomputable def TriangularWalk.lambda {n : ℕ} (W : TriangularWalk n) (i : Fin n) : ℝ :=
  sSup {v : ℝ | ∃ χ : AddChar (W.Target i) (unitary ℂ), χ ≠ 0 ∧ v = W.biasValue i χ}

/-- The law of `Z_t=∑_{j=1}^t Φ(X^j)` for independent source vectors. -/
noncomputable def TriangularWalk.walkLaw {n : ℕ} (W : TriangularWalk n) (t : ℕ)
    (z : ∀ i, W.Target i) : ℝ :=
  ∑ samples : Fin t → (∀ i, W.Source i),
    if (∀ i, z i = ∑ j, W.feature (samples j) i)
    then ∏ j, W.sampleMass (samples j) else 0

/-- Total variation from uniformity for the triangular walk. -/
noncomputable def TriangularWalk.tv {n : ℕ} (W : TriangularWalk n) (t : ℕ) : ℝ :=
  totalVariation (W.walkLaw t) (uniformMass (∀ i, W.Target i))

/-- The classical mixing time of the triangular walk, with times starting at one. -/
noncomputable def TriangularWalk.mixingTime {n : ℕ} (W : TriangularWalk n) (ε : ℝ) : ℕ∞ :=
  sInf {T : ℕ∞ | ∃ t : ℕ, 1 ≤ t ∧ T = t ∧ W.tv t ≤ ε}

/-- `λ=maxᵢ λᵢ`. -/
noncomputable def TriangularWalk.lambdaMax {n : ℕ} (W : TriangularWalk n) : ℝ :=
  sSup (Set.range W.lambda)

/-- `r=maxᵢ log |Bᵢ|`. -/
noncomputable def TriangularWalk.rMax {n : ℕ} (W : TriangularWalk n) : ℝ :=
  sSup (Set.range (fun i => Real.log (Fintype.card (W.Target i) : ℝ)))

/-- The corrected integer-valued version of (25). For `0<λ<1` it is the natural-number ceiling
of the printed real threshold. At `λ=0`, (24) gives mixing by time two; at `λ≥1` the displayed
estimate supplies no finite bound. -/
noncomputable def TriangularWalk.mixingBound {n : ℕ} (W : TriangularWalk n) (ε : ℝ) : ℕ∞ :=
  if W.lambdaMax ≤ 0 then 2
  else if 1 ≤ W.lambdaMax then ⊤
  else (Nat.ceil ((W.rMax + 2 * Real.log (n / ε)) / (-Real.log W.lambdaMax)) : ℕ∞)

end QSDMixing.GU.Supplement


