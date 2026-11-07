-- Prove2me | Definitions.Def_PlantedIQP_distributions
-- name    : PlantedIQP_distributions
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:21:13.218626+00:00
-- url     : https://prove2.me/theorems/a66e8db1-6073-49fd-bc35-cce6c7c75c45
-- title:
--   The laws $P_3(n)$, $P_2(n)$, $M(n)$ and the planted law $P_3(n,h)$
-- statement:
--   1. $P_3(n)$ is the uniform distribution on cubic polynomials with constant term $0$: all coefficients independent and uniform on $\mathbb F_2$.
--   2. $P_2(n)$ is the uniform distribution on polynomials of degree at most $2$ with constant term $0$.
--   3. $M(n)$, for a distribution $D$ on cubic polynomials, is the law of $f=g+f^{(3)}$ with $g\leftarrow P_2(n)$ and $f^{(3)}\leftarrow D$ independent.
--   4. The **planted law**: let $U=\mathrm{span}\{e_1,\dots,e_h\}$. Draw $f\leftarrow P_3(n)$, set to $0$ the coefficient of $x_ix_jx_k$ whenever $i<j<k\le h$ (giving $\tilde f$), draw $A\leftarrow GL(n,\mathbb F_2)$ uniformly and independently, and output the public polynomial and the secret space
--
--   $$
--   g=\tilde f\circ A,\qquad V=A^{-1}U .
--   $$
--
--   $P_3(n,h)$ is the law of $g$. The joint law of $(g,V)$ is kept, since the verifier of Theorem 43 knows $V$.
--
--   **Formalization Note** Laws on finite sets are weight functions (uniform finite averages); $D$ is a `PMF`. The planted law is stated for every $h$ ($h=0$ plants nothing); the source fixes $1\le h\le n$.
-- source:
--   Bläser, Gullans, Hangleiter, Liu, Qiao, Verifiable quantum advantage based on polynomials with planted structures, arXiv:2609.39918 (sha256 6e261694…), p.7, p.20 and Section 2.3, p.17

import Mathlib
import Definitions.Def_PlantedIQP_comp

set_option autoImplicit false

namespace PlantedIQP

/-!
# The distributions `P₃(n)`, `P₂(n)`, `M(n)` and the planted law `P₃(n, h)`

Bläser et al., arXiv:2609.39918 (sha256 6e261694…):
* p.7: "Let P₃(n) be the uniform distribution over cubic polynomials with constant term 0 in
  𝔽₂[x₁, …, xₙ]. That is, the coefficients of x_ix_jx_k, x_ix_j, and x_k, are sampled independently
  and uniformly from 𝔽₂."
* p.20: "Let P_d(n) be the uniform distribution over polynomials with degree at most d in
  𝔽₂[x₁, …, xₙ] with constant term 0 […] Let M(n) be the distribution over cubic Boolean polynomials
  in 𝔽₂[x₁, …, xₙ] obtained by defining f = g + f^{(3)}, where g ← P₂(n) and f^{(3)} is drawn from an
  arbitrary distribution D over cubic polynomials."
* Section 2.3, p.17: "Fix an integer 1 ≤ h ≤ n and let U = span{e₁, …, e_h}. We first sample a cubic
  Boolean polynomial f ← P₃(n). We then plant an independent space in its cubic component by setting
  the coefficient of x_ix_jx_k to zero whenever 1 ≤ i < j < k ≤ h, leaving all other coefficients
  unchanged. […] we independently sample A ← GL(n, 𝔽₂) uniformly and set g(x) = f̃(Ax), V = A⁻¹U,
  and then reduce g to its unique multilinear representation using xᵢ² = xᵢ. […] We denote the
  resulting distribution of g by P₃(n, h)."

**Formalization Note.**
* Distributions on finite sets are weight functions into `ℝ` (uniform finite averages); `D` in
  `M(n)` is a `PMF`, read through `ENNReal.toReal`.
* `plantedProb n h E` is the probability of the event `E(g, V)` for the joint law of the public
  polynomial `g` and the secret space `V = A⁻¹U`, i.e. the fraction of pairs `(f, A)` with
  `f ∈ P₃(n)`, `A ∈ GL(n, 𝔽₂)` for which `E` holds. `plantedWeight n h g` is the marginal `P₃(n, h)`.
* `U = span{e_i : i < h}` (indices `Fin n`). The source requires `1 ≤ h ≤ n`; the definition is
  stated for every `h` (at `h = 0` nothing is planted; for `h ≥ n` every cubic coefficient is zeroed).
* `V = A⁻¹U` is the preimage `{v : A v ∈ U}` (`Submodule.comap` of `A`).
-/

open Classical in
/-- The weight of `f` under `P₃(n)`: uniform on all cubic polynomials with constant term 0. -/
noncomputable def unifP3 (n : ℕ) (_f : CubicPoly n) : ℝ :=
  1 / (Fintype.card (CubicPoly n) : ℝ)

open Classical in
/-- The weight of `g` under `P₂(n)`: uniform on the polynomials of degree at most 2 with constant
term 0 (those with no cubic coefficient). -/
noncomputable def unifP2 (n : ℕ) (g : CubicPoly n) : ℝ :=
  if g.c3 = 0 then
    1 / ((Finset.univ.filter fun g' : CubicPoly n => g'.c3 = 0).card : ℝ)
  else 0

open Classical in
/-- The weight of `f` under `M(n)` with cubic-part law `D`: `f = g + f^{(3)}` with `g ← P₂(n)` and
`f^{(3)} ← D` independent (p.20). -/
noncomputable def mixM {n : ℕ} (D : PMF (CubicPoly n)) (f : CubicPoly n) : ℝ :=
  ∑ f3 : CubicPoly n, ∑ g : CubicPoly n,
    (D f3).toReal * unifP2 n g * (if g + f3 = f then 1 else 0)

/-- The coordinate subspace `U = span{e_i : i < h}` (Section 2.3). -/
noncomputable def coordSub (n h : ℕ) : Submodule (ZMod 2) (Vec n) :=
  Submodule.span (ZMod 2) (Set.range fun i : {i : Fin n // (i : ℕ) < h} => stdBasis i.1)

/-- Planting: zero the coefficient of `x_i x_j x_k` whenever all three indices are `< h`, leaving
all other coefficients unchanged (the polynomial `f̃` of Section 2.3). -/
def plant {n : ℕ} (h : ℕ) (f : CubicPoly n) : CubicPoly n :=
  ⟨fun S => if ∀ i ∈ S.1, (i : ℕ) < h then 0 else f.c3 S, f.c2, f.c1⟩

/-- The secret space `V = A⁻¹U = {v : A v ∈ U}`. -/
noncomputable def hiddenSpace {n : ℕ} (h : ℕ) (A : Matrix.GeneralLinearGroup (Fin n) (ZMod 2)) :
    Submodule (ZMod 2) (Vec n) :=
  (coordSub n h).comap (Matrix.mulVecLin (A : Matrix (Fin n) (Fin n) (ZMod 2)))

open Classical in
/-- The probability of the event `E(g, V)` under the joint planted law of `(g, V)`:
`f ← P₃(n)`, `A ← GL(n, 𝔽₂)` uniform and independent, `g = f̃ ◦ A`, `V = A⁻¹U` (Section 2.3). -/
noncomputable def plantedProb (n h : ℕ) (E : CubicPoly n → Submodule (ZMod 2) (Vec n) → Prop) : ℝ :=
  ((Finset.univ.filter fun p : CubicPoly n × Matrix.GeneralLinearGroup (Fin n) (ZMod 2) =>
      E ((plant h p.1).comp p.2) (hiddenSpace h p.2)).card : ℝ) /
    (Fintype.card (CubicPoly n × Matrix.GeneralLinearGroup (Fin n) (ZMod 2)) : ℝ)

/-- The weight of `g` under `P₃(n, h)`, the marginal law of the public polynomial. -/
noncomputable def plantedWeight (n h : ℕ) (g : CubicPoly n) : ℝ :=
  plantedProb n h (fun g' _ => g' = g)

end PlantedIQP


