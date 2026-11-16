-- Prove2me | Definitions.Def_SparseSDP_TwoSided_Supplement_cvec
-- name    : SparseSDP_TwoSided_Supplement_cvec
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:29:43.22072+00:00
-- url     : https://prove2.me/theorems/a52ff2a9-18fb-4d7a-94b2-289596d22bbe
-- title:
--   Complex vector primitives, $\mathrm{Haar}(\mathbb C^d)$ and squared-amplitude sampling, as charged programs
-- statement:
--   Complex vectors $x\in\mathbb C^d$ and the charged operations Algorithm 5 performs on them, in the published cost model of §2.2 (`SparseSDP.TwoSided.Prog`).
--
--   1. $ax+y$ for $a\in\mathbb C$ and the inner product $x^\dagger y$, each charged $8d$; the norm $\|x\|_2$, charged $4d+1$; $ax$ for real $a$, charged $2d$. A complex addition counts as $2$ real operations and a complex multiplication as $6$.
--   2. **Haar measure** $\mathrm{Haar}(\mathbb C^d)$: the law of $g/\|g\|_2$, where the $2d$ real and imaginary parts of $g\in\mathbb C^d$ are i.i.d. standard Gaussians. By unitary invariance of the complex Gaussian this is the unitarily invariant probability measure on the unit sphere of $\mathbb C^d$.
--   3. The draw of $u\sim\mathrm{Haar}(\mathbb C^d)$ from the random tape: $2d$ Gaussian draws, then normalization, at cost $O(d)$.
--   4. **Squared-amplitude sampling** of a coordinate $I$ of $\psi\in\mathbb C^d$ with $\mathbb P[I=i]=|\psi_i|^2/\|\psi\|_2^2$, via the published scan on the weights $|\psi_i|^2$ (one uniform draw).
--
--   These are the random and arithmetic building blocks of the simultaneous Gibbs estimator (Algorithm 5, lines 6–9).
--
--   **Formalization Note** The weights of the coordinate sampler are those of the $d$ complex coordinates, not of the $2d$ real parts. The statements of the supplement are about the tape law; `haarLaw` documents what `drawHaar` samples.
-- source:
--   Brandão, Dalzell, Gilyén, Vasconcelos, Solving Sparse SDPs in Sublinear Time, arXiv:2609.40302, §2.2, p. 15; §2.3, pp. 15–16; §2.4, p. 16; Algorithm 5, lines 6–9, p. 36; runtime paragraph, p. 39

import Mathlib
import Definitions.Def_SparseSDP_TwoSided_Prog

open MeasureTheory ProbabilityTheory Matrix

namespace SparseSDP.TwoSided.Supplement

open SparseSDP.TwoSided

/-- Complex vectors of length `d`.

Brandão, Dalzell, Gilyén, Vasconcelos, *Solving Sparse SDPs in Sublinear Time*, arXiv:2609.40302,
§5 (pp. 27–38): Algorithm 5 works with vectors in `ℂⁿ`.

**Formalization Note.** The published cost model `SparseSDP.TwoSided.Prog` (§2.2, p. 15) lists real
operations only. A complex scalar operation is charged as a fixed number of listed real operations:
complex addition `2`, complex multiplication `6` (four products, two sums), `|z|² = Re² + Im²` `3`,
real-times-complex `2`. Vector primitives of length `d` below are charged accordingly. -/
abbrev CVec (d : ℕ) : Type := Fin d → ℂ

variable {d : ℕ}

/-- `a x + y` for a complex scalar `a`, charged `8d` (one complex product and one complex sum per
coordinate). -/
noncomputable def caxpy (a : ℂ) (x y : CVec d) : Prog (CVec d) := op (8 * d) (a • x + y)

/-- The complex inner product `x†y = ∑ᵢ conj(xᵢ) yᵢ`, charged `8d`. -/
noncomputable def cdotp (x y : CVec d) : Prog ℂ := op (8 * d) (∑ i, star (x i) * y i)

/-- `‖x‖₂`, charged `4d + 1` (three operations for `|xᵢ|²`, one addition, one square root). -/
noncomputable def cnrm (x : CVec d) : Prog ℝ := op (4 * d + 1) (l2 x)

/-- `a x` for a real scalar `a`, charged `2d`. -/
noncomputable def cscale (a : ℝ) (x : CVec d) : Prog (CVec d) := op (2 * d) ((a : ℂ) • x)

/-- `g ↦ g/‖g‖₂` on `ℂᵈ`. -/
noncomputable def haarNormalize (g : CVec d) : CVec d := ((1 / l2 g : ℝ) : ℂ) • g

/-- `Haar(ℂᵈ)` (§2.4, p. 16): the law of `g/‖g‖₂` for `g ∈ ℂᵈ` whose `2d` real coordinates
(real and imaginary parts) are i.i.d. `N(0,1)`, i.e. `g` is a standard complex Gaussian vector up to
the scale `√2`, which the normalization removes.

**Formalization Note.** Unitary invariance of the complex Gaussian makes this the unitarily
invariant probability measure on the unit sphere of `ℂᵈ`. `g = 0` is a null event for `d ≥ 1`. The
statements of the supplement are about `tapeLaw`; this measure documents what `drawHaar` samples. -/
noncomputable def haarLaw (d : ℕ) : Measure (CVec d) :=
  (Measure.pi fun _ : Fin d => (gaussianReal 0 1).prod (gaussianReal 0 1)).map
    fun p => haarNormalize fun i => (⟨(p i).1, (p i).2⟩ : ℂ)

/-- Draw `u ∼ Haar(ℂᵈ)` from the tape (Algorithm 5, line 6): `2d` Gaussian draws, then normalize.
Cost `O(d)` ("Sampling and explicitly storing one Haar-random vector costs `O(n)`", p. 39). -/
noncomputable def drawHaar (d : ℕ) : Prog (CVec d) := do
  let mut g : CVec d := 0
  for i in List.finRange d do
    tick 1
    let x ← drawGauss
    let y ← drawGauss
    g ← op 1 (Function.update g i (⟨x, y⟩ : ℂ))
  let nu ← cnrm g
  let inv ← op 1 (1 / nu)
  cscale inv g

/-- Squared-amplitude sampling over the `d` complex coordinates (Algorithm 5, line 9; §2.3, p. 16):
`P[I = i] = |ψᵢ|²/‖ψ‖₂²`, by the published scan `sampleCat` on the weights `|ψᵢ|²`.

**Formalization Note.** The weights are those of the `d` complex coordinates, not of the `2d`
real and imaginary parts. -/
noncomputable def csampleCoord [NeZero d] (x : CVec d) : Prog (Fin d) := do
  let w ← op (3 * d) (fun i => Complex.normSq (x i))
  sampleCat w

end SparseSDP.TwoSided.Supplement


