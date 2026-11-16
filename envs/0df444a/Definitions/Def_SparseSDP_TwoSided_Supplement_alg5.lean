-- Prove2me | Definitions.Def_SparseSDP_TwoSided_Supplement_alg5
-- name    : SparseSDP_TwoSided_Supplement_alg5
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:32:02.561985+00:00
-- url     : https://prove2.me/theorems/d3ab125b-46ba-4079-8ba9-5642ad63e87e
-- title:
--   Algorithm 5 (Simultaneous Gibbs Expectation Estimator) as a charged program
-- statement:
--   **Algorithm 5.** Input: a Hamiltonian $H=\sum_{\ell=1}^h y_\ell B_\ell$ with a bound $B_H\ge\|y\|_1$, observables $A_1,\dots,A_m$, a norm bound $\omega$, accuracy $\alpha$ and failure probability $\delta$; all matrices are read through row readers.
--
--   1. Set $g=\max\{1,\lceil c_g\log(2m/\delta)\rceil\}$, $b=\max\{1,\lceil c_b\omega^2/\alpha^2\rceil\}$, $N=gb$, $\zeta=c_0\alpha/\omega$, $\eta=\delta/(2N)$, $L_H=\log\big((2/\zeta)\sqrt{n/\eta}\big)$ and $q_H=\min\{n,\lceil C_L\sqrt{\max\{1,B_H,L_H\}}\,L_H\rceil\}$.
--   2. For each group $a=1,\dots,g$ and sample $k=1,\dots,b$: draw $u\sim\mathrm{Haar}(\mathbb C^n)$; compute $\tilde v=\mathrm{L\acute anczosExp}(-H/2,u,q_H)\approx e^{-H/2}u$; set $\tilde W=\|\tilde v\|_2^2$ and $\tilde\psi=\tilde v/\|\tilde v\|_2$; sample $I$ with $\mathbb P[I=i]=|\tilde\psi_i|^2$; set $\tilde X_j=\tilde W\,Z_{A_j}(\tilde\psi,I)=\tilde W\operatorname{Re}\big([A_j\tilde\psi]_I/\tilde\psi_I\big)$ for all $j$, reading only row $I$ of each $A_j$.
--   3. Form the group ratios $\hat\mu_j^{(a)}=\sum_k\tilde X_j^{(a,k)}/\sum_k\tilde W^{(a,k)}$ and return $\hat\mu_j=\operatorname{median}_a\hat\mu_j^{(a)}$.
--
--   The universal constants $c_g,c_b,c_0,C_L>0$ are the $\Theta(\cdot)$ and "sufficiently small/large" constants of the algorithm. The product with $H$ is computed term by term through the row readers of the $B_\ell$.
--
--   **Formalization Note** The median of an even number of values is the lower median, charged $g^2+1$ per observable. The counts $g,b$ are at least one, which only matters at $m=0$. The Hamiltonian is passed as a list of (index, coefficient) pairs; for Theorem 5.1 it is $[(1,y_1),\dots,(h,y_h)]$.
-- source:
--   Brandão, Dalzell, Gilyén, Vasconcelos, Solving Sparse SDPs in Sublinear Time, arXiv:2609.40302, Algorithm 5, p. 36; Eqs. (173)–(176), p. 35; runtime paragraph, p. 39

import Mathlib
import Definitions.Def_SparseSDP_TwoSided_Supplement_FamOracle
import Definitions.Def_SparseSDP_TwoSided_Supplement_lanczosC

open Matrix

namespace SparseSDP.TwoSided.Supplement

open SparseSDP.TwoSided

/-- The universal constants that Algorithm 5 leaves as `Θ(·)` or "sufficiently small/large"
(Algorithm 5, lines 1–3, p. 36; Eqs. (173)–(176), p. 35): `c_g` of `g = Θ(log(2m/δ))`, `c_b` of
`b = Θ(ω²/α²)`, `c₀` of `ζ = c₀α/ω`, and `C_L`, the constant of Proposition 4.3 in the Lánczos
degree `q_H`. -/
structure Consts5 where
  /-- `c_g`. -/
  cg : ℝ
  /-- `c_b`. -/
  cb : ℝ
  /-- `c₀`. -/
  c0 : ℝ
  /-- `C_L`. -/
  CL : ℝ
  cg_pos : 0 < cg
  cb_pos : 0 < cb
  c0_pos : 0 < c0
  CL_pos : 0 < CL

/-- `g = ⌈c_g log(2m/δ)⌉`, at least one group (Algorithm 5, line 1; Eq. (173)). -/
noncomputable def groups5 (P : Consts5) (m : ℕ) (δ : ℝ) : ℕ :=
  max 1 ⌈P.cg * Real.log (2 * m / δ)⌉₊

/-- `b = ⌈c_b ω²/α²⌉`, at least one sample per group (Algorithm 5, line 1; Eq. (174)). -/
noncomputable def perGroup5 (P : Consts5) (ω α : ℝ) : ℕ :=
  max 1 ⌈P.cb * ω ^ 2 / α ^ 2⌉₊

/-- `L_H = log((2/ζ)√(n/η))` (Algorithm 5, line 3). -/
noncomputable def lanczosLog5 (n : ℕ) (ζ η : ℝ) : ℝ := Real.log (2 / ζ * √((n : ℝ) / η))

/-- `q_H = min{n, ⌈C_L √(max{1, B_H, L_H}) L_H⌉}` (Algorithm 5, line 3). -/
noncomputable def lanczosDeg5 (P : Consts5) (n : ℕ) (BH LH : ℝ) : ℕ :=
  min n ⌈P.CL * √(max 1 (max BH LH)) * LH⌉₊

/-- The lower median of a list: the entry of index `⌊(len − 1)/2⌋` of the sorted list (`0` for the
empty list). For an odd number of groups it is the median. -/
noncomputable def lowerMedian (v : List ℝ) : ℝ :=
  (v.mergeSort fun a b => decide (a ≤ b)).getD ((v.length - 1) / 2) 0

variable {ι : Type} {n : ℕ}

/-- One product with `H = ∑_{(ℓ, c) ∈ Hl} c B_ℓ`, row by row through the reader of the `B_ℓ`
("multiplying a vector by `H` costs `O(nhs_B)`", p. 39). -/
noncomputable def applyHC (accB : CRowAccess ι n) (Hl : List (ι × ℝ)) (v : CVec n) :
    Prog (CVec n) := do
  let mut out : CVec n := 0
  for i in List.finRange n do
    tick 1
    let mut x : ℂ := 0
    for p in Hl do
      tick 1
      let row ← accB.read p.1 i
      let z ← crowDot row v
      x ← op 4 (x + (p.2 : ℂ) * z)
    out ← op 2 (Function.update out i x)
  pure out

/-- The list form `[(1, y₁), …, (h, y_h)]` of `H = ∑_{ℓ=1}^h y_ℓ B_ℓ`. -/
def hamList {h : ℕ} (y : Fin h → ℝ) : List (Fin h × ℝ) := List.ofFn fun ℓ => (ℓ, y ℓ)

/-- **Algorithm 5** (Simultaneous Gibbs Expectation Estimator, p. 36) as a charged program.

Brandão, Dalzell, Gilyén, Vasconcelos, *Solving Sparse SDPs in Sublinear Time*, arXiv:2609.40302,
Algorithm 5, p. 36; Eqs. (173)–(176), p. 35.

Input: the Hamiltonian `H = ∑_{(ℓ,c) ∈ Hl} c B_ℓ` with the bound `B_H`, its terms read through
`accB`; the observables `A₁, …, A_m` read through `accA`; the norm bound `ω`, accuracy `α`, failure
probability `δ`. Lines 1–3 set `g`, `b`, `N = gb`, `ζ = c₀α/ω`, `η = δ/(2N)`, `L_H`, `q_H`. For every
group `a` and sample `k`: draw `u ∼ Haar(ℂⁿ)` (line 6), run the complex Lánczos of `K = −H/2` at `u`
with degree `q_H` (line 7), set `W̃ = ‖ṽ‖₂²`, `ψ̃ = ṽ/‖ṽ‖₂` (line 8), sample `I` with
`P[I = i] = |ψ̃ᵢ|²` (line 9), and set `X̃ⱼ = W̃ Z_{Aⱼ}(ψ̃, I) = W̃ Re([Aⱼψ̃]_I/ψ̃_I)` for all `j`,
reading only row `I` of each `Aⱼ` (lines 10–11). Then the group ratios `∑ₖX̃ⱼ/∑ₖW̃` (line 13) and
their median over the groups (line 15).

**Formalization Note.** The median of an even number of values is the lower median; it is charged
`g² + 1` per observable (a sort of `g` values). Readings of the base mission: the cost model is the
published `Prog`; the program reads the matrices only through `accB`, `accA`. -/
noncomputable def alg5 [NeZero n] (P : Consts5) (accB : CRowAccess ι n) (Hl : List (ι × ℝ))
    (BH : ℝ) (m : ℕ) (accA : CRowAccess (Fin m) n) (ω α δ : ℝ) : Prog (Fin m → ℝ) := do
  -- lines 1–3
  let g ← op 12 (groups5 P m δ)
  let b ← op 12 (perGroup5 P ω α)
  let N ← op 1 (g * b)
  let ζ ← op 2 (P.c0 * α / ω)
  let η ← op 2 (δ / (2 * (N : ℝ)))
  let LH ← op 8 (lanczosLog5 n ζ η)
  let q ← op 12 (lanczosDeg5 P n BH LH)
  let mut ratios : List (Fin m → ℝ) := []
  -- lines 4–13
  for _a in List.range g do
    tick 1
    let mut numer : Fin m → ℝ := 0
    let mut denom : ℝ := 0
    for _s in List.range b do
      tick 1
      -- line 6
      let u ← drawHaar n
      -- line 7
      let v ← lanczosProgC
        (fun w => do
          let hw ← applyHC accB Hl w
          cscale (-(1 / 2)) hw) u q
      -- line 8
      let nv ← cnrm v
      let W ← op 1 (nv ^ 2)
      let inv ← op 1 (1 / nv)
      let ψ ← cscale inv v
      -- line 9
      let I ← csampleCoord ψ
      -- lines 10–11
      let mut X : Fin m → ℝ := 0
      for j in List.finRange m do
        tick 1
        let row ← accA.read j I
        let yv ← crowDot row ψ
        let z ← op 12 ((yv / ψ I).re)
        X ← op 2 (Function.update X j (W * z))
      numer ← op m (numer + X)
      denom ← op 1 (denom + W)
    -- line 13
    let rat ← op (2 * m) (fun j => numer j / denom)
    tick 1
    ratios := ratios ++ [rat]
  -- lines 14–15
  let mut μ : Fin m → ℝ := 0
  for j in List.finRange m do
    tick 1
    let med ← op (g * g + 1) (lowerMedian (ratios.map fun r => r j))
    μ ← op 1 (Function.update μ j med)
  pure μ

end SparseSDP.TwoSided.Supplement


