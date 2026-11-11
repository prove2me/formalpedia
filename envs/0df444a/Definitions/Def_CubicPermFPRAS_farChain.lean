-- Prove2me | Definitions.Def_CubicPermFPRAS_farChain
-- name    : CubicPermFPRAS_farChain
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T09:57:01.930249+00:00
-- url     : https://prove2.me/theorems/53cc02c6-df7a-446b-a680-4859316e68af
-- title:
--   The FAR chain $P_{\mathrm{FAR}}$, its stationary distribution $\pi_B$ and the occupation variance
-- statement:
--   For the rescaled matrix $B$, the **FAR chain** on $\Omega$ has stationary weights $n^2B(M)$ for $M\in\mathcal P$ and $W(u,v)B(M)$ for $M\in\mathcal N(u,v)$; $\pi_B$ is their normalization and $Z$ the normalizing constant. Its transition probabilities are:
--
--   1. from $M\in\mathcal P$, deleting a given edge has probability $1/(2n)$;
--   2. from $N\in\mathcal N(u,v)$, adding $(u,v)$ has probability $nB(u,v)/(2W(u,v))$;
--   3. for $(y,z)\in N$, the left slide $N\setminus\{(y,z)\}\cup\{(u,z)\}$ has probability $B(u,z)s_v/(2W(u,v))$ and the right slide $N\setminus\{(y,z)\}\cup\{(y,v)\}$ has probability $B(y,v)/(2W(u,v))$;
--
--   and the remaining probability is on the self-loop. For $v\in V_2$, $p_v=\pi_B(\mathcal N(r,v))$, and for the chain started at $X_0\sim\pi_B$ the variance of the occupation frequency $T^{-1}\sum_{t<T}\mathbf 1\{X_t\in\mathcal N(r,v)\}$ equals
--   $$T^{-2}\sum_{s,t<T}\sum_x\pi_B(x)\,g(x)\,(P_{\mathrm{FAR}}^{|s-t|}g)(x),\qquad g=\mathbf 1_{\mathcal N(r,v)}-p_v.$$
-- source:
--   Chen, Guo, Vigoda, Yang, An Õ(n³)-time FPRAS for the Permanent, arXiv:2609.20717 (held version, sha256 9e14f335…), §5.5, p.16 (PDF 18); Lemma 19, p.17 (PDF 19)

import Mathlib
import Definitions.Def_CubicPermFPRAS_matchWeight

set_option autoImplicit false

namespace CubicPermFPRAS

noncomputable section

variable {n : ℕ}

/-- The unnormalized FAR stationary weight (§5.5, p.16 (PDF 18); arXiv:2609.20717, held
version sha256 9e14f335…): `n²B(M)` for `M ∈ P` and `W(u,v)B(M)` for `M ∈ N(u,v)`. Outside `Ω`
the value is `0`. -/
def farWeight (B : Matrix (Fin n) (Fin n) ℝ) (σ : Asg n) : ℝ :=
  if IsPerfect σ then (n : ℝ) ^ 2 * matchWeight B σ
  else ∑ u, ∑ v, if IsNear u v σ then Wfar B u v * matchWeight B σ else 0

/-- The normalizing constant `Z = n²B(P) + ∑_{u,v} W(u,v)B(N(u,v))` of `π_B` (p.16). -/
def farZ (B : Matrix (Fin n) (Fin n) ℝ) : ℝ := ∑ σ : Omega n, farWeight B σ.1

/-- The FAR stationary distribution `π_B` on `Ω` (p.16). -/
def piB (B : Matrix (Fin n) (Fin n) ℝ) (σ : Omega n) : ℝ := farWeight B σ.1 / farZ B

/-- The left slide `N \ {(y,z)} ∪ {(u,z)}` (moves the left hole from `u` to `y`). -/
def slideLeft (σ : Asg n) (u y z : Fin n) : Asg n :=
  Function.update (Function.update σ y none) u (some z)

/-- The off-diagonal FAR transition mass from `σ` to `τ`, summed over the moves of p.16 that
turn `σ` into `τ`: from `M ∈ P`, deleting an edge `(u, σ_u)` has probability `1/(2n)`; from
`N ∈ N(u,v)`, adding `(u,v)` has probability `nB(u,v)/(2W(u,v))`, and for each `(y,z) ∈ N` the
left slide `N \ {(y,z)} ∪ {(u,z)}` has probability `B(u,z)s_v/(2W(u,v))` and the right slide
`N \ {(y,z)} ∪ {(y,v)}` has probability `B(y,v)/(2W(u,v))`. -/
def farOff (B : Matrix (Fin n) (Fin n) ℝ) (σ τ : Asg n) : ℝ :=
  (if IsPerfect σ then
      ∑ u, if τ = Function.update σ u none then 1 / (2 * (n : ℝ)) else 0
    else 0) +
  ∑ u, ∑ v, if IsNear u v σ then
      (if τ = Function.update σ u (some v) then (n : ℝ) * B u v / (2 * Wfar B u v) else 0) +
      ∑ y, (match σ y with
        | none => 0
        | some z =>
          (if τ = slideLeft σ u y z then B u z * colSum B v / (2 * Wfar B u v) else 0) +
          (if τ = Function.update σ y (some v) then B y v / (2 * Wfar B u v) else 0))
    else 0

/-- The FAR transition matrix `P_FAR` on `Ω` (§5.5, p.16): the off-diagonal entries are
`farOff`, and "the remaining probability is assigned to the self-loop". -/
def farP (B : Matrix (Fin n) (Fin n) ℝ) : Matrix (Omega n) (Omega n) ℝ :=
  fun σ τ => if σ = τ then 1 - ∑ τ' ∈ Finset.univ.filter (· ≠ σ), farOff B σ.1 τ'.1
    else farOff B σ.1 τ.1

/-- `p_v = π_B(N(r,v))` (Lemma 19, p.17). -/
def holeProb (B : Matrix (Fin n) (Fin n) ℝ) (r v : Fin n) : ℝ :=
  ∑ σ : Omega n, if IsNear r v σ.1 then piB B σ else 0

/-- The variance of the occupation frequency `T⁻¹ ∑_{t<T} 1{X_t ∈ N(r,v)}` for the FAR chain
started at `X₀ ∼ π_B` (Lemma 19, p.17 (PDF 19)).

**Formalization Note.** For the stationary chain the covariance of `g(X_s)` and `g(X_t)` is
`∑_x π_B(x) g(x) (P^{|s−t|} g)(x)` with `g = 1_{N(r,v)} − p_v`, so the variance is
`T⁻² ∑_{s,t<T} ∑_x π_B(x) g(x) (P_FAR^{|s−t|} g)(x)`. -/
def occVar (B : Matrix (Fin n) (Fin n) ℝ) (r v : Fin n) (T : ℕ) : ℝ :=
  let g : Omega n → ℝ := fun σ => (if IsNear r v σ.1 then 1 else 0) - holeProb B r v
  ((T : ℝ) ^ 2)⁻¹ * ∑ s ∈ Finset.range T, ∑ t ∈ Finset.range T,
    ∑ x : Omega n, piB B x * g x * ((farP B ^ (max s t - min s t)).mulVec g) x

end

end CubicPermFPRAS


