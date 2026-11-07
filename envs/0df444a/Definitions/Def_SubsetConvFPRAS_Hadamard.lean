-- Prove2me | Definitions.Def_SubsetConvFPRAS_Hadamard
-- name    : SubsetConvFPRAS_Hadamard
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:19:36.319061+00:00
-- url     : https://prove2.me/theorems/23a76e88-4ffe-48e0-a445-a91154324038
-- title:
--   The Hadamard product $\mu\odot\nu$ and its birth–death Laplacian $\mathcal L$
-- statement:
--   Let $\mu,\nu:2^U\to\mathbb R_{\ge0}$. The **Hadamard product** (Definition 1.7) is $\rho(S)=\mu(S)\nu(S)/Z$ with $Z=\sum_S\mu(S)\nu(S)$.
--
--   The **Laplacian** $\mathcal L=\sum_u\mathcal L_u$ of (3), written with nonnegative rates: at $S$, the move at coordinate $u$ goes to $S\triangle\{u\}$ with rate $\mu(S+u)/\mu(S)$ if $u\notin S$ and $\nu(S-u)/\nu(S)$ if $u\in S$, and
--   $$(\mathcal Lf)(S)=\sum_{u\in U}|r_u(S)|\,\bigl(f(S)-f(S\triangle\{u\})\bigr).$$
--   On a common support an infeasible move has rate $0$, so it is omitted as the page says.
--
--   The file also defines the discrete gradients of Definition 4.1, $(\nabla_uf)(S)=f(S+u)-f(S-u)$, $\nabla^+_uf=\nabla_uf\cdot\mathbf 1[u\notin S]$, $\nabla^-_uf=\nabla_uf\cdot\mathbf 1[u\in S]$, the mixed difference $\Delta_{uv}f=\nabla_u\nabla_vf$, the downward curvature matrix $D^{\mu,\kappa}_S=A^{\mu^*,\kappa}_{U\setminus S}$ (p.19), and connectivity of a support under single-element additions and deletions.
--
--   These are the objects of Theorem 1.14 and of its Bochner identity, Proposition 4.2.
--
--   **Formalization Note** The page's $r_u(S)$ is signed and acts on $f(S+u)-f(S-u)$; here the sign is absorbed, which gives the same operator. At $S$ outside the support the rates are $x/0=0$; every statement weights $S$ by $\rho(S)=0$ there.
-- source:
--   Chen, Liu, An FPRAS for Counting Common Bases of Two Matroids, arXiv:2610.06724 (version held, sha256 6c1d68c2…919476), Definition 1.7 and (3), p.5; Definition 4.1 and p.19

import Mathlib
import Definitions.Def_SubsetConvFPRAS_SetWeights

open scoped Classical

namespace SubsetConvFPRAS

/-!
# The Hadamard product and its local chain

X. Chen, K. Liu, *An FPRAS for Counting Common Bases of Two Matroids*, arXiv:2610.06724 (version held,
sha256 6c1d68c2…), Definition 1.7, (3), pp.5–6; Definition 4.1, Proposition 4.2, p.19.

**Formalization Note.**
* `coordRate μ ν S u` is `|r_u(S)|`: the rate of adding `u ∉ S` is `μ(S+u)/μ(S)`, of deleting `u ∈ S` is
  `ν(S-u)/ν(S)`. With `f(S+u) - f(S-u)` this gives `L_u` of p.5, with the sign absorbed.
* On a common support an infeasible move has numerator `0`, so it is omitted as the page says. At `S`
  outside the support the rate is `x / 0 = 0`. Every statement weights `S` by `ρ(S)`, which is `0` there.
-/

variable {U : Type} [Fintype U] [DecidableEq U]

/-- `ρ = μ ⊙ ν`, Definition 1.7, p.5: `ρ(S) = μ(S) ν(S) / Z` with `Z = ∑_S μ(S) ν(S)`. -/
noncomputable def hadamard (μ ν : Finset U → ℝ) : Finset U → ℝ :=
  fun S => μ S * ν S / ∑ T, μ T * ν T

/-- `S` with the membership of `u` flipped: the target of the move at coordinate `u`. -/
def flip (S : Finset U) (u : U) : Finset U :=
  if u ∈ S then S.erase u else insert u S

/-- The rate of the move at coordinate `u` from `S`, p.5: `μ(S+u)/μ(S)` if `u ∉ S`, `ν(S-u)/ν(S)` if
`u ∈ S`. -/
noncomputable def coordRate (μ ν : Finset U → ℝ) (S : Finset U) (u : U) : ℝ :=
  if u ∈ S then ν (S.erase u) / ν S else μ (insert u S) / μ S

/-- The Laplacian `𝓛 = ∑_u 𝓛_u` of (3), p.5, in the positive sign:
`(𝓛 f)(S) = ∑_u |r_u(S)| (f(S) - f(S △ u))`. -/
noncomputable def hadLapl (μ ν : Finset U → ℝ) (f : Finset U → ℝ) : Finset U → ℝ :=
  fun S => ∑ u, coordRate μ ν S u * (f S - f (flip S u))

/-- The transition rates of the chain with Laplacian `𝓛`, as a function of the target state. -/
noncomputable def hadRate (μ ν : Finset U → ℝ) : Finset U → Finset U → ℝ :=
  fun S S' => ∑ u, if S' = flip S u then coordRate μ ν S u else 0

/-- The discrete gradient of Definition 4.1, p.19: `(∇_u f)(S) = f(S+u) - f(S-u)`. -/
def grad (u : U) (f : Finset U → ℝ) : Finset U → ℝ :=
  fun S => f (insert u S) - f (S.erase u)

/-- `(∇⁺ f)(S)`, Definition 4.1: the vector `(∇_u f)(S) 1[u ∉ S]`. -/
noncomputable def gradPlus (f : Finset U → ℝ) (S : Finset U) : U → ℝ :=
  fun u => if u ∉ S then grad u f S else 0

/-- `(∇⁻ f)(S)`, Definition 4.1: the vector `(∇_u f)(S) 1[u ∈ S]`. -/
noncomputable def gradMinus (f : Finset U → ℝ) (S : Finset U) : U → ℝ :=
  fun u => if u ∈ S then grad u f S else 0

/-- `(Δ_{uv} f)(S) = (∇_u ∇_v f)(S)`, Proposition 4.2, p.19. -/
def mixedDiff (u v : U) (f : Finset U → ℝ) : Finset U → ℝ := grad u (grad v f)

/-- The downward curvature matrix `D_S^{μ,κ} = A_{U∖S}^{μ*,κ}`, p.19. -/
noncomputable def downCurvMatrix (μ : Finset U → ℝ) (κ : ℝ) (S : Finset U) : Matrix U U ℝ :=
  curvMatrix (dual μ) κ Sᶜ

/-- The support of `μ` is connected under single-element additions and deletions (Theorem 1.14). -/
def SupportConnected (μ : Finset U → ℝ) : Prop :=
  ∀ S T, 0 < μ S → 0 < μ T →
    Relation.ReflTransGen (fun X Y => 0 < μ X ∧ 0 < μ Y ∧ ∃ u, Y = flip X u) S T

end SubsetConvFPRAS


